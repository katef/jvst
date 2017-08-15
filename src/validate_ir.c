#include "validate_ir.h"

#include "xalloc.h"
#include "jvst_macros.h"

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <string.h>
#include <inttypes.h>

#include <fsm/bool.h>
#include <fsm/fsm.h>
#include <fsm/out.h>
#include <fsm/options.h>
#include <fsm/pred.h>
#include <fsm/walk.h>
#include <re/re.h>

#include "validate_sbuf.h"
#include "validate_constraints.h"
#include "sjp_testing.h"

#define STMT_UNIMPLEMENTED(stmt) do { \
	fprintf(stderr, "%s:%d (%s) IR statement %s not yet implemented\n",	\
		__FILE__, __LINE__, __func__,					\
		jvst_ir_stmt_type_name((stmt)->type));				\
	abort();								\
} while(0)

#define EXPR_UNIMPLEMENTED(expr) do {						\
	fprintf(stderr, "%s:%d (%s) IR statement %s not yet implemented\n",	\
		__FILE__, __LINE__, __func__,					\
		jvst_ir_expr_type_name((expr)->type));				\
	abort();								\
} while(0)

const char *
jvst_invalid_msg(enum jvst_invalid_code code)
{
	switch(code) {
	case JVST_INVALID_UNEXPECTED_TOKEN:
		return "unexpected token";

	case JVST_INVALID_NOT_INTEGER:
		return "number is not an integer";

	case JVST_INVALID_NUMBER:
		return "number not valid";

	case JVST_INVALID_TOO_FEW_PROPS:
		return "too few properties";

	case JVST_INVALID_TOO_MANY_PROPS:
		return "too many properties";

	case JVST_INVALID_MISSING_REQUIRED_PROPERTIES:
		return "missing required properties";

	case JVST_INVALID_SPLIT_CONDITION:
		return "invalid split condition";

	case JVST_INVALID_BAD_PROPERTY_NAME:
		return "bad property name";

	case JVST_INVALID_MATCH_CASE:
		return "invalid match case (internal error)";
	}

	return "Unknown error";
}

enum {
	JVST_IR_STMT_CHUNKSIZE = 1024,
	JVST_IR_EXPR_CHUNKSIZE = 1024,
	JVST_IR_NUMROOTS  = 32,
};

enum {
	STMT_MARKSIZE = JVST_IR_STMT_CHUNKSIZE / CHAR_BIT +
		(JVST_IR_STMT_CHUNKSIZE % CHAR_BIT) ? 1 : 0,
};

struct jvst_ir_stmt_pool {
	struct jvst_ir_stmt_pool *next;
	struct jvst_ir_stmt items[JVST_IR_STMT_CHUNKSIZE];
	unsigned char marks[STMT_MARKSIZE];
};

static struct {
	struct jvst_ir_stmt_pool *head;
	size_t top;
	struct jvst_ir_stmt *freelist;
	struct jvst_ir_stmt **roots[JVST_IR_NUMROOTS];
	int nroots;
} stmt_pool;

static struct jvst_ir_stmt *
ir_stmt_alloc(void)
{
	struct jvst_ir_stmt *item;
	struct jvst_ir_stmt_pool *pool;

	if (stmt_pool.head == NULL) {
		goto new_pool;
	}

	if (stmt_pool.top < ARRAYLEN(stmt_pool.head->items)) {
		item = &stmt_pool.head->items[stmt_pool.top++];
		memset(item, 0, sizeof *item);
		return item;
	}

	if (stmt_pool.freelist != NULL) {
		item = stmt_pool.freelist;
		stmt_pool.freelist = stmt_pool.freelist->next;
		memset(item, 0, sizeof *item);
		return item;
	}

	// add collector here
	
new_pool:
	pool = xmalloc(sizeof *pool);
	memset(pool->items, 0, sizeof pool->items);
	memset(pool->marks, 0, sizeof pool->marks);
	pool->next = stmt_pool.head;
	stmt_pool.head = pool;
	stmt_pool.top = 1;
	return &pool->items[0];
}

static struct jvst_ir_stmt *
ir_stmt_new(enum jvst_ir_stmt_type type)
{
	struct jvst_ir_stmt *stmt;
	stmt = ir_stmt_alloc();
	stmt->type = type;

	return stmt;
}

static struct jvst_ir_stmt *
ir_stmt_invalid(enum jvst_invalid_code code)
{
	struct jvst_ir_stmt *stmt;
	stmt = ir_stmt_new(JVST_IR_STMT_INVALID);
	stmt->u.invalid.code = code;
	stmt->u.invalid.msg = jvst_invalid_msg(code); // XXX - even worth bothering with?

	return stmt;
}

static inline struct jvst_ir_stmt *
ir_stmt_valid(void)
{
	return ir_stmt_new(JVST_IR_STMT_VALID);
}

static inline struct jvst_ir_stmt *
ir_stmt_if(struct jvst_ir_expr *cond, struct jvst_ir_stmt *br_true, struct jvst_ir_stmt *br_false)
{
	struct jvst_ir_stmt *br;
	br = ir_stmt_new(JVST_IR_STMT_IF);
	br->u.if_.cond = cond;
	br->u.if_.br_true = br_true;
	br->u.if_.br_false = br_false;
	return br;
}

static inline struct jvst_ir_stmt *
ir_stmt_frame(void)
{
	struct jvst_ir_stmt *frame;
	frame = ir_stmt_new(JVST_IR_STMT_FRAME);
	frame->u.frame.nloops    = 0;
	frame->u.frame.ncounters = 0;
	frame->u.frame.nbitvecs  = 0;

	frame->u.frame.blockind = 0;
	frame->u.frame.ntemps  = 0;

	frame->u.frame.blocks = NULL;
	frame->u.frame.stmts = NULL;
	return frame;
}

static inline struct jvst_ir_stmt *
ir_stmt_block(struct jvst_ir_stmt *frame, const char *prefix)
{
	struct jvst_ir_stmt *blk;
	assert(frame != NULL);
	assert(frame->type == JVST_IR_STMT_FRAME);

	blk = ir_stmt_new(JVST_IR_STMT_BLOCK);
	blk->u.block.block_next = NULL;
	blk->u.block.lindex     = frame->u.frame.blockind++;
	blk->u.block.prefix     = prefix;
	blk->u.block.stmts      = NULL;

	return blk;
}

static inline struct jvst_ir_stmt *
ir_stmt_loop(struct jvst_ir_stmt *frame, const char *loopname)
{
	struct jvst_ir_stmt *loop;

	assert(loopname != NULL);
	assert(frame != NULL);
	assert(frame->type == JVST_IR_STMT_FRAME);

	loop = ir_stmt_new(JVST_IR_STMT_LOOP);

	loop->u.loop.name = loopname;
	loop->u.loop.ind  = frame->u.frame.nloops++;
	loop->u.loop.stmts = NULL;

	return loop;
}

static inline struct jvst_ir_stmt *
ir_stmt_break(struct jvst_ir_stmt *loop)
{
	struct jvst_ir_stmt *brk;
	brk = ir_stmt_new(JVST_IR_STMT_BREAK);

	// XXX - uniquify name!
	brk->u.break_.name = loop->u.loop.name;
	brk->u.break_.ind  = loop->u.loop.ind;
	brk->u.break_.loop = loop;

	return brk;
}

static inline struct jvst_ir_stmt *
ir_stmt_counter(struct jvst_ir_stmt *frame, const char *label)
{
	struct jvst_ir_stmt *counter;

	assert(label != NULL);
	assert(frame != NULL);
	assert(frame->type == JVST_IR_STMT_FRAME);

	counter = ir_stmt_new(JVST_IR_STMT_COUNTER);

	counter->u.counter.label = label;
	counter->u.counter.ind   = frame->u.frame.ncounters++;
	counter->u.counter.frame = frame;

	counter->next = frame->u.frame.counters;
	frame->u.frame.counters = counter;

	return counter;
}

static inline size_t
bv_count(struct jvst_ir_stmt *b)
{
	size_t n = 0;
	for(; b != NULL; b = b->next) {
		n++;
	}

	return n;
}

static inline struct jvst_ir_stmt *
ir_stmt_bitvec(struct jvst_ir_stmt *frame, const char *label, size_t nbits)
{
	struct jvst_ir_stmt *bitvec;

	assert(label != NULL);
	assert(frame != NULL);
	assert(frame->type == JVST_IR_STMT_FRAME);

	bitvec = ir_stmt_new(JVST_IR_STMT_BITVECTOR);

	bitvec->u.bitvec.label = label;
	bitvec->u.bitvec.ind   = frame->u.frame.nbitvecs++;
	bitvec->u.bitvec.frame = frame;
	bitvec->u.bitvec.nbits = nbits;

	bitvec->next = frame->u.frame.bitvecs;
	frame->u.frame.bitvecs = bitvec;

	// condition is <= because bitvecs can be removed, and the
	// nbitvecs value can't be decremented b/c it's used to generate
	// a unique identifier
	assert(bv_count(frame->u.frame.bitvecs) <= frame->u.frame.nbitvecs);

	return bitvec;
}

static inline struct jvst_ir_stmt *
ir_stmt_matcher(struct jvst_ir_stmt *frame, const char *name, struct fsm *dfa)
{
	struct jvst_ir_stmt *matcher;

	assert(name != NULL);
	assert(frame != NULL);
	assert(frame->type == JVST_IR_STMT_FRAME);

	matcher = ir_stmt_new(JVST_IR_STMT_MATCHER);

	matcher->u.matcher.name = name;
	matcher->u.matcher.ind  = frame->u.frame.nmatchers++;
	matcher->u.matcher.dfa  = dfa;

	matcher->next = frame->u.frame.matchers;
	frame->u.frame.matchers = matcher;

	return matcher;
}

static inline struct jvst_ir_stmt *
ir_stmt_counter_op(enum jvst_ir_stmt_type op, struct jvst_ir_stmt *counter)
{
	struct jvst_ir_stmt *opstmt;

	assert(counter->type == JVST_IR_STMT_COUNTER);
	assert((op == JVST_IR_STMT_INCR) || (op == JVST_IR_STMT_DECR));
	assert(counter != NULL);

	opstmt = ir_stmt_new(op);

	opstmt->u.counter_op.label = counter->u.counter.label;
	opstmt->u.counter_op.ind   = counter->u.counter.ind;
	opstmt->u.counter_op.counter = counter;

	return opstmt;
}

static inline struct jvst_ir_stmt *
ir_stmt_move(struct jvst_ir_expr *dst, struct jvst_ir_expr *src)
{
	struct jvst_ir_stmt *mv;

	assert(dst != NULL);
	assert(dst->type == JVST_IR_EXPR_ITEMP || dst->type == JVST_IR_EXPR_FTEMP);
	assert(src != NULL);

	mv = ir_stmt_new(JVST_IR_STMT_MOVE);
	mv->u.move.dst = dst;
	mv->u.move.src = src;

	return mv;
}

static inline struct jvst_ir_stmt *
ir_stmt_branch(struct jvst_ir_stmt *dest)
{
	struct jvst_ir_stmt *jmp;

	assert(dest != NULL);
	assert(dest->type == JVST_IR_STMT_BLOCK);

	jmp = ir_stmt_new(JVST_IR_STMT_BRANCH);
	jmp->u.branch = dest;

	return jmp;
}


/** expression pool and allocator **/

union expr_pool_item {
	union expr_pool_item *next;
	struct jvst_ir_expr expr;
};

struct jvst_ir_expr_pool {
	struct jvst_ir_expr_pool *next;
	union expr_pool_item items[JVST_IR_EXPR_CHUNKSIZE];
	unsigned char marks[STMT_MARKSIZE];
};

static struct {
	struct jvst_ir_expr_pool *head;
	size_t top;
	union expr_pool_item *freelist;
} expr_pool;

static struct jvst_ir_expr *
ir_expr_alloc(void)
{
	struct jvst_ir_expr *item;
	struct jvst_ir_expr_pool *pool;

	if (expr_pool.head == NULL) {
		goto new_pool;
	}

	if (expr_pool.top < ARRAYLEN(expr_pool.head->items)) {
		item = &expr_pool.head->items[expr_pool.top++].expr;
		memset(item, 0, sizeof *item);
		return item;
	}

	if (expr_pool.freelist != NULL) {
		item = &expr_pool.freelist->expr;
		expr_pool.freelist = expr_pool.freelist->next;
		memset(item, 0, sizeof *item);
		return item;
	}

	// add collector here
	
new_pool:
	pool = xmalloc(sizeof *pool);
	memset(pool->items, 0, sizeof pool->items);
	memset(pool->marks, 0, sizeof pool->marks);
	pool->next = expr_pool.head;
	expr_pool.head = pool;
	expr_pool.top = 1;
	return &pool->items[0].expr;
}

static struct jvst_ir_expr *
ir_expr_new(enum jvst_ir_expr_type type)
{
	struct jvst_ir_expr *expr;
	expr = ir_expr_alloc();
	expr->type = type;

	return expr;
}

static struct jvst_ir_expr *
ir_expr_ftemp(struct jvst_ir_stmt *frame)
{
	struct jvst_ir_expr *tmp;
	assert(frame->type == JVST_IR_STMT_FRAME);
	tmp = ir_expr_new(JVST_IR_EXPR_FTEMP);
	tmp->u.temp.ind = frame->u.frame.ntemps++;
	return tmp;
}

static struct jvst_ir_expr *
ir_expr_itemp(struct jvst_ir_stmt *frame)
{
	struct jvst_ir_expr *tmp;
	assert(frame->type == JVST_IR_STMT_FRAME);
	tmp = ir_expr_new(JVST_IR_EXPR_ITEMP);
	tmp->u.temp.ind = frame->u.frame.ntemps++;
	return tmp;
}

// Returns a temporary whose type matches that of expr
static struct jvst_ir_expr *
ir_expr_tmp(struct jvst_ir_stmt *frame, struct jvst_ir_expr *expr)
{
	switch (expr->type) {
	case JVST_IR_EXPR_NUM:
	case JVST_IR_EXPR_FTEMP:
	case JVST_IR_EXPR_TOK_NUM:
		return ir_expr_ftemp(frame);

	case JVST_IR_EXPR_INT:
	case JVST_IR_EXPR_SIZE:
	case JVST_IR_EXPR_TOK_TYPE:
	case JVST_IR_EXPR_TOK_LEN:
	case JVST_IR_EXPR_ITEMP:
	case JVST_IR_EXPR_SLOT:
	case JVST_IR_EXPR_COUNT:
	case JVST_IR_EXPR_BCOUNT:
	case JVST_IR_EXPR_SPLIT:
	case JVST_IR_EXPR_MATCH:
		return ir_expr_itemp(frame);

	case JVST_IR_EXPR_SEQ:
		return ir_expr_tmp(frame, expr->u.seq.expr);

		/*
		fprintf(stderr, "%s:%d (%s) condition %s not yet implemented\n",
			__FILE__, __LINE__, __func__, jvst_ir_expr_type_name(expr->type));
		abort();
		*/

	case JVST_IR_EXPR_NONE:
		fprintf(stderr, "%s:%d (%s) cannot assign temporary to expression %s\n",
			__FILE__, __LINE__, __func__, jvst_ir_expr_type_name(expr->type));
		abort();

	case JVST_IR_EXPR_NE:
	case JVST_IR_EXPR_LT:
	case JVST_IR_EXPR_LE:
	case JVST_IR_EXPR_EQ:
	case JVST_IR_EXPR_GE:
	case JVST_IR_EXPR_GT:
	case JVST_IR_EXPR_BTEST:
	case JVST_IR_EXPR_BTESTALL:
	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTONE:
	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_ISTOK:
	case JVST_IR_EXPR_TOK_COMPLETE:
	case JVST_IR_EXPR_ISINT:
	case JVST_IR_EXPR_AND:
	case JVST_IR_EXPR_OR:
	case JVST_IR_EXPR_NOT:
		fprintf(stderr, "%s:%d (%s) cannot assign temporary to boolean expression %s\n",
			__FILE__, __LINE__, __func__, jvst_ir_expr_type_name(expr->type));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown expression type %d\n",
		__FILE__, __LINE__, __func__, expr->type);
	abort();
}

static struct jvst_ir_expr *
ir_expr_num(double num)
{
	struct jvst_ir_expr *expr;
	expr = ir_expr_new(JVST_IR_EXPR_NUM);
	expr->u.vnum = num;
	return expr;
}

static struct jvst_ir_expr *
ir_expr_size(size_t sz)
{
	struct jvst_ir_expr *expr;
	expr = ir_expr_new(JVST_IR_EXPR_SIZE);
	expr->u.vsize = sz;
	return expr;
}

static struct jvst_ir_expr *
ir_expr_int(int64_t n)
{
	struct jvst_ir_expr *expr;
	expr = ir_expr_new(JVST_IR_EXPR_INT);
	expr->u.vint = n;
	return expr;
}

static struct jvst_ir_expr *
ir_expr_bool(int v)
{
	struct jvst_ir_expr *expr;
	expr = ir_expr_new(JVST_IR_EXPR_BOOL);
	expr->u.vbool = !!v;
	return expr;
}

static struct jvst_ir_expr *
ir_expr_op(enum jvst_ir_expr_type op,
	struct jvst_ir_expr *left, struct jvst_ir_expr *right)
{
	struct jvst_ir_expr *expr;

	switch (op) {
	case JVST_IR_EXPR_AND:
	case JVST_IR_EXPR_OR:
		expr = ir_expr_new(op);
		expr->u.and_or.left = left;
		expr->u.and_or.right = right;
		break;

	case JVST_IR_EXPR_NE:
	case JVST_IR_EXPR_LT:
	case JVST_IR_EXPR_LE:
	case JVST_IR_EXPR_EQ:
	case JVST_IR_EXPR_GE:
	case JVST_IR_EXPR_GT:
		expr = ir_expr_new(op);
		expr->u.cmp.left = left;
		expr->u.cmp.right = right;
		break;

	case JVST_IR_EXPR_NONE:
	case JVST_IR_EXPR_NUM:
	case JVST_IR_EXPR_SIZE:
	case JVST_IR_EXPR_INT:
	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_TOK_TYPE:
	case JVST_IR_EXPR_TOK_NUM:
	case JVST_IR_EXPR_TOK_COMPLETE:
	case JVST_IR_EXPR_TOK_LEN:
	case JVST_IR_EXPR_COUNT:
	case JVST_IR_EXPR_BTEST:
	case JVST_IR_EXPR_BTESTALL:
	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTONE:
	case JVST_IR_EXPR_BCOUNT:
	case JVST_IR_EXPR_ISTOK:
	case JVST_IR_EXPR_ISINT:
	case JVST_IR_EXPR_NOT:
	case JVST_IR_EXPR_SPLIT:
	case JVST_IR_EXPR_SLOT:
	case JVST_IR_EXPR_ITEMP:
	case JVST_IR_EXPR_FTEMP:
	case JVST_IR_EXPR_SEQ:
	case JVST_IR_EXPR_MATCH:
		fprintf(stderr, "invalid OP type: %s\n", jvst_ir_expr_type_name(op));
		abort();
	}

	return expr;
}

static struct jvst_ir_expr *
ir_expr_istok(enum SJP_EVENT tt)
{
	struct jvst_ir_expr *expr;
	expr = ir_expr_new(JVST_IR_EXPR_ISTOK);
	expr->u.istok.tok_type = tt;

	return expr;
}

static struct jvst_ir_expr *
ir_expr_count(struct jvst_ir_stmt *counter)
{
	struct jvst_ir_expr *expr;

	assert(counter->type == JVST_IR_STMT_COUNTER);

	expr = ir_expr_new(JVST_IR_EXPR_COUNT);
	expr->u.count.counter = counter;
	expr->u.count.label = counter->u.counter.label;
	expr->u.count.ind   = counter->u.counter.ind;

	return expr;
}

static inline struct jvst_ir_expr *
ir_expr_seq(struct jvst_ir_stmt *stmt, struct jvst_ir_expr *expr)
{
	struct jvst_ir_expr *eseq;

	assert(stmt != NULL);
	assert(expr != NULL);

	eseq = ir_expr_new(JVST_IR_EXPR_SEQ);
	eseq->u.seq.stmt = stmt;
	eseq->u.seq.expr = expr;

	return eseq;
}



/** mcase pool and allocator **/

struct jvst_ir_mcase_pool {
	struct jvst_ir_mcase_pool *next;
	struct jvst_ir_mcase items[JVST_IR_EXPR_CHUNKSIZE];
	unsigned char marks[STMT_MARKSIZE];
};

static struct {
	struct jvst_ir_mcase_pool *head;
	size_t top;
	struct jvst_ir_mcase *freelist;
} mcase_pool;

static struct jvst_ir_mcase *
ir_mcase_alloc(void)
{
	struct jvst_ir_mcase *item;
	struct jvst_ir_mcase_pool *pool;

	if (mcase_pool.head == NULL) {
		goto new_pool;
	}

	if (mcase_pool.top < ARRAYLEN(mcase_pool.head->items)) {
		item = &mcase_pool.head->items[mcase_pool.top++];
		memset(item, 0, sizeof *item);
		return item;
	}

	if (mcase_pool.freelist != NULL) {
		item = mcase_pool.freelist;
		mcase_pool.freelist = mcase_pool.freelist->next;
		memset(item, 0, sizeof *item);
		return item;
	}

	// XXX - add collector here

new_pool:
	pool = xmalloc(sizeof *pool);
	memset(pool->items, 0, sizeof pool->items);
	memset(pool->marks, 0, sizeof pool->marks);
	pool->next = mcase_pool.head;
	mcase_pool.head = pool;
	mcase_pool.top = 1;
	return &pool->items[0];
}

static struct jvst_ir_mcase *
ir_mcase_new(size_t which, struct jvst_ir_stmt *stmt)
{
	struct jvst_ir_mcase *mcase;

	mcase = ir_mcase_alloc();
	mcase->which = which;
	mcase->stmt = stmt;

	return mcase;
}

const char *
jvst_ir_stmt_type_name(enum jvst_ir_stmt_type type)
{
	switch (type) {
	case JVST_IR_STMT_INVALID:
		return "INVALID";
	case JVST_IR_STMT_NOP:	
		return "NOP";
	case JVST_IR_STMT_VALID:		
		return "VALID";
	case JVST_IR_STMT_IF:
		return "IF";
	case JVST_IR_STMT_LOOP:
		return "LOOP";
	case JVST_IR_STMT_SEQ:
		return "SEQ";
	case JVST_IR_STMT_BREAK:
		return "BREAK";
	case JVST_IR_STMT_TOKEN:
		return "TOKEN";    	
	case JVST_IR_STMT_CONSUME:
		return "CONSUME";  	
	case JVST_IR_STMT_FRAME:
		return "FRAME";    	
	case JVST_IR_STMT_COUNTER:
		return "COUNTER";  	
	case JVST_IR_STMT_MATCHER:
		return "MATCHER";  	
	case JVST_IR_STMT_BITVECTOR:
		return "BITVECTOR";	
	case JVST_IR_STMT_SPLITLIST:
		return "SPLITLIST";	
	case JVST_IR_STMT_BSET:
		return "BSET";
	case JVST_IR_STMT_BCLEAR:
		return "BCLEAR";   	
	case JVST_IR_STMT_INCR:
		return "INCR";
	case JVST_IR_STMT_DECR:
		return "DECR";
	case JVST_IR_STMT_MATCH:
		return "MATCH";    	
	case JVST_IR_STMT_SPLITVEC:
		return "SPLITVEC";
	case JVST_IR_STMT_BLOCK:
		return "BLOCK";
	case JVST_IR_STMT_BRANCH:
		return "BRANCH";
	case JVST_IR_STMT_CBRANCH:
		return "CBRANCH";
	case JVST_IR_STMT_MOVE:
		return "MOVE";
	case JVST_IR_STMT_CALL:
		return "CALL";
	case JVST_IR_STMT_PROGRAM:
		return "PROGRAM";
	}

	fprintf(stderr, "%s:%d unknown IR statement type %d in %s\n",
			__FILE__, __LINE__, type, __func__);
	abort();
}

const char *
jvst_ir_expr_type_name(enum jvst_ir_expr_type type)
{

	switch (type) {
	case JVST_IR_EXPR_NONE:
		return "NONE";

	case JVST_IR_EXPR_TOK_TYPE:
		return "TOK_TYPE";

	case JVST_IR_EXPR_TOK_NUM:
		return "TOK_NUM";

	case JVST_IR_EXPR_TOK_COMPLETE:
		return "TOK_COMPLETE";

	case JVST_IR_EXPR_TOK_LEN:
		return "TOK_LEN";

	case JVST_IR_EXPR_COUNT:
		return "COUNT";

	case JVST_IR_EXPR_BTEST:
		return "BTEST";

	case JVST_IR_EXPR_BTESTALL:
		return "BTESTALL";

	case JVST_IR_EXPR_BTESTANY:
		return "BTESTANY";

	case JVST_IR_EXPR_BTESTONE:
		return "BTESTONE";

	case JVST_IR_EXPR_BCOUNT:
		return "BCOUNT";

	case JVST_IR_EXPR_ISTOK:
		return "ISTOK";

	case JVST_IR_EXPR_AND:
		return "AND";

	case JVST_IR_EXPR_OR:
		return "OR";

	case JVST_IR_EXPR_NOT:
		return "NOT";

	case JVST_IR_EXPR_NE:
		return "NE";

	case JVST_IR_EXPR_LT:
		return "LT";

	case JVST_IR_EXPR_LE:
		return "LE";

	case JVST_IR_EXPR_EQ:
		return "EQ";

	case JVST_IR_EXPR_GE:
		return "GE";

	case JVST_IR_EXPR_GT:
		return "GT";

	case JVST_IR_EXPR_ISINT:
		return "ISINT";

	case JVST_IR_EXPR_SPLIT:
		return "SPLIT";

	case JVST_IR_EXPR_NUM:
		return "NUM";

	case JVST_IR_EXPR_INT:
		return "INT";

	case JVST_IR_EXPR_SIZE:
		return "SIZE";

	case JVST_IR_EXPR_BOOL:
		return "BOOL";

	case JVST_IR_EXPR_SLOT:
		return "SLOT";

	case JVST_IR_EXPR_ITEMP:
		return "ITEMP";

	case JVST_IR_EXPR_FTEMP:
		return "FTEMP";

	case JVST_IR_EXPR_SEQ:
		return "ESEQ";

	case JVST_IR_EXPR_MATCH:
		return "EMATCH";

	}

	fprintf(stderr, "%s:%d (%s) unknown IR expression node type %d\n",
		__FILE__, __LINE__, __func__, type);
	abort();
}

void
jvst_ir_dump_inner(struct sbuf *buf, struct jvst_ir_stmt *ir, int indent);

static
void dump_stmt_list_inner(struct sbuf *buf, struct jvst_ir_stmt *stmts, int indent)
{
	for (;stmts != NULL; stmts = stmts->next) {
		jvst_ir_dump_inner(buf, stmts, indent+2);
		if (stmts->next != NULL) {
			sbuf_snprintf(buf, ",\n");
		} else {
			sbuf_snprintf(buf, "\n");
		}
	}
}

static
void dump_stmt_list(struct sbuf *buf, enum jvst_ir_stmt_type type, struct jvst_ir_stmt *stmts, int indent)
{
	if (stmts == NULL) {
		sbuf_snprintf(buf, "%s()", jvst_ir_stmt_type_name(type));
		return;
	}

	sbuf_snprintf(buf, "%s(\n", jvst_ir_stmt_type_name(type));
	dump_stmt_list_inner(buf, stmts, indent);
	sbuf_indent(buf, indent);
	sbuf_snprintf(buf, ")");
}

void
jvst_ir_dump_expr(struct sbuf *buf, const struct jvst_ir_expr *expr, int indent)
{
	sbuf_indent(buf, indent);
	switch (expr->type) {
	case JVST_IR_EXPR_TOK_TYPE:
	case JVST_IR_EXPR_TOK_NUM:
	case JVST_IR_EXPR_TOK_COMPLETE:
	case JVST_IR_EXPR_TOK_LEN:
		sbuf_snprintf(buf, "%s", jvst_ir_expr_type_name(expr->type));
		return;

	case JVST_IR_EXPR_ISTOK:
		sbuf_snprintf(buf, "ISTOK($%s)",
				evt2name(expr->u.istok.tok_type));
		return;

	case JVST_IR_EXPR_INT:
		sbuf_snprintf(buf, "%" PRId64, expr->u.vint);
		return;

	case JVST_IR_EXPR_NUM:
		sbuf_snprintf(buf, "%.1f", expr->u.vnum);
		return;

	case JVST_IR_EXPR_SIZE:
		sbuf_snprintf(buf, "%zu", expr->u.vsize);
		return;

	case JVST_IR_EXPR_BOOL:
		sbuf_snprintf(buf, "%s", expr->u.vbool ? "TRUE" : "FALSE" );
		return;

	case JVST_IR_EXPR_AND:
	case JVST_IR_EXPR_OR:
		{
			const char *op = (expr->type == JVST_IR_EXPR_AND) ? "AND" : "OR";
			sbuf_snprintf(buf, "%s(\n",op);
			jvst_ir_dump_expr(buf,expr->u.and_or.left,indent+2);
			sbuf_snprintf(buf, ",\n");
			jvst_ir_dump_expr(buf,expr->u.and_or.right,indent+2);
			sbuf_snprintf(buf, "\n");
			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		return;

	case JVST_IR_EXPR_NOT:
		{
			sbuf_snprintf(buf, "NOT(\n");
			jvst_ir_dump_expr(buf,expr->u.and_or.left,indent+2);
			sbuf_snprintf(buf, ",\n");
			jvst_ir_dump_expr(buf,expr->u.and_or.right,indent+2);
			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		return;

	case JVST_IR_EXPR_NE:
	case JVST_IR_EXPR_LT:
	case JVST_IR_EXPR_LE:
	case JVST_IR_EXPR_EQ:
	case JVST_IR_EXPR_GE:
	case JVST_IR_EXPR_GT:
		{
			const char *op = jvst_ir_expr_type_name(expr->type);
			sbuf_snprintf(buf, "%s(\n", op);
			jvst_ir_dump_expr(buf,expr->u.and_or.left,indent+2);
			sbuf_snprintf(buf, ",\n");
			jvst_ir_dump_expr(buf,expr->u.and_or.right,indent+2);
			sbuf_snprintf(buf, "\n");
			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		return;

	case JVST_IR_EXPR_ISINT:
		sbuf_snprintf(buf, "ISINT(\n");
		jvst_ir_dump_expr(buf,expr->u.isint.arg,indent+2);
		sbuf_snprintf(buf, "\n");
		sbuf_indent(buf, indent);
		sbuf_snprintf(buf, ")");
		return;

	case JVST_IR_EXPR_SPLIT:
		{
			struct jvst_ir_stmt *stmts;
			if (expr->u.split.split_list != NULL) {
				struct jvst_ir_stmt *split_list;
				split_list = expr->u.split.split_list;
				assert(split_list->type == JVST_IR_STMT_SPLITLIST);
				sbuf_snprintf(buf, "SPLIT(list=%zu)",
					split_list->u.split_list.ind);
				return;
			}

			stmts = expr->u.split.frames;
			if (stmts == NULL) {
				sbuf_snprintf(buf, "SPLIT()");
			} else {
				sbuf_snprintf(buf, "SPLIT(\n");
				for (;stmts != NULL; stmts = stmts->next) {
					jvst_ir_dump_inner(buf, stmts, indent+2);
					if (stmts->next != NULL) {
						sbuf_snprintf(buf, ",\n");
					} else {
						sbuf_snprintf(buf, "\n");
					}
				}
				sbuf_indent(buf, indent);
				sbuf_snprintf(buf, ")");
			}
		}
		return;

	case JVST_IR_EXPR_COUNT:
		sbuf_snprintf(buf, "COUNT(%zu, \"%s_%zu\")",
			expr->u.count.ind,
			expr->u.count.label,
			expr->u.count.ind);
		return;

	case JVST_IR_EXPR_BTEST:
	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTALL:
	case JVST_IR_EXPR_BTESTONE:
	case JVST_IR_EXPR_BCOUNT:
		{
			struct jvst_ir_stmt *bv;
			bv = expr->u.btest.bitvec;

			sbuf_snprintf(buf, "%s(%zu, \"%s_%zu\", b0=%zu, b1=%zu)",
				jvst_ir_expr_type_name(expr->type),
				bv->u.bitvec.ind,
				bv->u.bitvec.label,
				bv->u.bitvec.ind,
				expr->u.btest.b0,
				expr->u.btest.b1);
		}
		return;

	case JVST_IR_EXPR_SEQ:
		sbuf_snprintf(buf, "%s(\n", jvst_ir_expr_type_name(expr->type));
		sbuf_indent(buf, indent+2);
		jvst_ir_dump_inner(buf,expr->u.seq.stmt,indent+2);

		sbuf_snprintf(buf, ",\n", jvst_ir_expr_type_name(expr->type));
		sbuf_indent(buf, indent+2);
		jvst_ir_dump_expr(buf,expr->u.seq.expr,indent+2);
		sbuf_snprintf(buf, "\n", jvst_ir_expr_type_name(expr->type));
		sbuf_indent(buf, indent);
		sbuf_snprintf(buf, ")", jvst_ir_expr_type_name(expr->type));
		return;

	case JVST_IR_EXPR_ITEMP:
	case JVST_IR_EXPR_FTEMP:
		sbuf_snprintf(buf, "%s(%zu)",
			jvst_ir_expr_type_name(expr->type),
			expr->u.temp.ind);
		return;

	case JVST_IR_EXPR_MATCH:
		sbuf_snprintf(buf, "%s(%zu)",
			jvst_ir_expr_type_name(expr->type),
			expr->u.match.ind);
		return;

	case JVST_IR_EXPR_SLOT:
		sbuf_snprintf(buf, "%s(%zu)",
			jvst_ir_expr_type_name(expr->type),
			expr->u.slot.ind);
		return;

	case JVST_IR_EXPR_NONE:
		fprintf(stderr, "%s:%d (%s) IR expression %s not yet implemented\n",
				__FILE__, __LINE__, __func__, jvst_ir_expr_type_name(expr->type));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown IR expression type %d\n",
			__FILE__, __LINE__, __func__, expr->type);
	abort();
}

// definition in validate_constraints.c
void
jvst_cnode_matchset_dump(struct jvst_cnode_matchset *ms, struct sbuf *buf, int indent);

void
jvst_ir_dump_inner(struct sbuf *buf, struct jvst_ir_stmt *ir, int indent)
{
	assert(ir != NULL);

	sbuf_indent(buf, indent);
	switch (ir->type) {
	case JVST_IR_STMT_INVALID:	
		sbuf_snprintf(buf,
			"INVALID(%d, \"%s\")",
			ir->u.invalid.code,
			ir->u.invalid.msg);
		return;

	case JVST_IR_STMT_NOP:
	case JVST_IR_STMT_VALID:
	case JVST_IR_STMT_TOKEN:
	case JVST_IR_STMT_CONSUME:
		sbuf_snprintf(buf, "%s", jvst_ir_stmt_type_name(ir->type));
		return;

	case JVST_IR_STMT_SEQ:
		dump_stmt_list(buf, ir->type, ir->u.stmt_list, indent);
		return;

	case JVST_IR_STMT_PROGRAM:
		dump_stmt_list(buf, ir->type, ir->u.program.frames, indent);
		return;

	case JVST_IR_STMT_FRAME:		
		{
			assert(ir->u.frame.stmts != NULL);
			sbuf_snprintf(buf, "FRAME(%zu,\n", ir->u.frame.frame_ind);

			if (ir->u.frame.counters) {
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "COUNTERS[\n");
				dump_stmt_list_inner(buf, ir->u.frame.counters, indent+2);
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "],\n");
			}

			if (ir->u.frame.matchers) {
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "MATCHERS[\n");
				dump_stmt_list_inner(buf, ir->u.frame.matchers, indent+2);
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "],\n");
			}

			if (ir->u.frame.bitvecs) {
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "BITVECS[\n");
				dump_stmt_list_inner(buf, ir->u.frame.bitvecs, indent+2);
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "],\n");
			}

			if (ir->u.frame.splits) {
				struct jvst_ir_stmt *spl;
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "SPLITS[\n");
				dump_stmt_list_inner(buf, ir->u.frame.splits, indent+2);
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "],\n");
			}

			dump_stmt_list_inner(buf, ir->u.frame.stmts, indent);

			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		return;

	case JVST_IR_STMT_LOOP:		
		{
			assert(ir->u.loop.stmts != NULL);
			sbuf_snprintf(buf, "LOOP(\"%s\",\n",
				ir->u.loop.name);
			dump_stmt_list_inner(buf, ir->u.loop.stmts, indent);
			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		return;

	case JVST_IR_STMT_IF:
		sbuf_snprintf(buf, "IF(\n");
		jvst_ir_dump_expr(buf, ir->u.if_.cond, indent+2);
		sbuf_snprintf(buf, ",\n");
		jvst_ir_dump_inner(buf, ir->u.if_.br_true, indent+2);
		sbuf_snprintf(buf, ",\n");
		jvst_ir_dump_inner(buf, ir->u.if_.br_false, indent+2);
		sbuf_snprintf(buf, "\n");
		sbuf_indent(buf, indent);
		sbuf_snprintf(buf, ")");
		return;

	case JVST_IR_STMT_MATCHER:
		sbuf_snprintf(buf, "MATCHER(%zu, \"%s_%zu\")",
			ir->u.matcher.ind, ir->u.matcher.name, ir->u.matcher.ind);
		return;

	case JVST_IR_STMT_BREAK:
		sbuf_snprintf(buf, "BREAK(\"%s_%zu\")", ir->u.break_.name, ir->u.break_.ind);
		return;

	case JVST_IR_STMT_MATCH:
		{
			struct jvst_ir_mcase *cases;
			sbuf_snprintf(buf, "MATCH(%zu,\n", ir->u.match.ind);

			if (ir->u.match.default_case != NULL) {
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "DEFAULT_CASE(\n");

				jvst_ir_dump_inner(buf, ir->u.match.default_case, indent+4);
				sbuf_snprintf(buf, "\n");

				sbuf_indent(buf, indent+2);
				if (ir->u.match.cases != NULL) {
					sbuf_snprintf(buf, "),\n");
				} else {
					sbuf_snprintf(buf, ")\n");
				}
			}

			for (cases = ir->u.match.cases; cases != NULL; cases = cases->next) {
				struct jvst_cnode_matchset *mset;

				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "CASE(%zu,\n", cases->which);

				for (mset=cases->matchset; mset != NULL; mset = mset->next) {
					jvst_cnode_matchset_dump(mset, buf, indent+4);
					sbuf_snprintf(buf, ",\n");
				}

				jvst_ir_dump_inner(buf, cases->stmt, indent+4);
				sbuf_snprintf(buf, "\n");

				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, ")");
				if (cases->next) {
					sbuf_snprintf(buf, ",\n");
				} else {
					sbuf_snprintf(buf, "\n");
				}
			}
			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		return;

	case JVST_IR_STMT_COUNTER:		
		sbuf_snprintf(buf, "COUNTER(%zu, \"%s_%zu\")",
			ir->u.counter.ind, ir->u.counter.label, ir->u.counter.ind);
		return;

	case JVST_IR_STMT_INCR:		
	case JVST_IR_STMT_DECR:		
		sbuf_snprintf(buf, "%s(%zu, \"%s_%zu\")",
			jvst_ir_stmt_type_name(ir->type),
			ir->u.counter_op.ind,
			ir->u.counter_op.label,
			ir->u.counter_op.ind);
		return;

	case JVST_IR_STMT_BSET:
	case JVST_IR_STMT_BCLEAR:
		{
			struct jvst_ir_stmt *bv;
			bv = ir->u.bitop.bitvec;
			sbuf_snprintf(buf, "%s(%zu, \"%s_%zu\", bit=%zu)",
				jvst_ir_stmt_type_name(ir->type),
				bv->u.bitvec.ind,
				bv->u.bitvec.label,
				bv->u.bitvec.ind,
				ir->u.bitop.bit);
		}
		return;

	case JVST_IR_STMT_BITVECTOR:		
		sbuf_snprintf(buf, "%s(%zu, \"%s_%zu\", nbits=%zu)",
			jvst_ir_stmt_type_name(ir->type),
			ir->u.bitvec.ind,
			ir->u.bitvec.label,
			ir->u.bitvec.ind,
			ir->u.bitvec.nbits);
		return;

	case JVST_IR_STMT_SPLITLIST:		
		{
			struct jvst_ir_stmt *fr;
			sbuf_snprintf(buf, "%s(%zu, %zu",
				jvst_ir_stmt_type_name(ir->type),
				ir->u.split_list.ind,
				ir->u.split_list.nframes);
			for (fr=ir->u.split_list.frames; fr != NULL; fr = fr->u.frame.split_next) {
				sbuf_snprintf(buf, ", %zu", fr->u.frame.frame_ind);
			}
			sbuf_snprintf(buf, ")");
		}
		return;

	case JVST_IR_STMT_SPLITVEC:
		{
			struct jvst_ir_stmt *bv;

			bv = ir->u.splitvec.bitvec;
			assert(bv != NULL);

			if (ir->u.splitvec.split_list != NULL) {
				struct jvst_ir_stmt *split_list;

				split_list = ir->u.splitvec.split_list;
				assert(split_list->type == JVST_IR_STMT_SPLITLIST);

				sbuf_snprintf(buf, "SPLITVEC(%zu, \"%s_%zu\", list=%zu)",
					bv->u.bitvec.ind, bv->u.bitvec.label, bv->u.bitvec.ind,
					split_list->u.split_list.ind);
				return;
			}

			sbuf_snprintf(buf, "SPLITVEC(%zu, \"%s_%zu\",\n",
				bv->u.bitvec.ind,
				bv->u.bitvec.label,
				bv->u.bitvec.ind);

			assert(ir->u.splitvec.split_frames != NULL);
			dump_stmt_list_inner(buf, ir->u.splitvec.split_frames, indent);
			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		return;

	case JVST_IR_STMT_BLOCK:
		{
			struct jvst_ir_stmt *stmts;

			stmts = ir->u.block.stmts;
			if (stmts == NULL) {
				sbuf_snprintf(buf, "BLOCK(%s_%zu)",
					ir->u.block.prefix,
					ir->u.block.lindex);
			} else {
				sbuf_snprintf(buf, "BLOCK(%s_%zu, \n",
						ir->u.block.prefix,
						ir->u.block.lindex);
				dump_stmt_list_inner(buf, stmts, indent);
				sbuf_indent(buf, indent);
				sbuf_snprintf(buf, ")");
			}
		}
		return;

	case JVST_IR_STMT_BRANCH:
		{
			assert(ir->u.branch != NULL);
			assert(ir->u.branch->type == JVST_IR_STMT_BLOCK);
			sbuf_snprintf(buf, "BRANCH(%s_%zu)",
					ir->u.branch->u.block.prefix,
					ir->u.branch->u.block.lindex);

		}
		return;

	case JVST_IR_STMT_CBRANCH:
		{
			struct jvst_ir_stmt *br_true, *br_false;
			assert(ir->u.cbranch.cond     != NULL);
			assert(ir->u.cbranch.br_true  != NULL);
			assert(ir->u.cbranch.br_false != NULL);
			assert(ir->u.cbranch.br_true->type  == JVST_IR_STMT_BLOCK);
			assert(ir->u.cbranch.br_false->type == JVST_IR_STMT_BLOCK);

			br_true  = ir->u.cbranch.br_true;
			br_false = ir->u.cbranch.br_false;

			sbuf_snprintf(buf, "CBRANCH(\n");
			jvst_ir_dump_expr(buf, ir->u.cbranch.cond, indent+2);
			sbuf_snprintf(buf, ",\n");
			sbuf_indent(buf, indent+2);
			sbuf_snprintf(buf, "%s_%zu,\n",
				br_true->u.block.prefix,
				br_true->u.block.lindex);
			sbuf_indent(buf, indent+2);
			sbuf_snprintf(buf, "%s_%zu,\n",
				br_false->u.block.prefix,
				br_false->u.block.lindex);
			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		return;

	case JVST_IR_STMT_MOVE:
		{
			sbuf_snprintf(buf, "%s(\n", jvst_ir_stmt_type_name(ir->type));
			// sbuf_indent(buf, indent+2);
			jvst_ir_dump_expr(buf, ir->u.move.dst, indent+2);

			sbuf_snprintf(buf, ",\n");
			// sbuf_indent(buf, indent+2);
			jvst_ir_dump_expr(buf, ir->u.move.src, indent+2);
			sbuf_snprintf(buf, "\n");
			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		return;

	case JVST_IR_STMT_CALL:
		{
			assert(ir->u.call.frame != NULL);
			assert(ir->u.call.frame->type == JVST_IR_STMT_FRAME);
			assert(ir->u.call.frame->u.frame.frame_ind > 0);
			sbuf_snprintf(buf, "%s(%zu)",
				jvst_ir_stmt_type_name(ir->type),
				ir->u.call.frame->u.frame.frame_ind);
		}
		return;
	}

	fprintf(stderr, "%s:%d unknown IR statement type %d in %s\n",
		__FILE__, __LINE__, ir->type, __func__);
	abort();
}

int
jvst_ir_dump(struct jvst_ir_stmt *ir, char *buf, size_t nb)
{
	struct sbuf b = {
	    .buf = buf, .cap = nb, .len = 0, .np = 0,
	};

	jvst_ir_dump_inner(&b, ir, 0);
	sbuf_snprintf(&b, "\n");
	return (b.len < b.cap) ? 0 : -1;
}

static struct jvst_ir_stmt *
ir_translate_number(struct jvst_cnode *top)
{
	struct jvst_ir_stmt *stmt, **spp;
	// struct jvst_ir_expr *expr, **epp;

	stmt = NULL;
	spp = &stmt;

	switch (top->type) {
	case JVST_CNODE_VALID:
		*spp = ir_stmt_new(JVST_IR_STMT_VALID);
		break;

	case JVST_CNODE_INVALID:
		*spp = ir_stmt_invalid(JVST_INVALID_UNEXPECTED_TOKEN);
		break;

	case JVST_CNODE_NUM_INTEGER:
		{
			struct jvst_ir_stmt *br;
			struct jvst_ir_expr *cond;
			cond = ir_expr_new(JVST_IR_EXPR_ISINT);
			cond->u.isint.arg = ir_expr_new(JVST_IR_EXPR_TOK_NUM);

			br = ir_stmt_new(JVST_IR_STMT_IF);
			br->u.if_.cond = cond;
			br->u.if_.br_true = ir_stmt_new(JVST_IR_STMT_VALID);
			br->u.if_.br_false = ir_stmt_invalid(JVST_INVALID_NOT_INTEGER);

			*spp = br;
		}
		break;

	case JVST_CNODE_NUM_RANGE:
		{
			struct jvst_ir_stmt *br;
			struct jvst_ir_expr *cond, *lower, *upper;

			lower = NULL;
			upper = NULL;
			if (top->u.num_range.flags & JVST_CNODE_RANGE_EXCL_MIN) {
				lower = ir_expr_op(JVST_IR_EXPR_GT,
						ir_expr_new(JVST_IR_EXPR_TOK_NUM),
						ir_expr_num(top->u.num_range.min));
			} else if (top->u.num_range.flags & JVST_CNODE_RANGE_MIN) {
				lower = ir_expr_op(JVST_IR_EXPR_GE,
						ir_expr_new(JVST_IR_EXPR_TOK_NUM),
						ir_expr_num(top->u.num_range.min));
			}

			if (top->u.num_range.flags & JVST_CNODE_RANGE_EXCL_MAX) {
				upper = ir_expr_op(JVST_IR_EXPR_LT,
						ir_expr_new(JVST_IR_EXPR_TOK_NUM),
						ir_expr_num(top->u.num_range.min));
			} else if (top->u.num_range.flags & JVST_CNODE_RANGE_MAX) {
				upper = ir_expr_op(JVST_IR_EXPR_LE,
						ir_expr_new(JVST_IR_EXPR_TOK_NUM),
						ir_expr_num(top->u.num_range.min));
			}

			assert((lower != NULL) || (upper != NULL));

			if (lower && upper) {
				cond = ir_expr_op(JVST_IR_EXPR_AND, lower, upper);
			} else if (lower) {
				cond = lower;
			} else {
				cond = upper;
			}

			br = ir_stmt_if(cond,
				ir_stmt_new(JVST_IR_STMT_VALID),
				ir_stmt_invalid(JVST_INVALID_NUMBER));
			*spp = br;
		}
		break;

	case JVST_CNODE_AND:
	case JVST_CNODE_OR:
	case JVST_CNODE_NOT:
	case JVST_CNODE_XOR:
		fprintf(stderr, "[%s:%d] cnode %s not yet implemented\n",
				__FILE__, __LINE__, 
				jvst_cnode_type_name(top->type));
		abort();

	default:
		fprintf(stderr, "[%s:%d] invalid cnode type %s for $NUMBER\n",
				__FILE__, __LINE__, 
				jvst_cnode_type_name(top->type));
		abort();
	}

	return stmt;
}

static void
merge_constraints(const struct fsm_state **orig, size_t n,
	struct fsm *dfa, struct fsm_state *comb)
{
	struct jvst_ir_mcase *mcase;
	size_t i;

	fprintf(stderr, "... MERGING CONSTRAINTS ... \n");
	for (mcase = NULL, i = 0; i < n; i++) {
		struct jvst_ir_mcase *c;

		if (!fsm_isend(dfa, orig[i])) {
			continue;
		}

		c = fsm_getopaque(dfa, orig[i]);
		if (c == NULL) {
			fprintf(stderr, "case is NULL!\n");
			continue;
		}

		fprintf(stderr, "merging case %p %zu\n", (void *)c, c->which);
	}

	for (mcase = NULL, i = 0; i < n; i++) {
		struct jvst_ir_mcase *newcase;
		struct jvst_ir_stmt *seq;

		if (!fsm_isend(dfa, orig[i])) {
			continue;
		}

		newcase = fsm_getopaque(dfa, orig[i]);
		if (mcase == NULL) {
			assert(newcase->stmt != NULL);
			mcase = newcase;
			continue;
		}

		if (newcase->stmt == NULL || mcase == newcase) {
			continue;
		}

		// if necessary, convert mcase statement to SEQ
		if (mcase->stmt->type == JVST_IR_STMT_SEQ) {
			seq = mcase->stmt;
		} else {
			seq = ir_stmt_new(JVST_IR_STMT_SEQ);
			seq->u.stmt_list = mcase->stmt;
			mcase->stmt = seq;
		}

		// have to append FRAMEs, but we can prepend everything
		// else...
		if (newcase->stmt->type == JVST_IR_STMT_FRAME) {
			struct jvst_ir_stmt **spp;
			for(spp = &seq->u.stmt_list; *spp != NULL; spp = &(*spp)->next) {
				continue;
			}

			*spp = newcase->stmt;
		} else {
			struct jvst_ir_stmt *stmt;
			stmt = newcase->stmt;
			assert(stmt->next == NULL);
			stmt->next = seq->u.stmt_list;
			seq->u.stmt_list = stmt;
		}

		newcase->stmt = NULL;  // so we don't process it twice (is this possible?)

		// NB: we have to remove cases where stmt==NULL after
		// the NFAs are merged
	}

	if (mcase != NULL) {
		fsm_setopaque(dfa, comb, mcase);
	}
}

#define UNASSIGNED_MATCH  (~(size_t)0)

struct ir_object_builder {
	struct jvst_ir_stmt *frame;
	struct jvst_ir_stmt *oloop;
	struct jvst_ir_stmt *match;
	struct jvst_ir_stmt **pre_loop;
	struct jvst_ir_stmt **post_loop;
	struct jvst_ir_stmt **pre_match;
	struct jvst_ir_stmt **post_match;
	struct jvst_ir_mcase **mcpp;
	struct jvst_ir_stmt *reqmask;
	struct fsm *matcher;

	bool consumed;
};

static struct jvst_ir_stmt *
obj_mcase_translate_inner(struct jvst_cnode *ctree, struct ir_object_builder *builder)
{
	switch (ctree->type) {
	case JVST_CNODE_OBJ_REQBIT:
		{
			struct jvst_ir_stmt *setbit;

			assert(builder->reqmask != NULL);

			setbit = ir_stmt_new(JVST_IR_STMT_BSET);
			setbit->u.bitop.frame = builder->reqmask->u.bitvec.frame;
			setbit->u.bitop.bitvec = builder->reqmask;
			setbit->u.bitop.bit   = ctree->u.reqbit.bit;

			return setbit;
		}

	case JVST_CNODE_VALID:
		builder->consumed = true;
		return ir_stmt_new(JVST_IR_STMT_VALID);

	case JVST_CNODE_INVALID:
		// XXX - better error message!
		builder->consumed = true;
		return ir_stmt_invalid(JVST_INVALID_BAD_PROPERTY_NAME);

	default:
		builder->consumed = true; // XXX - is this correct?
		return jvst_ir_translate(ctree);
	}
}

static struct jvst_ir_stmt *
obj_mcase_translate(struct jvst_cnode *ctree, struct ir_object_builder *builder)
{
	struct jvst_ir_stmt *stmt, **spp;
	struct jvst_cnode *n;

	if (ctree->type != JVST_CNODE_AND) {
		return obj_mcase_translate_inner(ctree,builder);
	}

	stmt = ir_stmt_new(JVST_IR_STMT_SEQ);
	spp = &stmt->u.stmt_list;
	for(n=ctree->u.ctrl; n != NULL; n=n->next) {
		*spp = obj_mcase_translate_inner(n,builder);
		spp = &(*spp)->next;
	}

	return stmt;
}

static struct ir_object_builder *obj_mcase_builder_state;

static int
obj_mcase_builder(const struct fsm *dfa, const struct fsm_state *st)
{
	struct jvst_cnode *node;
	struct jvst_ir_mcase *mcase;
	struct jvst_ir_stmt *stmt;

	if (!fsm_isend(dfa, st)) {
		return 1;
	}

	node = fsm_getopaque((struct fsm *)dfa, st);
	assert(node->type == JVST_CNODE_MATCH_CASE);
	assert(node->u.mcase.tmp == NULL);

	// XXX - this is a hack
	// Basically, we need to keep track of whether the property
	// value is consumed or not, and add a CONSUME statement after
	// translation if it isn't.
	obj_mcase_builder_state->consumed = false;
	stmt = obj_mcase_translate(node->u.mcase.constraint, obj_mcase_builder_state);
	if (!obj_mcase_builder_state->consumed) {
		struct jvst_ir_stmt *seq, **spp;
		seq = ir_stmt_new(JVST_IR_STMT_SEQ);
		spp = &seq->u.stmt_list;
		*spp = stmt;
		spp = &(*spp)->next;
		*spp = ir_stmt_new(JVST_IR_STMT_CONSUME);
		
		stmt = seq;
	}
	mcase = ir_mcase_new(UNASSIGNED_MATCH, stmt);
	mcase->matchset = node->u.mcase.matchset;

	node->u.mcase.tmp = mcase;
	fsm_setopaque((struct fsm *)dfa, (struct fsm_state *)st, mcase);

	return 1;
}

struct jvst_ir_stmt *
obj_default_case(void)
{
	return ir_stmt_new(JVST_IR_STMT_CONSUME);
}

static void
ir_translate_obj_inner(struct jvst_cnode *top, struct ir_object_builder *builder)
{
	// descend the cnode tree and handle various events
	switch (top->type) {
	case JVST_CNODE_VALID:
	case JVST_CNODE_INVALID:
		// VALID/INVALID should have been picked up in the
		// various cases...
		fprintf(stderr, "top node should not be VALID or INVALID\n");
		abort();
		return;

	case JVST_CNODE_OBJ_REQUIRED:
	case JVST_CNODE_OBJ_PROP_SET:
		fprintf(stderr, "canonified cnode trees should not have %s nodes\n",
			jvst_cnode_type_name(top->type));
		abort();
		return;

	case JVST_CNODE_MATCH_SWITCH:
		{
			size_t which;
			struct jvst_cnode *caselist;
			struct jvst_ir_stmt *frame, **spp, *matcher_stmt;

			// duplicate DFA.
			builder->matcher = fsm_clone(top->u.mswitch.dfa);

			// replace MATCH_CASE opaque entries in copy with jvst_ir_mcase nodes
			obj_mcase_builder_state = builder;
			fsm_all(builder->matcher, obj_mcase_builder);
			obj_mcase_builder_state = NULL;

			// assemble jvst_ir_mcase nodes into list for an MATCH_SWITCH node and number the cases
			which = 0;
			for (caselist = top->u.mswitch.cases; caselist != NULL; caselist = caselist->next) {
				struct jvst_ir_mcase *mc;
				assert(caselist->type == JVST_CNODE_MATCH_CASE);
				assert(caselist->u.mcase.tmp != NULL);

				mc = caselist->u.mcase.tmp;
				caselist->u.mcase.tmp = NULL;
				assert(mc->next == NULL);

				mc->which = ++which;
				*builder->mcpp = mc;
				builder->mcpp = &mc->next;
			}

			// 4. translate the default case
			//
			// Currently we do nothing, because the
			// default_case is always VALID.
			//
			// FIXME: is default_case always VALID?  in that
			// case we can eliminate it.  Otherwise, we need
			// to do something more sophisticated here.

			// 5. Add matcher statement to frame and fixup refs
			matcher_stmt = ir_stmt_matcher(builder->frame, "dfa", builder->matcher);
			builder->match->u.match.dfa = builder->matcher;
			builder->match->u.match.name = matcher_stmt->u.matcher.name;
			builder->match->u.match.ind  = matcher_stmt->u.matcher.ind;
		}
		return;

	case JVST_CNODE_COUNT_RANGE:
		{
			struct jvst_ir_stmt *counter, *check, **checkpp;
			struct jvst_ir_expr *check_expr;
			// 1. allocate a counter to keep track of the
			//    number of properties

			counter = ir_stmt_counter(builder->frame, "num_props");

			// 2. post-match, increment the counter
			assert(builder->post_match != NULL);
			assert(*builder->post_match == NULL);
			*builder->post_match = ir_stmt_counter_op(JVST_IR_STMT_INCR, counter);
			builder->post_match = &(*builder->post_match)->next;

			// 3. post-loop check that the counter is within
			// range
			assert(builder->post_loop != NULL);
			assert(*builder->post_loop == NULL);

			checkpp = builder->post_loop;
			if (top->u.counts.min > 0) {
				*checkpp = ir_stmt_if(
					ir_expr_op(JVST_IR_EXPR_GE,
						ir_expr_count(counter),
						ir_expr_size(top->u.counts.min)),
					NULL,
					ir_stmt_invalid(JVST_INVALID_TOO_FEW_PROPS));
				checkpp = &(*checkpp)->u.if_.br_true;
			}

			if (top->u.counts.max > 0) {
				*checkpp = ir_stmt_if(
					ir_expr_op(JVST_IR_EXPR_LE,
						ir_expr_count(counter),
						ir_expr_size(top->u.counts.max)),
					NULL,
					ir_stmt_invalid(JVST_INVALID_TOO_MANY_PROPS));
				checkpp = &(*checkpp)->u.if_.br_true;
			}

			builder->post_loop = checkpp;
		}
		return;

	case JVST_CNODE_OBJ_REQMASK:
		{
			struct jvst_ir_stmt *bitvec, **checkpp;
			struct jvst_ir_expr *allbits;

			// cnode simplification should ensure that we
			// have only one reqmask per object!
			assert(builder->reqmask == NULL);

			// 1. allocate bitvector
			bitvec = ir_stmt_bitvec(builder->frame, "reqmask", top->u.reqmask.nbits);
			builder->reqmask = bitvec;

			// 2. post-loop check that all bits of bitvector
			//    are set

			allbits = ir_expr_new(JVST_IR_EXPR_BTESTALL);
			allbits->u.btest.frame = bitvec->u.bitvec.frame;
			allbits->u.btest.bitvec = bitvec;
			allbits->u.btest.b0 = 0;
			allbits->u.btest.b1 = bitvec->u.bitvec.nbits-1;

			checkpp = builder->post_loop;
			*checkpp = ir_stmt_if(allbits,
					NULL,
					ir_stmt_invalid(JVST_INVALID_MISSING_REQUIRED_PROPERTIES));
			checkpp = &(*checkpp)->u.if_.br_true;

			builder->post_loop = checkpp;
		}
		return;

	case JVST_CNODE_AND:
		{
			struct jvst_cnode *n;
			for (n = top->u.ctrl; n != NULL; n = n->next) {
				ir_translate_obj_inner(n, builder);
			}
		}
		return;

	case JVST_CNODE_OR:
	case JVST_CNODE_NOT:
	case JVST_CNODE_XOR:
		fprintf(stderr, "[%s:%d] cnode %s not yet implemented\n",
				__FILE__, __LINE__, 
				jvst_cnode_type_name(top->type));
		abort();
		return;

	case JVST_CNODE_SWITCH:
	case JVST_CNODE_OBJ_PROP_MATCH:
	case JVST_CNODE_MATCH_CASE:
	case JVST_CNODE_OBJ_REQBIT:
		fprintf(stderr, "[%s:%d] invalid cnode type %s while handling properties of an OBJECT\n",
				__FILE__, __LINE__, 
				jvst_cnode_type_name(top->type));
		abort();

	case JVST_CNODE_ARR_ITEM:
	case JVST_CNODE_ARR_ADDITIONAL:
	case JVST_CNODE_ARR_UNIQUE:
	case JVST_CNODE_STR_MATCH:
	case JVST_CNODE_NUM_RANGE:
	case JVST_CNODE_NUM_INTEGER:
		fprintf(stderr, "[%s:%d] invalid cnode type %s for OBJECT\n",
				__FILE__, __LINE__, 
				jvst_cnode_type_name(top->type));
		abort();
	}

	fprintf(stderr, "[%s:%d] unknown cnode type %d\n",
			__FILE__, __LINE__, top->type);
	abort();
}

static struct jvst_ir_stmt *
ir_translate_object(struct jvst_cnode *top, struct jvst_ir_stmt *frame);

static struct jvst_ir_stmt *
ir_translate_object_inner(struct jvst_cnode *top, struct jvst_ir_stmt *frame);

// Checks if an AND node requires splitting the validator.  An AND node
// will not require splitting the validator if none of its children are
// control cnodes (OR, XOR, NOT).
static bool
cnode_and_requires_split(struct jvst_cnode *and_node)
{
	struct jvst_cnode *n;

	assert(and_node->type == JVST_CNODE_AND);

	for(n=and_node->u.ctrl; n != NULL; n = n->next) {
		switch (n->type) {
		case JVST_CNODE_OR:
		case JVST_CNODE_XOR:
		case JVST_CNODE_NOT:
			return true;

		case JVST_CNODE_AND:
			fprintf(stderr,
				"canonical cnode tree should not "
				"have ANDs as children of ANDs\n");
			abort();

		case JVST_CNODE_INVALID:
		case JVST_CNODE_VALID:
		case JVST_CNODE_SWITCH:
		case JVST_CNODE_COUNT_RANGE:
		case JVST_CNODE_STR_MATCH:
		case JVST_CNODE_NUM_RANGE:
		case JVST_CNODE_NUM_INTEGER:
		case JVST_CNODE_OBJ_PROP_SET:
		case JVST_CNODE_OBJ_PROP_MATCH:
		case JVST_CNODE_OBJ_REQUIRED:
		case JVST_CNODE_ARR_ITEM:
		case JVST_CNODE_ARR_ADDITIONAL:
		case JVST_CNODE_ARR_UNIQUE:
		case JVST_CNODE_OBJ_REQMASK:
		case JVST_CNODE_OBJ_REQBIT:
		case JVST_CNODE_MATCH_SWITCH:
		case JVST_CNODE_MATCH_CASE:
			/* nop */
			continue;
		}

		// fail if the node type isn't handled in the switch
		fprintf(stderr, "unknown cnode type %d\n", and_node->type);
		abort();
	}

	return false;
}

// Counts the number of split frames required and the number of control
// nodes that split the validator.  This is to allow us to optimize
// evaluation when there's 0-1 control nodes that split the validator.
static size_t
cnode_count_splits(struct jvst_cnode *top, size_t *np)
{
	struct jvst_cnode *node;
	size_t nsplit = 0, ncontrol = 0;

	// descend from top node, count number of splits and number of
	// control nodes.
	//
	// note that we use 'goto finish' instead of break.  This is
	// to let uncaught cases fall through the loop instead of using
	// a default case.  This allows the compiler to yell at us if we
	// add another cnode type and don't add a case here.
	switch (top->type) {
	case JVST_CNODE_AND:
		if (!cnode_and_requires_split(top)) {
			goto finish;
		}

		/* fallthrough */

	case JVST_CNODE_OR:
	case JVST_CNODE_XOR:
		ncontrol++;

		// all nodes require a split
		for (node=top->u.ctrl; node != NULL; node = node->next) {
			size_t nctrl;
			nsplit++;
			nctrl = 0;
			nsplit += cnode_count_splits(node, &nctrl);
			ncontrol += nctrl;
		}
		goto finish;

	case JVST_CNODE_NOT:
		// child requires a split
		ncontrol++;
		nsplit++;
		goto finish;

	case JVST_CNODE_INVALID:
	case JVST_CNODE_VALID:
	case JVST_CNODE_SWITCH:
	case JVST_CNODE_COUNT_RANGE:
	case JVST_CNODE_STR_MATCH:
	case JVST_CNODE_NUM_RANGE:
	case JVST_CNODE_NUM_INTEGER:
	case JVST_CNODE_OBJ_PROP_SET:
	case JVST_CNODE_OBJ_PROP_MATCH:
	case JVST_CNODE_OBJ_REQUIRED:
	case JVST_CNODE_ARR_ITEM:
	case JVST_CNODE_ARR_ADDITIONAL:
	case JVST_CNODE_ARR_UNIQUE:
	case JVST_CNODE_OBJ_REQMASK:
	case JVST_CNODE_OBJ_REQBIT:
	case JVST_CNODE_MATCH_SWITCH:
	case JVST_CNODE_MATCH_CASE:
		/* nop */
		goto finish;
	}

	// fail if the node type isn't handled in the switch
	fprintf(stderr, "unknown cnode type %d\n", top->type);
	abort();

finish:
	*np = ncontrol;
	return nsplit;
}

struct split_gather_data {
	struct jvst_ir_stmt **fpp;
	struct jvst_ir_stmt *bvec;
	size_t boff;
	size_t nframe; // number of frames
	size_t nctrl;  // number of control nodes
};

// Separates children of a control node into two separate linked lists:
// one control and one non-control. Returns opp when finished so the
// linked lists can be easily merged
struct jvst_cnode **
separate_control_nodes(struct jvst_cnode *top, struct jvst_cnode **cpp, struct jvst_cnode **opp)
{
	struct jvst_cnode *node, *next;
	for (node=top->u.ctrl; node != NULL; node = next) {
		next = node->next;

		switch (node->type) {
		case JVST_CNODE_AND:
		case JVST_CNODE_OR:
		case JVST_CNODE_XOR:
		case JVST_CNODE_NOT:
			if (node->type == top->type) {
				fprintf(stderr, "%s:%d canonical cnode tree should not "
						"have %s nodes as children of %s nodes\n",
					__FILE__, __LINE__,
					jvst_cnode_type_name(node->type),
					jvst_cnode_type_name(top->type));
				abort();
			}

			*cpp = node;
			cpp = &node->next;
			*cpp = NULL;
			continue;

		case JVST_CNODE_INVALID:
		case JVST_CNODE_VALID:
		case JVST_CNODE_SWITCH:
		case JVST_CNODE_COUNT_RANGE:
		case JVST_CNODE_STR_MATCH:
		case JVST_CNODE_NUM_RANGE:
		case JVST_CNODE_NUM_INTEGER:
		case JVST_CNODE_OBJ_PROP_SET:
		case JVST_CNODE_OBJ_PROP_MATCH:
		case JVST_CNODE_OBJ_REQUIRED:
		case JVST_CNODE_ARR_ITEM:
		case JVST_CNODE_ARR_ADDITIONAL:
		case JVST_CNODE_ARR_UNIQUE:
		case JVST_CNODE_OBJ_REQMASK:
		case JVST_CNODE_OBJ_REQBIT:
		case JVST_CNODE_MATCH_SWITCH:
		case JVST_CNODE_MATCH_CASE:
			*opp = node;
			opp = &node->next;
			*opp = NULL;
			continue;
		}

		fprintf(stderr, "[%s:%d] unknown cnode type %d\n",
				__FILE__, __LINE__, top->type);
		abort();
	}

	return opp;
}

static struct jvst_ir_expr *
split_gather(struct jvst_cnode *top, struct split_gather_data *data)
{
	struct jvst_cnode *node;
	size_t nf;

	// Gathers split information:
	//
	// 1. All frames required by split (and convenient count)
	// 2. Expression to evaluate split (in the general case)
	// 3. Number of splits

	switch (top->type) {
	case JVST_CNODE_AND:
		{
			struct jvst_cnode *next, *ctrl, *other, **opp;
			struct jvst_ir_expr *expr, **epp;
			size_t b0;

			// AND subnodes that are not control nodes (OR, XOR,
			// NOT) can be evaluated simultaneously in the same
			// validator and do not require a split.
			//
			// 1. Separate nodes into control and non-control nodes.
			ctrl = NULL;
			other = NULL;
			opp = separate_control_nodes(top, &ctrl, &other);

			expr = NULL;
			epp = &expr;

			top->u.ctrl = other;

			// 2. Create a single frame for all non-control nodes.
			//    - Create a temporary AND junction for the IR frame
			//    - Create the IR frame
			if (other != NULL) {
				struct jvst_ir_stmt *fr;
				struct jvst_ir_expr *e_and, *e_btest;

				b0 = data->boff++;
				data->nframe++;

				fr = ir_stmt_frame();
				fr->u.frame.stmts = ir_translate_object_inner(top, fr);
				*data->fpp = fr;
				data->fpp = &fr->next;

				e_btest = ir_expr_new(JVST_IR_EXPR_BTEST);
				e_btest->u.btest.frame = data->bvec->u.bitvec.frame;
				e_btest->u.btest.bitvec = data->bvec;
				e_btest->u.btest.b0 = b0;
				e_btest->u.btest.b1 = b0;

				if (ctrl != NULL) {
					e_and = ir_expr_new(JVST_IR_EXPR_AND);
					e_and->u.and_or.left = e_btest;
					*epp = e_and;
					epp = &e_and->u.and_or.right;
				} else {
					*epp = e_btest;
				}
			}

			// don't lose children of AND node
			*opp = ctrl;

			if (ctrl != NULL) {
				data->nctrl++;
			}

			// 3. Create separate frames for all control nodes.
			for (node = ctrl; node != NULL; node = node->next) {
				struct jvst_ir_expr *e_ctrl;
				e_ctrl = split_gather(node, data);
				if (node->next == NULL) {
					*epp = e_ctrl;
				} else {
					struct jvst_ir_expr *e_and;
					e_and = ir_expr_new(JVST_IR_EXPR_AND);
					e_and->u.and_or.left = e_ctrl;
					*epp = e_and;
					epp = &e_and->u.and_or.right;
				}
			}
			assert(expr != NULL);
			return expr;
		}

	case JVST_CNODE_OR:
		{
			struct jvst_cnode *next, *ctrl, *other, **opp;
			struct jvst_ir_expr *expr, **epp;

			// OR and XOR subnodes must all be evaluated
			// separately, but we can use BTESTANY to
			// evaluate children that are not control nodes.

			data->nctrl++;

			// 1. Separate nodes into control and non-control nodes.
			ctrl = NULL;
			other = NULL;
			opp = separate_control_nodes(top, &ctrl, &other);

			expr = NULL;
			epp = &expr;

			top->u.ctrl = other;

			if (other != NULL) {
				struct jvst_ir_expr *e_btest;
				size_t b0;

				b0 = data->boff;

				// 2. Create frames for all non-control nodes.
				for (node = other; node != NULL; node = node->next) {
					struct jvst_ir_stmt *fr;

					data->boff++;
					data->nframe++;

					fr = ir_stmt_frame();
					fr->u.frame.stmts = ir_translate_object_inner(node, fr);
					*data->fpp = fr;
					data->fpp = &fr->next;

				}

				e_btest = ir_expr_new(JVST_IR_EXPR_BTESTANY);
				e_btest->u.btest.frame = data->bvec->u.bitvec.frame;
				e_btest->u.btest.bitvec = data->bvec;
				e_btest->u.btest.b0 = b0;
				e_btest->u.btest.b1 = data->boff-1;

				if (ctrl != NULL) {
					struct jvst_ir_expr *e_or;
					e_or = ir_expr_new(JVST_IR_EXPR_OR);
					e_or->u.and_or.left = e_btest;
					*epp = e_or;
					epp = &e_or->u.and_or.right;
				} else {
					*epp = e_btest;
				}
			}

			// don't lose children of OR/XOR node
			*opp = ctrl;

			// 3. Create separate frames for all control nodes.
			for (node = ctrl; node != NULL; node = node->next) {
				struct jvst_ir_expr *e_ctrl;
				e_ctrl = split_gather(node, data);
				if (node->next == NULL) {
					*epp = e_ctrl;
				} else {
					struct jvst_ir_expr *e_or;
					e_or = ir_expr_new(JVST_IR_EXPR_OR);
					e_or->u.and_or.left = e_ctrl;
					*epp = e_or;
					epp = &e_or->u.and_or.right;
				}
			}

			assert(expr != NULL);
			return expr;
		}

	case JVST_CNODE_XOR:
	case JVST_CNODE_NOT:
		// fail if the node type isn't handled in the switch
		fprintf(stderr, "%s:%d cnode %s not yet implemented in %s\n",
			__FILE__, __LINE__, jvst_cnode_type_name(top->type), __func__);
		abort();

	case JVST_CNODE_INVALID:
	case JVST_CNODE_VALID:
	case JVST_CNODE_SWITCH:
	case JVST_CNODE_COUNT_RANGE:
	case JVST_CNODE_STR_MATCH:
	case JVST_CNODE_NUM_RANGE:
	case JVST_CNODE_NUM_INTEGER:
	case JVST_CNODE_OBJ_PROP_SET:
	case JVST_CNODE_OBJ_PROP_MATCH:
	case JVST_CNODE_OBJ_REQUIRED:
	case JVST_CNODE_ARR_ITEM:
	case JVST_CNODE_ARR_ADDITIONAL:
	case JVST_CNODE_ARR_UNIQUE:
	case JVST_CNODE_OBJ_REQMASK:
	case JVST_CNODE_OBJ_REQBIT:
	case JVST_CNODE_MATCH_SWITCH:
	case JVST_CNODE_MATCH_CASE:
		// fail if the node type isn't handled in the switch
		fprintf(stderr, "%s:%d cnode %s not supported in %s\n",
			__FILE__, __LINE__, jvst_cnode_type_name(top->type), __func__);
		abort();
	}

	// fail if the node type isn't handled in the switch
	fprintf(stderr, "unknown cnode type %d\n", top->type);
	abort();
}

static void
gather_remove_bvec(struct jvst_ir_stmt *frame, struct split_gather_data *gather)
{
	struct jvst_ir_stmt **bvpp;

	// remove bitvec, but keep counter the same so any
	// bitvectors added will still have unique names...
	for(bvpp = &frame->u.frame.bitvecs; *bvpp != NULL; bvpp = &(*bvpp)->next) {
		if (*bvpp == gather->bvec) {
			*bvpp = (*bvpp)->next;
			return;
		}
	}
}

static struct jvst_ir_stmt *
ir_translate_object_split(struct jvst_cnode *top, struct jvst_ir_stmt *frame)
{
	struct jvst_cnode *node;
	struct jvst_ir_stmt *frames, *cond, **spp;
	struct jvst_ir_expr *split;

	struct split_gather_data gather = { NULL };

	frames = NULL;
	gather.fpp = &frames;
	gather.bvec = ir_stmt_bitvec(frame, "splitvec", 0);

	split = split_gather(top, &gather);
	assert(frames != NULL);

	if (gather.nctrl == 0) {
		assert(gather.nframe == 1);
		assert(frames->next == NULL);

		gather_remove_bvec(frame, &gather);

		// retranslate to remove the extra frame
		return ir_translate_object_inner(top, frame);
	}

	if (gather.nctrl == 1) {
		struct jvst_ir_expr *cmp;

		gather_remove_bvec(frame, &gather);

		// replace bit logic with simpler SPLIT logic
		split = ir_expr_new(JVST_IR_EXPR_SPLIT);
		split->u.split.frames = frames;

		cmp = NULL;
		switch (top->type) {
		case JVST_CNODE_AND:
			fprintf(stderr, "%s:%d AND cnode should not have nctrl == 1 (either 0 or 2+) in %s\n",
					__FILE__, __LINE__, __func__);
			abort();

		case JVST_CNODE_OR:
			cmp = ir_expr_op(JVST_IR_EXPR_GE, split, ir_expr_size(1));
			break;

		case JVST_CNODE_NOT:
			cmp = ir_expr_op(JVST_IR_EXPR_EQ, split, ir_expr_size(0));
			break;

		case JVST_CNODE_XOR:
			cmp = ir_expr_op(JVST_IR_EXPR_EQ, split, ir_expr_size(1));
			break;

		default:
			fprintf(stderr, "%s:%d invalid cnode type for %s: %s\n",
					__FILE__, __LINE__, __func__, jvst_cnode_type_name(top->type));
			abort();
		}

		cond = ir_stmt_if(cmp,
			ir_stmt_new(JVST_IR_STMT_VALID),
			ir_stmt_invalid(JVST_INVALID_SPLIT_CONDITION));  // XXX - improve error message!

		return cond;
	}

	// needs full bitvec logic
	cond = ir_stmt_new(JVST_IR_STMT_SEQ);
	spp = &cond->u.stmt_list;

	gather.bvec->u.bitvec.nbits = gather.nframe;
	assert(gather.boff == gather.nframe);

	*spp = ir_stmt_new(JVST_IR_STMT_SPLITVEC);
	(*spp)->u.splitvec.split_frames = frames;

	(*spp)->u.splitvec.frame = frame;
	(*spp)->u.splitvec.bitvec = gather.bvec;

	spp = &(*spp)->next;
	*spp = ir_stmt_new(JVST_IR_STMT_IF);
	*spp = ir_stmt_if(split,
		ir_stmt_new(JVST_IR_STMT_VALID),
		ir_stmt_invalid(JVST_INVALID_SPLIT_CONDITION));  // XXX - improve error message!

	return cond;
}

static struct jvst_ir_stmt *
ir_translate_object_inner(struct jvst_cnode *top, struct jvst_ir_stmt *frame)
{
	struct jvst_ir_stmt *stmt, *pseq, **spp, **pseqpp;
	struct jvst_cnode *pmatch;
	struct fsm_options *opts;
	const char *loopname;
	size_t nreqs;
	
	struct ir_object_builder builder = { 0 };

	builder.frame = frame;

	stmt = ir_stmt_new(JVST_IR_STMT_SEQ);
	spp = &stmt->u.stmt_list;
	builder.pre_loop = spp;

	builder.oloop = ir_stmt_loop(frame,"L_OBJ");
	*spp = builder.oloop;
	builder.post_loop = &builder.oloop->next;

	spp = &(*spp)->u.loop.stmts;

	*spp = ir_stmt_new(JVST_IR_STMT_TOKEN);
	spp = &(*spp)->next;

	pseq = ir_stmt_new(JVST_IR_STMT_SEQ);
	*spp = ir_stmt_if(
		ir_expr_istok(SJP_OBJECT_END),
		ir_stmt_break(builder.oloop),
		pseq);

	builder.pre_match = &pseq->u.stmt_list;
	pseqpp = &pseq->u.stmt_list;

	builder.match = ir_stmt_new(JVST_IR_STMT_MATCH);
	builder.mcpp = &builder.match->u.match.cases;

	*pseqpp = builder.match;
	builder.match->u.match.default_case = obj_default_case();
	pseqpp = &(*pseqpp)->next;
	builder.post_match = pseqpp;
	assert(pseqpp != NULL);
	assert(*pseqpp == NULL);

	builder.matcher = NULL;

	ir_translate_obj_inner(top, &builder);

	if (builder.match->u.match.default_case == NULL) {
		builder.match->u.match.default_case = obj_default_case();
	}

	// handle post-loop constraints
	if (*builder.post_loop == NULL) {
		*builder.post_loop = ir_stmt_new(JVST_IR_STMT_VALID);
	}

	return stmt;
}

static struct jvst_ir_stmt *
ir_translate_object(struct jvst_cnode *top, struct jvst_ir_stmt *frame)
{
	switch (top->type) {
	case JVST_CNODE_AND:
	case JVST_CNODE_OR:
	case JVST_CNODE_NOT:
	case JVST_CNODE_XOR:
		return ir_translate_object_split(top, frame);

	default:
		return ir_translate_object_inner(top,frame);
	}
}

static struct jvst_ir_stmt *
ir_translate_type(enum SJP_EVENT type, struct jvst_cnode *top, struct jvst_ir_stmt *frame)
{
	switch (type) {
	case SJP_NUMBER:
		return ir_translate_number(top);

	case SJP_OBJECT_BEG:
		return ir_translate_object(top, frame);

	case SJP_NONE:
	case SJP_NULL:
	case SJP_TRUE:
	case SJP_FALSE:
	case SJP_STRING:
	case SJP_ARRAY_BEG:
		return ir_stmt_new(JVST_IR_STMT_NOP);

	case SJP_OBJECT_END:
	case SJP_ARRAY_END:
		fprintf(stderr, "%s:%d Invalid event type %d\n",
			__FILE__, __LINE__, type);
		abort();

	default:
		fprintf(stderr, "%s:%d Unknown event type %d\n",
			__FILE__, __LINE__, type);
		abort();
	}
}

struct jvst_ir_stmt *
jvst_ir_translate(struct jvst_cnode *ctree)
{
	struct jvst_ir_stmt *frame, **spp;
	int count_valid, count_invalid, count_other;
	enum jvst_cnode_type dft_case;
	size_t i;

	if (ctree->type != JVST_CNODE_SWITCH) {
		fprintf(stderr, "%s:%d translation must start at a SWITCH node\n",
			__FILE__, __LINE__);
		abort();
	}

	frame = ir_stmt_frame();
	spp = &frame->u.frame.stmts;

	// 1) Emit TOKEN
	*spp = ir_stmt_new(JVST_IR_STMT_TOKEN);
	spp = &(*spp)->next;

	// 2) count clauses that are VALID / INVALID / neither
	count_valid = 0;
	count_invalid = 0;
	count_other = 0;
	for (i=0; i < ARRAYLEN(ctree->u.sw); i++) {
		switch (ctree->u.sw[i]->type) {
		case JVST_CNODE_INVALID:
			count_invalid++;
			break;

		case JVST_CNODE_VALID:
			count_valid++;
			break;

		default:
			count_other++;
			break;
		}
	}

	// 3) pick default case (VALID/INVALID)
	// at least two cases should always be INVALID (OBJECT_END,
	// ARRAY_END)
	dft_case = (count_valid > count_invalid) ? JVST_CNODE_VALID : JVST_CNODE_INVALID;

	// 4) write IF tree, descending for each type
	for (i=0; i < ARRAYLEN(ctree->u.sw); i++) {
		struct jvst_ir_stmt *stmt, *br_true;

		if (ctree->u.sw[i]->type == dft_case) {
			continue;
		}

		switch (ctree->u.sw[i]->type) {
		case JVST_CNODE_INVALID:
			br_true = ir_stmt_invalid(JVST_INVALID_UNEXPECTED_TOKEN);
			break;

		case JVST_CNODE_VALID:
			br_true = ir_stmt_valid();
			break;

		default:
			br_true = ir_translate_type(i, ctree->u.sw[i], frame);
			break;
		}

		*spp = ir_stmt_if(ir_expr_istok(i), br_true, NULL);
		spp = &(*spp)->u.if_.br_false;
	}

	*spp = (dft_case == JVST_CNODE_VALID)
		? ir_stmt_new(JVST_IR_STMT_VALID) 
		: ir_stmt_invalid(JVST_INVALID_UNEXPECTED_TOKEN)
		;

	return frame;
}

struct addr_fixup_list;

static struct jvst_ir_stmt *
jvst_ir_stmt_copy_inner(struct jvst_ir_stmt *ir, struct addr_fixup_list *fixups);

static void
addr_fixup_add_stmt(struct addr_fixup_list *l, struct jvst_ir_stmt *stmt, struct jvst_ir_stmt **addrp, struct jvst_ir_stmt *v);

static void
addr_fixup_add_expr(struct addr_fixup_list *l, struct jvst_ir_expr *expr, struct jvst_ir_stmt **addrp, struct jvst_ir_stmt *v);

struct jvst_ir_expr *
jvst_ir_expr_copy(struct jvst_ir_expr *ir, struct addr_fixup_list *fixups)
{
	struct jvst_ir_expr *copy;

	copy = ir_expr_new(ir->type);

	switch (ir->type) {
	case JVST_IR_EXPR_ISTOK:
		copy->u.istok = ir->u.istok;
		return copy;

	case JVST_IR_EXPR_ITEMP:
	case JVST_IR_EXPR_FTEMP:
		copy->u.temp = ir->u.temp;
		return copy;

	case JVST_IR_EXPR_SEQ:
		return ir_expr_seq(
			jvst_ir_stmt_copy_inner(ir->u.seq.stmt, fixups),
			jvst_ir_expr_copy(ir->u.seq.expr, fixups));

	case JVST_IR_EXPR_TOK_TYPE:
	case JVST_IR_EXPR_TOK_NUM:
	case JVST_IR_EXPR_TOK_COMPLETE:
	case JVST_IR_EXPR_TOK_LEN:
		return copy;

	case JVST_IR_EXPR_NUM:
		copy->u.vnum = ir->u.vnum;
		return copy;

	case JVST_IR_EXPR_INT:
		copy->u.vint = ir->u.vint;
		return copy;

	case JVST_IR_EXPR_SIZE:
		copy->u.vsize = ir->u.vsize;
		return copy;

	case JVST_IR_EXPR_COUNT:
		{
			assert(ir->u.count.counter != NULL);
			assert(ir->u.count.counter->type == JVST_IR_STMT_COUNTER);
			assert(ir->u.count.counter->data != NULL);
			assert(ir->u.count.counter->data != ir->u.count.counter);
			assert(((struct jvst_ir_stmt *)ir->u.count.counter->data)->type == JVST_IR_STMT_COUNTER);

			copy->u.count = ir->u.count;
			copy->u.count.counter = copy->u.count.counter->data;

			return copy;
		}

	case JVST_IR_EXPR_MATCH:
		{
			assert(ir->u.match.dfa != NULL);
			copy->u.match = ir->u.match;

			return copy;
		}

	case JVST_IR_EXPR_SPLIT:
		{
			assert(ir->u.split.frames == NULL);
			assert(ir->u.split.split_list != NULL);
			assert(ir->u.split.split_list->type == JVST_IR_STMT_SPLITLIST);

			// XXX - not sure if we need to use ir->u.split.split_list->data
			//
			// We should only copy SPLIT after linearization and during an 
			// optimization phase, so the split list shouldn't need to be
			// copied.
			//
			// This would probably be safer if split lists just stored the
			// frame index.
			copy->u.split = ir->u.split;
			return copy;
		}

	case JVST_IR_EXPR_NE:
	case JVST_IR_EXPR_LT:
	case JVST_IR_EXPR_LE:
	case JVST_IR_EXPR_EQ:
	case JVST_IR_EXPR_GE:
	case JVST_IR_EXPR_GT:
		copy->u.cmp.left = jvst_ir_expr_copy(ir->u.cmp.left, fixups);
		copy->u.cmp.right = jvst_ir_expr_copy(ir->u.cmp.right, fixups);
		return copy;

	case JVST_IR_EXPR_ISINT:
		copy->u.isint.arg = jvst_ir_expr_copy(ir->u.isint.arg, fixups);
		return copy;

	case JVST_IR_EXPR_SLOT:
		copy->u.slot = copy->u.slot;
		return copy;

	case JVST_IR_EXPR_BCOUNT:
	case JVST_IR_EXPR_BTEST:
	case JVST_IR_EXPR_BTESTALL:
	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTONE:
		{
			assert(ir->u.btest.frame != NULL);
			assert(ir->u.btest.bitvec != NULL);
			assert(ir->u.btest.bitvec->data != NULL);
			copy->u.btest = ir->u.btest;
			copy->u.btest.bitvec = ir->u.btest.bitvec->data;
			assert(copy->u.btest.bitvec->type == JVST_IR_STMT_BITVECTOR);

			if (ir->u.btest.frame->data == NULL) {
				addr_fixup_add_expr(fixups, ir, &copy->u.btest.frame, ir->u.btest.frame);
			} else {
				copy->u.btest.frame = ir->u.btest.frame->data;
			}

			return copy;
		}

	case JVST_IR_EXPR_NONE:
	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_AND:
	case JVST_IR_EXPR_OR:
	case JVST_IR_EXPR_NOT:
		fprintf(stderr, "%s:%d (%s) copying IR expression %s not yet implemented\n",
				__FILE__, __LINE__, __func__, 
				jvst_ir_expr_type_name(ir->type));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown IR statement type %d\n",
			__FILE__, __LINE__, __func__, ir->type);
	abort();
}

static struct jvst_ir_stmt *
ir_deepcopy_stmtlist(struct jvst_ir_stmt *l, struct addr_fixup_list *fixups)
{
	struct jvst_ir_stmt *n, *copy = NULL, **spp = &copy;

	for (n = l; n != NULL; n = n->next) {
		struct jvst_ir_stmt *c;
		c = jvst_ir_stmt_copy_inner(n, fixups);
		*spp = c;
		spp = &c->next;
	}

	return copy;
}

struct addr_fixup {
	struct jvst_ir_stmt **addrp;
	struct jvst_ir_stmt *orig_value;
	union {
		struct jvst_ir_stmt *stmt;
		struct jvst_ir_expr *expr;
	} elt;
	int stmt;
};

struct addr_fixup_list {
	size_t len;
	size_t cap;
	struct addr_fixup *fixups;
};

struct addr_fixup *
addr_fixup_add_inner(struct addr_fixup_list *l, struct jvst_ir_stmt **addrp, struct jvst_ir_stmt *v)
{
	size_t i;

	if (l->len >= l->cap) {
		size_t newsz = l->cap;
		if (newsz < 4) {
			newsz = 4;
		} else if (newsz < 1024) {
			newsz *= 2;
		} else {
			newsz += newsz/4;
		}

		assert(newsz > l->cap+1);
		l->fixups = xrealloc(l->fixups, newsz * sizeof l->fixups[0]);
		l->cap = newsz;
	}

	i = l->len++;
	assert(l->len <= l->cap);

	l->fixups[i].addrp = addrp;
	l->fixups[i].orig_value = v;

	return &l->fixups[i];
}

static void
addr_fixup_add_stmt(struct addr_fixup_list *l, struct jvst_ir_stmt *stmt, struct jvst_ir_stmt **addrp, struct jvst_ir_stmt *v)
{
	struct addr_fixup *f;

	f = addr_fixup_add_inner(l, addrp, v);
	f->stmt = 1;
	f->elt.stmt = stmt;
}

static void
addr_fixup_add_expr(struct addr_fixup_list *l, struct jvst_ir_expr *expr, struct jvst_ir_stmt **addrp, struct jvst_ir_stmt *v)
{
	struct addr_fixup *f;

	f = addr_fixup_add_inner(l, addrp, v);
	f->stmt = 0;
	f->elt.expr = expr;
}

static void
addr_fixup_free(struct addr_fixup_list *l)
{
	if (l == NULL) {
		return;
	}

	free(l->fixups);
}

static void
ir_frame_copy_counters(struct jvst_ir_stmt **cpp, struct jvst_ir_stmt *c);

static void
ir_frame_copy_bitvecs(struct jvst_ir_stmt **bvpp, struct jvst_ir_stmt *bv);

static struct jvst_ir_stmt *
ir_copy_stmtlist(struct jvst_ir_stmt *n);

static struct jvst_ir_stmt *
jvst_ir_stmt_copy_inner(struct jvst_ir_stmt *ir, struct addr_fixup_list *fixups)
{
	struct jvst_ir_stmt *copy;

	copy = ir_stmt_new(ir->type);

	switch (ir->type) {
	case JVST_IR_STMT_NOP:
	case JVST_IR_STMT_VALID:
	case JVST_IR_STMT_TOKEN:
	case JVST_IR_STMT_CONSUME:
		return copy;

	case JVST_IR_STMT_INVALID:
		copy->u.invalid = ir->u.invalid;
		return copy;

	case JVST_IR_STMT_FRAME:
		{
			struct jvst_ir_stmt *stmt, **spp;

			assert(ir->data == NULL);
			ir->data = copy;

			copy->u.frame = ir->u.frame;

			ir_frame_copy_counters(&copy->u.frame.counters, ir->u.frame.counters);
			ir_frame_copy_bitvecs(&copy->u.frame.bitvecs, ir->u.frame.bitvecs);
			copy->u.frame.matchers = ir_copy_stmtlist(ir->u.frame.matchers);

			// XXX - this needs some rethinking.  We're using frames to hold
			// blocks and a statement list, and the can hold the same objects,
			// which makes it awkward to copy them.
			//
			// Currently:
			//   1. If ir->u.frame.blocks != NULL, copy blocks.
			//   	Then, if ir->u.frame.stmts != NULL, iterate through the
			//   	   blocks, if the statement is not a block, error out
			//   	   (abort).  If the statement is a block, wire its copy
			//   	   into the statement list
			//
			//   2. If ir->u.frame.blocks == NULL, copy ir->u.frame.stmts
			//      verbatim.
			if (ir->u.frame.blocks) {
				spp = &copy->u.frame.blocks;
				*spp = NULL;
				for (stmt = ir->u.frame.blocks; stmt != NULL; stmt = stmt->next) {
					*spp = jvst_ir_stmt_copy_inner(stmt, fixups);
					spp = &(*spp)->u.block.block_next;
				}

				spp = &copy->u.frame.stmts;
				*spp = NULL;
				for (stmt = ir->u.frame.stmts; stmt != NULL; stmt = stmt->next) {
					struct jvst_ir_stmt *newblk;

					if (stmt->type != JVST_IR_STMT_BLOCK) {
						fprintf(stderr, "%s:%d (%s) invalid statement in FRAME with blocks list: %s\n",
							__FILE__, __LINE__, __func__, jvst_ir_stmt_type_name(stmt->type));
					}

					newblk = stmt->data;
					assert(newblk != NULL);
					assert(newblk->type == JVST_IR_STMT_BLOCK);

					*spp = newblk;
					spp = &newblk->next;
				}
			} else {
				spp = &copy->u.frame.stmts;
				*spp = NULL;
				for (stmt = ir->u.frame.stmts; stmt != NULL; stmt = stmt->next) {
					*spp = jvst_ir_stmt_copy_inner(stmt, fixups);
					spp = &(*spp)->next;
				}
			}
		}
		return copy;

	case JVST_IR_STMT_IF:
		{
			struct jvst_ir_stmt *stmt, **spp;

			copy->u.if_.cond     = jvst_ir_expr_copy(ir->u.if_.cond, fixups);
			copy->u.if_.br_true  = jvst_ir_stmt_copy_inner(ir->u.if_.br_true, fixups);
			copy->u.if_.br_false = jvst_ir_stmt_copy_inner(ir->u.if_.br_false, fixups);
		}
		return copy;

	case JVST_IR_STMT_PROGRAM:
		copy->u.program.frames = ir_deepcopy_stmtlist(ir->u.program.frames, fixups);
		return copy;

	case JVST_IR_STMT_SEQ:
		copy->u.stmt_list = ir_deepcopy_stmtlist(ir->u.stmt_list, fixups);
		return copy;

	case JVST_IR_STMT_MATCHER:
		copy->u.matcher = ir->u.matcher;
		return copy;

	case JVST_IR_STMT_MOVE:
		{
			struct jvst_ir_expr *dst, *src;
			dst = jvst_ir_expr_copy(ir->u.move.dst, fixups);
			src = jvst_ir_expr_copy(ir->u.move.src, fixups);
			return ir_stmt_move(dst,src);
		}

	case JVST_IR_STMT_INCR:
		{
			assert(ir->u.counter_op.counter != NULL);
			assert(ir->u.counter_op.counter->type == JVST_IR_STMT_COUNTER);
			assert(ir->u.counter_op.counter->data != NULL);

			copy->u.counter_op = ir->u.counter_op;
			copy->u.counter_op.counter = copy->u.counter_op.counter->data;

			return copy;
		}

	case JVST_IR_STMT_BSET:
		{
			assert(ir->u.bitop.bitvec != NULL);
			assert(ir->u.bitop.bitvec->type == JVST_IR_STMT_BITVECTOR);
			assert(ir->u.bitop.bitvec->data != NULL);
			assert(((struct jvst_ir_stmt *)ir->u.bitop.bitvec->data)->type == JVST_IR_STMT_BITVECTOR);

			copy->u.bitop = ir->u.bitop;
			copy->u.bitop.bitvec = copy->u.bitop.bitvec->data;

			return copy;
		}

	case JVST_IR_STMT_SPLITVEC:
		{
			assert(ir->u.splitvec.bitvec != NULL);
			assert(ir->u.splitvec.bitvec->type == JVST_IR_STMT_BITVECTOR);
			assert(ir->u.splitvec.bitvec->data != NULL);
			assert(((struct jvst_ir_stmt *)ir->u.splitvec.bitvec->data)->type == JVST_IR_STMT_BITVECTOR);

			copy->u.splitvec = ir->u.splitvec;
			copy->u.splitvec.bitvec = copy->u.splitvec.bitvec->data;

			return copy;
		}

	case JVST_IR_STMT_BLOCK:
		{
			assert(ir->data == NULL);

			copy->u.block = ir->u.block;
			copy->u.block.block_next = NULL;
			copy->u.block.stmts = NULL;
			ir->data = copy;

			copy->u.block.stmts = ir_deepcopy_stmtlist(ir->u.block.stmts, fixups);
			return copy;
		}

	case JVST_IR_STMT_CBRANCH:
		{
			copy->u.cbranch.cond = jvst_ir_expr_copy(ir->u.cbranch.cond, fixups);

			if (ir->u.cbranch.br_true != NULL) {
				if (ir->u.cbranch.br_true->data == NULL) {
					addr_fixup_add_stmt(fixups, ir, &copy->u.cbranch.br_true, ir->u.cbranch.br_true);
				} else {
					copy->u.cbranch.br_true = ir->u.cbranch.br_true->data;
				}
			}

			if (ir->u.cbranch.br_false != NULL) {
				if (ir->u.cbranch.br_false->data == NULL) {
					addr_fixup_add_stmt(fixups, ir, &copy->u.cbranch.br_false, ir->u.cbranch.br_false);
				} else {
					copy->u.cbranch.br_false = ir->u.cbranch.br_false->data;
				}
			}

			return copy;
		}

	case JVST_IR_STMT_BRANCH:
		{
			if (ir->u.branch != NULL) {
				if (ir->u.branch->data == NULL) {
					addr_fixup_add_stmt(fixups, ir, &copy->u.branch, ir->u.branch);
				} else {
					copy->u.branch = ir->u.branch->data;
				}
			}

			return copy;
		}

	case JVST_IR_STMT_CALL:
		{
			assert(ir->u.call.frame != NULL);
			if (ir->u.call.frame->data == NULL) {
				addr_fixup_add_stmt(fixups, ir, &copy->u.call.frame, ir->u.call.frame);
			} else {
				copy->u.call.frame = ir->u.call.frame->data;
			}
			return copy;
		}
		/* need to fixup frame and block references */

	case JVST_IR_STMT_LOOP:
	case JVST_IR_STMT_BREAK:
	case JVST_IR_STMT_BCLEAR:
	case JVST_IR_STMT_DECR:
	case JVST_IR_STMT_MATCH:
		fprintf(stderr, "%s:%d (%s) copying IR statement %s not yet implemented\n",
				__FILE__, __LINE__, __func__, 
				jvst_ir_stmt_type_name(ir->type));
		abort();

	case JVST_IR_STMT_COUNTER:
	case JVST_IR_STMT_BITVECTOR:
	case JVST_IR_STMT_SPLITLIST:
		fprintf(stderr, "%s:%d (%s) IR statement %s should be copied as part of the frame\n",
				__FILE__, __LINE__, __func__, 
				jvst_ir_stmt_type_name(ir->type));
		abort();

	}

	fprintf(stderr, "%s:%d (%s) unknown IR statement type %d\n",
			__FILE__, __LINE__, __func__, ir->type);
	abort();
}

static void
fixup_addresses(struct addr_fixup_list *fixups)
{
	size_t i,n;
	n = fixups->len;
	for (i=0; i < n; i++) {
		struct jvst_ir_stmt **addrp, *orig;
		addrp = fixups->fixups[i].addrp;
		orig = fixups->fixups[i].orig_value;

		assert(orig->data != NULL);
		*addrp = orig->data;
	}
}

struct jvst_ir_stmt *
jvst_ir_stmt_copy(struct jvst_ir_stmt *ir)
{
	struct addr_fixup_list fixups = { 0 };
	struct jvst_ir_stmt *copy;

	copy = jvst_ir_stmt_copy_inner(ir, &fixups);
	fixup_addresses(&fixups);
	addr_fixup_free(&fixups);

	return copy;
}

struct op_linearizer {
	struct jvst_ir_stmt *orig_frame;
	struct jvst_ir_stmt *frame;
	struct jvst_ir_stmt **fpp;

	struct jvst_ir_stmt *valid_block;
	struct jvst_ir_stmt *invalid_blocks;

	struct jvst_ir_stmt **ipp;
	struct jvst_ir_stmt **bpp;
};

static struct jvst_ir_stmt *
ir_copy_stmtlist(struct jvst_ir_stmt *n)
{
	struct jvst_ir_stmt *copy, **spp;
	copy = NULL;
	spp = &copy;

	for( ; n != NULL; n = n->next) {
		*spp = jvst_ir_stmt_copy(n);
		spp = &(*spp)->next;
	}

	return copy;
}

static void
ir_linearize_stmt(struct op_linearizer *oplin, struct jvst_ir_stmt *stmt);

void
ir_linearize_stmtlist(struct op_linearizer *oplin, struct jvst_ir_stmt *stmt)
{
	struct jvst_ir_stmt *s;

	for (s = stmt; s != NULL; s = s->next) {
		ir_linearize_stmt(oplin, s);
	}
}

static void
ir_flatten_block(struct jvst_ir_stmt *block)
{
	struct jvst_ir_stmt **spp;
	assert(block != NULL);
	assert(block->type == JVST_IR_STMT_BLOCK);

	for (spp = &block->u.block.stmts; *spp != NULL; ) {
		struct jvst_ir_stmt *next, **slpp;

		if ((*spp)->type != JVST_IR_STMT_SEQ) {
			spp = &(*spp)->next;
			continue;
		}

		next = (*spp)->next;
		*spp = (*spp)->u.stmt_list;
		for (slpp = spp; *slpp != NULL; slpp = &(*slpp)->next) {
			continue;
		}

		*slpp = next;

		// NB: don't update spp because it now points at the head of
		// the SEQ() statement list
	}
}

static struct jvst_ir_stmt *
ir_linearize_branch_final_dest(struct jvst_ir_stmt *dest)
{
	struct jvst_ir_stmt *stmt;

follow:
	assert(dest != NULL);
	assert(dest->type == JVST_IR_STMT_BLOCK);

	stmt = dest->u.block.stmts;
	assert(stmt != NULL);

	if (stmt->type != JVST_IR_STMT_BRANCH) {
		return dest;
	}

	dest = stmt->u.branch;
	goto follow;
}

static void
ir_prune_block(struct jvst_ir_stmt *block)
{
	struct jvst_ir_stmt *stmt;

	assert(block != NULL);
	assert(block->type == JVST_IR_STMT_BLOCK);

	for (stmt = block->u.block.stmts; stmt != NULL; stmt = stmt->next) {
		switch (stmt->type) {
		case JVST_IR_STMT_CBRANCH:
			stmt->u.cbranch.br_true = ir_linearize_branch_final_dest(stmt->u.cbranch.br_true);
			stmt->u.cbranch.br_false = ir_linearize_branch_final_dest(stmt->u.cbranch.br_false);
			stmt->next = NULL;
			return;

		case JVST_IR_STMT_BRANCH:
			stmt->u.branch = ir_linearize_branch_final_dest(stmt->u.branch);
			stmt->next = NULL;
			return;

		default:
			/* nop */
			break;
		}
	}
}

static struct jvst_ir_stmt *
block_find_branch(struct jvst_ir_stmt *blk)
{
	struct jvst_ir_stmt *stmt;
	for (stmt = blk->u.block.stmts; stmt != NULL; stmt = stmt->next) {
		switch (stmt->type) {
		case JVST_IR_STMT_BRANCH:
		case JVST_IR_STMT_CBRANCH:
			return stmt;

		default:
			break; /* nop */
		}
	}

	return NULL;
}

static struct jvst_ir_stmt **
sort_unsorted_blocks(struct jvst_ir_stmt *blk, struct jvst_ir_stmt **bpp)
{
	struct jvst_ir_stmt *b, *succ;

	for (b = blk; b != NULL; b = succ) {
		struct jvst_ir_stmt *stmt;

		assert(bpp != &b->u.block.block_next); // guard against loops

		*bpp = b;
		bpp = &b->u.block.block_next;
		b->u.block.sorted = true;

		succ = NULL;

		stmt = block_find_branch(b);
		if (stmt == NULL) {
			continue;
		}

		switch (stmt->type) {
		case JVST_IR_STMT_BRANCH:
			assert(stmt->u.branch != NULL);
			assert(stmt->u.branch->type == JVST_IR_STMT_BLOCK);

			if (!stmt->u.branch->u.block.sorted) {
				succ = stmt->u.branch;
			}
			break;

		case JVST_IR_STMT_CBRANCH:
			assert(stmt->u.cbranch.br_false != NULL);
			assert(stmt->u.cbranch.br_false->type == JVST_IR_STMT_BLOCK);

			if (!stmt->u.cbranch.br_false->u.block.sorted) {
				succ = stmt->u.cbranch.br_false;
				continue;
			}

			assert(stmt->u.cbranch.br_true != NULL);
			assert(stmt->u.cbranch.br_true->type == JVST_IR_STMT_BLOCK);

			if (!stmt->u.cbranch.br_true->u.block.sorted) {
				succ = stmt->u.cbranch.br_true;
			}
			break;

		default:
			assert(! "should not reach");
		}
	}

	return bpp;
}

static struct jvst_ir_stmt *
ir_topo_sort_blocks(struct jvst_ir_stmt *blist)
{
	struct jvst_ir_stmt **q, *b, *next, *ordered, **bpp;
	size_t i,n;

	for (n=0, b=blist; b != NULL; b = b->u.block.block_next) {
		assert(b->type == JVST_IR_STMT_BLOCK);
		n++;
	}

	// avoid trivial cases
	if (n < 3) {
		return blist;
	}

	q = xmalloc(n * sizeof *q);

	for (i=0, b=blist; b != NULL; i++, b = next) {
		next = b->u.block.block_next;
		b->u.block.block_next = NULL;
		b->u.block.sorted = false;

		assert(i < n);
		q[i] = b;
	}

	ordered = NULL;
	bpp = &ordered;

	for (i=0; i < n; i++) {
		struct jvst_ir_stmt *blk;

		blk = q[i];
		if (blk->u.block.sorted) {
			continue;
		}
		
		bpp = sort_unsorted_blocks(blk, bpp);
	}

	free(q);

	return ordered;
}

static void
ir_mark_reachable(struct jvst_ir_stmt *entry)
{
	struct jvst_ir_stmt *stmt;

	assert(entry != NULL);
	assert(entry->type == JVST_IR_STMT_BLOCK);

	entry->u.block.reachable = true;
	for (stmt = entry->u.block.stmts; stmt != NULL; stmt = stmt->next) {
		switch (stmt->type) {
		case JVST_IR_STMT_BRANCH:
			assert(stmt->u.branch != NULL);
			assert(stmt->u.branch->type == JVST_IR_STMT_BLOCK);

			if (!stmt->u.branch->u.block.reachable) {
				ir_mark_reachable(stmt->u.branch);
			}
			break;

		case JVST_IR_STMT_CBRANCH:
			assert(stmt->u.cbranch.br_true != NULL);
			assert(stmt->u.cbranch.br_true->type == JVST_IR_STMT_BLOCK);

			if (!stmt->u.cbranch.br_true->u.block.reachable) {
				ir_mark_reachable(stmt->u.cbranch.br_true);
			}

			assert(stmt->u.cbranch.br_false != NULL);
			assert(stmt->u.cbranch.br_false->type == JVST_IR_STMT_BLOCK);

			if (!stmt->u.cbranch.br_false->u.block.reachable) {
				ir_mark_reachable(stmt->u.cbranch.br_false);
			}
			break;

		default:
			break;
		}
	}
}

static struct jvst_ir_stmt *
ir_remove_unreachable_blocks(struct jvst_ir_stmt *entry)
{
	struct jvst_ir_stmt *blk, **bpp;

	// mark all blocks as not reachable to start with
	for (blk = entry; blk != NULL; blk = blk->next) {
		assert(blk->type == JVST_IR_STMT_BLOCK);
		blk->u.block.reachable = false;
	}

	ir_mark_reachable(entry);

	for (bpp=&entry; *bpp != NULL; ) {
		if ((*bpp)->u.block.reachable) {
			bpp = &(*bpp)->u.block.block_next;
			continue;
		}

		// unreachable, remove block
		*bpp = (*bpp)->u.block.block_next;
	}

	return entry;
}

static void
ir_assemble_basic_blocks(struct jvst_ir_stmt *frame)
{
	struct jvst_ir_stmt **ipp, *blk, **bpp, *entry;

	entry = frame->u.frame.blocks;

	/* first a quick check to ensure that blocks aren't
	 * connected to other statements
	 *
	 * XXX - this only checks in one direction, but that's
	 * probably sufficient
	 */
	for (blk = entry; blk != NULL; blk = blk->u.block.block_next) {
		assert(blk->type == JVST_IR_STMT_BLOCK);
		assert(blk->next == NULL);
	}

	// some small optimizations before we schedule the
	// blocks

	// flatten SEQs
	for (blk = entry; blk != NULL; blk = blk->u.block.block_next) {
		ir_flatten_block(blk);
	}

	// prune any code after the first branch or
	// cbranch
	for (blk = entry; blk != NULL; blk = blk->u.block.block_next) {
		ir_prune_block(blk);
	}

	// Mark all blocks as unvisited.  Then mark reachable blocks.
	// Then eliminate unreachable blocks.
	entry = ir_remove_unreachable_blocks(entry);
	assert(entry != NULL);

	// generate traces, sort blocks pseudo-topologically
	entry = ir_topo_sort_blocks(entry);
	assert(entry != NULL);

	frame->u.frame.blocks = entry;

	// now assemble blocks together
	ipp = &frame->u.frame.stmts;
	for (blk = entry; blk != NULL; blk = blk->u.block.block_next) {
		// assert to ensure that unprocessed blocks are still unconnected
		assert(blk->next == NULL);

		*ipp = blk;
		ipp = &blk->next;
	}
}

static void
ir_flatten_frame(struct jvst_ir_stmt *frame)
{
	struct jvst_ir_stmt **ipp, *blk;

	assert(frame->type == JVST_IR_STMT_FRAME);

	// assemble a linear statement list by flattening the blocks
	ipp = &frame->u.frame.stmts;
	for (blk = frame->u.frame.blocks; blk != NULL; blk = blk->u.block.block_next) {
		*ipp = blk;
		ipp = &blk->next;

		*ipp = blk->u.block.stmts;
		for (; (*ipp) != NULL; ipp = &(*ipp)->next) {
			continue;
		}

		blk->u.block.stmts = NULL;
	}
}

static void
ir_assemble_fixup_jumps(struct jvst_ir_stmt *frame)
{
	struct jvst_ir_stmt **ipp;
	for (ipp = &frame->u.frame.stmts; *ipp != NULL; ipp = &(*ipp)->next) {
		if ((*ipp)->type != JVST_IR_STMT_BRANCH) {
			continue;
		}

		if ((*ipp)->next == NULL) {
			continue;
		}

		if ((*ipp)->next->type != JVST_IR_STMT_BLOCK) {
			continue;
		}

		if ((*ipp)->u.branch == (*ipp)->next) {
			*ipp = (*ipp)->next;
		}
	}
}

static void
ir_frame_copy_counters(struct jvst_ir_stmt **cpp, struct jvst_ir_stmt *c)
{
	for (; c != NULL; c = c->next) {
		struct jvst_ir_stmt *cc;

		assert(c->data == NULL);

		cc = ir_stmt_new(JVST_IR_STMT_COUNTER);
		cc->u.counter.label = c->u.counter.label;
		cc->u.counter.ind   = c->u.counter.ind;
		cc->u.counter.frame_off = c->u.counter.frame_off;

		assert(c->u.counter.frame != NULL);
		assert(c->u.counter.frame->data != NULL);
		assert(((struct jvst_ir_stmt *)c->u.counter.frame->data)->type == JVST_IR_STMT_FRAME);
		cc->u.counter.frame = c->u.counter.frame->data;

		c->data = cc;

		*cpp = cc;
		cpp = &cc->next;
	}

	*cpp = NULL;
}

static void
ir_frame_copy_bitvecs(struct jvst_ir_stmt **bvpp, struct jvst_ir_stmt *bv)
{
	for (; bv != NULL; bv = bv->next) {
		struct jvst_ir_stmt *bvc;

		assert(bv->data == NULL);

		bvc = ir_stmt_new(JVST_IR_STMT_BITVECTOR);
		bvc->u.bitvec.label = bv->u.bitvec.label;
		bvc->u.bitvec.ind   = bv->u.bitvec.ind;
		bvc->u.bitvec.nbits = bv->u.bitvec.nbits;
		bvc->u.bitvec.frame_off = bv->u.counter.frame_off;

		assert(bv->u.bitvec.frame != NULL);
		assert(bv->u.bitvec.frame->data != NULL);
		assert(((struct jvst_ir_stmt *)bv->u.bitvec.frame->data)->type == JVST_IR_STMT_FRAME);
		bvc->u.bitvec.frame = bv->u.bitvec.frame->data;

		bv->data = bvc;

		*bvpp = bvc;
		bvpp = &bvc->next;
	}
	*bvpp = NULL;
}

static struct jvst_ir_stmt *
ir_linearize_frame(struct op_linearizer *oplin, struct jvst_ir_stmt *fr)
{
	struct jvst_ir_stmt *copy, *entry;
	struct op_linearizer frame_oplin = { 0 };

	assert(fr->type == JVST_IR_STMT_FRAME);
	assert(fr->u.frame.blocks == NULL);
	assert(fr->u.frame.blockind == 0);

	copy = ir_stmt_new(fr->type);
	copy->u.frame = fr->u.frame;
	fr->data = copy;

	*oplin->fpp = copy;
	oplin->fpp = &copy->next;

	copy->u.frame.matchers = ir_copy_stmtlist(fr->u.frame.matchers);

	ir_frame_copy_counters(&copy->u.frame.counters, fr->u.frame.counters);
	ir_frame_copy_bitvecs(&copy->u.frame.bitvecs, fr->u.frame.bitvecs);

	// splitlists should only be present after linearization
	assert(fr->u.frame.splits == NULL);
	assert(fr->u.frame.nsplits == 0);

	copy->u.frame.stmts = NULL;

	frame_oplin.orig_frame = fr;
	frame_oplin.frame = copy;
	frame_oplin.fpp = oplin->fpp;

	entry = ir_stmt_block(copy, "entry");
	copy->u.frame.blocks = entry;
	frame_oplin.bpp = &entry->u.block.block_next;
	frame_oplin.ipp = &entry->u.block.stmts;

	ir_linearize_stmtlist(&frame_oplin, fr->u.frame.stmts);

	if (frame_oplin.valid_block != NULL) {
		*frame_oplin.bpp = frame_oplin.valid_block;
		frame_oplin.bpp = &frame_oplin.valid_block->u.block.block_next;
	}

	if (frame_oplin.invalid_blocks != NULL) {
		*frame_oplin.bpp = frame_oplin.invalid_blocks;
	}

	ir_assemble_basic_blocks(copy);

	oplin->fpp = frame_oplin.fpp;
	return copy;
}

static struct jvst_ir_stmt LOOP_BLOCK;

static struct jvst_ir_stmt *
ir_linearize_block(struct op_linearizer *oplin, const char *prefix, struct jvst_ir_stmt *stmt, struct jvst_ir_stmt *blknext)
{
	struct jvst_ir_stmt *blk;
	struct op_linearizer block_oplin;

	assert(blknext == NULL || blknext == &LOOP_BLOCK || blknext->type == JVST_IR_STMT_BLOCK);

	block_oplin = *oplin;

	blk = ir_stmt_block(oplin->frame, prefix);

	*block_oplin.bpp = blk;
	block_oplin.bpp = &blk->u.block.block_next;

	block_oplin.ipp = &blk->u.block.stmts;
	*block_oplin.ipp = ir_stmt_new(JVST_IR_STMT_NOP);

	ir_linearize_stmtlist(&block_oplin, stmt);

	if (blknext == &LOOP_BLOCK) {
		struct jvst_ir_stmt *jmp;

		jmp = ir_stmt_new(JVST_IR_STMT_BRANCH);
		jmp->u.branch = blk;

		*block_oplin.ipp = jmp;
		block_oplin.ipp = &jmp->next;
	} else if (blknext != NULL) {
		struct jvst_ir_stmt *jmp;

		jmp = ir_stmt_new(JVST_IR_STMT_BRANCH);
		jmp->u.branch = blknext;

		*block_oplin.ipp = jmp;
		block_oplin.ipp = &jmp->next;
	}

	oplin->bpp = block_oplin.bpp;
	oplin->fpp = block_oplin.fpp;

	oplin->valid_block = block_oplin.valid_block;
	oplin->invalid_blocks = block_oplin.invalid_blocks;

	return blk;
}

static struct jvst_ir_expr *
ir_linearize_operand(struct op_linearizer *oplin, struct jvst_ir_expr *expr)
{
	switch (expr->type) {
	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_ISTOK:
	case JVST_IR_EXPR_TOK_COMPLETE:
	case JVST_IR_EXPR_ISINT:
	case JVST_IR_EXPR_NE:
	case JVST_IR_EXPR_LT:
	case JVST_IR_EXPR_LE:
	case JVST_IR_EXPR_EQ:
	case JVST_IR_EXPR_GE:
	case JVST_IR_EXPR_GT:
	case JVST_IR_EXPR_BTEST:
	case JVST_IR_EXPR_BTESTALL:
	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTONE:
	case JVST_IR_EXPR_AND:
	case JVST_IR_EXPR_OR:
	case JVST_IR_EXPR_NOT:
	case JVST_IR_EXPR_SEQ:
		fprintf(stderr, "%s:%d (%s) expression %s is not a comparison operand\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(expr->type));
		abort();

	case JVST_IR_EXPR_TOK_TYPE:
	case JVST_IR_EXPR_TOK_NUM:
	case JVST_IR_EXPR_TOK_LEN:
	case JVST_IR_EXPR_SLOT:
	case JVST_IR_EXPR_ITEMP:
	case JVST_IR_EXPR_FTEMP:
		return expr;

	case JVST_IR_EXPR_NUM:
		{
			struct jvst_ir_expr *eseq, *tmp;
			struct jvst_ir_stmt *mv;

			tmp = ir_expr_ftemp(oplin->frame);
			mv = ir_stmt_move(tmp, expr);

			eseq = ir_expr_seq(mv, tmp);

			return eseq;
		}

	case JVST_IR_EXPR_SIZE:
		{
			struct jvst_ir_expr *eseq, *tmp;
			struct jvst_ir_stmt *mv;

			mv = ir_stmt_new(JVST_IR_STMT_MOVE);
			tmp = ir_expr_itemp(oplin->frame);
			mv->u.move.dst = tmp;
			mv->u.move.src = expr;

			eseq = ir_expr_new(JVST_IR_EXPR_SEQ);
			eseq->u.seq.stmt = mv;
			eseq->u.seq.expr = tmp;

			return eseq;
		}

	case JVST_IR_EXPR_COUNT:
		{
			struct jvst_ir_expr *eseq, *tmp;
			struct jvst_ir_stmt *mv;

			mv = ir_stmt_new(JVST_IR_STMT_MOVE);
			tmp = ir_expr_itemp(oplin->frame);
			mv->u.move.dst = tmp;
			mv->u.move.src = expr;

			eseq = ir_expr_new(JVST_IR_EXPR_SEQ);
			eseq->u.seq.stmt = mv;
			eseq->u.seq.expr = tmp;

			return eseq;
		}

	case JVST_IR_EXPR_SPLIT:
		{
			struct jvst_ir_stmt *splitlist, *fr, **fpp, *mv, *eseq;
			struct jvst_ir_expr *tmp, *spl;

			splitlist = ir_stmt_new(JVST_IR_STMT_SPLITLIST);
			splitlist->u.split_list.ind = oplin->frame->u.frame.nsplits++;
			{
				struct jvst_ir_stmt **slpp;
				for (slpp=&oplin->frame->u.frame.splits; *slpp != NULL; slpp = &(*slpp)->next) {
					continue;
				}

				*slpp = splitlist;
			}

			fpp = &splitlist->u.split_list.frames;
			for (fr = expr->u.split.frames; fr != NULL; fr = fr->next) {
				struct jvst_ir_stmt *newfr;

				newfr = ir_linearize_frame(oplin, fr);
				*fpp = newfr;
				fpp = &newfr->u.frame.split_next;
				splitlist->u.split_list.nframes++;
			}

			tmp = ir_expr_itemp(oplin->frame);
			spl = ir_expr_new(JVST_IR_EXPR_SPLIT);
			spl->u.split.frames = NULL;
			spl->u.split.split_list = splitlist;

			mv = ir_stmt_move(tmp, spl);
			return ir_expr_seq(mv, tmp);
		}

	case JVST_IR_EXPR_BCOUNT:
		/* need to handle remapping things here ... */

	case JVST_IR_EXPR_NONE:
		fprintf(stderr, "%s:%d (%s) expression %s is not yet implemented\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(expr->type));
		abort();

	default:
		fprintf(stderr, "%s:%d (%s) unknown expression type %s\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(expr->type));
		abort();

	}
}

static struct jvst_ir_expr *
ir_linearize_cmp(struct op_linearizer *oplin, struct jvst_ir_expr *cond)
{
	struct jvst_ir_expr *lhs, *rhs, *lin_cond;
	assert(cond->type == JVST_IR_EXPR_NE  || cond->type == JVST_IR_EXPR_LT ||
		cond->type == JVST_IR_EXPR_LE || cond->type == JVST_IR_EXPR_EQ ||
		cond->type == JVST_IR_EXPR_GE || cond->type == JVST_IR_EXPR_GT);

	lhs = ir_linearize_operand(oplin, cond->u.cmp.left);
	rhs = ir_linearize_operand(oplin, cond->u.cmp.right);

	if (lhs == cond->u.cmp.left && rhs == cond->u.cmp.right) {
		return cond;
	}

	lin_cond = ir_expr_new(cond->type);
	lin_cond->u.cmp.left  = lhs;
	lin_cond->u.cmp.right = rhs;

	return lin_cond;
}

static struct jvst_ir_stmt *
ir_linearize_cond(struct op_linearizer *oplin, struct jvst_ir_expr *cond, struct jvst_ir_stmt *btrue, struct jvst_ir_stmt *bfalse)
{
	struct jvst_ir_stmt *cbr;
	struct jvst_ir_expr *brcond;

	(void)oplin;

	switch (cond->type) {
	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_ISTOK:
	case JVST_IR_EXPR_TOK_COMPLETE:
	case JVST_IR_EXPR_ISINT:
		brcond = cond;
		break;

	case JVST_IR_EXPR_NE:
	case JVST_IR_EXPR_LT:
	case JVST_IR_EXPR_LE:
	case JVST_IR_EXPR_EQ:
	case JVST_IR_EXPR_GE:
	case JVST_IR_EXPR_GT:
		brcond = ir_linearize_cmp(oplin, cond);
		break;

	case JVST_IR_EXPR_BTEST:
	case JVST_IR_EXPR_BTESTALL:
	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTONE:
		{
			brcond = ir_expr_new(cond->type);
			brcond->u.btest = cond->u.btest;

			assert(cond->u.btest.frame != NULL);
			assert(cond->u.btest.frame->type == JVST_IR_STMT_FRAME);
			assert(cond->u.btest.frame->data != NULL);
			assert(((struct jvst_ir_stmt *)cond->u.btest.frame->data)->type == JVST_IR_STMT_FRAME);

			brcond->u.btest.frame = cond->u.btest.frame->data;

			assert(cond->u.btest.bitvec != NULL);
			assert(cond->u.btest.bitvec->type == JVST_IR_STMT_BITVECTOR);
			assert(cond->u.btest.bitvec->data != NULL);
			assert(((struct jvst_ir_stmt *)cond->u.btest.bitvec->data)->type == JVST_IR_STMT_BITVECTOR);

			brcond->u.btest.bitvec = cond->u.btest.bitvec->data;
		}
		break;

	case JVST_IR_EXPR_AND:
		{
			struct jvst_ir_stmt *btrue1, *cbr1, *cbr2;
			struct op_linearizer and_oplin;

			btrue1 = ir_stmt_block(oplin->frame, "and_true");
			cbr1 = ir_linearize_cond(oplin, cond->u.and_or.left, btrue1, bfalse);

			and_oplin = *oplin;
			*and_oplin.bpp = btrue1;
			and_oplin.bpp = &btrue1->u.block.block_next;
			and_oplin.ipp = &btrue1->u.block.stmts;

			cbr2 = ir_linearize_cond(&and_oplin, cond->u.and_or.right, btrue, bfalse);
			*and_oplin.ipp = cbr2;

			oplin->fpp = and_oplin.fpp;
			oplin->bpp = and_oplin.bpp;
			oplin->valid_block = and_oplin.valid_block;
			oplin->invalid_blocks = and_oplin.invalid_blocks;

			return cbr1;
		}

	case JVST_IR_EXPR_OR:
		{
			struct jvst_ir_stmt *bfalse1, *cbr1, *cbr2;
			struct op_linearizer or_oplin;

			bfalse1 = ir_stmt_block(oplin->frame, "or_false");
			cbr1 = ir_linearize_cond(oplin, cond->u.and_or.left, btrue, bfalse1);

			or_oplin = *oplin;
			*or_oplin.bpp = bfalse1;
			or_oplin.bpp = &bfalse1->u.block.block_next;
			or_oplin.ipp = &bfalse1->u.block.stmts;

			cbr2 = ir_linearize_cond(&or_oplin, cond->u.and_or.right, btrue, bfalse);
			*or_oplin.ipp = cbr2;

			oplin->fpp = or_oplin.fpp;
			oplin->bpp = or_oplin.bpp;
			oplin->valid_block = or_oplin.valid_block;
			oplin->invalid_blocks = or_oplin.invalid_blocks;

			return cbr1;
		}

	case JVST_IR_EXPR_NOT:
	case JVST_IR_EXPR_SEQ:
		fprintf(stderr, "%s:%d (%s) complex condition %s not yet implemented\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(cond->type));
		abort();

	case JVST_IR_EXPR_NONE:
	case JVST_IR_EXPR_NUM:
	case JVST_IR_EXPR_SIZE:
	case JVST_IR_EXPR_TOK_TYPE:
	case JVST_IR_EXPR_TOK_NUM:
	case JVST_IR_EXPR_TOK_LEN:
	case JVST_IR_EXPR_COUNT:
	case JVST_IR_EXPR_BCOUNT:
	case JVST_IR_EXPR_SPLIT:
	case JVST_IR_EXPR_SLOT:
	case JVST_IR_EXPR_ITEMP:
	case JVST_IR_EXPR_FTEMP:
		fprintf(stderr, "%s:%d (%s) expression %s is not a boolean condition\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(cond->type));
		abort();

	default:
		fprintf(stderr, "%s:%d (%s) unknown expression type %s\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(cond->type));
		abort();

	}

	cbr = ir_stmt_new(JVST_IR_STMT_CBRANCH);
	cbr->u.cbranch.cond = brcond;
	cbr->u.cbranch.br_true = btrue;
	cbr->u.cbranch.br_false = bfalse;

	return cbr;
}

static struct jvst_ir_expr *
ir_linearize_rewrite_expr(struct jvst_ir_stmt *frame, struct jvst_ir_expr *expr)
{
	struct jvst_ir_expr *copy;

	switch (expr->type) {
	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_ISTOK:
	case JVST_IR_EXPR_TOK_COMPLETE:
	case JVST_IR_EXPR_ISINT:
	case JVST_IR_EXPR_NONE:
	case JVST_IR_EXPR_NUM:
	case JVST_IR_EXPR_INT:
	case JVST_IR_EXPR_SIZE:
	case JVST_IR_EXPR_TOK_TYPE:
	case JVST_IR_EXPR_TOK_NUM:
	case JVST_IR_EXPR_TOK_LEN:
	case JVST_IR_EXPR_ITEMP:
	case JVST_IR_EXPR_FTEMP:
	case JVST_IR_EXPR_SLOT:
	case JVST_IR_EXPR_MATCH:
	case JVST_IR_EXPR_BTEST:
	case JVST_IR_EXPR_BTESTALL:
	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTONE:
		return expr;

	case JVST_IR_EXPR_NE:
	case JVST_IR_EXPR_LT:
	case JVST_IR_EXPR_LE:
	case JVST_IR_EXPR_EQ:
	case JVST_IR_EXPR_GE:
	case JVST_IR_EXPR_GT:
		{
			struct jvst_ir_expr *lhs, *rhs, *cmp;

			lhs = ir_linearize_rewrite_expr(frame, expr->u.cmp.left);
			rhs = ir_linearize_rewrite_expr(frame, expr->u.cmp.right);

			if (lhs->type == JVST_IR_EXPR_SEQ) {
				cmp = ir_expr_op(expr->type, lhs->u.seq.expr, rhs);
				cmp = ir_linearize_rewrite_expr(frame, cmp);

				copy = ir_expr_seq(lhs->u.seq.stmt, cmp);
				return ir_linearize_rewrite_expr(frame, copy);
			}

			if (rhs->type == JVST_IR_EXPR_SEQ) {
				struct jvst_ir_expr *tmp, *eseq1, *cmp;
				struct jvst_ir_stmt *mv;

				tmp = ir_expr_tmp(frame, lhs);
				mv = ir_stmt_move(tmp, lhs);

				cmp = ir_expr_op(expr->type, tmp, rhs->u.seq.expr);
				cmp = ir_linearize_rewrite_expr(frame, cmp);

				eseq1 = ir_expr_seq(rhs->u.seq.stmt, cmp);
				eseq1 = ir_linearize_rewrite_expr(frame, eseq1);

				copy = ir_expr_seq(mv, eseq1);
				return ir_linearize_rewrite_expr(frame, copy);
			}

			if (lhs == expr->u.cmp.left && rhs == expr->u.cmp.right) {
				return expr;
			}

			return ir_expr_op(expr->type, lhs, rhs);
		}
		break;

	case JVST_IR_EXPR_SEQ:
		{
			struct jvst_ir_expr *subexpr;
			struct jvst_ir_stmt *seq, **ipp;

			subexpr = expr->u.seq.expr;
			if (subexpr->type != JVST_IR_EXPR_SEQ) {
				return expr;
			}

			seq = ir_stmt_new(JVST_IR_STMT_SEQ);
			ipp = &seq->u.stmt_list;
			*ipp = expr->u.seq.stmt;
			ipp = &(*ipp)->next;
			*ipp = subexpr->u.seq.stmt;

			copy = ir_expr_seq(seq, subexpr->u.seq.expr);
			return ir_linearize_rewrite_expr(frame, copy);
		}

	case JVST_IR_EXPR_COUNT:
	case JVST_IR_EXPR_BCOUNT:
	case JVST_IR_EXPR_SPLIT:
		fprintf(stderr, "%s:%d (%s) condition %s not yet implemented\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(expr->type));
		abort();

	case JVST_IR_EXPR_AND:
	case JVST_IR_EXPR_OR:
	case JVST_IR_EXPR_NOT:
		fprintf(stderr, "%s:%d (%s) cannot rewrite complex condition %s\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(expr->type));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown expression type %s\n",
			__FILE__, __LINE__, __func__,
			jvst_ir_expr_type_name(expr->type));
	abort();
}

static void
ir_linearize_emit_expr(struct op_linearizer *oplin, struct jvst_ir_stmt *cbr)
{
	struct jvst_ir_expr *cond;

	assert(cbr != NULL);
	assert(cbr->type == JVST_IR_STMT_CBRANCH);

	cond = ir_linearize_rewrite_expr(oplin->frame, cbr->u.cbranch.cond);
	if (cond->type == JVST_IR_EXPR_SEQ) {
		struct jvst_ir_stmt *pre;

		pre = jvst_ir_stmt_copy(cond->u.seq.stmt);
		*oplin->ipp = pre;
		oplin->ipp = &pre->next;

		cbr->u.cbranch.cond = cond->u.seq.expr;
	}

	*oplin->ipp = cbr;
	oplin->ipp = &cbr->next;
}

static struct jvst_ir_stmt *
ir_linearize_if(struct op_linearizer *oplin, struct jvst_ir_stmt *stmt)
{
	struct jvst_ir_stmt *cbr, *br_true, *br_false, *br_join;

	assert(stmt->type == JVST_IR_STMT_IF);

	br_join  = ir_stmt_block(oplin->frame, "join");

	br_true  = ir_linearize_block(oplin, "true", stmt->u.if_.br_true, br_join);
	br_false = ir_linearize_block(oplin, "false", stmt->u.if_.br_false, br_join);

	cbr = ir_linearize_cond(oplin, stmt->u.if_.cond, br_true, br_false);

	ir_linearize_emit_expr(oplin, cbr);

	// add to the block list after br_true and br_false to help the
	// block sorter place the join after the true/false branches
	*oplin->bpp = br_join;
	oplin->bpp = &br_join->u.block.block_next;

	oplin->ipp = &br_join->u.block.stmts;
	*oplin->ipp = ir_stmt_new(JVST_IR_STMT_NOP);

	return cbr;
}

struct jvst_ir_stmt *
ir_add_valid_block(struct op_linearizer *oplin, struct jvst_ir_stmt *stmt)
{
	struct jvst_ir_stmt *vblock, *vstmt;

	if (oplin->valid_block != NULL) {
		return oplin->valid_block;
	}

	vblock = ir_stmt_block(oplin->frame, "valid");
	vstmt = jvst_ir_stmt_copy(stmt);
	assert(vstmt->next == NULL);

	vblock->u.block.stmts = vstmt;
	oplin->valid_block = vblock;

	return vblock;
}

static void
ir_jump_valid_block(struct op_linearizer *oplin, struct jvst_ir_stmt *stmt)
{
	struct jvst_ir_stmt *vblock, *jmp;

	vblock = ir_add_valid_block(oplin, stmt);
	jmp = ir_stmt_new(JVST_IR_STMT_BRANCH);
	jmp->u.branch = vblock;
	*oplin->ipp = jmp;
	oplin->ipp = &jmp->next;
}

static struct jvst_ir_stmt *
ir_add_invalid_block(struct op_linearizer *oplin, int ecode)
{
	struct jvst_ir_stmt *invblock, *jmp;
	struct jvst_ir_stmt *invstmt;
	char *pfx, prefix[64];

	for (invblock = oplin->invalid_blocks; invblock != NULL; invblock = invblock->u.block.block_next) {
		struct jvst_ir_stmt *inv;
		inv = invblock->u.block.stmts;

		assert(inv != NULL);
		assert(inv->type == JVST_IR_STMT_INVALID);
		assert(inv->next == NULL);

		if (inv->u.invalid.code == ecode) {
			return invblock;
		}
	}

	snprintf(prefix, sizeof prefix, "invalid_%d", ecode);
	// XXX - probably a memory leak!  need better handling of string
	// allocation
	pfx = xmalloc(strlen(prefix)+1);
	strcpy(pfx, prefix);

	invblock = ir_stmt_block(oplin->frame, pfx);
	invstmt = ir_stmt_invalid(ecode);
	assert(invstmt->next == NULL);

	invblock->u.block.stmts = invstmt;
	invblock->u.block.block_next = oplin->invalid_blocks;
	oplin->invalid_blocks = invblock;

	return invblock;
}

static void
ir_jump_invalid_block(struct op_linearizer *oplin, struct jvst_ir_stmt *stmt)
{
	struct jvst_ir_stmt *invblock, *jmp;

	assert(stmt->type == JVST_IR_STMT_INVALID);

	invblock = ir_add_invalid_block(oplin, stmt->u.invalid.code);

	jmp = ir_stmt_branch(invblock);
	*oplin->ipp = jmp;
	oplin->ipp = &jmp->next;
}

static void
ir_linearize_stmt(struct op_linearizer *oplin, struct jvst_ir_stmt *stmt)
{
	struct jvst_ir_stmt *linstmt;

	switch (stmt->type) {
	case JVST_IR_STMT_NOP:
	case JVST_IR_STMT_TOKEN:
	case JVST_IR_STMT_CONSUME:
	case JVST_IR_STMT_INCR:
	case JVST_IR_STMT_BSET:
		linstmt = jvst_ir_stmt_copy(stmt);
		*oplin->ipp = linstmt;
		oplin->ipp = &linstmt->next;
		return;

	case JVST_IR_STMT_VALID:
		ir_jump_valid_block(oplin, stmt);
		return;

	case JVST_IR_STMT_INVALID:
		ir_jump_invalid_block(oplin, stmt);
		return;

	case JVST_IR_STMT_FRAME:
		{
			struct jvst_ir_stmt *fr, *call;

			fr = ir_linearize_frame(oplin, stmt);
			call = ir_stmt_new(JVST_IR_STMT_CALL);
			call->u.call.frame = fr;
			*oplin->ipp = call;
			oplin->ipp = &call->next;
		}
		return;

	case JVST_IR_STMT_IF:
		ir_linearize_if(oplin, stmt);
		return;

	case JVST_IR_STMT_SEQ:
		{
			struct op_linearizer seq_oplin;
			struct jvst_ir_stmt *seq;

			seq = ir_stmt_new(JVST_IR_STMT_SEQ);
			*oplin->ipp = seq;
			oplin->ipp = &seq->next;

			seq_oplin = *oplin;
			seq_oplin.ipp = &seq->u.stmt_list;

			ir_linearize_stmtlist(&seq_oplin, stmt->u.stmt_list);

			oplin->valid_block = seq_oplin.valid_block;
			oplin->invalid_blocks = seq_oplin.invalid_blocks;
			oplin->ipp = seq_oplin.ipp;
			oplin->fpp = seq_oplin.fpp;
			oplin->bpp = seq_oplin.bpp;
		}
		return;

	case JVST_IR_STMT_LOOP:
		{
			struct jvst_ir_stmt *block, *end_block, *loopjmp;

			assert(stmt->u.loop.loop_block == NULL);
			assert(stmt->u.loop.end_block == NULL);

			end_block = ir_stmt_block(oplin->frame, "loop_end");
			stmt->u.loop.end_block = end_block;

			block = ir_linearize_block(oplin, "loop", stmt->u.loop.stmts, &LOOP_BLOCK);
			stmt->u.loop.loop_block = block;

			// add to the block list after the loop block to
			// help block sorter order the loop end after
			// the loop body
			*oplin->bpp = end_block;
			oplin->bpp = &end_block->u.block.block_next;

			loopjmp = ir_stmt_branch(block);
			*oplin->ipp = loopjmp;
			oplin->ipp = &loopjmp->next;

			oplin->ipp = &end_block->u.block.stmts;
			*oplin->ipp = ir_stmt_new(JVST_IR_STMT_NOP);
		}
		return;

	case JVST_IR_STMT_BREAK:
		{
			struct jvst_ir_stmt *loop, *end_blk, *jmp;

			loop = stmt->u.break_.loop;
			assert(loop != NULL);

			end_blk = loop->u.loop.end_block;
			assert(end_blk != NULL);
			assert(end_blk->type == JVST_IR_STMT_BLOCK);

			jmp = ir_stmt_new(JVST_IR_STMT_BRANCH);
			jmp->u.branch = end_blk;
			*oplin->ipp = jmp;
			oplin->ipp = &jmp->next;
		}
		return;

	case JVST_IR_STMT_MATCH:
		{
			struct jvst_ir_stmt *join, *mv, *nbr, **blkpp;
			struct jvst_ir_expr *mreg, *match;
			struct jvst_ir_mcase *mc;

			mreg = ir_expr_itemp(oplin->frame);
			match = ir_expr_new(JVST_IR_EXPR_MATCH);
			match->u.match.dfa  = stmt->u.match.dfa;
			match->u.match.name = stmt->u.match.name;
			match->u.match.ind  = stmt->u.match.ind;
			mv = ir_stmt_move(mreg, match);

			*oplin->ipp = mv;
			oplin->ipp = &mv->next;

			join = ir_stmt_block(oplin->frame, "M_join");

			{
				struct jvst_ir_stmt *cblk, *cbr;
				struct jvst_ir_expr *cond;
				cblk = ir_linearize_block(oplin, "M", stmt->u.match.default_case, join);

				cond = ir_expr_new(JVST_IR_EXPR_EQ);
				cond->u.cmp.left  = mreg;
				/// HERE ///
				cond->u.cmp.right = ir_expr_size(0);

				cbr = ir_stmt_new(JVST_IR_STMT_CBRANCH);
				cbr->u.cbranch.cond = cond;
				cbr->u.cbranch.br_true = cblk;
				cbr->u.cbranch.br_false = NULL;

				*oplin->ipp = cbr;
				oplin->ipp = &cbr->next;

				blkpp = &cbr->u.cbranch.br_false;
			}

			for (mc = stmt->u.match.cases; mc != NULL; mc = mc->next) {
				struct jvst_ir_stmt *condblk, *cblk, *cbr, **ipp;
				struct jvst_ir_expr *cond;

				condblk = ir_stmt_block(oplin->frame, "M_next");
				*blkpp = condblk;
				*oplin->bpp = condblk;
				oplin->bpp = &condblk->u.block.block_next;

				ipp = &condblk->u.block.stmts;

				cblk = ir_linearize_block(oplin, "M", mc->stmt, join);

				cond = ir_expr_new(JVST_IR_EXPR_EQ);
				cond->u.cmp.left  = mreg;
				cond->u.cmp.right = ir_expr_size(mc->which);

				cbr = ir_stmt_new(JVST_IR_STMT_CBRANCH);
				cbr->u.cbranch.cond = cond;
				cbr->u.cbranch.br_true = cblk;
				cbr->u.cbranch.br_false = NULL;

				*ipp = cbr;
				ipp = &cbr->next;

				blkpp = &cbr->u.cbranch.br_false;
			}

			// add to the block list after the default and
			// non-default cases to help block sorter place
			// the join after all the cases
			*oplin->bpp = join;
			oplin->bpp = &join->u.block.block_next;

			{
				struct jvst_ir_stmt *eblk;
				eblk = ir_add_invalid_block(oplin, JVST_INVALID_MATCH_CASE);

				*blkpp = eblk;
			}

			oplin->ipp = &join->u.block.stmts;
			*oplin->ipp = ir_stmt_new(JVST_IR_STMT_NOP);
		}
		return;


	case JVST_IR_STMT_SPLITVEC:
		{
			struct jvst_ir_stmt *splitlist, *fr, **fpp, *splv, *bv, *bvc;

			splitlist = ir_stmt_new(JVST_IR_STMT_SPLITLIST);
			splitlist->u.split_list.ind = oplin->frame->u.frame.nsplits++;
			{
				struct jvst_ir_stmt **slpp;
				for (slpp=&oplin->frame->u.frame.splits; *slpp != NULL; slpp = &(*slpp)->next) {
					continue;
				}

				*slpp = splitlist;
			}

			fpp = &splitlist->u.split_list.frames;
			for (fr = stmt->u.splitvec.split_frames; fr != NULL; fr = fr->next) {
				struct jvst_ir_stmt *newfr;

				newfr = ir_linearize_frame(oplin, fr);
				*fpp = newfr;
				fpp = &newfr->u.frame.split_next;
				splitlist->u.split_list.nframes++;
			}

			splv = ir_stmt_new(JVST_IR_STMT_SPLITVEC);
			splv->u.splitvec.split_frames = NULL;
			splv->u.splitvec.split_list = splitlist;

			bv = stmt->u.splitvec.bitvec;
			assert(bv != NULL);
			assert(bv->type == JVST_IR_STMT_BITVECTOR);
			assert(bv->data != NULL);

			bvc = bv->data;
			assert(bvc->type == JVST_IR_STMT_BITVECTOR);

			splv->u.splitvec.bitvec = bvc;

			*oplin->ipp = splv;
			oplin->ipp = &splv->next;
		}
		return;

	case JVST_IR_STMT_BCLEAR:
	case JVST_IR_STMT_DECR:
		fprintf(stderr, "%s:%d (%s) linearizing IR statement %s not yet implemented\n",
				__FILE__, __LINE__, __func__, 
				jvst_ir_stmt_type_name(stmt->type));
		abort();

	case JVST_IR_STMT_COUNTER:
	case JVST_IR_STMT_MATCHER:
	case JVST_IR_STMT_BITVECTOR:
	case JVST_IR_STMT_SPLITLIST:
		fprintf(stderr, "%s:%d (%s) IR statement %s should not be encountered while linearizing\n",
				__FILE__, __LINE__, __func__, 
				jvst_ir_stmt_type_name(stmt->type));
		abort();

	case JVST_IR_STMT_BLOCK:
	case JVST_IR_STMT_BRANCH:
	case JVST_IR_STMT_CBRANCH:
	case JVST_IR_STMT_MOVE:
	case JVST_IR_STMT_CALL:
	case JVST_IR_STMT_PROGRAM:
		fprintf(stderr, "%s:%d (%s) linearized IR statement %s encountered while linearizing\n",
				__FILE__, __LINE__, __func__, 
				jvst_ir_stmt_type_name(stmt->type));
		abort();

	}

	fprintf(stderr, "%s:%d (%s) unknown IR statement type %d\n",
			__FILE__, __LINE__, __func__, stmt->type);
	abort();
}

struct jvst_ir_stmt *
jvst_ir_linearize(struct jvst_ir_stmt *ir)
{
	struct jvst_ir_stmt *prog, *fr;
	size_t frame_ind;
	struct op_linearizer oplin = { 0 };

	assert(ir->type == JVST_IR_STMT_FRAME);
	oplin.frame = NULL;
	oplin.fpp = &oplin.frame;
	oplin.ipp = NULL;

	ir_linearize_frame(&oplin, ir);

	prog = ir_stmt_new(JVST_IR_STMT_PROGRAM);

	for (frame_ind = 1, fr = oplin.frame; fr != NULL; frame_ind++, fr = fr->next) {
		assert(fr->type == JVST_IR_STMT_FRAME);
		fr->u.frame.frame_ind = frame_ind;
	}

	prog->u.program.frames = oplin.frame;
	return prog;
}

void
jvst_ir_print(struct jvst_ir_stmt *stmt)
{
	size_t i;
	// FIXME: gross hack
	char buf[65536] = {0}; // 64K

	jvst_ir_dump(stmt, buf, sizeof buf);
	for (i=0; i < 72; i++) {
		fprintf(stderr, "-");
	}
	fprintf(stderr, "\n");
	fprintf(stderr, "%s\n", buf);
}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
