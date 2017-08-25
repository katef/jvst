#include "validate_testing.h"

#include <assert.h>
#include <string.h>
#include <stdarg.h>

#include "jvst_macros.h"

#include "validate.h"
#include "validate_testing.h"
#include "validate_constraints.h"

int ntest;
int nfail;
int nskipped;

int
report_tests(void)
{
	if (nskipped > 0) {
		printf("%d tests, %d failures, %d skipped\n", ntest, nfail, nskipped);
	} else {
		printf("%d tests, %d failures\n", ntest, nfail);
	}

	return ((nfail == 0) && (ntest > 0)) ?  EXIT_SUCCESS : EXIT_FAILURE;
}

enum { NUM_TEST_THINGS = 1024 };

// arena allocators to make it easy to programmatically set up a schema
static struct ast_schema ar_schema[NUM_TEST_THINGS];
static struct ast_property_schema ar_props[NUM_TEST_THINGS];
static struct ast_string_set ar_stringsets[NUM_TEST_THINGS];
static struct ast_property_names ar_propnames[NUM_TEST_THINGS];
static struct ast_schema_set ar_schemasets[NUM_TEST_THINGS];

static struct jvst_cnode ar_cnodes[NUM_TEST_THINGS];
static struct jvst_cnode_matchset ar_cnode_matchsets[NUM_TEST_THINGS];

static struct jvst_ir_stmt ar_ir_stmts[NUM_TEST_THINGS];
static struct jvst_ir_expr ar_ir_exprs[NUM_TEST_THINGS];
static struct jvst_ir_mcase ar_ir_mcases[NUM_TEST_THINGS];
static size_t ar_ir_splitinds[NUM_TEST_THINGS];

static struct jvst_op_program ar_op_prog[NUM_TEST_THINGS];
static struct jvst_op_proc ar_op_proc[NUM_TEST_THINGS];
static struct jvst_op_instr ar_op_instr[NUM_TEST_THINGS];

static double ar_op_float[NUM_TEST_THINGS];
static int64_t ar_op_iconst[NUM_TEST_THINGS];
static struct jvst_op_proc *ar_op_splits[NUM_TEST_THINGS];
static size_t ar_op_splitmax[NUM_TEST_THINGS];

enum { NUM_VM_PROGRAMS = 64 };
static struct jvst_vm_program ar_vm_progs[NUM_VM_PROGRAMS];
static uint32_t ar_vm_code[NUM_TEST_THINGS];

// Returns a constant empty schema
struct ast_schema *
empty_schema(void)
{
	static struct ast_schema empty = {0};
	return &empty;
}

struct json_string
newstr(const char *s)
{
	struct json_string str = {.s = s, .len = strlen(s)};
	return str;
}

static struct ast_string_set *
stringset_alloc(struct arena_info *A)
{
	struct ast_string_set *elt;
	size_t i, max;

	max = ARRAYLEN(ar_stringsets);
	i   = A->nstr++;
	if (A->nstr >= max) {
		fprintf(stderr, "too many string sets: %zu max\n", max);
		abort();
	}

	elt = &ar_stringsets[i];
	memset(elt, 0, sizeof *elt);

	return elt;
}

struct ast_string_set *
stringset(struct arena_info *A, ...)
{
	struct ast_string_set *ss = NULL, **ssp = &ss;
	va_list args;

	va_start(args, A);
	for (;;) {
		struct ast_string_set *elt;
		struct json_string str;
		const char *s;
		size_t i;

		if (s = va_arg(args, const char *), s == NULL) {
			break;
		}

		elt      = stringset_alloc(A);
		elt->str = newstr(s);
		*ssp     = elt;
		ssp      = &elt->next;
	}
	va_end(args);

	return ss;
}

struct ast_schema_set *
schema_set(struct arena_info *A, ...)
{
	struct ast_schema_set *sset, **sp;
	struct ast_schema *s;
	size_t max;
	va_list args;

	va_start(args, A);

	sset = NULL;
	sp   = &sset;
	max  = sizeof ar_schemasets / sizeof ar_schemasets[0];
	while (s = va_arg(args, struct ast_schema *), s != NULL) {
		struct ast_schema_set *elt;
		size_t i;

		i = A->nset++;
		if (A->nset >= max) {
			fprintf(stderr, "too many schema sets: %zu max\n", max);
			abort();
		}

		elt = &ar_schemasets[i];
		memset(elt, 0, sizeof *elt);
		elt->schema = s;
		*sp	 = elt;
		sp	  = &elt->next;
	}

	va_end(args);

	return sset;
}

size_t
schema_set_count(struct ast_schema_set *s)
{
	size_t n;
	for (n = 0; s != NULL; s = s->next, n++) {
		continue;
	}

	return n;
}

struct ast_property_names *
newpropnames(struct arena_info *A, ...)
{
	size_t i, max;
	struct ast_property_names *pnames, **pp;
	va_list args;

	pnames = NULL;
	pp     = &pnames;

	va_start(args, A);
	for (;;) {
		const char *n;
		struct ast_string_set *set;

		n = va_arg(args, const char *);
		if (n == NULL) {
			break;
		}

		set = va_arg(args, struct ast_string_set *);
		i   = A->npnames++;
		max = ARRAYLEN(ar_propnames);
		if (A->nschema >= max) {
			fprintf(stderr, "too many schema: %zu max\n", max);
			abort();
		}

		*pp = &ar_propnames[i];
		memset(*pp, 0, sizeof **pp);
		(*pp)->set	     = set;
		(*pp)->pattern.dialect = RE_LITERAL;
		(*pp)->pattern.str     = newstr(n);
		(*pp)->pattern.fsm     = NULL;

		pp = &(*pp)->next;
	}
	va_end(args);

	return pnames;
}

struct ast_schema *
newschema(struct arena_info *A, int types)
{
	size_t i, max;
	struct ast_schema *s;

	i   = A->nschema++;
	max = sizeof ar_schema / sizeof ar_schema[0];
	if (A->nschema >= max) {
		fprintf(stderr, "too many schema: %zu max\n", max);
		abort();
	}

	s = &ar_schema[i];
	memset(s, 0, sizeof *s);
	s->types = types;
	return s;
}

struct ast_schema *
newschema_p(struct arena_info *A, int types, ...)
{
	size_t i, max;
	struct ast_schema *s;
	const char *pname;
	va_list args;

	i   = A->nschema++;
	max = ARRAYLEN(ar_schema);
	if (A->nschema >= max) {
		fprintf(stderr, "too many schema: %zu max\n", max);
		abort();
	}

	s = &ar_schema[i];
	memset(s, 0, sizeof *s);
	s->types = types;

	va_start(args, types);
	for (;;) {
		pname = va_arg(args, const char *);
		if (pname == NULL) {
			break;
		}

		// big dumb if-else chain gets the job done...
		if (strcmp(pname, "minProperties") == 0) {
			s->kws |= KWS_MINMAX_PROPERTIES;
			s->min_properties = va_arg(args, ast_count);
		} else if (strcmp(pname, "maxProperties") == 0) {
			s->kws |= KWS_MINMAX_PROPERTIES;
			s->max_properties = va_arg(args, ast_count);
		} else if (strcmp(pname, "properties") == 0) {
			s->properties.set = va_arg(args, struct ast_property_schema *);
		} else if (strcmp(pname, "required") == 0) {
			s->required.set = va_arg(args, struct ast_string_set *);
		} else if (strcmp(pname, "minimum") == 0) {
			s->kws |= KWS_MINIMUM;
			s->minimum = va_arg(args, double);
		} else if (strcmp(pname, "dep_strings") == 0) {
			s->dependencies_strings.set = va_arg(args, struct ast_property_names *);
		} else if (strcmp(pname, "dep_schema") == 0) {
			s->dependencies_schema.set = va_arg(args, struct ast_property_schema *);
		} else if (strcmp(pname, "anyOf") == 0) {
			struct ast_schema_set *sset;
			sset = va_arg(args, struct ast_schema_set *);
			s->some_of.set = sset;
			s->some_of.min = 1;
			s->some_of.max = schema_set_count(sset);
		} else if (strcmp(pname, "allOf") == 0) {
			struct ast_schema_set *sset;
			sset = va_arg(args, struct ast_schema_set *);
			s->some_of.set = sset;
			s->some_of.min = schema_set_count(sset);
			s->some_of.max = s->some_of.min;
		} else if (strcmp(pname, "oneOf") == 0) {
			struct ast_schema_set *sset;
			sset = va_arg(args, struct ast_schema_set *);
			s->some_of.set = sset;
			s->some_of.min = 1;
			s->some_of.max = 1;
		} else {
			// okay to abort() a test if the test writer forgot to add a
			// property to the big dumb if-else chain
			fprintf(stderr, "unsupported schema property '%s'\n", pname);
			abort();
		}
	}
	va_end(args);

	return s;
}

struct ast_property_schema *
newprops(struct arena_info *A, ...)
{
	struct ast_property_schema *props = NULL;
	struct ast_property_schema **pp   = &props;
	size_t max			  = sizeof ar_props / sizeof ar_props[0];
	va_list args;

	va_start(args, A);

	for (;;) {
		const char *name;
		struct ast_schema *schema;
		struct ast_property_schema *p;
		size_t i;

		name = va_arg(args, const char *);
		if (name == NULL) {
			break;
		}

		i = A->nprop++;
		if (A->nprop >= max) {
			fprintf(stderr, "too many properties: %zu max\n", max);
			abort();
		}

		p = &ar_props[i];
		memset(p, 0, sizeof *p);

		p->pattern.str     = newstr(name);
		p->pattern.dialect = RE_LITERAL;
		p->schema	  = va_arg(args, struct ast_schema *);

		*pp = p;
		pp  = &p->next;
	}

	va_end(args);

	return props;
}

const char *
jvst_ret2name(int ret)
{
	switch (ret) {
	case JVST_INVALID:
		return "INVALID";
	case JVST_VALID:
		return "VALID";
	case JVST_MORE:
		return "MORE";
	default:
		return "UNKNOWN";
	}
}

struct jvst_cnode *
newcnode_valid(void)
{
	static struct jvst_cnode n = {.type = JVST_CNODE_VALID};
	return &n;
}

struct jvst_cnode *
newcnode_invalid(void)
{
	static struct jvst_cnode n = {.type = JVST_CNODE_INVALID};
	return &n;
}

struct jvst_cnode *
newcnode(struct arena_info *A, enum jvst_cnode_type type)
{
	size_t i, max;
	struct jvst_cnode *node;
	const char *pname;

	i   = A->ncnode++;
	max = ARRAYLEN(ar_cnodes);
	if (A->ncnode >= max) {
		fprintf(stderr, "too many cnodes: %zu max\n", max);
		abort();
	}

	node = &ar_cnodes[i];
	memset(node, 0, sizeof *node);
	node->type = type;

	return node;
}

struct jvst_cnode *
newcnode_switch(struct arena_info *A, int isvalid, ...)
{
	struct jvst_cnode *node;
	size_t i;
	va_list args;

	node = newcnode(A, JVST_CNODE_SWITCH);
	for (i = 0; i < SJP_EVENT_MAX; i++) {
		node->u.sw[i] = isvalid ? newcnode_valid() : newcnode_invalid();
	}

	// ARRAY_END and OBJECT_END should not be valid by default...
	node->u.sw[SJP_ARRAY_END]  = newcnode_invalid();
	node->u.sw[SJP_OBJECT_END] = newcnode_invalid();

	va_start(args, isvalid);
	for (;;) {
		enum SJP_EVENT evt;
		struct jvst_cnode *child;

		evt = va_arg(args, enum SJP_EVENT);
		if (evt == SJP_NONE) {
			break;
		}

		if (evt >= SJP_EVENT_MAX) {
			fprintf(stderr, "invalid event %d\n", evt);
			abort();
		}

		child		= va_arg(args, struct jvst_cnode *);
		node->u.sw[evt] = child;
	}
	va_end(args);

	return node;
}

struct jvst_cnode *
newcnode_bool(struct arena_info *A, enum jvst_cnode_type type, ...)
{
	struct jvst_cnode *node, **pp;
	va_list args;

	if ((type != JVST_CNODE_AND) && (type != JVST_CNODE_OR) && (type != JVST_CNODE_XOR)) {
		fprintf(stderr, "invalid cnode type for %s: %d\n", __func__, type);
		abort();
	}

	node = newcnode(A, type);
	pp   = &node->u.ctrl;
	*pp  = NULL;

	va_start(args, type);
	for (;;) {
		struct jvst_cnode *child;

		child = va_arg(args, struct jvst_cnode *);
		if (child == NULL) {
			break;
		}

		*pp = child;
		pp  = &child->next;
	}
	va_end(args);

	return node;
}

struct jvst_cnode *
newcnode_propset(struct arena_info *A, ...)
{
	struct jvst_cnode *node, **mlp;
	va_list args;

	node = newcnode(A, JVST_CNODE_OBJ_PROP_SET);
	mlp  = &node->u.prop_set;
	*mlp = NULL;

	va_start(args, A);
	for (;;) {
		struct jvst_cnode *match;
		match = va_arg(args, struct jvst_cnode *);
		if (match == NULL) {
			break;
		}
		*mlp = match;
		mlp  = &(*mlp)->next;
	}
	va_end(args);

	return node;
}

struct jvst_cnode *
newcnode_prop_match(struct arena_info *A, enum re_dialect dialect, const char *pat,
		    struct jvst_cnode *constraint)
{
	struct jvst_cnode *node;

	node = newcnode(A, JVST_CNODE_OBJ_PROP_MATCH);

	node->u.prop_match.match.dialect = dialect;
	node->u.prop_match.match.str     = newstr(pat);
	node->u.prop_match.match.fsm     = NULL;
	node->u.prop_match.constraint    = constraint;

	return node;
}

struct jvst_cnode *
newcnode_range(struct arena_info *A, enum jvst_cnode_rangeflags flags, double min, double max)
{
	struct jvst_cnode *node, **pp;
	node = newcnode(A, JVST_CNODE_NUM_RANGE);
	node->u.num_range.flags = flags;
	node->u.num_range.min   = min;
	node->u.num_range.max   = max;
	return node;
}

struct jvst_cnode *
newcnode_counts(struct arena_info *A, size_t min, size_t max)
{
	struct jvst_cnode *node, **pp;
	node = newcnode(A, JVST_CNODE_COUNT_RANGE);
	node->u.counts.min = min;
	node->u.counts.max = max;
	return node;
}

struct jvst_cnode *
newcnode_required(struct arena_info *A, struct ast_string_set *sset)
{
	struct ast_string_set **spp;
	struct jvst_cnode *node;
	va_list args;

	node = newcnode(A, JVST_CNODE_OBJ_REQUIRED);
	node->u.required = sset;

	return node;
}

struct jvst_cnode *
newcnode_reqmask(struct arena_info *A, size_t nbits)
{
	struct jvst_cnode *node;

	node = newcnode(A, JVST_CNODE_OBJ_REQMASK);
	node->u.reqmask.nbits = nbits;

	return node;
}

struct jvst_cnode *
newcnode_reqbit(struct arena_info *A, size_t bit)
{
	struct jvst_cnode *node;

	node = newcnode(A, JVST_CNODE_OBJ_REQBIT);
	node->u.reqbit.bit = bit;

	return node;
}

struct jvst_cnode *
newcnode_mswitch(struct arena_info *A, struct jvst_cnode *dft, ...)
{
	struct jvst_cnode *node, **cpp;
	va_list args;

	node = newcnode(A, JVST_CNODE_MATCH_SWITCH);
	node->u.mswitch.default_case = dft;
	cpp = &node->u.mswitch.cases;

	va_start(args, dft);
	for(;;) {
		struct jvst_cnode *c;
		c = va_arg(args, struct jvst_cnode *);
		if (c == NULL) {
			break;
		}

		*cpp = c;
		cpp = &(*cpp)->next;
	}
	va_end(args);

	return node;
}

struct jvst_cnode *
newcnode_mcase(struct arena_info *A, struct jvst_cnode_matchset *mset,
	struct jvst_cnode *constraint)
{
	struct jvst_cnode *node;
	node = newcnode(A, JVST_CNODE_MATCH_CASE);
	node->u.mcase.matchset = mset;
	node->u.mcase.constraint = constraint;

	return node;
}

static struct jvst_cnode_matchset *
newmatchset_alloc(struct arena_info *A)
{
	size_t i, max;
	struct jvst_cnode_matchset *mset;

	i   = A->nmatchsets++;
	max = ARRAYLEN(ar_cnode_matchsets);
	if (i >= max) {
		fprintf(stderr, "too many cnode matchsets: %zu max\n", max);
		abort();
	}

	mset = &ar_cnode_matchsets[i];
	memset(mset, 0, sizeof *mset);
	return mset;
}

struct jvst_cnode_matchset *
newmatchset(struct arena_info *A, ...)
{
	struct jvst_cnode_matchset *head, **mspp;
	va_list args;

	head = NULL;
	mspp = &head;

	va_start(args, A);
	for (;;) {
		struct jvst_cnode_matchset *mset;
		int dialect;
		const char *pat;

		dialect = va_arg(args, int);
		if (dialect == -1) {
			break;
		}
		pat = va_arg(args, const char *);

		mset = newmatchset_alloc(A);
		mset->match.dialect = dialect;
		mset->match.str = newstr(pat);

		*mspp = mset;
		mspp = &(*mspp)->next;
	}
	va_end(args);

	return head;
}

struct jvst_ir_expr *
newir_expr(struct arena_info *A, enum jvst_ir_expr_type type)
{
	size_t i, max;
	struct jvst_ir_expr *expr;

	i   = A->nexpr++;
	max = ARRAYLEN(ar_ir_exprs);
	if (A->nexpr >= max) {
		fprintf(stderr, "too many IR expr nodes: %zu max\n", max);
		abort();
	}

	expr = &ar_ir_exprs[i];
	memset(expr, 0, sizeof *expr);
	expr->type = type;

	return expr;
}

struct jvst_ir_stmt v_frameindex;
struct jvst_ir_stmt v_splitlist;
const struct jvst_ir_stmt *const frameindex = &v_frameindex;
const struct jvst_ir_stmt *const splitlist = &v_splitlist;

struct jvst_ir_stmt *
newir_stmt(struct arena_info *A, enum jvst_ir_stmt_type type)
{
	size_t i, max;
	struct jvst_ir_stmt *stmt;

	i   = A->nstmt++;
	max = ARRAYLEN(ar_ir_stmts);
	if (A->nstmt >= max) {
		fprintf(stderr, "too many IR stmt nodes: %zu max\n", max);
		abort();
	}

	stmt = &ar_ir_stmts[i];
	memset(stmt, 0, sizeof *stmt);
	stmt->type = type;

	return stmt;
}

struct jvst_ir_stmt *
newir_invalid(struct arena_info *A, int code, const char *msg)
{
	struct jvst_ir_stmt *stmt;
	stmt = newir_stmt(A,JVST_IR_STMT_INVALID);
	stmt->u.invalid.code = code;
	stmt->u.invalid.msg = msg;
	return stmt;
}

static void ir_stmt_list(struct jvst_ir_stmt **spp, va_list args)
{
	struct jvst_ir_stmt *stmt;

	*spp = NULL;
	stmt = va_arg(args, struct jvst_ir_stmt *);
	for(; stmt != NULL; stmt = va_arg(args, struct jvst_ir_stmt *)) {
		*spp = stmt;
		spp = &(*spp)->next;
	}
}

struct jvst_ir_stmt *
newir_frame(struct arena_info *A, ...)
{
	struct jvst_ir_stmt *fr, **spp, **cpp, **mpp, **bvpp, **slpp;
	va_list args;

	fr = newir_stmt(A,JVST_IR_STMT_FRAME);
	va_start(args, A);
	spp = &fr->u.frame.stmts;
	*spp = NULL;

	cpp = &fr->u.frame.counters;
	mpp = &fr->u.frame.matchers;
	bvpp = &fr->u.frame.bitvecs;
	slpp = &fr->u.frame.splits;

	for (;;) {
		struct jvst_ir_stmt *stmt;

		stmt = va_arg(args, struct jvst_ir_stmt *);
		if (stmt == NULL) {
			goto end_loop;
		}

		if (stmt == frameindex) {
			fr->u.frame.frame_ind = (size_t)va_arg(args, int);
			continue;
		}

		switch (stmt->type) {
		case JVST_IR_STMT_COUNTER:
			fr->u.frame.ncounters++;
			*cpp = stmt;
			cpp = &stmt->next;
			break;

		case JVST_IR_STMT_MATCHER:
			fr->u.frame.nmatchers++;
			*mpp = stmt;
			mpp = &stmt->next;
			break;

		case JVST_IR_STMT_BITVECTOR:
			fr->u.frame.nbitvecs++;
			*bvpp = stmt;
			bvpp = &stmt->next;
			break;

		case JVST_IR_STMT_SPLITLIST:
			fr->u.frame.nsplits++;
			*slpp = stmt;
			slpp = &stmt->next;
			break;

		default:
			*spp = stmt;
			spp = &stmt->next;
			break;
		}
	}

end_loop:
	va_end(args);

	assert(fr->u.frame.stmts != NULL);
	return fr;
}

struct jvst_ir_stmt *
newir_program(struct arena_info *A, ...)
{
	struct jvst_ir_stmt *prog, **fpp;
	va_list args;

	prog = newir_stmt(A,JVST_IR_STMT_PROGRAM);
	fpp = &prog->u.program.frames;

	va_start(args, A);
	for(;;) {
		struct jvst_ir_stmt *fr;

		fr = va_arg(args, struct jvst_ir_stmt *);
		if (fr == NULL) {
			break;
		}

		assert(fr->type == JVST_IR_STMT_FRAME);
		*fpp = fr;
		fpp = &fr->next;
	}
	va_end(args);

	assert(prog->u.program.frames != NULL);
	return prog;
}

struct jvst_ir_stmt *
newir_seq(struct arena_info *A, ...)
{
	struct jvst_ir_stmt *seq;
	va_list args;

	seq = newir_stmt(A,JVST_IR_STMT_SEQ);
	va_start(args, A);
	ir_stmt_list(&seq->u.stmt_list, args);
	va_end(args);

	return seq;
}

struct jvst_ir_stmt *
newir_block(struct arena_info *A, size_t lind, const char *prefix, ...)
{
	struct jvst_ir_stmt *blk;
	va_list args;

	blk = newir_stmt(A,JVST_IR_STMT_BLOCK);
	blk->u.block.lindex  = lind;
	blk->u.block.prefix = prefix;

	va_start(args, prefix);
	ir_stmt_list(&blk->u.block.stmts, args);
	va_end(args);

	return blk;
}

struct jvst_ir_stmt *
newir_branch(struct arena_info *A, size_t lind, const char *prefix)
{
	struct jvst_ir_stmt *br, *blk;

	blk = newir_stmt(A,JVST_IR_STMT_BLOCK);
	blk->u.block.lindex  = lind;
	blk->u.block.prefix = prefix;

	br = newir_stmt(A,JVST_IR_STMT_BRANCH);
	br->u.branch = blk;

	return br;
}

struct jvst_ir_stmt *
newir_cbranch(struct arena_info *A,
	struct jvst_ir_expr *cond,
	size_t li_true, const char *pfx_true,
	size_t li_false, const char *pfx_false)
{
	struct jvst_ir_stmt *cbr, *t_blk, *f_blk;

	t_blk = newir_stmt(A,JVST_IR_STMT_BLOCK);
	t_blk->u.block.lindex  = li_true;
	t_blk->u.block.prefix = pfx_true;

	f_blk = newir_stmt(A,JVST_IR_STMT_BLOCK);
	f_blk->u.block.lindex  = li_false;
	f_blk->u.block.prefix = pfx_false;

	cbr = newir_stmt(A,JVST_IR_STMT_CBRANCH);
	cbr->u.cbranch.cond = cond;
	cbr->u.cbranch.br_true = t_blk;
	cbr->u.cbranch.br_false = f_blk;

	return cbr;
}

struct jvst_ir_stmt *
newir_loop(struct arena_info *A, const char *loopname, size_t ind, ...)
{
	struct jvst_ir_stmt *loop;
	va_list args;

	loop = newir_stmt(A,JVST_IR_STMT_LOOP);
	loop->u.loop.name = loopname;
	loop->u.loop.ind  = ind;
	va_start(args, ind);
	ir_stmt_list(&loop->u.loop.stmts, args);
	va_end(args);

	return loop;
}

struct jvst_ir_stmt *
newir_break(struct arena_info *A, const char *loopname, size_t ind)
{
	struct jvst_ir_stmt *stmt;
	stmt = newir_stmt(A,JVST_IR_STMT_BREAK);
	stmt->u.break_.name = loopname;
	stmt->u.break_.ind  = ind;
	stmt->u.break_.loop = NULL;

	return stmt;
}

struct jvst_ir_stmt *
newir_if(struct arena_info *A, struct jvst_ir_expr *cond,
	struct jvst_ir_stmt *br_true, struct jvst_ir_stmt *br_false)
{
	struct jvst_ir_stmt *br;
	va_list args;

	br = newir_stmt(A,JVST_IR_STMT_IF);
	br->u.if_.cond = cond;
	br->u.if_.br_true = br_true;
	br->u.if_.br_false = br_false;

	return br;
}

struct jvst_ir_stmt *
newir_counter(struct arena_info *A, size_t ind, const char *label)
{
	struct jvst_ir_stmt *stmt;

	stmt = newir_stmt(A,JVST_IR_STMT_COUNTER);
	stmt->u.counter.ind = ind;
	stmt->u.counter.label = label;

	return stmt;
}

struct jvst_ir_stmt *
newir_matcher(struct arena_info *A, size_t ind, const char *name)
{
	struct jvst_ir_stmt *stmt;

	stmt = newir_stmt(A,JVST_IR_STMT_MATCHER);
	stmt->u.matcher.ind = ind;
	stmt->u.matcher.name = name;

	return stmt;
}

struct jvst_ir_stmt *
newir_bitvec(struct arena_info *A, size_t ind, const char *label, size_t nbits)
{
	struct jvst_ir_stmt *stmt;

	stmt = newir_stmt(A,JVST_IR_STMT_BITVECTOR);
	stmt->u.bitvec.ind = ind;
	stmt->u.bitvec.label = label;
	stmt->u.bitvec.nbits = nbits;

	return stmt;
}

struct jvst_ir_stmt *
newir_match(struct arena_info *A, size_t ind, ...)
{
	struct jvst_ir_stmt *stmt;
	struct jvst_ir_mcase *c, **cpp;
	va_list args;

	stmt = newir_stmt(A,JVST_IR_STMT_MATCH);
	stmt->u.match.ind = ind;
	stmt->u.match.cases = NULL;

	cpp = &stmt->u.match.cases;
	va_start(args, ind);
	c = va_arg(args, struct jvst_ir_mcase *);
	for(; c != NULL; c = va_arg(args, struct jvst_ir_mcase *)) {
		// filter cases for which==0, which we turn into the default
		// case
		//
		// FIXME: should probably give this as an explicit arg...
		if (c->which == 0) {
			stmt->u.match.default_case = c->stmt;
			continue;
		}

		*cpp = c;
		cpp = &(*cpp)->next;
	}
	va_end(args);

	return stmt;
}

struct jvst_ir_stmt *
newir_splitlist(struct arena_info *A, size_t ind, size_t n, ...)
{
	size_t i;
	va_list args;
	struct jvst_ir_stmt *sl, **fpp;
	size_t off,max, *inds;

	sl = newir_stmt(A,JVST_IR_STMT_SPLITLIST);
	sl->u.split_list.ind = ind;
	sl->u.split_list.nframes = n;

	if (n == 0) {
		return sl;
	}

	off = A->nsplitinds;
	max = ARRAYLEN(ar_ir_splitinds);
	if (off+n >= max) {
		fprintf(stderr, "too many IR split indices: %zu max\n", max);
		abort();
	}

	A->nsplitinds += n;
	inds = &ar_ir_splitinds[off];

	va_start(args, n);
	for (i=0; i < n; i++) {
		size_t ind;

		inds[i] = (size_t)va_arg(args, int);
	}
	va_end(args);

	sl->u.split_list.frame_indices = inds;

	return sl;
}

struct jvst_ir_stmt *
newir_splitvec(struct arena_info *A, size_t ind, const char *label, ...)
{
	struct jvst_ir_stmt *stmt, **spp, *fr, *bv;
	va_list args;

	stmt = newir_stmt(A,JVST_IR_STMT_SPLITVEC);
	bv = newir_stmt(A, JVST_IR_STMT_BITVECTOR);
	bv->u.bitvec.label = label;
	bv->u.bitvec.ind = ind;

	stmt->u.splitvec.bitvec = bv;

	spp = &stmt->u.splitvec.split_frames;

	va_start(args, label);
	while (fr = va_arg(args, struct jvst_ir_stmt *), fr != NULL) {
		if (fr == splitlist) {
			struct jvst_ir_stmt *sl;
			size_t ind;

			assert(stmt->u.splitvec.split_frames == NULL);

			ind = va_arg(args, int);
			assert(ind >= 0);
			stmt->u.splitvec.split_list = newir_splitlist(A, (size_t)ind, 0);
			goto end;
		}

		assert(fr->type == JVST_IR_STMT_FRAME);
		*spp = fr;
		spp = &(*spp)->next;
	}

end:
	va_end(args);
	return stmt;
}

struct jvst_ir_stmt *
newir_incr(struct arena_info *A, size_t ind, const char *label)
{
	struct jvst_ir_stmt *stmt;

	stmt = newir_stmt(A,JVST_IR_STMT_INCR);
	stmt->u.counter_op.ind = ind;
	stmt->u.counter_op.label = label;

	return stmt;
}

struct jvst_ir_stmt *
newir_bitop(struct arena_info *A, enum jvst_ir_stmt_type op, size_t ind, const char *label, size_t bit)
{
	struct jvst_ir_stmt *stmt, *bv;

	assert((op == JVST_IR_STMT_BSET) || (op == JVST_IR_STMT_BCLEAR));

	// should really link this up, but we currently cheese it...
	bv = newir_stmt(A,JVST_IR_STMT_BITVECTOR);
	bv->u.bitvec.label = label;
	bv->u.bitvec.ind = ind;

	stmt = newir_stmt(A,op);
	stmt->u.bitop.bitvec = bv;
	stmt->u.bitop.bit = bit;

	return stmt;
}

struct jvst_ir_stmt *
newir_move(struct arena_info *A, struct jvst_ir_expr *tmp, struct jvst_ir_expr *expr)
{
	struct jvst_ir_stmt *mv;

	assert(tmp->type == JVST_IR_EXPR_FTEMP || tmp->type == JVST_IR_EXPR_ITEMP);

	// should really link this up, but we currently cheese it...
	mv = newir_stmt(A,JVST_IR_STMT_MOVE);
	mv->u.move.dst = tmp;
	mv->u.move.src = expr;

	return mv;
}

struct jvst_ir_stmt *
newir_call(struct arena_info *A, size_t frame_ind)
{
	struct jvst_ir_stmt *stmt, *fr;

	assert(frame_ind > 0);

	// should really link this up, but we currently cheese it...
	fr = newir_stmt(A,JVST_IR_STMT_FRAME);
	fr->u.frame.frame_ind = frame_ind;

	stmt = newir_stmt(A,JVST_IR_STMT_CALL);
	stmt->u.call.frame = fr;

	return stmt;
}

struct jvst_ir_mcase *
newir_case(struct arena_info *A, size_t ind, struct jvst_cnode_matchset *mset, struct jvst_ir_stmt *frame)
{
	size_t i, max;
	struct jvst_ir_mcase *c;

	i = A->nmcases++;
	max = ARRAYLEN(ar_ir_mcases);
	if (A->nexpr >= max) {
		fprintf(stderr, "too many IR expr nodes: %zu max\n", max);
		abort();
	}

	c  = &ar_ir_mcases[i];
	memset(c , 0, sizeof *c );
	c->which = ind;
	c->matchset = mset;
	c->stmt = frame;

	return c;
}

struct jvst_ir_expr *
newir_istok(struct arena_info *A, enum SJP_EVENT tt)
{
	struct jvst_ir_expr *expr;
	expr = newir_expr(A,JVST_IR_EXPR_ISTOK);
	expr->u.istok.tok_type = tt;
	return expr;
}

struct jvst_ir_expr *
newir_isint(struct arena_info *A, struct jvst_ir_expr *arg)
{
	struct jvst_ir_expr *expr;
	expr = newir_expr(A,JVST_IR_EXPR_ISINT);
	expr->u.isint.arg = arg;
	return expr;
}

struct jvst_ir_expr *
newir_num(struct arena_info *A, double num)
{
	struct jvst_ir_expr *expr;
	expr = newir_expr(A,JVST_IR_EXPR_NUM);
	expr->u.vnum = num;
	return expr;
}

struct jvst_ir_expr *
newir_size(struct arena_info *A, size_t sz)
{
	struct jvst_ir_expr *expr;
	expr = newir_expr(A,JVST_IR_EXPR_SIZE);
	expr->u.vsize = sz;
	return expr;
}

struct jvst_ir_expr *
newir_count(struct arena_info *A, size_t ind, const char *label)
{
	struct jvst_ir_expr *expr;
	expr = newir_expr(A,JVST_IR_EXPR_COUNT);
	expr->u.count.label = label;
	expr->u.count.ind = ind;
	return expr;
}

struct jvst_ir_expr *
newir_btest(struct arena_info *A, size_t ind, const char *label, size_t b)
{
	struct jvst_ir_expr *expr;
	struct jvst_ir_stmt *bv;

	// should really link this up, but we currently cheese it...
	bv = newir_stmt(A,JVST_IR_STMT_BITVECTOR);
	bv->u.bitvec.label = label;
	bv->u.bitvec.ind = ind;

	expr = newir_expr(A,JVST_IR_EXPR_BTEST);
	expr->u.btest.bitvec = bv;
	expr->u.btest.b0 = b;
	expr->u.btest.b1 = b;
	return expr;
}

struct jvst_ir_expr *
newir_btestall(struct arena_info *A, size_t ind, const char *label, size_t b0, size_t b1)
{
	struct jvst_ir_expr *expr;
	struct jvst_ir_stmt *bv;

	// should really link this up, but we currently cheese it...
	bv = newir_stmt(A,JVST_IR_STMT_BITVECTOR);
	bv->u.bitvec.label = label;
	bv->u.bitvec.ind = ind;

	expr = newir_expr(A,JVST_IR_EXPR_BTESTALL);
	expr->u.btest.bitvec = bv;
	expr->u.btest.b0 = b0;
	expr->u.btest.b1 = b1;
	return expr;
}

struct jvst_ir_expr *
newir_btestany(struct arena_info *A, size_t ind, const char *label, size_t b0, size_t b1)
{
	struct jvst_ir_expr *expr;
	struct jvst_ir_stmt *bv;

	// should really link this up, but we currently cheese it...
	bv = newir_stmt(A,JVST_IR_STMT_BITVECTOR);
	bv->u.bitvec.label = label;
	bv->u.bitvec.ind = ind;

	expr = newir_expr(A,JVST_IR_EXPR_BTESTANY);
	expr->u.btest.bitvec = bv;
	expr->u.btest.b0 = b0;
	expr->u.btest.b1 = b1;
	return expr;
}

struct jvst_ir_expr *
newir_split(struct arena_info *A, ...)
{
	struct jvst_ir_expr *expr;
	struct jvst_ir_stmt **spp, *fr;
	va_list args;

	expr = newir_expr(A,JVST_IR_EXPR_SPLIT);
	spp = &expr->u.split.frames;

	va_start(args, A);
	while (fr = va_arg(args, struct jvst_ir_stmt *), fr != NULL) {
		if (fr == splitlist) {
			struct jvst_ir_stmt *sl;
			size_t ind;

			assert(expr->u.split.frames == NULL);

			ind = va_arg(args, int);
			assert(ind >= 0);
			expr->u.split.split_list = newir_splitlist(A, (size_t)ind, 0);
			goto end;
		}

		assert(fr->type == JVST_IR_STMT_FRAME);
		*spp = fr;
		spp = &(*spp)->next;
	}

end:
	va_end(args);
	return expr;
}

struct jvst_ir_expr *
newir_itemp(struct arena_info *A, size_t ind)
{
	struct jvst_ir_expr *expr;

	expr = newir_expr(A,JVST_IR_EXPR_ITEMP);
	expr->u.temp.ind = ind;

	return expr;
}

struct jvst_ir_expr *
newir_ftemp(struct arena_info *A, size_t ind)
{
	struct jvst_ir_expr *expr;

	expr = newir_expr(A,JVST_IR_EXPR_FTEMP);
	expr->u.temp.ind = ind;

	return expr;
}

struct jvst_ir_expr *
newir_slot(struct arena_info *A, size_t ind)
{
	struct jvst_ir_expr *expr;

	expr = newir_expr(A,JVST_IR_EXPR_SLOT);
	expr->u.slot.ind = ind;

	return expr;
}

struct jvst_ir_expr *
newir_eseq(struct arena_info *A, struct jvst_ir_stmt *stmt, struct jvst_ir_expr *expr)
{
	struct jvst_ir_expr *eseq;

	eseq = newir_expr(A,JVST_IR_EXPR_SEQ);
	eseq->u.seq.stmt = stmt;
	eseq->u.seq.expr = expr;

	return eseq;
}

struct jvst_ir_expr *
newir_ematch(struct arena_info *A, size_t mind)
{
	struct jvst_ir_expr *ematch;

	ematch = newir_expr(A,JVST_IR_EXPR_MATCH);
	ematch->u.match.ind = mind;

	return ematch;
}

struct jvst_ir_expr *
newir_op(struct arena_info *A, enum jvst_ir_expr_type op,
		struct jvst_ir_expr *left,
		struct jvst_ir_expr *right)
{
	struct jvst_ir_expr *expr;

	switch (op) {
	case JVST_IR_EXPR_AND:
	case JVST_IR_EXPR_OR:
		expr = newir_expr(A,op);
		expr->u.and_or.left = left;
		expr->u.and_or.right = right;
		break;

	case JVST_IR_EXPR_NE:
	case JVST_IR_EXPR_LT:
	case JVST_IR_EXPR_LE:
	case JVST_IR_EXPR_EQ:
	case JVST_IR_EXPR_GE:
	case JVST_IR_EXPR_GT:
		expr = newir_expr(A,op);
		expr->u.cmp.left = left;
		expr->u.cmp.right = right;
		break;

	case JVST_IR_EXPR_NONE:
	case JVST_IR_EXPR_NUM:
	case JVST_IR_EXPR_INT:
	case JVST_IR_EXPR_SIZE:
	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_TOK_TYPE:
	case JVST_IR_EXPR_TOK_NUM:
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

struct jvst_op_instr v_oplabel;
struct jvst_op_instr v_opslots;

struct jvst_op_proc v_opfloat;
struct jvst_op_proc v_opconst;
struct jvst_op_proc v_opdfa;
struct jvst_op_proc v_opsplit;

const struct jvst_op_instr *const oplabel = &v_oplabel;
const struct jvst_op_instr *const opslots = &v_opslots;

const struct jvst_op_proc *const opfloat = &v_opfloat;
const struct jvst_op_proc *const opconst = &v_opconst;
const struct jvst_op_proc *const opdfa   = &v_opdfa;
const struct jvst_op_proc *const opsplit = &v_opsplit;

static double *
newfloats(struct arena_info *A, double *fv, size_t n)
{
	size_t i,off,max;
	double *flts;

	max = ARRAYLEN(ar_op_float);
	if (A->nfloat + n > max) {
		fprintf(stderr, "%s:%d (%s) too many floats (%zu max)\n",
			__FILE__, __LINE__, __func__, max);
		abort();
	}

	off = A->nfloat;
	A->nfloat += n;

	flts = &ar_op_float[off];
	if (fv != NULL) {
		for (i=0; i < n; i++) {
			flts[i] = fv[i];
		}
	}

	return flts;
}

static int64_t *
newconsts(struct arena_info *A, int64_t *cv, size_t n)
{
	size_t i,off,max;
	int64_t *iconsts;

	max = ARRAYLEN(ar_op_iconst);
	if (A->nconst + n > max) {
		fprintf(stderr, "%s:%d (%s) too many integer constants (%zu max)\n",
			__FILE__, __LINE__, __func__, max);
		abort();
	}

	off = A->nconst;
	A->nconst += n;

	iconsts = &ar_op_iconst[off];
	for (i=0; i < n; i++) {
		iconsts[i] = cv[i];
	}

	return iconsts;
}

static size_t *
newsplitmax(struct arena_info *A, size_t *smv, size_t n)
{
	size_t i,off,max;
	size_t *splitmax;

	off = A->nsplitmax;
	max = ARRAYLEN(ar_op_splitmax);
	if (off + n > max) {
		fprintf(stderr, "%s:%d (%s) too many splits (%zu max)\n",
			__FILE__, __LINE__, __func__, max);
		abort();
	}
	A->nsplitmax += n;

	splitmax = &ar_op_splitmax[off];
	for (i=0; i < n; i++) {
		splitmax[i] = smv[i];
	}

	return splitmax;
}

static struct jvst_op_proc **
newsplits(struct arena_info *A, struct jvst_op_proc **sv, size_t n)
{
	size_t i,off,max;
	struct jvst_op_proc **splits;

	max = ARRAYLEN(ar_op_splits);
	if (A->nsplit + n > max) {
		fprintf(stderr, "%s:%d (%s) too many splits (%zu max)\n",
			__FILE__, __LINE__, __func__, max);
		abort();
	}

	off = A->nsplit;
	A->nsplit += n;

	splits = &ar_op_splits[off];
	for (i=0; i < n; i++) {
		splits[i] = sv[i];
	}

	return splits;
}

struct jvst_op_program *
newop_program(struct arena_info *A, ...)
{
	size_t i, max;
	struct jvst_op_program *prog;
	struct jvst_op_proc **procpp;
	size_t nfloat = 0;
	size_t nconst = 0;
	size_t nsplit = 0;
	double flt[16] = { 0.0 };
	int64_t iconsts[16] = { 0 };
	size_t splitmax[16] = { 0 };
	struct jvst_op_proc *splits[64] = { NULL };
	va_list args;

	i   = A->nprog++;
	max = ARRAYLEN(ar_op_prog);
	if (A->nprog >= max) {
		fprintf(stderr, "too many OP programs: %zu max\n", max);
		abort();
	}

	prog  = &ar_op_prog[i];
	memset(prog, 0, sizeof *prog);
	procpp = &prog->procs;

	va_start(args, A);
	for (;;) {
		struct jvst_op_proc *proc;
		proc = va_arg(args, struct jvst_op_proc *);
		if (proc == NULL) {
			break;
		}

		if (proc == opfloat) {
			int ind;

			ind = nfloat++;
			if (nfloat >= ARRAYLEN(flt)) {
				fprintf(stderr, "%s:%d (%s) too many floats! (max is %zu)\n",
					__FILE__, __LINE__, __func__, ARRAYLEN(flt));
				abort();
			}
			flt[ind] = va_arg(args, double);
			continue;
		}

		if (proc == opconst) {
			int ind;

			ind = nconst++;
			if (nconst >= ARRAYLEN(iconsts)) {
				fprintf(stderr, "%s:%d (%s) too many integer constants! (max is %zu)\n",
					__FILE__, __LINE__, __func__, ARRAYLEN(iconsts));
				abort();
			}
			iconsts[ind] = va_arg(args, int64_t);
			continue;
		}

		if (proc == opsplit) {
			int ind;
			int j,n,off;
			struct jvst_op_proc *spl, **splpp;

			ind = nsplit++;
			if (nsplit>= ARRAYLEN(splitmax)) {
				fprintf(stderr, "%s:%d (%s) too many splits ! (max is %zu)\n",
					__FILE__, __LINE__, __func__, ARRAYLEN(splitmax));
				abort();
			}

			n = va_arg(args, int);
			off = (ind>0) ? splitmax[ind-1] : 0;

			if (off+n >= (int)ARRAYLEN(splits)) {
				fprintf(stderr, "%s:%d (%s) too many total split functions ! (max is %zu)\n",
					__FILE__, __LINE__, __func__, ARRAYLEN(splits));
				abort();
			}

			splitmax[ind] = off+n;

			for (j=0; j < n; j++) {
				int pind;
				pind = va_arg(args, int);

				splits[off + j] = newop_proc(A, NULL);
				splits[off + j]->proc_index = pind;
			}

			continue;
		}

		if (proc == opdfa) {
			int ndfa;

			ndfa = va_arg(args, int);
			prog->ndfa += ndfa;
			continue;
		}

		*procpp = proc;
		procpp = &proc->next;
	}
	va_end(args);

	if (nfloat > 0) {
		prog->fdata = newfloats(A, flt, nfloat);
		prog->nfloat = nfloat;
	}

	if (nconst > 0) {
		prog->cdata = newconsts(A, iconsts, nconst);
		prog->nconst = nconst;
	}

	if (nsplit > 0) {
		prog->splitmax = newsplitmax(A, splitmax, nsplit);
		prog->splits = newsplits(A, splits, splitmax[nsplit-1]);
		prog->nsplit = nsplit;
	}

	return prog;
}

struct jvst_op_proc *
newop_proc(struct arena_info *A, ...)
{
	size_t i, max;
	struct jvst_op_proc *proc;
	struct jvst_op_instr **ipp;
	va_list args;


	i   = A->nproc++;
	max = ARRAYLEN(ar_op_proc);
	if (A->nproc >= max) {
		fprintf(stderr, "too many OP procs: %zu max\n", max);
		abort();
	}

	proc  = &ar_op_proc[i];
	memset(proc, 0, sizeof *proc);
	ipp = &proc->ilist;

	va_start(args, A);
	for (;;) {
		struct jvst_op_instr *instr;
		const char *label = NULL;

fetch:
		instr = va_arg(args, struct jvst_op_instr *);
		if (instr == NULL) {
			break;
		}

		if (instr == oplabel) {
			label = va_arg(args, const char *);
			goto fetch;
		}

		if (instr == opslots) {
			int nslots;

			nslots = va_arg(args, int);
			proc->nslots += nslots;
			continue;
		}

		if (label != NULL) {
			instr->label = label;
		}

		{
			struct jvst_op_proc *ptest = (struct jvst_op_proc *)instr;

			if (ptest == opfloat) {
				fprintf(stderr, "%s:%d (%s) opfloat belongs on programs, not procs\n",
					__FILE__, __LINE__, __func__);
				abort();
			}

			if (ptest == opconst) {
				fprintf(stderr, "%s:%d (%s) opconst belongs on programs, not procs\n",
					__FILE__, __LINE__, __func__);
				abort();
			}

			if (ptest == opsplit) {
				fprintf(stderr, "%s:%d (%s) opsplit belongs on programs, not procs\n",
					__FILE__, __LINE__, __func__);
				abort();
			}

			if (ptest == opdfa) {
				fprintf(stderr, "%s:%d (%s) opdfa belongs on programs, not procs\n",
					__FILE__, __LINE__, __func__);
				abort();
			}
		}

		*ipp = instr;
		ipp = &instr->next;
	}
	va_end(args);

	return proc;
}


struct jvst_op_instr *
newop_instr(struct arena_info *A, enum jvst_vm_op op)
{
	size_t i, max;
	struct jvst_op_instr *instr;
	va_list args;

	i   = A->ninstr++;
	max = ARRAYLEN(ar_op_instr);
	if (A->nproc >= max) {
		fprintf(stderr, "too many OP procs: %zu max\n", max);
		abort();
	}

	instr = &ar_op_instr[i];
	memset(instr, 0, sizeof *instr);

	instr->op = op;
	return instr;
}

struct jvst_op_instr *
newop_cmp(struct arena_info *A, enum jvst_vm_op op,
	struct jvst_op_arg arg1, struct jvst_op_arg arg2)
{
	struct jvst_op_instr *instr;

	switch (op) {
	case JVST_OP_ILT:
	case JVST_OP_ILE:
	case JVST_OP_IEQ:
	case JVST_OP_IGE:
	case JVST_OP_IGT:
	case JVST_OP_INEQ:
	case JVST_OP_FLT:
	case JVST_OP_FLE:
	case JVST_OP_FEQ:
	case JVST_OP_FGE:
	case JVST_OP_FGT:
	case JVST_OP_FNEQ:
	case JVST_OP_FINT:
		instr = newop_instr(A, op);
		instr->args[0] = arg1;
		instr->args[1] = arg2;
		return instr;

	case JVST_OP_NOP:
	case JVST_OP_PROC:
	case JVST_OP_BR:
	case JVST_OP_CBT:
	case JVST_OP_CBF:
	case JVST_OP_CALL:
	case JVST_OP_SPLIT:
	case JVST_OP_SPLITV:
	case JVST_OP_TOKEN:
	case JVST_OP_CONSUME:
	case JVST_OP_MATCH:
	case JVST_OP_FLOAD:
	case JVST_OP_ILOAD:
	case JVST_OP_INCR:
	case JVST_OP_BSET:
	case JVST_OP_BAND:
	case JVST_OP_VALID:
	case JVST_OP_INVALID:
	case JVST_OP_MOVE:
		fprintf(stderr, "%s:%d (%s) OP %s is not a comparison\n",
			__FILE__, __LINE__, __func__, jvst_op_name(op));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) Unknown OP %d\n",
		__FILE__, __LINE__, __func__, op);
	abort();
}

struct jvst_op_instr *
newop_bitop(struct arena_info *A, enum jvst_vm_op op, int frame_off, int bit)
{
	struct jvst_op_instr *instr;

	instr = newop_instr(A, op);
	instr->args[0] = oparg_slot(frame_off);
	instr->args[1] = oparg_lit(bit);
	return instr;
}

struct jvst_op_instr *
newop_instr2(struct arena_info *A, enum jvst_vm_op op,
	struct jvst_op_arg arg1, struct jvst_op_arg arg2)
{
	struct jvst_op_instr *instr;

	instr = newop_instr(A, op);
	instr->args[0] = arg1;
	instr->args[1] = arg2;
	return instr;
}

enum { ARG_NONE, ARG_BOOL, ARG_INT, ARG_FLOAT };
enum { ARG_READABLE, ARG_WRITEABLE };

static int
arg_okay(struct jvst_op_arg arg, int kind, int writeable)
{
	switch (arg.type) {
	case JVST_VM_ARG_NONE:
		return (kind == ARG_NONE) && (writeable == ARG_WRITEABLE);

	case JVST_VM_ARG_TT:
	case JVST_VM_ARG_TLEN:
	case JVST_VM_ARG_M:
	case JVST_VM_ARG_TOKTYPE:
	case JVST_VM_ARG_CONST:
		return (kind == ARG_INT) && (writeable == ARG_READABLE);

	case JVST_VM_ARG_TNUM:
		return (kind == ARG_FLOAT) && (writeable == ARG_READABLE);

	case JVST_VM_ARG_SLOT:
		return (kind == ARG_INT) || (kind == ARG_FLOAT);

	default:
		fprintf(stderr, "%s:%d (%s) unknown argument type %d\n",
			__FILE__, __LINE__, __func__, arg.type);
		abort();
	}
}

struct jvst_op_instr *
newop_load(struct arena_info *A, enum jvst_vm_op op,
	struct jvst_op_arg arg1, struct jvst_op_arg arg2)
{
	struct jvst_op_instr *instr;

	switch (op) {
	case JVST_OP_FLOAD:
		if (!arg_okay(arg1, ARG_FLOAT, ARG_WRITEABLE)) {
			fprintf(stderr, "%s:%d (%s) FLOAD first argument is not a writable float (type=%d)\n",
				__FILE__, __LINE__, __func__, arg1.type);
			abort();
		}

		if (!arg_okay(arg2, ARG_FLOAT, ARG_READABLE) && !arg_okay(arg2, ARG_INT, ARG_READABLE)) {
			fprintf(stderr, "%s:%d (%s) FLOAD first argument is not a readable float (type=%d)\n",
				__FILE__, __LINE__, __func__, arg2.type);
			abort();
		}
		goto make_op;

	case JVST_OP_ILOAD:
		instr = newop_instr(A, op);
		if (!arg_okay(arg1, ARG_INT, ARG_WRITEABLE)) {
			fprintf(stderr, "%s:%d (%s) ILOAD first argument is not a writable int (type=%d)\n",
				__FILE__, __LINE__, __func__, arg1.type);
			abort();
		}

		if (!arg_okay(arg2, ARG_INT, ARG_READABLE)) {
			fprintf(stderr, "%s:%d (%s) ILOAD first argument is not a readable int (type=%d)\n",
				__FILE__, __LINE__, __func__, arg2.type);
			abort();
		}
		goto make_op;

	case JVST_OP_MOVE:
		// XXX - add some rules!
		goto make_op;

	case JVST_OP_ILT:
	case JVST_OP_ILE:
	case JVST_OP_IEQ:
	case JVST_OP_IGE:
	case JVST_OP_IGT:
	case JVST_OP_INEQ:
	case JVST_OP_FLT:
	case JVST_OP_FLE:
	case JVST_OP_FEQ:
	case JVST_OP_FGE:
	case JVST_OP_FGT:
	case JVST_OP_FNEQ:
	case JVST_OP_FINT:
	case JVST_OP_NOP:
	case JVST_OP_PROC:
	case JVST_OP_BR:
	case JVST_OP_CBT:
	case JVST_OP_CBF:
	case JVST_OP_CALL:
	case JVST_OP_SPLIT:
	case JVST_OP_SPLITV:
	case JVST_OP_TOKEN:
	case JVST_OP_CONSUME:
	case JVST_OP_MATCH:
	case JVST_OP_INCR:
	case JVST_OP_BSET:
	case JVST_OP_BAND:
	case JVST_OP_VALID:
	case JVST_OP_INVALID:
		fprintf(stderr, "OP %s is not a load\n",
			jvst_op_name(op));
		abort();
	}

	fprintf(stderr, "Unknown OP %d\n", op);
	abort();

make_op:
	instr = newop_instr(A, op);
	instr->args[0] = arg1;
	instr->args[1] = arg2;
	return instr;
}

struct jvst_op_instr *
newop_br(struct arena_info *A, enum jvst_vm_op op, const char *label)
{
	struct jvst_op_instr *instr;

	switch (op) {
	case JVST_OP_BR:
	case JVST_OP_CBT:
	case JVST_OP_CBF:
		instr = newop_instr(A, op);
		instr->args[0].type = JVST_VM_ARG_LABEL;
		instr->args[0].u.label = label;
		return instr;

	case JVST_OP_ILT:
	case JVST_OP_ILE:
	case JVST_OP_IEQ:
	case JVST_OP_IGE:
	case JVST_OP_IGT:
	case JVST_OP_INEQ:
	case JVST_OP_FLT:
	case JVST_OP_FLE:
	case JVST_OP_FEQ:
	case JVST_OP_FGE:
	case JVST_OP_FGT:
	case JVST_OP_FNEQ:
	case JVST_OP_FINT:
	case JVST_OP_NOP:
	case JVST_OP_PROC:
	case JVST_OP_CALL:
	case JVST_OP_SPLIT:
	case JVST_OP_SPLITV:
	case JVST_OP_TOKEN:
	case JVST_OP_CONSUME:
	case JVST_OP_MATCH:
	case JVST_OP_FLOAD:
	case JVST_OP_ILOAD:
	case JVST_OP_INCR:
	case JVST_OP_BSET:
	case JVST_OP_BAND:
	case JVST_OP_VALID:
	case JVST_OP_INVALID:
	case JVST_OP_MOVE:
		fprintf(stderr, "%s:%d (%s) OP %s is not a branch\n",
		__FILE__, __LINE__, __func__, jvst_op_name(op));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown OP %d\n",
		__FILE__, __LINE__, __func__, op);
	abort();
}

struct jvst_op_instr *
newop_match(struct arena_info *A, int64_t dfa)
{
	struct jvst_op_instr *instr;
	instr = newop_instr(A, JVST_OP_MATCH);
	instr->args[0] = oparg_lit(dfa);
	instr->args[1] = oparg_none();
	return instr;
}

struct jvst_op_instr *
newop_call(struct arena_info *A, struct jvst_op_arg dest)
{
	struct jvst_op_instr *instr;
	instr = newop_instr(A, JVST_OP_CALL);
	instr->args[0] = dest;
	return instr;
}

struct jvst_op_instr *
newop_incr(struct arena_info *A, size_t slot)
{
	struct jvst_op_instr *instr;
	instr = newop_instr(A, JVST_OP_INCR);
	instr->args[0] = oparg_slot(slot);
	instr->args[1] = oparg_lit(1);
	return instr;
}

struct jvst_op_instr *
newop_invalid(struct arena_info *A, enum jvst_invalid_code ecode)
{
	struct jvst_op_instr *instr;
	instr = newop_instr(A, JVST_OP_INVALID);
	instr->args[0].type = JVST_VM_ARG_CONST;
	instr->args[0].u.index = ecode;
	return instr;
}

struct label {
	const char *name;
	uint32_t off;
};

static int
findlbl(const struct label labels[], int nlbl, const char *lbl)
{
	int i;

	// dumb linear scan... should be fine
	// for testing purposes
	for (i=0; i < nlbl; i++) {
		if (strcmp(lbl, labels[i].name) == 0) {
			return i;
		}
	}

	return -1;
}

struct jvst_vm_program *
newvm_program(struct arena_info *A, ...)
{
	struct jvst_vm_program *prog;
	va_list args;
	size_t ind,max,nlbl,nproc,off,nsplit;
	uint32_t pc;

	struct label labels[64];
	uint32_t soff[16]  = { 0 };
	uint32_t procs[16] = { 0 };
	uint32_t code[256] = { 0 };

	memset(labels, 0, sizeof labels);

	ind = A->nvmprog++;
	max = ARRAYLEN(ar_vm_code);
	if (A->nvmprog > max) {
		fprintf(stderr, "too many vm programs: %zu max\n", max);
		abort();
	}

	prog = &ar_vm_progs[ind];
	memset(prog, 0, sizeof *prog);

	// first pass, find all labels
	va_start(args, A);
	nlbl = 0;
	nproc = 0;
	nsplit = 0;
	pc = 0;
	for (;;) {
		int op = va_arg(args, int);
		switch (op) {
		case VM_END:
			goto end_label_scan;

		case VM_DFA:
			{
				int n;
				n = va_arg(args, int);
				prog->ndfa = n;
			}
			break;

		case VM_FLOATS:
			{
				int i,n;
				double *fv;

				n = va_arg(args, int);
				fv = newfloats(A, NULL, n);
				for (i=0; i < n; i++) {
					fv[i] = va_arg(args, double);
				}

				prog->fdata = fv;
				prog->nfloat = n;
			}
			break;

		case VM_LABEL:
			{
				size_t ind;
				if (nlbl >= ARRAYLEN(labels)) {
					fprintf(stderr, "too many instructions: %zu max\n",
							ARRAYLEN(labels));
					abort();
				}

				ind = nlbl++;
				labels[ind].name = va_arg(args, const char *);
				labels[ind].off = pc;
			}
			break;

		case VM_SPLIT: 
			{
				int ind, off, i, n;
				if (nsplit >= ARRAYLEN(soff)) {
					fprintf(stderr, "too many splits: %zu max\n",
							ARRAYLEN(soff));
					abort();
				}

				n = va_arg(args, int);

				off = (nsplit>0) ? soff[nsplit-1] : 0;
				soff[nsplit++] = off+n;

				// skip proc indices for now...
				for (i=0; i < n; i++) {
					(void) va_arg(args, int);
				}
			}
			break;

		default:
			if (op == JVST_OP_PROC) {
				assert(nproc < ARRAYLEN(procs));
				procs[nproc++] = pc;
			}

			// eat two int arguments
			va_arg(args, int);
			va_arg(args, int);
			pc++;
			break;

		case JVST_OP_BR:
		case JVST_OP_CBT:
		case JVST_OP_CBF:
			// eat label
			va_arg(args, const char *);
			pc++;
			break;

		case JVST_OP_CALL:
			{
				// eat proc index
				(void) va_arg(args, int);
				pc++;
			}
			break;

		}

		if (pc > ARRAYLEN(code)) {
			fprintf(stderr, "too many instructions: %zu max\n",
					ARRAYLEN(code));
			abort();
		}
	}
end_label_scan:
	va_end(args);

	/* allocate split storage */
	if (nsplit > 0) {
		int off, nentries;
		size_t i;

		nentries = nsplit + 1 + soff[nsplit-1];
		max = ARRAYLEN(ar_vm_code);
		off = A->nvmcode;

		assert(nentries >= 0 && max >= (size_t)nentries);
		if ((size_t)off + nentries >= max) {
			fprintf(stderr, "splits require too much data: %zu max\n", max);
			abort();
		}

		A->nvmcode += nentries;
		prog->sdata = &ar_vm_code[off];
		prog->nsplit = nsplit;

		prog->sdata[0] = 0;
		for (i=0; i < nsplit; i++) {
			prog->sdata[i+1] = soff[i];
		}
	}

	/* second pass, all labels are already set */
	va_start(args, A);
	pc = 0;
	nsplit = 0;
	for (;;) {
		int op = va_arg(args, int);

		switch (op) {
		case VM_END:
			goto end_instructions;

		case VM_FLOATS:
			{
				int i,n = va_arg(args, int);
				for (i=0; i < n; i++) {
					(void)va_arg(args, double);
				}
			}
			continue;

		case VM_SPLIT: 
			{
				int ind, off, i,n;

				ind = nsplit++;
				assert(nsplit <= prog->nsplit);

				n = va_arg(args, int);
				assert(prog->sdata[ind+1] == prog->sdata[ind] + n);
				off = prog->sdata[prog->nsplit] + prog->sdata[ind];

				for (i=0; i < n; i++) {
					int proc_ind;

					proc_ind = va_arg(args, int);
					assert(proc_ind >= 1 && (size_t)proc_ind <= nproc);

					prog->sdata[off+i] = procs[proc_ind-1];
				}
			}
			break;

		case VM_DFA:
			(void)va_arg(args, int);
			continue;

		case VM_LABEL:
			// eat label argument
			(void)va_arg(args, const char *);
			continue;

		case JVST_OP_BR:
		case JVST_OP_CBT:
		case JVST_OP_CBF:
			{
				const char *lbl;
				int i;
				int32_t delta;

				lbl = va_arg(args, const char *);
				i = findlbl(labels, nlbl, lbl);
				if (i < 0 || (size_t)i >= nlbl) {
					fprintf(stderr, "%s:%d (%s) could not find label %s\n",
						__FILE__, __LINE__, __func__, lbl);
					abort();
				}

				delta = labels[i].off - pc;
				assert(delta >= JVST_VM_BARG_MIN && delta <= JVST_VM_BARG_MAX);

				code[pc++] = VMBR(op,delta);
			}
			break;

		case JVST_OP_CALL:
			{
				int proc_ind;
				long delta;

				proc_ind = va_arg(args, int);
				assert(proc_ind >= 1 && (size_t)proc_ind <= nproc);

				delta = (long)procs[proc_ind-1] - (long)pc;
				code[pc++] = VMBR(op,delta);
			}
			break;

		default:
			{
				int a0,a1;

				assert(op >= 0 && op <= JVST_OP_MAX);

				a0 = va_arg(args, int);
				a1 = va_arg(args, int);

				code[pc++] = VMOP(op,a0,a1);
			}
			break;
		}

		assert(pc <= ARRAYLEN(code));
	}
end_instructions:
	va_end(args);

	// allocate code
	max = ARRAYLEN(ar_vm_code);
	off = A->nvmcode;
	assert(max >= pc);
	assert(off+pc >= off);
	if (off +pc >= max) {
		fprintf(stderr, "too many vm opcodes: %zu max\n", max);
		abort();
	}

	A->nvmcode += pc;
	prog->ncode = pc;
	prog->code = &ar_vm_code[off];
	memcpy(prog->code, code, pc * sizeof code[0]);

	return prog;
}

void
buffer_diff(FILE *f, const char *buf1, const char *buf2, size_t n)
{
	size_t i, linenum, beg, off;

	// slightly tedious job of finding first difference and printing out
	// both up to that point...
	for (i=0, linenum=1, off=0; i < n; i++) {
		size_t j;
		char line1[256], line2[256];

		if (buf1[i] == buf2[i]) {
			if (buf1[i] == '\0') {
				fprintf(f, "INTERNAL ERROR: cannot find difference.\n");
				abort();
			}

			if (buf1[i] == '\n') {
				size_t n;
				n = i-off;
				if (n >= sizeof line1) {
					n = sizeof line1 - 1;
				}
				if (n > 0) {
					memcpy(line1,&buf1[off],n);
					memcpy(line2,&buf2[off],n);
				}
				line1[n] = '\0';
				line2[n] = '\0';

				fprintf(f, "%3zu | %-40.40s | %-40.40s\n",
						linenum, line1, line2);

				linenum++;
				off = i+1;
			}

			continue;
		}

		// difference
		fprintf(f, "difference at line %zu, column %zu:\n", linenum, i-off+1);
		fprintf(f, "EXPECTED: ");
		for(j=off; j < n && buf2[j] != '\n'; j++) {
			fputc(buf2[j], stderr);
		}
		fprintf(f, "\n");

		fprintf(f, "ACTUAL  : ");
		for(j=off; j < n && buf1[j] != '\n'; j++) {
			fputc(buf1[j], stderr);
		}
		fprintf(f, "\n");

		fprintf(f, "DIFF    : ");
		for(j=off; j < i; j++) {
			fputc(' ', stderr);
		}
		fprintf(f, "^\n");

		break;
	}
}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
