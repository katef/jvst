#include "validate_op.h"

#include <assert.h>
#include <inttypes.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

#include "sjp_parser.h"
#include "sjp_testing.h"

#include "xalloc.h"
#include "jvst_macros.h"

#include "validate_sbuf.h"

/** some OP encoding constants **/

// 16-bit signed constants can be inlined into the opcodes
//
// XXX - implement constant storage + ILOAD for larger values
#define MIN_CONST_VALUE ((int64_t)(-32768))
#define MAX_CONST_VALUE ((int64_t)( 32767))

#define MAX_CONST_SIZE ((size_t)(65535))

/** memory pool allocation **/

enum {
	JVST_OP_CHUNKSIZE = 1024,
	JVST_OP_NUMROOTS  = 32,
};

#define POOLTYPE(name, itemtype, n)	\
	struct name { 			\
		struct name *next;	\
		itemtype items[n];	\
		unsigned char marks[(n / CHAR_BIT) + !!(n % CHAR_BIT)]; \
	}

void pool_gc(void *freelist, char *items, size_t itemsize, size_t n, unsigned char *marks)
{
	size_t i, off;
	for (off = 0,i=0; i < n; i++,off += itemsize) {
		void *p;
		int mi = i / CHAR_BIT;
		int b = 1 << (i % CHAR_BIT);
		if (marks[mi] & b) {
			continue;
		}

		p = &items[off];
		memcpy(freelist, &p, sizeof p);
		freelist = p;
	}
}

void pool_no_gc(void) {}

#define POOL_INNER(name, ptname, itemtype, n, gcf)		\
	POOLTYPE(ptname, itemtype, n); 				\
	static struct {						\
		struct ptname *head;				\
		size_t top;					\
		void *freelist;					\
	} name;							\
	itemtype *name ## _alloc(void) {			\
		itemtype *item;					\
		struct ptname *pool;				\
		if (name.head == NULL) {			\
			goto new_pool;				\
		}						\
		if (name.top < ARRAYLEN(name.head->items)) {	\
			item = &name.head->items[name.top++]; 	\
			memset(item, 0, sizeof *item); 		\
			return item;				\
		}						\
		if (name.freelist == NULL && gcf != pool_no_gc) {	\
			gcf();					\
		}						\
		if (name.freelist != NULL) {			\
			item = name.freelist; 			\
			memcpy(&name.freelist, item, sizeof name.freelist); \
			memset(item, 0, sizeof *item);		\
			return item;				\
		}						\
new_pool:							\
		pool = xmalloc(sizeof *pool);			\
		memset(pool->items, 0, sizeof pool->items);	\
		memset(pool->marks, 0, sizeof pool->marks);	\
		pool->next = name.head; 			\
		name.head = pool;				\
		name.top = 1;					\
		return &pool->items[0]; 			\
	}							\

#define POOL(name, ptname, itemtype, n, gcf)			\
	POOL_INNER(name, ptname, itemtype, n,gcf)		\
	struct SYMCAT(eat_semi_, __LINE__) { char c; }

static int prog_nroots = 0;
static struct jvst_op_program *progs_roots[JVST_OP_NUMROOTS];

static void
prog_gc(void);

POOL(instr_pool, jvst_op_instr_pool, struct jvst_op_instr, JVST_OP_CHUNKSIZE, prog_gc);
POOL(block_pool, jvst_op_block_pool, struct jvst_op_block, JVST_OP_CHUNKSIZE, prog_gc);
POOL(proc_pool, jvst_op_proc_pool, struct jvst_op_proc, JVST_OP_CHUNKSIZE, prog_gc);
POOL(prog_pool, jvst_op_prog_pool, struct jvst_op_program, JVST_OP_CHUNKSIZE, prog_gc);

static void prog_gc(void)
{
	// currently nop
}

static struct jvst_op_instr *
op_instr_new(enum jvst_vm_op type)
{
	struct jvst_op_instr *op;
	op = instr_pool_alloc();
	op->op = type;

	return op;
}

static struct jvst_op_block *
op_block_new(struct jvst_op_instr *ilist, const char *lblfmt, va_list args)
{
	struct jvst_op_block *b;
	b = block_pool_alloc();
	vsnprintf(b->label, sizeof b->label, lblfmt, args);
	b->ilist = ilist;

	return b;
}

static struct jvst_op_block *
op_block_newf(struct jvst_op_instr *ilist, const char *lblfmt, ...)
{
	struct jvst_op_block *b;
	va_list args;

	va_start(args, lblfmt);
	b = op_block_new(ilist, lblfmt, args);
	va_end(args);

	return b;
}

static struct jvst_op_proc *
op_proc_new(void)
{
	return proc_pool_alloc();
}

static struct jvst_op_program *
op_prog_new(struct jvst_op_proc *procs)
{
	struct jvst_op_program *prog;
	prog = prog_pool_alloc();
	prog->procs = procs;

	return prog;
}

static void
op_arg_dump(struct sbuf *buf, struct jvst_op_arg arg)
{
	switch (arg.type) {
	case JVST_VM_ARG_NONE:
		return;

	case JVST_VM_ARG_FLAG:
		sbuf_snprintf(buf,"%%FLAG");
		return;

	case JVST_VM_ARG_PC:
		sbuf_snprintf(buf,"%%PC");
		return;

	case JVST_VM_ARG_TT:
		sbuf_snprintf(buf,"%%TT");
		return;

	case JVST_VM_ARG_TNUM:
		sbuf_snprintf(buf,"%%TN");
		return;
	case JVST_VM_ARG_TLEN:
		sbuf_snprintf(buf,"%%TL");
		return;
	case JVST_VM_ARG_TCOMPLETE:
		sbuf_snprintf(buf,"%%TC");
		return;

	case JVST_VM_ARG_M:
		sbuf_snprintf(buf,"%%M");
		return;

	case JVST_VM_ARG_INT:
		sbuf_snprintf(buf,"%%I%" PRId64, arg.u.index);
		return;

	case JVST_VM_ARG_FLOAT:
		sbuf_snprintf(buf,"%%F%" PRId64, arg.u.index);
		return;

	case JVST_VM_ARG_TOKTYPE:
		sbuf_snprintf(buf,"$%s", evt2name(arg.u.index));
		return;

	case JVST_VM_ARG_CONST:
		sbuf_snprintf(buf,"$%" PRId64, arg.u.index);
		return;

	case JVST_VM_ARG_POOL:
		sbuf_snprintf(buf,"POOL(%" PRId64 ")", arg.u.index);
		return;

	case JVST_VM_ARG_SLOT:
		sbuf_snprintf(buf,"SLOT(%" PRId64 ")", arg.u.index);
		return;

	case JVST_VM_ARG_LABEL:
		sbuf_snprintf(buf,":%s", (void *)arg.u.label);
		return;

	case JVST_VM_ARG_INSTR:
		{
			const char *lbl;

			lbl = NULL;
			if (arg.u.dest != NULL && arg.u.dest->label != NULL) {
				lbl = arg.u.dest->label;
			}

			sbuf_snprintf(buf,":%s", lbl);
		}
		return;
	}

	fprintf(stderr, "%s:%d (%s) Unknown OP arg type %02x\n",
		__FILE__, __LINE__, __func__, arg.type);
	abort();
}

static void
op_instr_dump(struct sbuf *buf, struct jvst_op_instr *instr)
{
	switch (instr->op) {
	case JVST_OP_NOP:
		sbuf_snprintf(buf, "NOP");
		break;

	case JVST_OP_PROC:
		sbuf_snprintf(buf, "PROC ");
		op_arg_dump(buf, instr->u.args[0]);
		break;

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
		sbuf_snprintf(buf, "%s ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->u.args[0]);
		sbuf_snprintf(buf, ", ");
		op_arg_dump(buf, instr->u.args[1]);
		break;

	case JVST_OP_FINT:
		sbuf_snprintf(buf, "%s ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->u.args[0]);
		break;

	case JVST_OP_BR:
	case JVST_OP_CBT:
	case JVST_OP_CBF:
		{
			const char *lbl = NULL;

			switch (instr->u.args[0].type) {
			case JVST_VM_ARG_INSTR:
				lbl = instr->u.args[0].u.dest->label;
				break;

			case JVST_VM_ARG_LABEL:
				lbl = instr->u.args[0].u.label;
				break;

			default:
				/* nop */
				break;
			}

			if (lbl == NULL) {
				lbl = "(null)";
			}

			sbuf_snprintf(buf, "%s :%s", jvst_op_name(instr->op), lbl);
		}
		break;

	case JVST_OP_CALL:
		sbuf_snprintf(buf, "%s %zu",
			jvst_op_name(instr->op),
			(instr->u.call.dest != NULL)
			 	? instr->u.call.dest->proc_index
				: instr->u.call.proc_index);
		break;

	case JVST_OP_MATCH:
	case JVST_OP_INCR:
		sbuf_snprintf(buf, "%s ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->u.args[0]);
		break;

	case JVST_OP_SPLITV:
	case JVST_OP_SPLIT:
	case JVST_OP_FLOAD:
	case JVST_OP_ILOAD:
		sbuf_snprintf(buf, "%s ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->u.args[0]);
		sbuf_snprintf(buf, ", ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->u.args[1]);
		break;

	case JVST_OP_TOKEN:
	case JVST_OP_CONSUME:
	case JVST_OP_VALID:
		sbuf_snprintf(buf, "%s", jvst_op_name(instr->op));
		break;

	case JVST_OP_INVALID:
		sbuf_snprintf(buf, "%s %d",
			jvst_op_name(instr->op),
			instr->u.args[0].u.index);
		break;

	case JVST_OP_BAND:
	case JVST_OP_BSET:
		sbuf_snprintf(buf, "%s ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->u.args[0]);
		sbuf_snprintf(buf, ", ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->u.args[1]);
		break;

	case JVST_OP_BTEST:
		fprintf(stderr, "%s:%d (%s) OP %s not yet implemented\n",
			__FILE__, __LINE__, __func__, jvst_op_name(instr->op));
		abort();

	default:
		fprintf(stderr, "%s:%d (%s) Unknown OP arg type %02x\n",
				__FILE__, __LINE__, __func__, instr->op);
		abort();

	}
}

static void
op_block_dump(struct sbuf *buf, struct jvst_op_block *b, int indent)
{
	size_t bi;

	for (bi=0; b != NULL; bi++, b=b->next) {
		size_t i;
		struct jvst_op_instr *instr;

		sbuf_indent(buf, indent);
		sbuf_snprintf(buf, "BLOCK %zu %s\n", bi, b->label);

		for (i=0, instr = b->ilist; instr != NULL; i++, instr = instr->next) {
			sbuf_indent(buf, indent);
			if (instr->label != NULL) {
				sbuf_snprintf(buf, "\n%s:\n", instr->label);
				sbuf_indent(buf, indent);
			}

			sbuf_snprintf(buf, "%5zu\t", i+1);
			op_instr_dump(buf, instr);
			sbuf_snprintf(buf, "\n");
		}
	}
}

void
jvst_op_block_debug(struct jvst_op_block *blk)
{
	static char buf[65536];
	struct sbuf b = {
	    .buf = buf, .cap = sizeof buf, .len = 0, .np = 0,
	};

	memset(buf,0,sizeof buf);

	op_block_dump(&b, blk, 0);
	buf[sizeof buf - 1] = '\0';
	fprintf(stderr, "%s\n", buf);
}

static void
op_proc_dump(struct sbuf *buf, struct jvst_op_proc *proc, size_t fno, int indent)
{
	size_t i;
	struct jvst_op_instr *instr;

	sbuf_indent(buf, indent);
	sbuf_snprintf(buf, ".PROC %zu %zu\n", fno, proc->nslots);

	sbuf_indent(buf, indent);
	sbuf_snprintf(buf, ".DATA\n");

	for (i=0; i < proc->nfloat; i++) {
		sbuf_indent(buf, indent+2);
		sbuf_snprintf(buf, "FLOAT(%zu)\t%g\n", i, proc->fdata[i]);
	}

	if (proc->nfloat > 0) {
		sbuf_snprintf(buf, "\n");
	}

	for (i=0; i < proc->nconst; i++) {
		sbuf_indent(buf, indent+2);
		sbuf_snprintf(buf, "CONST(%zu)\t%" PRId64 "\t%" PRIu64 "\n",
			i, proc->cdata[i], (uint64_t) proc->cdata[i]);
	}

	if (proc->nconst > 0) {
		sbuf_snprintf(buf, "\n");
	}

	for (i=0; i < proc->nsplit; i++) {
		struct jvst_op_proc *p;
		size_t c;

		assert(proc->splits != NULL);

		sbuf_indent(buf, indent+2);
		sbuf_snprintf(buf, "SPLIT(%zu)\t", i);
		for (c=0, p = proc->splits[i]; p != NULL; c++, p = p->split_next) {
			sbuf_snprintf(buf, " %zu", p->proc_index);

			if (c >= 6 && p->next != NULL) {
				sbuf_snprintf(buf, "\n");
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "\t\t");
			}
		}

		sbuf_snprintf(buf, "\n");
	}

	if (proc->nsplit > 0) {
		sbuf_snprintf(buf, "\n");
	}

	// surely we can provide more data than this?
	for (i=0; i < proc->ndfa; i++) {
		sbuf_indent(buf, indent+2);
		sbuf_snprintf(buf, "DFA(%zu)\n", i);
	}

	if (proc->ndfa> 0) {
		sbuf_snprintf(buf, "\n");
	}

	if (proc->nsplit> 0) {
		sbuf_snprintf(buf, "\n");
	}

	sbuf_indent(buf, indent);
	sbuf_snprintf(buf, ".CODE\n");

	for (i=0, instr = proc->ilist; instr != NULL; i++, instr = instr->next) {
		sbuf_indent(buf, indent);
		if (instr->label != NULL) {
			sbuf_snprintf(buf, "\n%s:\n", instr->label);
			sbuf_indent(buf, indent);
		}

		sbuf_snprintf(buf, "%5zu\t", i+1);
		op_instr_dump(buf, instr);
		sbuf_snprintf(buf, "\n");
	}
}

void
jvst_op_dump_inner(struct sbuf *buf, struct jvst_op_program *prog, int indent)
{
	struct jvst_op_proc *proc;
	size_t i;

	assert(prog != NULL);
	sbuf_indent(buf, indent);
	sbuf_snprintf(buf, ".PROGRAM\n\n");
	for (i=0, proc=prog->procs; proc != NULL; i++, proc=proc->next) {
		op_proc_dump(buf, proc, i, indent);
		sbuf_snprintf(buf, "\n");
	}

}

const char *
jvst_op_name(enum jvst_vm_op op)
{
	switch (op) {
	case JVST_OP_NOP:	return "NOP";
	case JVST_OP_PROC:	return "PROC";
	case JVST_OP_ILT:       return "ILT";
	case JVST_OP_ILE:       return "ILE";
	case JVST_OP_IEQ:       return "IEQ";
	case JVST_OP_IGE:       return "IGE";
	case JVST_OP_IGT:       return "IGT";
	case JVST_OP_INEQ:      return "INEQ";
	case JVST_OP_FLT:       return "FLT";
	case JVST_OP_FLE:       return "FLE";
	case JVST_OP_FEQ:       return "FEQ";
	case JVST_OP_FGE:       return "FGE";
	case JVST_OP_FGT:       return "FGT";
	case JVST_OP_FNEQ:      return "FNEQ";
	case JVST_OP_FINT:      return "FINT";
	case JVST_OP_BR:        return "BR";
	case JVST_OP_CBT:       return "CBT";
	case JVST_OP_CBF:      	return "CBF";
	case JVST_OP_CALL:      return "CALL";
	case JVST_OP_SPLIT:     return "SPLIT";
	case JVST_OP_SPLITV:    return "SPLITV";
	case JVST_OP_TOKEN:     return "TOKEN";
	case JVST_OP_CONSUME:   return "CONSUME";
	case JVST_OP_MATCH:     return "MATCH";
	case JVST_OP_FLOAD:     return "FLOAD";
	case JVST_OP_ILOAD:     return "ILOAD";
	case JVST_OP_INCR:      return "INCR";
	case JVST_OP_BSET:      return "BSET";
	case JVST_OP_BTEST:     return "BTEST";
	case JVST_OP_BAND:      return "BAND";
	case JVST_OP_VALID:     return "VALID";
	case JVST_OP_INVALID:   return "INVALID";
	case JVST_OP_MOVE: 	return "MOVE";
	}

	fprintf(stderr, "Unknown OP %d\n", op);
	abort();
}

int
jvst_op_dump(struct jvst_op_program *prog, char *buf, size_t nb)
{
	struct sbuf b = {
	    .buf = buf, .cap = nb, .len = 0, .np = 0,
	};

	jvst_op_dump_inner(&b, prog, 0);
	sbuf_snprintf(&b, "\n");
	return (b.len < b.cap) ? 0 : -1;
}

struct asm_addr_fixup {
	struct jvst_op_instr *instr;
	struct jvst_op_arg *arg;
	struct jvst_ir_stmt *ir;
};

struct asm_addr_fixup_list {
	size_t len;
	size_t cap;
	struct asm_addr_fixup *elts;
};

static void
asm_addr_fixup_list_free(struct asm_addr_fixup_list *l)
{
	if (l == NULL) {
		return;
	}

	free(l->elts);
}

static void
asm_addr_fixup_add(struct asm_addr_fixup_list *l,
	struct jvst_op_instr *instr, struct jvst_op_arg *arg, struct jvst_ir_stmt *ir)
{
	size_t i;

	assert(l != NULL);
	assert(l->len <= l->cap);
	if (l->len >= l->cap) {
		size_t newsz = l->cap;

		if (newsz < 4) {
			newsz = 4;
		} else if (newsz < 2048) {
			newsz *= 2;
		} else {
			newsz += newsz/4;
		}

		assert(newsz > l->cap+1);

		l->elts = xrealloc(l->elts, newsz * sizeof l->elts[0]);
		l->cap  = newsz;
	}

	i = l->len++;
	assert(i < l->cap);

	l->elts[i].instr = instr;
	l->elts[i].arg   = arg;
	l->elts[i].ir    = ir;
}

static void
asm_fixup_addr(struct asm_addr_fixup *fix)
{
	switch (fix->instr->op) {
	case JVST_OP_BR:
	case JVST_OP_CBT:
	case JVST_OP_CBF:
		assert(fix->ir != NULL);
		assert(fix->ir->data != NULL);
		fix->arg->type = JVST_VM_ARG_INSTR;
		fix->arg->u.dest = fix->ir->data;
		return;

	case JVST_OP_CALL:
		fprintf(stderr, "%s:%d (%s) address fixup for op %s not yet implemented\n",
			__FILE__, __LINE__, __func__, jvst_op_name(fix->instr->op));
		abort();

	case JVST_OP_NOP:
	case JVST_OP_PROC:
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
	case JVST_OP_SPLIT:
	case JVST_OP_SPLITV:
	case JVST_OP_TOKEN:
	case JVST_OP_CONSUME:
	case JVST_OP_MATCH:
	case JVST_OP_FLOAD:
	case JVST_OP_ILOAD:
	case JVST_OP_INCR:
	case JVST_OP_BSET:
	case JVST_OP_BTEST:
	case JVST_OP_BAND:
	case JVST_OP_VALID:
	case JVST_OP_INVALID:
	case JVST_OP_MOVE:
		fprintf(stderr, "%s:%d (%s) invalid op %s for address lookup\n",
			__FILE__, __LINE__, __func__, jvst_op_name(fix->instr->op));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown op %d\n",
		__FILE__, __LINE__, __func__, fix->instr->op);
	abort();
}

static void
asm_fixup_addresses(struct asm_addr_fixup_list *l)
{
	size_t i,n;

	n = l->len;
	for (i=0; i < n; i++) {
		asm_fixup_addr(&l->elts[i]);
	}
}

struct op_assembler {
	struct jvst_op_program *prog;
	struct jvst_op_proc **procpp;
	struct jvst_op_proc *currproc;
	struct jvst_op_block **bpp;
	struct jvst_op_instr **ipp;

	double *fdata;
	size_t maxfloat;

	int64_t *cdata;
	size_t maxconst;

	struct jvst_op_proc **splits;
	size_t maxsplit;

	size_t nlbl;
	size_t ntmp;

	struct jvst_ir_stmt *label_block;

	struct asm_addr_fixup_list *fixups;
};

static struct jvst_op_proc *
op_assemble_frame(struct op_assembler *opasm, struct jvst_ir_stmt *top);

static struct jvst_op_arg
arg_none(void)
{
	struct jvst_op_arg arg = {
		.type = JVST_VM_ARG_NONE,
		.u = { .index = 0 },
	};

	return arg;
}

static struct jvst_op_arg
arg_special(enum jvst_op_arg_type type)
{
	struct jvst_op_arg arg = { 0 };

	switch (type) {
	case JVST_VM_ARG_FLAG:
	case JVST_VM_ARG_PC:
	case JVST_VM_ARG_TT:
	case JVST_VM_ARG_TNUM:
	case JVST_VM_ARG_TLEN:
	case JVST_VM_ARG_TCOMPLETE:
	case JVST_VM_ARG_M:
		arg.type = type;
		return arg;

	case JVST_VM_ARG_NONE:
	case JVST_VM_ARG_INT:
	case JVST_VM_ARG_FLOAT:
	case JVST_VM_ARG_TOKTYPE:
	case JVST_VM_ARG_CONST:
	case JVST_VM_ARG_POOL:
	case JVST_VM_ARG_SLOT:
	case JVST_VM_ARG_INSTR:
	case JVST_VM_ARG_LABEL:
		fprintf(stderr, "%s:%d (%s) arg type %d is not a special arg\n",
			__FILE__, __LINE__, __func__, type);
		abort();
	}
}

static struct jvst_op_arg
arg_const(int64_t v)
{
	struct jvst_op_arg arg = {
		.type  = JVST_VM_ARG_CONST,
		.u = { .index = v },
	};

	if (v > MAX_CONST_VALUE) {
		fprintf(stderr, "%s:%d (%s) large constants (%" PRId64 " > max %" PRId64 ") not yet implemented\n",
				__FILE__, __LINE__, __func__,
				v, (int64_t) MAX_CONST_VALUE);
		abort();
	}

	if (v < MIN_CONST_VALUE) {
		fprintf(stderr, "%s:%d (%s) large negative constants (%" PRId64 " < min %" PRId64 ") not yet implemented\n",
				__FILE__, __LINE__, __func__,
				v, (int64_t) MIN_CONST_VALUE);
		abort();
	}

	return arg;
}

static struct jvst_op_arg
arg_tt(enum SJP_EVENT tt)
{
	struct jvst_op_arg arg = {
		.type  = JVST_VM_ARG_TOKTYPE,
		.u = { .index = tt },
	};

	return arg;
}

static struct jvst_op_arg
arg_itmp(struct op_assembler *opasm)
{
	struct jvst_op_arg arg = {
		.type  = JVST_VM_ARG_INT,
		.u = { .index = opasm->ntmp++ },
	};

	return arg;
}

static struct jvst_op_arg
arg_ftmp(struct op_assembler *opasm)
{
	struct jvst_op_arg arg = {
		.type  = JVST_VM_ARG_FLOAT,
		.u = { .index = opasm->ntmp++ },
	};

	return arg;
}

static struct jvst_op_arg
arg_slot(size_t ind)
{
	struct jvst_op_arg arg = {
		.type  = JVST_VM_ARG_SLOT,
		.u = { .index = ind },
	};

	return arg;
}

static int64_t
proc_add_split(struct op_assembler *opasm, struct jvst_ir_stmt *frames)
{
	struct jvst_op_proc *parent, *split_procs, **splpp;
	struct jvst_ir_stmt *fr;
	size_t ind;

	assert(opasm  != NULL);
	assert(frames != NULL);

	parent = opasm->currproc;
	assert(parent != NULL);

	split_procs = NULL;
	splpp = &split_procs;

	for (fr = frames; fr != NULL; fr = fr->next) {
		struct jvst_op_proc *p;

		assert(fr->type == JVST_IR_STMT_FRAME);

		p = op_assemble_frame(opasm, fr);

		*splpp = p;
		splpp = &p->split_next;
	}

	ind = parent->nsplit++;
	if (parent->nsplit > opasm->maxsplit) {
		size_t newmax;
		struct jvst_op_proc **pv;

		if (opasm->maxsplit < 4) {
			newmax = 4;
		} else if (opasm->maxsplit < 1024) {
			newmax = 2*opasm->maxsplit;
		} else {
			newmax = opasm->maxsplit;
			newmax += newmax/4;
		}

		assert(newmax > opasm->maxsplit+1);
		pv = xrealloc(opasm->splits, newmax * sizeof opasm->splits[0]);
		assert(pv != NULL);

		opasm->splits = pv;
		opasm->maxsplit = newmax;

		parent->splits = opasm->splits;
	}

	assert(split_procs != NULL);
	parent->splits[ind] = split_procs;

	return (int64_t)ind;
}

static int64_t
proc_add_float(struct op_assembler *opasm, double v)
{
	struct jvst_op_proc *proc;
	size_t ind;

	proc = opasm->currproc;
	assert(proc != NULL);

	ind = proc->nfloat++;
	if (proc->nfloat > opasm->maxfloat) {
		size_t newmax;
		double *fv;

		if (opasm->maxfloat < 4) {
			newmax = 4;
		} else if (opasm->maxfloat < 1024) {
			newmax = 2*opasm->maxfloat;
		} else {
			newmax = opasm->maxfloat;
			newmax += newmax/4;
		}

		assert(newmax > opasm->maxfloat+1);
		fv = xrealloc(opasm->fdata, newmax * sizeof opasm->fdata[0]);
		assert(fv != NULL);
		opasm->fdata = fv;
		opasm->maxfloat = newmax;

		proc->fdata = opasm->fdata;
	}

	proc->fdata[ind] = v;

	return (int64_t)ind;
}

static int64_t
proc_add_uconst(struct op_assembler *opasm, uint64_t v)
{
	struct jvst_op_proc *proc;
	size_t ind;

	proc = opasm->currproc;
	assert(proc != NULL);

	ind = proc->nconst++;
	if (proc->nconst > opasm->maxconst) {
		size_t newmax;
		int64_t *cv;

		if (opasm->maxconst < 4) {
			newmax = 4;
		} else if (opasm->maxconst < 1024) {
			newmax = 2*opasm->maxconst;
		} else {
			newmax = opasm->maxconst;
			newmax += newmax/4;
		}

		assert(newmax > opasm->maxconst+1);
		cv = xrealloc(opasm->cdata, newmax * sizeof opasm->cdata[0]);
		assert(cv != NULL);
		opasm->cdata = cv;
		opasm->maxconst = newmax;

		proc->cdata = opasm->cdata;
	}

	proc->cdata[ind] = (int64_t)v;

	return (int64_t)ind;
}

static void
emit_instr(struct op_assembler *opasm, struct jvst_op_instr *instr)
{
	if (opasm->label_block) {
		char *lbl, tmp[128];
		size_t n;

		/* label instruction */
		snprintf(tmp, sizeof tmp, "%s_%zu",
			opasm->label_block->u.block.prefix,
			opasm->label_block->u.block.lindex);

		// XXX - fix string allocations! (this leaks)
		n = strlen(tmp)+1;
		lbl = xmalloc(n);
		memcpy(lbl, tmp, n);
		instr->label = lbl;

		assert(opasm->label_block->data == NULL);
		opasm->label_block->data = instr;

		opasm->label_block = NULL;
	}

	*opasm->ipp = instr;
	opasm->ipp = &instr->next;
}

static struct jvst_op_instr *
emit_branch(struct op_assembler *opasm, enum jvst_vm_op op, struct jvst_op_block *block)
{
	struct jvst_op_instr *instr;
	switch (op) {
	case JVST_OP_BR:
	case JVST_OP_CBT:
	case JVST_OP_CBF:
		goto emit_branch;

	case JVST_OP_NOP:
	case JVST_OP_PROC:
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
	case JVST_OP_BTEST:
	case JVST_OP_BAND:
	case JVST_OP_VALID:
	case JVST_OP_INVALID:
	case JVST_OP_MOVE:
		fprintf(stderr, "op %s is not a branch\n", jvst_op_name(op));
		abort();

	}

	fprintf(stderr, "unknown op %d\n", op);
	abort();

emit_branch:
	instr = op_instr_new(op);
	instr->u.branch.label = block->label;
	instr->u.branch.dest = block;

	emit_instr(opasm, instr);

	return instr;
}

static struct jvst_op_instr *
emit_cond(struct op_assembler *opasm, enum jvst_vm_op op, 
	struct jvst_op_arg a0, struct jvst_op_arg a1)
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
		goto emit_cond;

	case JVST_OP_BR:
	case JVST_OP_CBT:
	case JVST_OP_CBF:
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
	case JVST_OP_BTEST:
	case JVST_OP_BAND:
	case JVST_OP_VALID:
	case JVST_OP_INVALID:
	case JVST_OP_MOVE:
		fprintf(stderr, "op %s is not a conditional\n", jvst_op_name(op));
		abort();
	}

	fprintf(stderr, "unknown op %d\n", op);
	abort();

emit_cond:
	instr = op_instr_new(op);
	instr->u.args[0] = a0;
	instr->u.args[1] = a1;
	emit_instr(opasm, instr);

	return instr;
}

static void
op_assemble(struct op_assembler *opasm, struct jvst_ir_stmt *stmt);

static struct jvst_op_instr *
instr_last(struct jvst_op_instr *first)
{
	assert(first != NULL);
	while (first->next != NULL) {
		first = first->next;
	}
	return first;
}

static struct jvst_op_block *
branch_chain_dest(struct jvst_op_block *b)
{
	for(;;) {
		assert(b != NULL);
		assert(b->ilist != NULL);
		if (b->ilist->op != JVST_OP_BR) {
			return b;
		}

		b = b->ilist->u.branch.dest;
	}
}

static struct jvst_op_block *
last_unmarked_branch(struct jvst_op_block *b)
{
	struct jvst_op_instr *br, *instr;
	br = NULL;
	for (instr = b->ilist; instr != NULL; instr=instr->next) {
		switch (instr->op) {
		case JVST_OP_BR:
		case JVST_OP_CBT:
		case JVST_OP_CBF:
			assert(instr->u.branch.dest != NULL);
			if (! instr->u.branch.dest->work) {
				br = instr;
			}
			break;

		default:
			/* nop */
			break;
		}
	}

	return (br != NULL) ? br->u.branch.dest : NULL;
}

static struct jvst_op_block **
sort_last_unmarked_dest(struct jvst_op_block *b, struct jvst_op_block **qpp)
{
	if (b->work) {
		return qpp;
	}

	b->work = 1;
	*qpp = b;
	qpp = &b->next;
	*qpp = NULL;

	for(;;) {
		struct jvst_op_block *br;
		br = last_unmarked_branch(b);
		if (br == NULL) {
			break;
		}

		qpp = sort_last_unmarked_dest(br, qpp);
	}

	return qpp;
}

static struct jvst_op_block *
resort_blocks(struct jvst_op_block *blk)
{
	size_t i,n;

	struct jvst_op_block *b, **q, *ordered, **opp;
	// Mark all blocks as unvisited for sorting
	for (n=0, b=blk; b != NULL; b = b->next) {
		b->work = 0;
		n++;
	}

	// trivial cases...
	if (n < 2) {
		return blk;
	}

	// load queue for sorting
	q = xmalloc(n * sizeof *q);
	for (i=0,b = blk; b != NULL; i++, b=b->next) {
		q[i] = b;
	}

	ordered = NULL;
	opp = &ordered;
	for (i=0; i < n; i++) {
		if (q[i]->work) {
			continue;
		}

		opp = sort_last_unmarked_dest(q[i], opp);
	}

	free(q);

	return ordered;
}

static void
mark_reachable(struct jvst_op_block *blk)
{
	struct jvst_op_instr *instr;

	blk->work = 1;
	for(instr = blk->ilist; instr != NULL; instr = instr->next) {
		struct jvst_op_block *dst;

		switch (instr->op) {
		case JVST_OP_BR:
		case JVST_OP_CBT:
		case JVST_OP_CBF:
			assert(instr->u.branch.dest != NULL);
			if (instr->u.branch.dest->work == 0) {
				mark_reachable(instr->u.branch.dest);
			}
			break;

		default:
			/* nop */
			break;
		}
	}

	for (; blk != NULL; blk = blk->next) {

	}
}

static void
op_finish_proc(struct jvst_op_proc *proc)
{
	(void)proc;
}

static void
op_assemble_seq(struct op_assembler *opasm, struct jvst_ir_stmt *stmt_list)
{
	struct jvst_ir_stmt *stmt;

	for (stmt = stmt_list; stmt != NULL; stmt = stmt->next) {
		op_assemble(opasm, stmt);
	}
}

static struct jvst_op_proc *
op_assemble_frame(struct op_assembler *opasm, struct jvst_ir_stmt *top)
{
	struct op_assembler frame_opasm;
	struct jvst_op_proc *proc;
	struct jvst_op_block *block;
	struct jvst_ir_stmt *stmt;
	size_t nslots, off;

	assert(top->type == JVST_IR_STMT_FRAME);

	// allocate slots for counters
	off = 0;
	for (stmt = top->u.frame.counters; stmt != NULL; stmt = stmt->next) {
		assert(stmt->type == JVST_IR_STMT_COUNTER);
		stmt->u.counter.frame_off = off++;
	}

	// allocate slots for bit vectors
	for (stmt = top->u.frame.bitvecs; stmt != NULL; stmt = stmt->next) {
		assert(stmt->type == JVST_IR_STMT_BITVECTOR);
		stmt->u.bitvec.frame_off = off++;
	}

	// can't rely on top->u.frame.ncounters or top->u.frame.nbitvecs
	// because they're not decremented if a bitvec or counter is
	// removed to keep names unique
	nslots = off;

	proc = op_proc_new();
	proc->nslots = nslots;
	*opasm->procpp = proc;
	opasm->procpp = &proc->next;
	
	frame_opasm = *opasm;
	frame_opasm.nlbl = 0;
	frame_opasm.ntmp = 0;

	frame_opasm.fdata = NULL;
	frame_opasm.maxfloat = 0;

	frame_opasm.cdata = NULL;
	frame_opasm.maxconst = 0;

	frame_opasm.splits = NULL;
	frame_opasm.maxsplit = 0;

	frame_opasm.currproc = proc;
	frame_opasm.ipp = &proc->ilist;

	// XXX - allocate storage for floats, dfas, splits
	op_assemble_seq(&frame_opasm, top->u.frame.stmts);

	op_finish_proc(proc);

	opasm->procpp = frame_opasm.procpp;

	return proc;
}

static struct jvst_op_block LOOP_BLOCK;

static void
opasm_setup_block(struct op_assembler *block_opasm, struct op_assembler *opasm, struct jvst_op_block *block)
{
	*opasm->bpp = block;
	opasm->bpp = &block->next;

	*block_opasm = *opasm;
	block_opasm->ipp = &block->ilist;
}

static void
opasm_finish_block(struct op_assembler *block_opasm, struct op_assembler *opasm)
{
	opasm->nlbl = block_opasm->nlbl;
	opasm->ntmp = block_opasm->ntmp;
	opasm->bpp  = block_opasm->bpp;
	opasm->procpp = block_opasm->procpp;
}

static struct jvst_op_block *
op_assemble_block(struct op_assembler *opasm, struct jvst_ir_stmt *top, const char *prefix, struct jvst_op_block *bnext)
{
	struct op_assembler block_opasm;
	struct jvst_op_proc *proc;
	struct jvst_op_block *block;

	if (prefix == NULL) {
		prefix = "L";
	}
	block = op_block_newf(NULL, "%s_%" PRId64, prefix, opasm->nlbl++);

	opasm_setup_block(&block_opasm, opasm, block);

	// XXX - allocate storage for floats, dfas, splits
	op_assemble_seq(&block_opasm, top);

	if (bnext == &LOOP_BLOCK) {
		emit_branch(&block_opasm, JVST_OP_BR, block);
	} else if (bnext != NULL) {
		emit_branch(&block_opasm, JVST_OP_BR, bnext);
	}

	opasm_finish_block(&block_opasm, opasm);

	return block;
}

enum { ARG_NONE, ARG_BOOL, ARG_FLOAT, ARG_INT, ARG_DEST };

static int
op_arg_type(enum jvst_op_arg_type type)
{
	switch (type) {
	case JVST_VM_ARG_NONE:
		return ARG_NONE;

	case JVST_VM_ARG_FLAG:
	case JVST_VM_ARG_PC:
	case JVST_VM_ARG_TT:
	case JVST_VM_ARG_TLEN:
	case JVST_VM_ARG_TCOMPLETE:
	case JVST_VM_ARG_M:
	case JVST_VM_ARG_INT:
	case JVST_VM_ARG_SLOT:
	case JVST_VM_ARG_TOKTYPE:
	case JVST_VM_ARG_CONST:
	case JVST_VM_ARG_POOL:
		return ARG_INT;

	case JVST_VM_ARG_TNUM:
	case JVST_VM_ARG_FLOAT:
		return ARG_FLOAT;

	case JVST_VM_ARG_INSTR:
	case JVST_VM_ARG_LABEL:
		return ARG_DEST;
	}

	fprintf(stderr, "%s:%d (%s) unknown op arg type %d\n",
		__FILE__, __LINE__, __func__, type);
	abort();
}

static struct jvst_op_arg
emit_cond_arg(struct op_assembler *opasm, struct jvst_ir_expr *arg)
{
	struct jvst_op_arg a;

	switch (arg->type) {
	case JVST_IR_EXPR_NONE:
		return arg_none();

	case JVST_IR_EXPR_NUM:
		{
			int64_t fidx;
			struct jvst_op_arg freg;
			struct jvst_op_instr *instr;

			fidx = proc_add_float(opasm, arg->u.vnum);
			freg = arg_ftmp(opasm);
			instr = op_instr_new(JVST_OP_FLOAD);
			instr->u.args[0] = freg;
			instr->u.args[1] = arg_const(fidx);
			emit_instr(opasm, instr);
			return freg;
		}

	case JVST_IR_EXPR_TOK_TYPE:
		return arg_special(JVST_VM_ARG_TT);

	case JVST_IR_EXPR_TOK_NUM:
		return arg_special(JVST_VM_ARG_TNUM);

	case JVST_IR_EXPR_TOK_LEN:
		return arg_special(JVST_VM_ARG_TLEN);

	case JVST_IR_EXPR_TOK_COMPLETE:
		return arg_special(JVST_VM_ARG_TCOMPLETE);

	case JVST_IR_EXPR_COUNT:
		{
			struct jvst_op_arg ireg;
			struct jvst_op_instr *instr;
			struct jvst_ir_stmt *counter;

			counter = arg->u.count.counter;
			assert(counter != NULL);
			assert(counter->type == JVST_IR_STMT_COUNTER);

			ireg = arg_itmp(opasm);
			instr = op_instr_new(JVST_OP_ILOAD);
			instr->u.args[0] = ireg;
			instr->u.args[1] = arg_slot(counter->u.counter.frame_off);
			emit_instr(opasm, instr);
			return ireg;
		}

	case JVST_IR_EXPR_SIZE:
		{
			struct jvst_op_arg ireg;
			struct jvst_op_instr *instr;
			size_t v;

			v = arg->u.vsize;

			// XXX - check that SIZE fits in an ILOAD-able constant...
			if (v > MAX_CONST_SIZE) {
				fprintf(stderr, "%s:%d (%s) large sizes (%zu > max %zu) not yet implemented\n",
						__FILE__, __LINE__, __func__,
						v, (size_t) MAX_CONST_SIZE);
				abort();
			}

			ireg = arg_itmp(opasm);
			instr = op_instr_new(JVST_OP_ILOAD);
			instr->u.args[0] = ireg;
			instr->u.args[1] = arg_const(v);

			emit_instr(opasm, instr);
			return ireg;
		}

	// SPLIT(i, reg):
	// splits execution using split 'i' (data attached to current
	// proc), returns number of valid returns in reg
	case JVST_IR_EXPR_SPLIT:
		{
			struct jvst_op_instr *instr;
			struct jvst_op_arg ireg;
			int64_t split_ind;

			ireg = arg_itmp(opasm);
			split_ind = proc_add_split(opasm, arg->u.split.frames);

			instr = op_instr_new(JVST_OP_SPLIT);
			instr->u.args[0] = arg_const(split_ind);
			instr->u.args[1] = ireg;

			emit_instr(opasm, instr);

			return ireg;
		}

	case JVST_IR_EXPR_INT:
	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_BCOUNT:
	case JVST_IR_EXPR_BTEST:
	case JVST_IR_EXPR_BTESTALL:
	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTONE:
	case JVST_IR_EXPR_SLOT:
	case JVST_IR_EXPR_ITEMP:
	case JVST_IR_EXPR_FTEMP:
	case JVST_IR_EXPR_SEQ:
	case JVST_IR_EXPR_MATCH:
		fprintf(stderr, "%s:%d (%s) expression %s not yet implemented\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(arg->type));
		abort();

	case JVST_IR_EXPR_ISTOK:
	case JVST_IR_EXPR_ISINT:
	case JVST_IR_EXPR_NE:
	case JVST_IR_EXPR_LT:
	case JVST_IR_EXPR_LE:
	case JVST_IR_EXPR_EQ:
	case JVST_IR_EXPR_GE:
	case JVST_IR_EXPR_GT:
	case JVST_IR_EXPR_AND:
	case JVST_IR_EXPR_OR:
	case JVST_IR_EXPR_NOT:
		fprintf(stderr, "%s:%d (%s) expression %s is not an argument\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(arg->type));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown expression type %d\n",
			__FILE__, __LINE__, __func__,
			arg->type);
	abort();
}

static struct jvst_op_instr *
emit_cmp(struct op_assembler *opasm, struct jvst_ir_expr *expr, 
	struct jvst_op_arg a0, struct jvst_op_arg a1)
{
	int t0, t1;
	enum jvst_vm_op op;

	t0 = op_arg_type(a0.type);
	t1 = op_arg_type(a1.type);
	if (t0 != t1) {
		char msg[128] = {0};
		struct sbuf b = { .buf = msg, .cap = sizeof msg };
		sbuf_snprintf(&b, "%s:%d (%s) types of op arguments ", __FILE__, __LINE__, __func__);
		op_arg_dump(&b, a0);
		sbuf_snprintf(&b, " and ");
		op_arg_dump(&b, a1);
		sbuf_snprintf(&b, " do not agree");
		fprintf(stderr, "%s\n", b.buf);
		abort();
	}

	assert((t0 == ARG_INT) || (t0 == ARG_FLOAT));
	assert((t1 == ARG_INT) || (t1 == ARG_FLOAT));

	switch (expr->type) {
	case JVST_IR_EXPR_NE:
		op = (t1 == ARG_INT) ? JVST_OP_INEQ : JVST_OP_FNEQ;
		goto emit;

	case JVST_IR_EXPR_LT:
		op = (t1 == ARG_INT) ? JVST_OP_ILT : JVST_OP_FLT;
		goto emit;

	case JVST_IR_EXPR_LE:
		op = (t1 == ARG_INT) ? JVST_OP_ILE : JVST_OP_FLE;
		goto emit;

	case JVST_IR_EXPR_EQ:
		op = (t1 == ARG_INT) ? JVST_OP_IEQ : JVST_OP_FEQ;
		goto emit;

	case JVST_IR_EXPR_GE:
		op = (t1 == ARG_INT) ? JVST_OP_IGE : JVST_OP_FGE;
		goto emit;

	case JVST_IR_EXPR_GT:
		op = (t1 == ARG_INT) ? JVST_OP_IGT : JVST_OP_FGT;
		goto emit;

	case JVST_IR_EXPR_NONE:
	case JVST_IR_EXPR_ISTOK:
	case JVST_IR_EXPR_ISINT:
	case JVST_IR_EXPR_AND:
	case JVST_IR_EXPR_OR:
	case JVST_IR_EXPR_NOT:
	case JVST_IR_EXPR_BTEST:
	case JVST_IR_EXPR_BTESTALL:
	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTONE:
	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_NUM:
	case JVST_IR_EXPR_INT:
	case JVST_IR_EXPR_SIZE:
	case JVST_IR_EXPR_TOK_TYPE:
	case JVST_IR_EXPR_TOK_NUM:
	case JVST_IR_EXPR_TOK_COMPLETE:
	case JVST_IR_EXPR_TOK_LEN:
	case JVST_IR_EXPR_COUNT:
	case JVST_IR_EXPR_BCOUNT:
	case JVST_IR_EXPR_SPLIT:
	case JVST_IR_EXPR_SLOT:
	case JVST_IR_EXPR_ITEMP:
	case JVST_IR_EXPR_FTEMP:
	case JVST_IR_EXPR_SEQ:
	case JVST_IR_EXPR_MATCH:
		fprintf(stderr, "%s:%d (%s) IR expression %s is not a comparison\n",
			__FILE__, __LINE__, __func__, jvst_ir_expr_type_name(expr->type));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown IR expression %d\n",
		__FILE__, __LINE__, __func__, expr->type);
	abort();

emit:
	return emit_cond(opasm, op, a0, a1);
}

static void
op_assemble_cond(struct op_assembler *opasm, struct jvst_ir_expr *cond)
{
	switch (cond->type) {
	case JVST_IR_EXPR_NONE:
		fprintf(stderr, "%s:%d (%s) invalid NONE expression\n",
			__FILE__, __LINE__, __func__);
		abort();

	case JVST_IR_EXPR_ISTOK:
		emit_cond(opasm, JVST_OP_IEQ,
			arg_special(JVST_VM_ARG_TT), arg_tt(cond->u.istok.tok_type));
		return;

	case JVST_IR_EXPR_ISINT:
		emit_cond(opasm, JVST_OP_FINT,
			arg_special(JVST_VM_ARG_TNUM), arg_none());
		return;

	case JVST_IR_EXPR_NE:
	case JVST_IR_EXPR_LT:
	case JVST_IR_EXPR_LE:
	case JVST_IR_EXPR_EQ:
	case JVST_IR_EXPR_GE:
	case JVST_IR_EXPR_GT:
		{
			struct jvst_op_arg a0,a1;
			a0 = emit_cond_arg(opasm, cond->u.cmp.left);
			a1 = emit_cond_arg(opasm, cond->u.cmp.right);
			emit_cmp(opasm, cond, a0,a1);
		}
		return;

	case JVST_IR_EXPR_BTEST:
		assert(cond->u.btest.b0 == cond->u.btest.b1);
		/* fallthrough */

	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTALL:
		{
			struct jvst_ir_stmt *bv;
			uint64_t mask;
			size_t nb, b0,b1, nbm;
			int64_t cidx;
			struct jvst_op_arg iarg0, ireg1, slot;
			struct jvst_op_instr *instr;

			bv = cond->u.btest.bitvec;
			assert(bv != NULL);
			assert(bv->type == JVST_IR_STMT_BITVECTOR);

			nb = bv->u.bitvec.nbits;

			// XXX - remove this limitation!
			if (nb > 64) {
				fprintf(stderr, "%s:%d (%s) bitvectors with more than 64 bits are currently unsupported\n",
						__FILE__, __LINE__, __func__);
				abort();
			}

			b0 = cond->u.btest.b0;
			b1 = cond->u.btest.b1;
			if (b1 == (size_t)-1) {
				b1 = nb-1;
			}

			if (b0 >= nb || b1 >= nb || b0 > b1) {
				fprintf(stderr, "%s:%d (%s) invalid bit range (%zu - %zu) for bitvector with %zu bits\n",
						__FILE__, __LINE__, __func__, b0,b1,nb);
				abort();
			}

			nbm = b1-b0+1;

			// XXX - remove 64-bit limitation!
			if (nbm == 64) {
				mask = ~(uint64_t)0;
			} else {
				mask = (((uint64_t)1) << nbm) - 1;
				mask = mask << b0;
			}

			if (mask <= MAX_CONST_VALUE) {
				iarg0 = arg_const(mask);
			} else {
				// emit mask constant and load
				cidx = proc_add_uconst(opasm, mask);
				iarg0 = arg_itmp(opasm);
				instr = op_instr_new(JVST_OP_ILOAD);
				instr->u.args[0] = iarg0;
				instr->u.args[1] = arg_const(cidx);
				emit_instr(opasm, instr);
			}

			// emit slot load
			ireg1 = arg_itmp(opasm);
			instr = op_instr_new(JVST_OP_ILOAD);
			instr->u.args[0] = ireg1;
			instr->u.args[1] = arg_slot(bv->u.bitvec.frame_off);
			emit_instr(opasm, instr);

			// emit AND
			instr = op_instr_new(JVST_OP_BAND);
			instr->u.args[0] = ireg1;
			instr->u.args[1] = iarg0;
			emit_instr(opasm, instr);

			// emit test
			//
			switch (cond->type) {
			case JVST_IR_EXPR_BTESTANY:
				emit_cond(opasm, JVST_OP_INEQ, ireg1, arg_const(0));
				break;

			case JVST_IR_EXPR_BTEST:
			case JVST_IR_EXPR_BTESTALL:
				emit_cond(opasm, JVST_OP_IEQ, ireg1, iarg0);
				break;

			default:
				assert( !"unreachable" );
			}
		}
		return;

	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_TOK_COMPLETE:
	case JVST_IR_EXPR_BTESTONE:
		fprintf(stderr, "%s:%d (%s) expression %s not yet supported\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(cond->type));
		abort();

	case JVST_IR_EXPR_AND:
	case JVST_IR_EXPR_OR:
	case JVST_IR_EXPR_NOT:
		fprintf(stderr, "%s:%d (%s) expression %s is not a simple boolean condition\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(cond->type));
		abort();

	case JVST_IR_EXPR_NUM:
	case JVST_IR_EXPR_INT:
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
	case JVST_IR_EXPR_SEQ:
	case JVST_IR_EXPR_MATCH:
		fprintf(stderr, "%s:%d (%s) expression %s is not a boolean condition\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(cond->type));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown expression type %d\n",
		__FILE__, __LINE__, __func__, cond->type);
	abort();
}

static void
op_assemble_match(struct op_assembler *opasm, struct jvst_ir_stmt *stmt)
{
	struct jvst_ir_mcase *mc;
	struct jvst_op_instr *instr;
	struct jvst_op_block *cblk, *cjoin;
	size_t dfa;

	// XXX - duplicate DFA and replace mcases with appropriate integer cases
	// XXX - allocate DFA table

	assert(stmt->type == JVST_IR_STMT_MATCH);

	dfa = opasm->currproc->ndfa++;

	instr = op_instr_new(JVST_OP_MATCH);
	instr->u.args[0] = arg_const(dfa);
	instr->u.args[1] = arg_none();

	*opasm->ipp = instr;
	opasm->ipp = &instr->next;

	cjoin = op_assemble_block(opasm, NULL, "match_join", NULL);
	cjoin->ilist = op_instr_new(JVST_OP_NOP);

	// default case
	cblk = op_assemble_block(opasm, stmt->u.match.default_case, "M", cjoin);
	instr = op_instr_new(JVST_OP_IEQ);
	instr->u.args[0] = arg_special(JVST_VM_ARG_M);
	instr->u.args[1] = arg_const(0);

	*opasm->ipp = instr;
	opasm->ipp = &instr->next;

	emit_branch(opasm, JVST_OP_CBT, cblk);

	for (mc = stmt->u.match.cases; mc != NULL; mc = mc->next) {
		cblk = op_assemble_block(opasm, mc->stmt, "M", cjoin);
		instr = op_instr_new(JVST_OP_IEQ);
		instr->u.args[0] = arg_special(JVST_VM_ARG_M);
		instr->u.args[1] = arg_const(mc->which);

		*opasm->ipp = instr;
		opasm->ipp = &instr->next;

		emit_branch(opasm, JVST_OP_CBT, cblk);
	}

	opasm->ipp = &cjoin->ilist;
}

static void
op_assemble(struct op_assembler *opasm, struct jvst_ir_stmt *stmt)
{
	struct jvst_op_instr *instr;
	struct jvst_op_block *block;
	const char *label;

	switch (stmt->type) {
	case JVST_IR_STMT_NOP:
		return;

	case JVST_IR_STMT_FRAME:
		{
			struct jvst_op_proc *proc;
			proc = op_assemble_frame(opasm, stmt);
			if (opasm->ipp != NULL) {
				instr = op_instr_new(JVST_OP_CALL);
				instr->u.call.dest = proc;
				emit_instr(opasm, instr);
			}
		}
		return;

	case JVST_IR_STMT_TOKEN:
		emit_instr(opasm, op_instr_new(JVST_OP_TOKEN));
		return;

	case JVST_IR_STMT_CONSUME:
		emit_instr(opasm, op_instr_new(JVST_OP_CONSUME));
		return;

	case JVST_IR_STMT_INCR:
		{
			struct jvst_ir_stmt *counter;
			counter = stmt->u.counter_op.counter;
			assert(counter != NULL);
			assert(counter->type == JVST_IR_STMT_COUNTER);

			instr = op_instr_new(JVST_OP_INCR);
			instr->u.args[0] = arg_slot(counter->u.counter.frame_off);
			instr->u.args[1] = arg_none();
			emit_instr(opasm, instr);
		}
		return;

	case JVST_IR_STMT_BSET:
		{
			struct jvst_ir_stmt *bv;
			bv = stmt->u.bitop.bitvec;
			assert(bv != NULL);
			assert(bv->type == JVST_IR_STMT_BITVECTOR);

			instr = op_instr_new(JVST_OP_BSET);
			instr->u.args[0] = arg_slot(bv->u.bitvec.frame_off);
			instr->u.args[1] = arg_const(stmt->u.bitop.bit);
			emit_instr(opasm, instr);
		}
		return;

	case JVST_IR_STMT_SPLITVEC:
		{
			struct jvst_ir_stmt *bv;
			int64_t split_ind;

			bv = stmt->u.splitvec.bitvec;
			assert(bv != NULL);
			assert(bv->type == JVST_IR_STMT_BITVECTOR);

			split_ind = proc_add_split(opasm, stmt->u.splitvec.split_frames);

			instr = op_instr_new(JVST_OP_SPLITV);
			instr->u.args[0] = arg_const(split_ind);
			instr->u.args[1] = arg_slot(bv->u.bitvec.frame_off);

			emit_instr(opasm, instr);

		}
		return;

	case JVST_IR_STMT_BLOCK:
		opasm->label_block = stmt;
		return;

	case JVST_IR_STMT_BRANCH:
		instr = op_instr_new(JVST_OP_BR);
		asm_addr_fixup_add(opasm->fixups, instr, &instr->u.args[0], stmt->u.branch);
		emit_instr(opasm, instr);
		return;

	case JVST_IR_STMT_CBRANCH:
		// XXX - refactor into its own function

		/* emit condition */
		op_assemble_cond(opasm, stmt->u.cbranch.cond);

		if (stmt->next == NULL) {
			goto cbranch_3;
		}

		if (stmt->u.cbranch.br_false == stmt->next) {
			goto cbranch_1;
		}

		if (stmt->u.cbranch.br_true == stmt->next) {
			goto cbranch_2;
		}

		goto cbranch_3;

cbranch_1:
		instr = op_instr_new(JVST_OP_CBT);
		asm_addr_fixup_add(opasm->fixups, instr, &instr->u.args[0], stmt->u.cbranch.br_true);
		emit_instr(opasm, instr);
		return;

cbranch_2:
		instr = op_instr_new(JVST_OP_CBF);
		asm_addr_fixup_add(opasm->fixups, instr, &instr->u.args[0], stmt->u.cbranch.br_false);
		emit_instr(opasm, instr);
		return;

cbranch_3:
		instr = op_instr_new(JVST_OP_CBT);
		asm_addr_fixup_add(opasm->fixups, instr, &instr->u.args[0], stmt->u.cbranch.br_true);
		emit_instr(opasm, instr);

		instr = op_instr_new(JVST_OP_BR);
		asm_addr_fixup_add(opasm->fixups, instr, &instr->u.args[0], stmt->u.cbranch.br_false);
		emit_instr(opasm, instr);
		return;

	case JVST_IR_STMT_VALID:
		emit_instr(opasm, op_instr_new(JVST_OP_VALID));
		return;

	case JVST_IR_STMT_INVALID:
		instr = op_instr_new(JVST_OP_INVALID);
		instr->u.args[0] = arg_const(stmt->u.invalid.code);
		emit_instr(opasm, instr);
		return;

	case JVST_IR_STMT_BCLEAR:
	case JVST_IR_STMT_DECR:
	case JVST_IR_STMT_MOVE:
	case JVST_IR_STMT_CALL:
	case JVST_IR_STMT_PROGRAM:
		fprintf(stderr, "%s:%d (%s) IR statement %s not yet implemented\n",
			__FILE__, __LINE__, __func__, jvst_ir_stmt_type_name(stmt->type));
		abort();

	case JVST_IR_STMT_MATCH:
	case JVST_IR_STMT_BREAK:
	case JVST_IR_STMT_LOOP:
	case JVST_IR_STMT_SEQ:
	case JVST_IR_STMT_IF:

	case JVST_IR_STMT_COUNTER:
	case JVST_IR_STMT_MATCHER:
	case JVST_IR_STMT_BITVECTOR:
	case JVST_IR_STMT_SPLITLIST:
		fprintf(stderr, "%s:%d (%s) should not encounter IR statement %s in op assembly\n",
			__FILE__, __LINE__, __func__, jvst_ir_stmt_type_name(stmt->type));
		abort();
	}

	fprintf(stderr, "unknown IR statement %d\n", stmt->type);
	abort();
}

struct jvst_op_program *
jvst_op_assemble(struct jvst_ir_stmt *ir)
{
	struct op_assembler opasm = { 0 };
	struct asm_addr_fixup_list fixups = { 0 };
	struct jvst_op_program *prog;
	struct jvst_ir_stmt *fr;
	size_t i;

	assert(ir != NULL);
	assert(ir->type == JVST_IR_STMT_PROGRAM);

	opasm.prog = op_prog_new(NULL);
	opasm.procpp = &opasm.prog->procs;
	opasm.fixups = &fixups;

	for (i=0, fr=ir->u.program.frames; fr != NULL; i++, fr = fr->next) {
		struct jvst_op_proc *proc;

		proc = op_assemble_frame(&opasm, fr);
		proc->proc_index = i;
	}

	asm_fixup_addresses(&fixups);
	asm_addr_fixup_list_free(&fixups);

	return opasm.prog;
}

void
jvst_op_print(struct jvst_op_program *prog)
{
	size_t i;
	// FIXME: gross hack
	char buf[65536] = {0}; // 64K

	jvst_op_dump(prog, buf, sizeof buf);
	for (i=0; i < 72; i++) {
		fprintf(stderr, "-");
	}
	fprintf(stderr, "\n");
	fprintf(stderr, "%s\n", buf);
}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
