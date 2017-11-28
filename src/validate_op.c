#include "validate_op.h"

#include <inttypes.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stddef.h>
#include <string.h>
#include <math.h>

#include <assert.h>

#include <fsm/fsm.h>
#include <fsm/pred.h>
#include <fsm/walk.h>

#include "sjp_parser.h"
#include "sjp_testing.h"

#include "xalloc.h"
#include "jvst_macros.h"

#include "validate_sbuf.h"

#define DEBUG_DFA 0

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

	case JVST_VM_ARG_TT:
		sbuf_snprintf(buf,"%%TT");
		return;

	case JVST_VM_ARG_TNUM:
		sbuf_snprintf(buf,"%%TN");
		return;

	case JVST_VM_ARG_TLEN:
		sbuf_snprintf(buf,"%%TL");
		return;

	case JVST_VM_ARG_M:
		sbuf_snprintf(buf,"%%M");
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

	case JVST_VM_ARG_CALL:
		{
			if (arg.u.proc == NULL) {
				sbuf_snprintf(buf,"<null>");
			} else {
				sbuf_snprintf(buf, "$%zu", arg.u.proc->proc_index);
			}
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
		return;

	case JVST_OP_PROC:
		sbuf_snprintf(buf, "PROC ");
		op_arg_dump(buf, instr->args[0]);
		return;

	case JVST_OP_ICMP:
	case JVST_OP_FCMP:
		sbuf_snprintf(buf, "%s ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->args[0]);
		sbuf_snprintf(buf, ", ");
		op_arg_dump(buf, instr->args[1]);
		return;

	case JVST_OP_FINT:
		sbuf_snprintf(buf, "%s ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->args[0]);
		if (instr->args[1].type != JVST_VM_ARG_NONE) {
			sbuf_snprintf(buf, ", ");
			op_arg_dump(buf, instr->args[1]);
		}
		return;

	case JVST_OP_JMP:
		{
			const char *cond, *lbl = NULL;
			int cfield;

			assert(instr->args[0].type == JVST_VM_ARG_CONST);

			cfield = instr->args[0].u.index;

			cond = jvst_vm_br_cond_name(cfield);

			switch (instr->args[1].type) {
			case JVST_VM_ARG_INSTR:
				lbl = instr->args[1].u.dest->label;
				break;

			case JVST_VM_ARG_LABEL:
				lbl = instr->args[1].u.label;
				break;

			default:
				/* nop */
				break;
			}

			if (lbl == NULL) {
				lbl = "(null)";
			}

			sbuf_snprintf(buf, "%s %c%s :%s",
				jvst_op_name(instr->op),
				(cfield & 0x08) ? '~' : ' ',
				cond, lbl);
		}
		return;

	case JVST_OP_CALL:
		sbuf_snprintf(buf, "%s ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->args[0]);
		// XXX - dump address in args[1] 
		return;

	case JVST_OP_MATCH:
		sbuf_snprintf(buf, "%s ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->args[0]);
		return;

	case JVST_OP_INCR:
	case JVST_OP_SPLITV:
	case JVST_OP_SPLIT:
	case JVST_OP_FLOAD:
	case JVST_OP_ILOAD:
	case JVST_OP_MOVE:
		sbuf_snprintf(buf, "%s ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->args[0]);
		sbuf_snprintf(buf, ", ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->args[1]);
		return;

	case JVST_OP_TOKEN:
		sbuf_snprintf(buf, "%s", jvst_op_name(instr->op));
		if (instr->args[1].type != JVST_VM_ARG_NONE) {
			sbuf_snprintf(buf, " ");
			op_arg_dump(buf, instr->args[1]);
		}
		return;

	case JVST_OP_CONSUME:
		sbuf_snprintf(buf, "%s", jvst_op_name(instr->op));
		return;

	case JVST_OP_RETURN:
		sbuf_snprintf(buf, "%s %d",
			jvst_op_name(instr->op),
			instr->args[0].u.index);
		return;

	case JVST_OP_BAND:
	case JVST_OP_BSET:
		sbuf_snprintf(buf, "%s ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->args[0]);
		sbuf_snprintf(buf, ", ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->args[1]);
		return;

	}

	fprintf(stderr, "%s:%d (%s) Unknown OP arg type %02x\n",
			__FILE__, __LINE__, __func__, instr->op);
	abort();
}

static void
op_proc_dump(struct sbuf *buf, struct jvst_op_proc *proc, size_t fno, int indent)
{
	size_t i;
	struct jvst_op_instr *instr;

	sbuf_indent(buf, indent);
	sbuf_snprintf(buf, ".PROC %zu %zu\n", fno, proc->nslots);

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

	sbuf_indent(buf, indent);
	sbuf_snprintf(buf, ".DATA\n");

	for (i=0; i < prog->nfloat; i++) {
		sbuf_indent(buf, indent+2);
		sbuf_snprintf(buf, "FLOAT(%zu)\t%g\n", i, prog->fdata[i]);
	}

	if (prog->nfloat > 0) {
		sbuf_snprintf(buf, "\n");
	}

	for (i=0; i < prog->nconst; i++) {
		sbuf_indent(buf, indent+2);
		sbuf_snprintf(buf, "CONST(%zu)\t%" PRId64 "\t%" PRIu64 "\n",
			i, prog->cdata[i], (uint64_t) prog->cdata[i]);
	}

	if (prog->nconst > 0) {
		sbuf_snprintf(buf, "\n");
	}

	for (i=0; i < prog->nsplit; i++) {
		size_t si,off,max;
		size_t c;

		assert(prog->splitoff != NULL);
		assert(prog->splits   != NULL);

		off = (i > 0) ? prog->splitoff[i-1] : 0;
		max = prog->splitoff[i];

		sbuf_indent(buf, indent+2);
		sbuf_snprintf(buf, "SPLIT(%zu)\t", i);
		for (c=0, si=off; si < max; c++, si++) {
			struct jvst_op_proc *p;
			p = prog->splits[si];
			sbuf_snprintf(buf, " %zu", p->proc_index);

			if (c >= 6 && p->next != NULL) {
				sbuf_snprintf(buf, "\n");
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "\t\t");
				c = 0;
			}
		}

		sbuf_snprintf(buf, "\n");
	}

	if (prog->nsplit > 0) {
		sbuf_snprintf(buf, "\n");
	}

	// surely we can provide more data than this?
	for (i=0; i < prog->ndfa; i++) {
		sbuf_indent(buf, indent+2);
		sbuf_snprintf(buf, "DFA(%zu)\n", i);
	}

	if (prog->ndfa> 0) {
		sbuf_snprintf(buf, "\n");
	}

	if (prog->nsplit> 0) {
		sbuf_snprintf(buf, "\n");
	}

	for (i=0, proc=prog->procs; proc != NULL; i++, proc=proc->next) {
		op_proc_dump(buf, proc, i, indent);
		sbuf_snprintf(buf, "\n");
	}

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

enum addr_fixup_type {
	FIXUP_ARG,
	FIXUP_PROC,
	FIXUP_SPLIT,
};

struct asm_addr_fixup {
	struct jvst_op_instr *instr;
	struct jvst_ir_stmt *ir;

	union {
		struct jvst_op_arg *arg;
		struct jvst_op_proc **procp;
		struct {
			struct jvst_op_program *prog;
			size_t split_ind;
		} split;
	} u;

	enum addr_fixup_type type;
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

static struct asm_addr_fixup *
asm_addr_fixup_alloc(struct asm_addr_fixup_list *l)
{
	size_t i;

	assert(l != NULL);
	assert(l->len <= l->cap);
	if (l->len >= l->cap) {
		l->elts = xenlargevec(l->elts, &l->cap, 1, sizeof l->elts[0]);
	}

	i = l->len++;
	assert(i < l->cap);

	return &l->elts[i];
}

static void
asm_addr_fixup_add_dest(struct asm_addr_fixup_list *l,
	struct jvst_op_instr *instr, struct jvst_op_arg *arg, struct jvst_ir_stmt *ir)
{
	struct asm_addr_fixup *fixup;

	fixup = asm_addr_fixup_alloc(l);

	fixup->instr = instr;
	fixup->ir    = ir;
	fixup->u.arg = arg;
	fixup->type  = FIXUP_ARG;
}

static void
asm_addr_fixup_add_split(struct asm_addr_fixup_list *l,
	struct jvst_op_instr *instr, struct jvst_op_program *prog, size_t split_ind, struct jvst_ir_stmt *ir)
{
	struct asm_addr_fixup *fixup;

	fixup = asm_addr_fixup_alloc(l);

	fixup->type    = FIXUP_SPLIT;
	fixup->instr   = instr;
	fixup->ir      = ir;
	fixup->u.split.prog = prog;
	fixup->u.split.split_ind = split_ind;
}

static void
asm_addr_fixup_add_proc(struct asm_addr_fixup_list *l,
	struct jvst_op_instr *instr, struct jvst_op_proc **procp, struct jvst_ir_stmt *ir)
{
	struct asm_addr_fixup *fixup;

	fixup = asm_addr_fixup_alloc(l);

	fixup->instr   = instr;
	fixup->ir      = ir;
	fixup->u.procp = procp;
	fixup->type    = FIXUP_PROC;
}

static void
asm_fixup_addr(struct asm_addr_fixup *fix)
{
	switch (fix->instr->op) {
	case JVST_OP_JMP:
		assert(fix->ir != NULL);
		assert(fix->ir->data != NULL);
		assert(fix->type == FIXUP_ARG);
		fix->u.arg->type = JVST_VM_ARG_INSTR;
		fix->u.arg->u.dest = fix->ir->data;
		return;

	case JVST_OP_CALL:
		assert(fix->ir != NULL);
		assert(fix->ir->data != NULL);
		assert(fix->type == FIXUP_ARG);
		fix->u.arg->type = JVST_VM_ARG_CALL;
		fix->u.arg->u.proc = fix->ir->data;
		return;

	case JVST_OP_SPLIT:
	case JVST_OP_SPLITV:
		{
			size_t ind, max;
			struct jvst_op_program *prog;

			assert(fix->ir != NULL);
			assert(fix->ir->type == JVST_IR_STMT_FRAME);
			assert(fix->ir->data != NULL);
			assert(fix->type == FIXUP_SPLIT);

			prog = fix->u.split.prog;
			ind = fix->u.split.split_ind;

			assert(prog != NULL);
			assert(prog->splits != NULL);
			assert(prog->splitoff != NULL);
			assert(prog->nsplit > 0);

			max = prog->splitoff[prog->nsplit-1];

			assert(ind < max);

			prog->splits[ind] = fix->ir->data;
		}
		return;

		fprintf(stderr, "%s:%d (%s) address fixup for op %s not yet implemented\n",
			__FILE__, __LINE__, __func__, jvst_op_name(fix->instr->op));
		abort();

	case JVST_OP_NOP:
	case JVST_OP_PROC:
	case JVST_OP_ICMP:
	case JVST_OP_FCMP:
	case JVST_OP_FINT:
	case JVST_OP_TOKEN:
	case JVST_OP_CONSUME:
	case JVST_OP_MATCH:
	case JVST_OP_FLOAD:
	case JVST_OP_ILOAD:
	case JVST_OP_INCR:
	case JVST_OP_BSET:
	case JVST_OP_BAND:
	case JVST_OP_RETURN:
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
	struct jvst_ir_stmt *ir;
	struct jvst_op_program *prog;
	struct jvst_op_proc **procpp;
	struct jvst_op_proc *currproc;
	struct jvst_op_instr **ipp;

	/* float pool list */
	double *fdata;
	size_t maxfloat;

	/* integer pool list */
	int64_t *cdata;
	size_t maxconst;

	/* split lists
	 *
	 * lists are maintained with two structures:
	 *   1) master list of pointers to procs used in a split
	 *   2) list of offsets into the master list
	 *
	 * To find the procs for split k:
	 *   i0 = splitoff[k-1] 	for k > 0
	 *        0			for k = 0
	 *
	 *   i1 = splitoff[k]
	 *
	 * The procs for split k are then:
	 * 	splits[i0], splits[i0+1], ..., splits[i1-1]
	 */
	struct jvst_op_proc **splits;
	size_t maxsplits;

	size_t *splitoff;
	size_t maxsplitoff;

	/* dfa list */
	size_t maxdfa;
	struct jvst_vm_dfa *dfas;

	/* instruction list */
	size_t maxinstr;
	struct jvst_op_instr *ilist;

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
	case JVST_VM_ARG_TT:
	case JVST_VM_ARG_TNUM:
	case JVST_VM_ARG_TLEN:
	case JVST_VM_ARG_M:
		arg.type = type;
		return arg;

	case JVST_VM_ARG_NONE:
	case JVST_VM_ARG_TOKTYPE:
	case JVST_VM_ARG_CONST:
	case JVST_VM_ARG_POOL:
	case JVST_VM_ARG_SLOT:
	case JVST_VM_ARG_INSTR:
	case JVST_VM_ARG_LABEL:
	case JVST_VM_ARG_CALL:
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
arg_slot(size_t ind)
{
	struct jvst_op_arg arg = {
		.type  = JVST_VM_ARG_SLOT,
		.u = { .index = ind },
	};

	return arg;
}

static struct jvst_op_arg
arg_new_slot(struct op_assembler *opasm)
{
	struct jvst_op_arg arg = {
		.type  = JVST_VM_ARG_SLOT,
		.u = { 0 },
	};

	assert(opasm->currproc != NULL);

	arg.u.index = opasm->currproc->nslots++;

	return arg;
}

static int64_t
proc_add_split(struct op_assembler *opasm, struct jvst_op_instr *instr, struct jvst_ir_stmt *splitlist)
{
	struct jvst_op_program *prog;

	struct jvst_op_proc *split_procs, **splpp;
	struct jvst_ir_stmt *frames;
	size_t i,n, ind, off, max;

	assert(opasm  != NULL);
	assert(splitlist != NULL);
	assert(splitlist->type == JVST_IR_STMT_SPLITLIST);

	assert(opasm->ir != NULL);
	assert(opasm->ir->type == JVST_IR_STMT_PROGRAM);

	prog = opasm->prog;
	assert(prog != NULL);

	n=splitlist->u.split_list.nframes;
	if (prog->nsplit >= opasm->maxsplitoff) {
		opasm->splitoff = xenlargevec(opasm->splitoff,
			&opasm->maxsplitoff, 1, sizeof opasm->splitoff[0]);
		prog->splitoff = opasm->splitoff;
	}

	ind = prog->nsplit++;
	assert(ind < opasm->maxsplitoff);
	off = (ind > 0) ? prog->splitoff[ind-1] : 0;
	max = off + n;
	prog->splitoff[ind] = max;

	if (max > opasm->maxsplits) {
		opasm->splits = xenlargevec(opasm->splits,
			&opasm->maxsplits, max, sizeof opasm->splits[0]);
		prog->splits = opasm->splits;
	}

	assert(max <= opasm->maxsplits);

	frames = opasm->ir->u.program.frames;
	for (i=0; i < n; i++) {
		struct jvst_op_proc **plist;
		struct jvst_ir_stmt *fr;
		size_t ind;

		plist = &prog->splits[i+off];
		ind = splitlist->u.split_list.frame_indices[i];

		// XXX - replace this with something better!
		//
		// Q: can we guarantee that the splitlist indices are
		// sorted and that the ir program's frame list is sorted
		// by frame_ind?  if so, we can make a single pass
		// through the frame list
		for (fr = frames; fr != NULL; fr = fr->next) {
			assert(fr->type == JVST_IR_STMT_FRAME);
			if (fr->u.frame.frame_ind == ind) {
				break;
			}
		}

		if (fr == NULL) {
			fprintf(stderr, "%s:%d (%s) cannot find frame %zu\n",
				__FILE__, __LINE__, __func__, ind);
			abort();
		}

		if (fr->data != NULL) {
			*plist = fr->data;
		} else {
			asm_addr_fixup_add_split(opasm->fixups, instr, prog, i+off, fr);
		}
	}

	return (int64_t)ind;
}

static int64_t
proc_add_float(struct op_assembler *opasm, double v)
{
	struct jvst_op_program *prog;
	size_t ind;

	prog = opasm->prog;
	assert(prog != NULL);

	ind = prog->nfloat++;
	if (prog->nfloat > opasm->maxfloat) {
		opasm->fdata = xenlargevec(opasm->fdata, &opasm->maxfloat, 1, sizeof opasm->fdata[0]);
		prog->fdata = opasm->fdata;
	}

	prog->fdata[ind] = v;

	return (int64_t)ind;
}

static int64_t
proc_add_uconst(struct op_assembler *opasm, uint64_t v)
{
	struct jvst_op_program *prog;
	size_t ind;

	prog = opasm->prog;
	assert(prog != NULL);

	ind = prog->nconst++;
	if (prog->nconst > opasm->maxconst) {
		opasm->cdata = xenlargevec(opasm->cdata, &opasm->maxconst, 1, sizeof opasm->cdata[0]);
		prog->cdata = opasm->cdata;
	}

	prog->cdata[ind] = (int64_t)v;

	return (int64_t)ind;
}

static int64_t
proc_add_dfa(struct op_assembler *opasm, struct fsm *fsm)
{
	struct jvst_op_program *prog;
	size_t ind;

	prog = opasm->prog;
	assert(prog != NULL);

	ind = prog->ndfa++;
	if (prog->ndfa > opasm->maxdfa) {
		opasm->dfas = xenlargevec(opasm->dfas, &opasm->maxdfa, 1, sizeof opasm->dfas[0]);
		prog->dfas = opasm->dfas;
	}

	assert(ind < opasm->maxdfa);

	jvst_op_build_vm_dfa(fsm, &prog->dfas[ind]);
	if (DEBUG_DFA) {
		jvst_vm_dfa_debug(&prog->dfas[ind]);
	}

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
emit_cond(struct op_assembler *opasm, enum jvst_vm_op op, 
	struct jvst_op_arg a0, struct jvst_op_arg a1)
{
	struct jvst_op_instr *instr;
	switch (op) {
	case JVST_OP_ICMP:
	case JVST_OP_FCMP:
	case JVST_OP_FINT:
		instr = op_instr_new(op);
		instr->args[0] = a0;
		instr->args[1] = a1;
		emit_instr(opasm, instr);

		return instr;

	case JVST_OP_JMP:
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
	case JVST_OP_RETURN:
	case JVST_OP_MOVE:
		fprintf(stderr, "op %s is not a conditional\n", jvst_op_name(op));
		abort();
	}

	fprintf(stderr, "unknown op %d\n", op);
	abort();
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
	struct jvst_ir_stmt *stmt;
	size_t nslots, temp_off, off;

	assert(top->type == JVST_IR_STMT_FRAME);

	// allocate slots for counters, count total number of counters
	// and bitvectors (in off).  NB: can't rely on
	// top->u.frame.ncounters or top->u.frame.nbitvecs because
	// they're not decremented if a bitvec or counter is removed to
	// keep names unique
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

	proc = op_proc_new();
	proc->temp_off = off;
	proc->nslots = off + top->u.frame.ntemps;
	*opasm->procpp = proc;
	opasm->procpp = &proc->next;

	top->data = proc;

	frame_opasm = *opasm;
	frame_opasm.nlbl = 0;
	frame_opasm.ntmp = 0;

	frame_opasm.currproc = proc;
	frame_opasm.ipp = &proc->ilist;

	// XXX - allocate storage for floats, dfas, splits
	op_assemble_seq(&frame_opasm, top->u.frame.stmts);

	opasm->procpp    = frame_opasm.procpp;

	opasm->fdata     = frame_opasm.fdata;
	opasm->maxfloat  = frame_opasm.maxfloat;

	opasm->cdata     = frame_opasm.cdata;
	opasm->maxconst  = frame_opasm.maxconst;

	opasm->splits    = frame_opasm.splits;
	opasm->maxsplits = frame_opasm.maxsplits;

	opasm->splitoff  = frame_opasm.splitoff;
	opasm->maxsplitoff = frame_opasm.maxsplitoff;

	opasm->dfas      = frame_opasm.dfas;
	opasm->maxdfa    = frame_opasm.maxdfa;

	return proc;
}

enum { ARG_NONE, ARG_SLOT, ARG_BOOL, ARG_FLOAT, ARG_INT, ARG_DEST, ARG_PROC };

static int
op_arg_type(enum jvst_op_arg_type type)
{
	switch (type) {
	case JVST_VM_ARG_NONE:
		return ARG_NONE;

	case JVST_VM_ARG_TT:
	case JVST_VM_ARG_TLEN:
	case JVST_VM_ARG_M:
	case JVST_VM_ARG_SLOT:
	case JVST_VM_ARG_TOKTYPE:
	case JVST_VM_ARG_CONST:
	case JVST_VM_ARG_POOL:
		return ARG_INT;

	case JVST_VM_ARG_TNUM:
		return ARG_FLOAT;

	case JVST_VM_ARG_INSTR:
	case JVST_VM_ARG_LABEL:
		return ARG_DEST;
	case JVST_VM_ARG_CALL:
		return ARG_PROC;
	}

	fprintf(stderr, "%s:%d (%s) unknown op arg type %d\n",
		__FILE__, __LINE__, __func__, type);
	abort();
}

static int
ir_expr_type(enum jvst_ir_expr_type type)
{
	switch (type) {
	case JVST_IR_EXPR_NUM:
	case JVST_IR_EXPR_TOK_NUM:
	case JVST_IR_EXPR_FTEMP:
		return ARG_FLOAT;

	case JVST_IR_EXPR_NONE:
		return ARG_NONE;

	case JVST_IR_EXPR_SLOT:
		return ARG_SLOT;

	case JVST_IR_EXPR_TOK_TYPE:
	case JVST_IR_EXPR_TOK_LEN:
	case JVST_IR_EXPR_COUNT:
	case JVST_IR_EXPR_SIZE:
	case JVST_IR_EXPR_SPLIT:
	case JVST_IR_EXPR_ITEMP:
	case JVST_IR_EXPR_INT:
	case JVST_IR_EXPR_BCOUNT:
	case JVST_IR_EXPR_MATCH:
		return ARG_INT;

	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_BTEST:
	case JVST_IR_EXPR_BTESTALL:
	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTONE:
	case JVST_IR_EXPR_ISTOK:
	case JVST_IR_EXPR_ISINT:
	case JVST_IR_EXPR_MULTIPLE_OF:
	case JVST_IR_EXPR_NE:
	case JVST_IR_EXPR_LT:
	case JVST_IR_EXPR_LE:
	case JVST_IR_EXPR_EQ:
	case JVST_IR_EXPR_GE:
	case JVST_IR_EXPR_GT:
		return ARG_BOOL;

	case JVST_IR_EXPR_AND:
	case JVST_IR_EXPR_OR:
	case JVST_IR_EXPR_NOT:
	case JVST_IR_EXPR_SEQ:
		fprintf(stderr, "%s:%d (%s) expression %s is invalid while assembling\n",
			__FILE__, __LINE__, __func__, jvst_ir_expr_type_name(type));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown expr type %d\n",
		__FILE__, __LINE__, __func__, type);
	abort();
}

static struct jvst_op_arg
emit_match(struct op_assembler *opasm, struct jvst_ir_expr *expr);

static struct jvst_op_arg
emit_float_arg(struct op_assembler *opasm, double x)
{
	struct jvst_op_instr *instr;
	int64_t fidx;
	struct jvst_op_arg freg;

	fidx = proc_add_float(opasm, x);
	freg = arg_new_slot(opasm);

	instr = op_instr_new(JVST_OP_FLOAD);
	instr->args[0] = freg;
	instr->args[1] = arg_const(fidx);
	emit_instr(opasm, instr);

	return freg;
}

static struct jvst_op_arg
emit_op_arg(struct op_assembler *opasm, struct jvst_ir_expr *arg)
{
	struct jvst_op_arg a;

	switch (arg->type) {
	case JVST_IR_EXPR_NONE:
		return arg_none();

	case JVST_IR_EXPR_NUM:
		return emit_float_arg(opasm, arg->u.vnum);

	case JVST_IR_EXPR_TOK_TYPE:
		return arg_special(JVST_VM_ARG_TT);

	case JVST_IR_EXPR_TOK_NUM:
		return arg_special(JVST_VM_ARG_TNUM);

	case JVST_IR_EXPR_TOK_LEN:
		return arg_special(JVST_VM_ARG_TLEN);

	case JVST_IR_EXPR_COUNT:
		{
			struct jvst_op_arg ireg;
			struct jvst_op_instr *instr;
			struct jvst_ir_stmt *counter;

			counter = arg->u.count.counter;
			assert(counter != NULL);
			assert(counter->type == JVST_IR_STMT_COUNTER);

			return arg_slot(counter->u.counter.frame_off);
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

			return arg_const(v);
		}

	// SPLIT(i, reg):
	// splits execution using split 'i' (data attached to current
	// proc), returns number of valid returns in reg
	case JVST_IR_EXPR_SPLIT:
		{
			struct jvst_op_instr *instr;
			struct jvst_op_arg ireg;
			struct jvst_ir_stmt *splitlist;
			int64_t split_ind;

			ireg = arg_new_slot(opasm);
			instr = op_instr_new(JVST_OP_SPLIT);

			splitlist = arg->u.split.split_list;
			assert(splitlist != NULL);
			assert(splitlist->type == JVST_IR_STMT_SPLITLIST);

			split_ind = proc_add_split(opasm, instr, splitlist);

			instr->args[0] = arg_const(split_ind);
			instr->args[1] = ireg;

			emit_instr(opasm, instr);

			return ireg;
		}

	case JVST_IR_EXPR_SLOT:
		return arg_slot(arg->u.slot.ind);

	case JVST_IR_EXPR_ITEMP:
	case JVST_IR_EXPR_FTEMP:
		return arg_slot(opasm->currproc->temp_off + arg->u.temp.ind);

	case JVST_IR_EXPR_MATCH:
		return emit_match(opasm, arg);

	case JVST_IR_EXPR_INT:
	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_BCOUNT:
		fprintf(stderr, "%s:%d (%s) expression %s not yet implemented\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(arg->type));
		abort();

	case JVST_IR_EXPR_BTEST:
	case JVST_IR_EXPR_BTESTALL:
	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTONE:
	case JVST_IR_EXPR_ISTOK:
	case JVST_IR_EXPR_ISINT:
	case JVST_IR_EXPR_MULTIPLE_OF:
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
			__FILE__, __LINE__, __func__, jvst_ir_expr_type_name(arg->type));
		abort();

	case JVST_IR_EXPR_SEQ:
		fprintf(stderr, "%s:%d (%s) expression %s is invalid while assembling\n",
			__FILE__, __LINE__, __func__, jvst_ir_expr_type_name(arg->type));
		abort();

	}

	fprintf(stderr, "%s:%d (%s) unknown expression type %d\n",
			__FILE__, __LINE__, __func__,
			arg->type);
	abort();
}

static enum jvst_vm_br_cond
cmp_br_type(enum jvst_ir_expr_type type)
{
	switch (type) {
	case JVST_IR_EXPR_NE: return JVST_VM_BR_NE;
	case JVST_IR_EXPR_LT: return JVST_VM_BR_LT;
	case JVST_IR_EXPR_LE: return JVST_VM_BR_LE;
	case JVST_IR_EXPR_EQ: return JVST_VM_BR_EQ;
	case JVST_IR_EXPR_GE: return JVST_VM_BR_GE;
	case JVST_IR_EXPR_GT: return JVST_VM_BR_GT;

	case JVST_IR_EXPR_NONE:
	case JVST_IR_EXPR_ISTOK:
	case JVST_IR_EXPR_ISINT:
	case JVST_IR_EXPR_MULTIPLE_OF:
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
			__FILE__, __LINE__, __func__, jvst_ir_expr_type_name(type));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown IR expression %d\n",
		__FILE__, __LINE__, __func__, type);
	abort();
}

#if 0
static void
cmp_type(enum jvst_ir_expr_type type, enum jvst_vm_op *iopp, enum jvst_vm_op *fopp)
{
	switch (type) {
	case JVST_IR_EXPR_NE:
		*iopp = JVST_OP_INEQ; *fopp = JVST_OP_FNEQ;
		return;

	case JVST_IR_EXPR_LT:
		*iopp = JVST_OP_ILT; *fopp = JVST_OP_FLT;
		return;

	case JVST_IR_EXPR_LE:
		*iopp = JVST_OP_ILE; *fopp = JVST_OP_FLE;
		return;

	case JVST_IR_EXPR_EQ:
		*iopp = JVST_OP_IEQ; *fopp = JVST_OP_FEQ;
		return;

	case JVST_IR_EXPR_GE:
		*iopp = JVST_OP_IGE; *fopp = JVST_OP_FGE;
		return;

	case JVST_IR_EXPR_GT:
		*iopp = JVST_OP_IGT; *fopp = JVST_OP_FGT;
		return;

	case JVST_IR_EXPR_NONE:
	case JVST_IR_EXPR_ISTOK:
	case JVST_IR_EXPR_ISINT:
	case JVST_IR_EXPR_MULTIPLE_OF:
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
			__FILE__, __LINE__, __func__, jvst_ir_expr_type_name(type));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown IR expression %d\n",
		__FILE__, __LINE__, __func__, type);
	abort();
}
#endif /* 0 */

static enum jvst_vm_br_cond
emit_cmp(struct op_assembler *opasm, struct jvst_ir_expr *expr)
{
	struct jvst_op_arg a0,a1;
	enum jvst_vm_br_cond brc;
	int t0, t1;
	enum jvst_vm_op cmp;

	brc = cmp_br_type(expr->type);

	t0 = ir_expr_type(expr->u.cmp.left->type);
	t1 = ir_expr_type(expr->u.cmp.right->type);

	if (t0 == ARG_SLOT) {
		t0 = t1;
		if (t0 == ARG_SLOT) {
			t0 = t1 = ARG_INT;
		}
	}

	a0 = emit_op_arg(opasm, expr->u.cmp.left);
	a1 = emit_op_arg(opasm, expr->u.cmp.right);

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

	if (t0 == ARG_INT) {
		cmp = JVST_OP_ICMP;
	} else if (t0 == ARG_FLOAT) {
		cmp = JVST_OP_FCMP;
	} else {
		fprintf(stderr, "%s:%d (%s) only ARG_INT and ARG_FLOAT are supported (type is %d)\n",
			__FILE__, __LINE__, __func__, t0);
		abort();
	}

	emit_cond(opasm, cmp, a0, a1);
	return brc;
}

static enum jvst_vm_br_cond
op_assemble_cond(struct op_assembler *opasm, struct jvst_ir_expr *cond)
{
	switch (cond->type) {
	case JVST_IR_EXPR_NONE:
		fprintf(stderr, "%s:%d (%s) invalid NONE expression\n",
			__FILE__, __LINE__, __func__);
		abort();

	case JVST_IR_EXPR_ISTOK:
		emit_cond(opasm, JVST_OP_ICMP,
			arg_special(JVST_VM_ARG_TT), arg_tt(cond->u.istok.tok_type));
		return JVST_VM_BR_EQ;

	case JVST_IR_EXPR_ISINT:
		emit_cond(opasm, JVST_OP_FINT,
			arg_special(JVST_VM_ARG_TNUM), arg_none());
		return JVST_VM_BR_NE;

	case JVST_IR_EXPR_MULTIPLE_OF:
		{
			struct jvst_op_arg a,b;
			int64_t fidx;
			double div;

			div = cond->u.multiple_of.divisor;

			if (ceil(div) == div && div < MAX_CONST_VALUE) {
				b = arg_const((int64_t)div);
			} else {
				b = emit_float_arg(opasm, div);
			}
			a = emit_op_arg(opasm, cond->u.multiple_of.arg);
			emit_cond(opasm, JVST_OP_FINT, a,b);
		}
		return JVST_VM_BR_NE;

	case JVST_IR_EXPR_NE:
	case JVST_IR_EXPR_LT:
	case JVST_IR_EXPR_LE:
	case JVST_IR_EXPR_EQ:
	case JVST_IR_EXPR_GE:
	case JVST_IR_EXPR_GT:
		return emit_cmp(opasm, cond);

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
			struct jvst_op_arg iarg0, ireg1, slot, icmp;
			struct jvst_op_instr *instr;
			enum jvst_vm_br_cond brc;

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
				iarg0 = arg_new_slot(opasm);
				instr = op_instr_new(JVST_OP_ILOAD);
				instr->args[0] = iarg0;
				instr->args[1] = arg_const(cidx);
				emit_instr(opasm, instr);
			}

			// emit slot load
			ireg1 = arg_new_slot(opasm);
			instr = op_instr_new(JVST_OP_MOVE);
			instr->args[0] = ireg1;
			instr->args[1] = arg_slot(bv->u.bitvec.frame_off);
			emit_instr(opasm, instr);

			// emit AND
			instr = op_instr_new(JVST_OP_BAND);
			instr->args[0] = ireg1;
			instr->args[1] = iarg0;
			emit_instr(opasm, instr);

			// emit test
			//
			switch (cond->type) {
			case JVST_IR_EXPR_BTESTANY:
				// emit_cond(opasm, JVST_OP_INEQ, ireg1, arg_const(0));
				icmp = arg_const(0);
				brc = JVST_VM_BR_NE;
				// emit_cond(opasm, JVST_OP_ICMP, ireg1, arg_const(0));
				// return JVST_VM_BR_NE;
				break;

			case JVST_IR_EXPR_BTEST:
			case JVST_IR_EXPR_BTESTALL:
				icmp = iarg0;
				brc = JVST_VM_BR_EQ;
				// emit_cond(opasm, JVST_OP_IEQ, ireg1, iarg0);
				// emit_cond(opasm, JVST_OP_ICMP, ireg1, iarg0);
				// return JVST_VM_BR_EQ;
				break;

			default:
				assert( !"unreachable" );
			}

			emit_cond(opasm, JVST_OP_ICMP, ireg1, icmp);
			return brc;
		}

	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_BTESTONE:
		fprintf(stderr, "%s:%d (%s) expression %s not yet supported\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(cond->type));
		abort();

	case JVST_IR_EXPR_AND:
	case JVST_IR_EXPR_OR:
	case JVST_IR_EXPR_NOT:
		fprintf(stderr, "%s:%d (%s) expression %s is invalid while assembling opcodes\n",
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

static struct jvst_op_arg
emit_match(struct op_assembler *opasm, struct jvst_ir_expr *expr)
{
	struct jvst_op_instr *instr;
	struct jvst_op_arg ireg;
	size_t dfa;

	// XXX - allocate DFA table, replacing mcases with appropriate
	//       integer results

	assert(expr->type == JVST_IR_EXPR_MATCH);

	dfa = proc_add_dfa(opasm, expr->u.match.dfa);
	// assert(dfa == expr->u.match.ind);

	instr = op_instr_new(JVST_OP_MATCH);
	instr->args[0] = arg_const(dfa);
	instr->args[1] = arg_none();

	emit_instr(opasm, instr);

	return arg_special(JVST_VM_ARG_M);
}

static enum jvst_vm_br_cond
cmp_negate(enum jvst_vm_br_cond brc)
{
	switch (brc) {
	case JVST_VM_BR_NEVER: return JVST_VM_BR_ALWAYS;
	case JVST_VM_BR_LT: return JVST_VM_BR_GE;
	case JVST_VM_BR_LE: return JVST_VM_BR_GT;
	case JVST_VM_BR_EQ: return JVST_VM_BR_NE;
	case JVST_VM_BR_GE: return JVST_VM_BR_LT;
	case JVST_VM_BR_GT: return JVST_VM_BR_LE;
	case JVST_VM_BR_NE: return JVST_VM_BR_EQ;
	case JVST_VM_BR_ALWAYS: return JVST_VM_BR_NEVER;
	default:
		fprintf(stderr, "%s:%d (%s) unknown branch condition 0x%02x\n",
			__FILE__, __LINE__, __func__, (unsigned int)brc);
	}
}

static void
op_assemble_cbranch(struct op_assembler *opasm, struct jvst_ir_stmt *stmt)
{
	struct jvst_op_instr *instr;
	enum jvst_vm_br_cond brc;
	struct jvst_ir_stmt *dest;

	/* emit condition */
	brc = op_assemble_cond(opasm, stmt->u.cbranch.cond);

	if (stmt->next == NULL) {
		goto emit_two_branches;
	}

	if (stmt->u.cbranch.br_false == stmt->next) {
		instr = op_instr_new(JVST_OP_JMP);
		instr->args[0] = arg_const(brc);
		asm_addr_fixup_add_dest(opasm->fixups, instr, &instr->args[1], stmt->u.cbranch.br_true);
		emit_instr(opasm, instr);
		return;
	}

	if (stmt->u.cbranch.br_true == stmt->next) {
		brc = cmp_negate(brc);
		instr = op_instr_new(JVST_OP_JMP);
		instr->args[0] = arg_const(brc);
		asm_addr_fixup_add_dest(opasm->fixups, instr, &instr->args[1], stmt->u.cbranch.br_false);
		emit_instr(opasm, instr);
		return;
	}

emit_two_branches:
	instr = op_instr_new(JVST_OP_JMP);
	instr->args[0] = arg_const(brc);
	asm_addr_fixup_add_dest(opasm->fixups, instr, &instr->args[1], stmt->u.cbranch.br_true);
	emit_instr(opasm, instr);

	// emit second branch
	instr = op_instr_new(JVST_OP_JMP);
	instr->args[0] = arg_const(JVST_VM_BR_ALWAYS);
	asm_addr_fixup_add_dest(opasm->fixups, instr, &instr->args[1], stmt->u.cbranch.br_false);
	emit_instr(opasm, instr);
}

static void
op_assemble(struct op_assembler *opasm, struct jvst_ir_stmt *stmt)
{
	struct jvst_op_instr *instr;
	const char *label;

	switch (stmt->type) {
	case JVST_IR_STMT_NOP:
		return;

	case JVST_IR_STMT_TOKEN:
		emit_instr(opasm, op_instr_new(JVST_OP_TOKEN));
		return;

	case JVST_IR_STMT_UNTOKEN:
		{
			instr = op_instr_new(JVST_OP_TOKEN);
			instr->args[1] = arg_const(-1);
			instr->args[0] = arg_none();
			emit_instr(opasm, instr);
		}
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
			instr->args[0] = arg_slot(counter->u.counter.frame_off);
			instr->args[1] = arg_const(1);
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
			instr->args[0] = arg_slot(bv->u.bitvec.frame_off);
			instr->args[1] = arg_const(stmt->u.bitop.bit);
			emit_instr(opasm, instr);
		}
		return;

	case JVST_IR_STMT_SPLITVEC:
		{
			struct jvst_ir_stmt *bv, *splitlist, *frames;
			int64_t split_ind;

			bv = stmt->u.splitvec.bitvec;
			assert(bv != NULL);
			assert(bv->type == JVST_IR_STMT_BITVECTOR);

			splitlist = stmt->u.splitvec.split_list;
			assert(splitlist != NULL);
			assert(splitlist->type == JVST_IR_STMT_SPLITLIST);

			instr = op_instr_new(JVST_OP_SPLITV);
			split_ind = proc_add_split(opasm, instr, splitlist);

			instr->args[0] = arg_const(split_ind);
			instr->args[1] = arg_slot(bv->u.bitvec.frame_off);

			emit_instr(opasm, instr);

		}
		return;

	case JVST_IR_STMT_BLOCK:
		opasm->label_block = stmt;
		return;

	case JVST_IR_STMT_BRANCH:
		instr = op_instr_new(JVST_OP_JMP);
		instr->args[0] = arg_const(JVST_VM_BR_ALWAYS);
		asm_addr_fixup_add_dest(opasm->fixups, instr, &instr->args[1], stmt->u.branch);
		emit_instr(opasm, instr);
		return;

	case JVST_IR_STMT_CBRANCH:
		op_assemble_cbranch(opasm, stmt);
		return;

	case JVST_IR_STMT_VALID:
	case JVST_IR_STMT_INVALID:
		{
			int ecode = 0;

			if (stmt->type == JVST_IR_STMT_INVALID) {
				ecode = stmt->u.invalid.code;
			}

			instr = op_instr_new(JVST_OP_RETURN);
			instr->args[0] = arg_const(ecode);
			emit_instr(opasm, instr);
		}
		return;

	case JVST_IR_STMT_MOVE:
		{
			struct jvst_ir_expr *dst, *src;
			src = stmt->u.move.src;
			dst = stmt->u.move.dst;

			if (src->type == JVST_IR_EXPR_NUM) {
				int64_t fidx;

				assert(dst->type == JVST_IR_EXPR_FTEMP || dst->type == JVST_IR_EXPR_SLOT);

				fidx = proc_add_float(opasm, src->u.vnum);
				instr = op_instr_new(JVST_OP_FLOAD);
				instr->args[0] = emit_op_arg(opasm, dst);
				instr->args[1] = arg_const(fidx);
				emit_instr(opasm, instr);
				return;
			}

			instr = op_instr_new(JVST_OP_MOVE);

			switch (dst->type) {
			case JVST_IR_EXPR_SLOT:
			case JVST_IR_EXPR_ITEMP:
			case JVST_IR_EXPR_FTEMP:
				instr->args[0] = emit_op_arg(opasm, dst);
				break;

			default:
				fprintf(stderr, "%s:%d (%s) expect MOVE destination to be a slot, not %s\n",
						__FILE__, __LINE__, __func__, jvst_ir_expr_type_name(stmt->u.move.dst->type));
				abort();
			}

			instr->args[1] = emit_op_arg(opasm, src);
			emit_instr(opasm, instr);
		}
		return;

	case JVST_IR_STMT_CALL:
		{
			instr = op_instr_new(JVST_OP_CALL);
			assert(stmt->u.call.frame != NULL);

			instr->args[0] = arg_const(stmt->u.call.frame->u.frame.frame_ind);
			asm_addr_fixup_add_dest(opasm->fixups, instr, &instr->args[0], stmt->u.call.frame);
			emit_instr(opasm, instr);
		}
		return;

	case JVST_IR_STMT_BCLEAR:
	case JVST_IR_STMT_DECR:
		fprintf(stderr, "%s:%d (%s) IR statement %s not yet implemented\n",
			__FILE__, __LINE__, __func__, jvst_ir_stmt_type_name(stmt->type));
		abort();

	case JVST_IR_STMT_MATCH:
	case JVST_IR_STMT_BREAK:
	case JVST_IR_STMT_LOOP:
	case JVST_IR_STMT_SEQ:
	case JVST_IR_STMT_IF:
	case JVST_IR_STMT_FRAME:
	case JVST_IR_STMT_CALL_ID:

	case JVST_IR_STMT_COUNTER:
	case JVST_IR_STMT_MATCHER:
	case JVST_IR_STMT_BITVECTOR:
	case JVST_IR_STMT_SPLITLIST:
	case JVST_IR_STMT_PROGRAM:
		fprintf(stderr, "%s:%d (%s) should not encounter IR statement %s in op assembly\n",
			__FILE__, __LINE__, __func__, jvst_ir_stmt_type_name(stmt->type));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown IR statement %d\n",
		__FILE__, __LINE__, __func__, stmt->type);
	abort();
}

struct jvst_op_program *
jvst_op_assemble(struct jvst_ir_stmt *ir)
{
	struct op_assembler opasm = { 0 };
	struct asm_addr_fixup_list fixups = { 0 };
	struct jvst_ir_stmt *fr;
	size_t i;

	assert(ir != NULL);
	assert(ir->type == JVST_IR_STMT_PROGRAM);

	opasm.ir     = ir;
	opasm.prog   = op_prog_new(NULL);
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
jvst_op_debug(struct jvst_op_program *prog)
{
	jvst_op_print(stderr, prog);
}

void
jvst_op_print(FILE *f, struct jvst_op_program *prog)
{
	size_t i;
	// FIXME: gross hack
	char buf[65536] = {0}; // 64K

	jvst_op_dump(prog, buf, sizeof buf);
	for (i=0; i < 72; i++) {
		fprintf(f, "-");
	}
	fprintf(f, "\n");
	fprintf(f, "%s\n", buf);
}

struct dfa_lookup {
	const struct fsm_state *st;
	size_t ind;
};

static int
dfa_cmp(const void *pa, const void *pb)
{
	const struct dfa_lookup *a = pa, *b = pb;

	if (a->st == b->st) {
		return 0;
	}

	return a->st < b->st ? -1 : 1;
}

static size_t
fsm_state_ind(size_t n, struct dfa_lookup *tbl, const struct fsm_state *st)
{
	struct dfa_lookup *found, key = { .st = st };

	found = bsearch(&key, tbl, n, sizeof tbl[0], dfa_cmp);
	assert(found != NULL);
	return found->ind;
}

struct dfa_builder {
	struct jvst_vm_dfa *dfa;
	struct dfa_lookup *lookup;

	size_t last_state;
	size_t state_off;
	size_t edge_off;
	size_t end_off;
};

static int
collect_and_number_states(const struct fsm *fsm, const struct fsm_state *st, void *opaque)
{
	struct dfa_builder *b = opaque;
	size_t off = b->state_off++;

	if (fsm_isend(fsm,st)) {
		struct jvst_ir_mcase *mc;
		size_t endoff;

		mc = fsm_getopaque((struct fsm *)fsm, st);
		endoff = b->end_off++;

		b->dfa->endstates[2*endoff+0] = off;
		b->dfa->endstates[2*endoff+1] = mc->which;
	}

	b->lookup[off].st  = st;
	b->lookup[off].ind = off;

	return 1;
}

static int
collect_transitions(const struct fsm *fsm,
	const struct fsm_state *st0, unsigned int lbl, const struct fsm_state *st1,
	void *opaque)
{
	struct dfa_builder *b = opaque;
	int *s0p, *s1p;
	size_t i0, i1;
	size_t edge_ind;

	(void)fsm;

	i0 = fsm_state_ind(b->dfa->nstates, b->lookup, st0);
	i1 = fsm_state_ind(b->dfa->nstates, b->lookup, st1);

	assert(i0 >= 0 && i0 < b->dfa->nstates);
	assert(i1 >= 0 && i1 < b->dfa->nstates);

	edge_ind = b->edge_off++;
	if (i0 != b->last_state) {
		size_t j;
		assert(i0 > b->last_state);
		for (j=b->last_state; j < i0; j++) {
			b->dfa->offs[j+1] = edge_ind;
		}
		b->last_state = i0;
	}

	// XXX - check for overflow
	b->dfa->transitions[2*edge_ind+0] = (int)lbl;
	b->dfa->transitions[2*edge_ind+1] = (int)i1;

	return 1;
}

void
jvst_op_build_vm_dfa(struct fsm *fsm, struct jvst_vm_dfa *dfa)
{
	struct dfa_builder b = { 0 };
	size_t i, nstates, nedges, nends, nelts;
	int *elts;
	struct dfa_lookup *tbl;

	nstates = fsm_countstates(fsm);
	nedges  = fsm_countedges(fsm);
	nends   = fsm_count(fsm, fsm_isend);

	(void) jvst_vm_dfa_init(dfa, nstates, nedges, nends);
	tbl = xmalloc(nstates * sizeof *tbl);

	for (i=0; i < nstates+1; i++) {
		dfa->offs[i] = 0;
	}

	b.dfa = dfa;
	b.lookup = tbl;

	fsm_walk_states(fsm, &b, collect_and_number_states);
	qsort(tbl, nstates, sizeof tbl[0], dfa_cmp);
	fsm_walk_edges(fsm,  &b, collect_transitions);
	for (; b.last_state < nstates; b.last_state++) {
		b.dfa->offs[b.last_state+1] = b.edge_off;
	}

	free(tbl);
}

void
jvst_vm_dfa_debug(struct jvst_vm_dfa *dfa)
{
	size_t i,n;

	n = dfa->nstates;
	fprintf(stderr, "%zu states, starting, and count\n", n);
	for (i=0; i < n; i++) {
		fprintf(stderr, "%5zu %5d %5d\n", i, dfa->offs[i], dfa->offs[i+1] - dfa->offs[i]);
	}

	fprintf(stderr, "\n%d transitions\n", dfa->offs[n]);
	assert(dfa->offs[n] == (int)dfa->nedges);
	for (i=0; i < n; i++) {
		size_t j, ne, off;
		off = dfa->offs[i];

		ne = dfa->offs[i+1] - off;
		fprintf(stderr, "state %zu, %zu transitions\n", i, ne);
		for (j=0; j < ne; j++) {
			fprintf(stderr, "%5zu %5d %5d\n", i,
				dfa->transitions[2*(off+j) + 0],
				dfa->transitions[2*(off+j) + 1]);
		}
	}

	n = dfa->nends;
	fprintf(stderr, "\n%zu end states\n", n);
	for (i=0; i < n; i++) {
		fprintf(stderr, "%5d %5d\n", dfa->endstates[2*i+0], dfa->endstates[2*i+1]);
	}
}

struct op_encoder {
	size_t len;
	size_t cap;
	uint32_t *code;
};

static void
encoder_init(struct op_encoder *enc)
{
	enc->len = 0;
	enc->cap = 8;
	enc->code = xmalloc(enc->cap * sizeof enc->code[0]);
}

static uint32_t
encoder_emit(struct op_encoder *enc, uint32_t code)
{
	size_t ind;
	if (enc->len >= enc->cap) {
		enc->code = xenlargevec(enc->code, &enc->cap, 1, sizeof enc->code[0]);
	}

	ind = enc->len++;
	assert(ind < enc->cap);

	enc->code[ind] = code;

	return ind;
}

static uint16_t
encode_arg(struct jvst_op_arg arg)
{
	switch (arg.type) {
	case JVST_VM_ARG_TT:
		return VMREG(JVST_VM_TT);
	case JVST_VM_ARG_TNUM:
		return VMREG(JVST_VM_TNUM);
	case JVST_VM_ARG_TLEN:
		return VMREG(JVST_VM_TLEN);
	case JVST_VM_ARG_M:
		return VMREG(JVST_VM_M);

	case JVST_VM_ARG_SLOT:
	case JVST_VM_ARG_POOL:
		return VMSLOT(arg.u.index);

	case JVST_VM_ARG_TOKTYPE:
	case JVST_VM_ARG_CONST:
		return VMLIT(arg.u.index);

	case JVST_VM_ARG_NONE:
		return 0;

	case JVST_VM_ARG_INSTR:
	case JVST_VM_ARG_LABEL:
	case JVST_VM_ARG_CALL:
		fprintf(stderr, "%s:%d (%s) unexpected opcode argument type %d\n",
				__FILE__, __LINE__, __func__, arg.type);
		abort();

	default:
		fprintf(stderr, "%s:%d (%s) unknown opcode argument type %d\n",
				__FILE__, __LINE__, __func__, arg.type);
		abort();
	}
}

static void
encode_pass1(struct op_encoder *enc, struct jvst_op_instr *first)
{
	struct jvst_op_instr *instr;

	for (instr = first; instr != NULL; instr = instr->next) {
		uint32_t cp;
		uint16_t a,b;

		switch (instr->op) {
		case JVST_OP_JMP:
			{
				assert(instr->args[0].type == JVST_VM_ARG_CONST);
				assert(instr->args[1].type == JVST_VM_ARG_INSTR);
				assert(instr->args[1].u.dest != NULL);

				cp = encoder_emit(enc, VMBR(instr->op, instr->args[0].u.index, 0));
				instr->code_off = cp;
			}
			break;

		case JVST_OP_CALL:
			{
				assert(instr->args[0].type == JVST_VM_ARG_CALL);
				assert(instr->args[0].u.dest != NULL);

				cp = encoder_emit(enc, VMBR(instr->op, JVST_VM_BR_ALWAYS, 0));
				instr->code_off = cp;
			}
			break;

		case JVST_OP_TOKEN:
		case JVST_OP_CONSUME:

		case JVST_OP_NOP:
		case JVST_OP_PROC:
		case JVST_OP_ICMP:
		case JVST_OP_FCMP:
		case JVST_OP_FINT:
		case JVST_OP_SPLIT:
		case JVST_OP_SPLITV:
		case JVST_OP_MATCH:
		case JVST_OP_FLOAD:
		case JVST_OP_ILOAD:
		case JVST_OP_MOVE:
		case JVST_OP_INCR:
		case JVST_OP_BSET:
		case JVST_OP_BAND:
		case JVST_OP_RETURN:
			a = encode_arg(instr->args[0]);
			b = encode_arg(instr->args[1]);

			cp = encoder_emit(enc, VMOP(instr->op, a, b));
			instr->code_off = cp;
			break;

		default:
			fprintf(stderr, "%s:%d (%s) unknown opcode statement %d\n",
					__FILE__, __LINE__, __func__, instr->op);
			abort();
		}
	}
}

static void
encode_pass2(struct op_encoder *enc, struct jvst_op_instr *first)
{
	struct jvst_op_instr *instr;

	(void)enc;
	for (instr = first; instr != NULL; instr = instr->next) {
		uint32_t cp;
		uint32_t br;
		enum jvst_vm_br_cond brc;
		int64_t delta;

		switch (instr->op) {
		case JVST_OP_JMP:
			assert(instr->args[0].type == JVST_VM_ARG_CONST);
			assert(instr->args[1].type == JVST_VM_ARG_INSTR ||
				instr->args[1].type == JVST_VM_ARG_CALL);
			assert(instr->args[1].u.dest != NULL);

			cp = instr->code_off;
			brc = instr->args[0].u.index;
			br = instr->args[1].u.dest->code_off;

			delta = (int64_t)br - (int64_t)cp;
			if (delta < JVST_VM_BARG_MIN || delta > JVST_VM_BARG_MAX) {
				// XXX - add in support for branch to a register
				// destination
				fprintf(stderr, "%s:%d (%s) unsupported branch distance %zd\n",
					__FILE__, __LINE__, __func__, delta);
				abort();
			}

			enc->code[cp] = VMBR(instr->op, brc, (long)delta);
			break;

		case JVST_OP_CALL:
			assert(instr->args[0].type == JVST_VM_ARG_INSTR ||
				instr->args[0].type == JVST_VM_ARG_CALL);
			assert(instr->args[0].u.dest != NULL);

			cp = instr->code_off;
			brc = JVST_VM_BR_ALWAYS;
			br = instr->args[0].u.proc->code_off;

			delta = (int64_t)br - (int64_t)cp;
			if (delta < JVST_VM_BARG_MIN || delta > JVST_VM_BARG_MAX) {
				// XXX - add in support for branch to a register
				// destination
				fprintf(stderr, "%s:%d (%s) unsupported branch distance %zd\n",
					__FILE__, __LINE__, __func__, delta);
				abort();
			}

			enc->code[cp] = VMBR(instr->op, brc, (long)delta);
			break;


		default:
			/* nop */
			break;
		}
	}
}

struct jvst_vm_program *
jvst_op_encode(struct jvst_op_program *prog)
{
	struct jvst_vm_program *vmprog;
	struct jvst_op_proc *proc;

	struct op_encoder enc = { 0 };

	vmprog = xmalloc(sizeof *vmprog);
	memset(vmprog, 0, sizeof *vmprog);

	// encode floating point constants
	if (prog->nfloat > 0) {
		size_t nb = prog->nfloat * sizeof vmprog->fdata[0];
		vmprog->fdata = xmalloc(nb);
		vmprog->nfloat = prog->nfloat;
		memcpy(vmprog->fdata, prog->fdata, nb);
	}

	// encode large integer constants
	if (prog->nconst > 0) {
		size_t nb = prog->nconst * sizeof vmprog->cdata[0];
		vmprog->cdata = xmalloc(nb);
		vmprog->nconst = prog->nconst;
		memcpy(vmprog->cdata, prog->cdata, nb);
	}

	// encode dfa tables
	if (prog->ndfa > 0) {
		size_t i,n,nb;

		n = prog->ndfa;
		nb = n * sizeof vmprog->dfas[0];

		vmprog->dfas = xmalloc(nb);
		vmprog->ndfa = n;

		for (i=0; i < n; i++) {
			jvst_vm_dfa_copy(&vmprog->dfas[i], &prog->dfas[i]);
		}
	}

	encoder_init(&enc);

	// first pass, encode data, set branch dests to zero
	for (proc = prog->procs; proc != NULL; proc = proc->next) {
		struct jvst_op_instr *instr;
		uint16_t a,b;

		proc->code_off = encoder_emit(&enc,
			VMOP(JVST_OP_PROC, VMLIT(proc->nslots), VMLIT(0)));

		assert(proc->ilist != NULL);
		encode_pass1(&enc, proc->ilist);
	}

	// second pass, set branch dests and calls to real location
	for (proc = prog->procs; proc != NULL; proc = proc->next) {
		assert(proc->ilist != NULL);
		encode_pass2(&enc, proc->ilist);
	}

	// encode splits last, after proc indexes have been generated
	if (prog->nsplit > 0) {
		size_t i, nentries, nsdata, off;
		uint32_t *sdata;

		nentries = prog->splitoff[prog->nsplit-1];
		nsdata = prog->nsplit + 1 + nentries;

		sdata = xmalloc(nsdata * sizeof *sdata);

		sdata[0] = 0;
		for (i=0; i < prog->nsplit; i++) {
			sdata[i+1] = prog->splitoff[i];
		}

		off = prog->nsplit+1;
		for (i=0; i < nentries; i++) {
			assert(prog->splits[i] != NULL);
			sdata[off+i] = prog->splits[i]->code_off;
		}

		vmprog->nsplit = prog->nsplit;
		vmprog->sdata  = sdata;
	}

	vmprog->ncode = enc.len;
	vmprog->code  = enc.code;

	return vmprog;
}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
