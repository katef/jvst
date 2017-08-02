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

#define MAX_CONST_SIZE ((size_t)(1UL << 16)-1)


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
		sbuf_snprintf(buf,"%%I%" PRId64, arg.index);
		return;

	case JVST_VM_ARG_FLOAT:
		sbuf_snprintf(buf,"%%F%" PRId64, arg.index);
		return;

	case JVST_VM_ARG_TOKTYPE:
		sbuf_snprintf(buf,"$%s", evt2name(arg.index));
		return;

	case JVST_VM_ARG_CONST:
		sbuf_snprintf(buf,"$%" PRId64, arg.index);
		return;

	case JVST_VM_ARG_SLOT:
		sbuf_snprintf(buf,"SLOT(%" PRId64 ")", arg.index);
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

	case JVST_OP_FRAME:
		sbuf_snprintf(buf, "FRAME ");
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
		sbuf_snprintf(buf, "%s :%s",
			jvst_op_name(instr->op),
			(instr->u.branch.dest != NULL)
				? instr->u.branch.dest->label
				: instr->u.branch.label);
		break;

	case JVST_OP_CALL:
		sbuf_snprintf(buf, "%s %zu",
			jvst_op_name(instr->op),
			(instr->u.call.dest != NULL)
			 	? instr->u.call.dest->proc_index
				: instr->u.call.proc_index);
		break;

	case JVST_OP_SPLIT:
	case JVST_OP_SPLITV:
	case JVST_OP_MATCH:
	case JVST_OP_INCR:
		sbuf_snprintf(buf, "%s ", jvst_op_name(instr->op));
		op_arg_dump(buf, instr->u.args[0]);
		break;

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
			instr->u.ecode);
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

	for (i=0; i < proc->nconst; i++) {
		sbuf_indent(buf, indent+2);
		sbuf_snprintf(buf, "CONST(%zu)\t%" PRId64 "\t%" PRIu64 "\n",
			i, proc->cdata[i], (uint64_t) proc->cdata[i]);
	}

	if (proc->nfloat > 0) {
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

	// surely we can provide more data than this?
	for (i=0; i < proc->nsplit; i++) {
		struct jvst_op_proc *spl;
		int j;

		sbuf_indent(buf, indent+2);
		sbuf_snprintf(buf, "SPLIT(%zu)\n", i);
		sbuf_indent(buf, indent+7);
		for (j=0, spl=proc->splits[i]; spl != NULL; spl = spl->split_next) {
			sbuf_snprintf(buf, " %zu", spl->proc_index);
			if (++j > 10) {
				sbuf_snprintf(buf, "\n");
				sbuf_indent(buf, indent+7);
			}
		}
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
	case JVST_OP_FRAME:     return "FRAME";
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

	size_t nlbl;
	size_t ntmp;
};

static struct jvst_op_arg
arg_none(void)
{
	struct jvst_op_arg arg = {
		.type = JVST_VM_ARG_NONE,
		.index = 0,
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
	case JVST_VM_ARG_SLOT:
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
		.index = v,
	};

	return arg;
}

static struct jvst_op_arg
arg_tt(enum SJP_EVENT tt)
{
	struct jvst_op_arg arg = {
		.type  = JVST_VM_ARG_TOKTYPE,
		.index = tt,
	};

	return arg;
}

static struct jvst_op_arg
arg_itmp(struct op_assembler *opasm)
{
	struct jvst_op_arg arg = {
		.type  = JVST_VM_ARG_INT,
		.index = opasm->ntmp++,
	};

	return arg;
}

static struct jvst_op_arg
arg_ftmp(struct op_assembler *opasm)
{
	struct jvst_op_arg arg = {
		.type  = JVST_VM_ARG_FLOAT,
		.index = opasm->ntmp++,
	};

	return arg;
}

static struct jvst_op_arg
arg_slot(size_t ind)
{
	struct jvst_op_arg arg = {
		.type  = JVST_VM_ARG_SLOT,
		.index = ind,
	};

	return arg;
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

// XXX - replace dumb label lookup with something better?
static struct jvst_op_block *
block_lookup(struct op_assembler *opasm, const char *name)
{
	struct jvst_op_block *b;

	assert(opasm->currproc != NULL);
	for(b = opasm->currproc->blocks; b != NULL; b = b->next) {
		if (strcmp(b->label,name) == 0) {
			return b;
		}
	}

	return NULL;
}

static struct jvst_op_block *
add_block(struct op_assembler *opasm, struct jvst_op_instr *ilist, const char *fmt, ...)
{
	va_list args;
	struct jvst_op_block *block;

	assert(opasm != NULL);
	assert(fmt != NULL);

	va_start(args, fmt);
	block = op_block_new(ilist, fmt, args);
	va_end(args);

	assert(block_lookup(opasm, block->label) == NULL);

	*opasm->bpp = block;
	opasm->bpp = &block->next;

	return block;
}

static struct jvst_op_block *
add_valid_block(struct op_assembler *opasm)
{
	struct jvst_op_instr *instr;
	struct jvst_op_block *block;

	assert(opasm != NULL);
	if (block = block_lookup(opasm, "valid"), block != NULL) {
		return block;
	}

	instr = op_instr_new(JVST_OP_VALID);
	return add_block(opasm, instr, "valid");
}

static struct jvst_op_block *
add_invalid_block(struct op_assembler *opasm, enum jvst_invalid_code ecode)
{
	struct jvst_op_instr *instr;
	struct jvst_op_block *block;
	char label[sizeof block->label];

	assert(opasm != NULL);
	snprintf(label, sizeof label, "invalid_%d", ecode);
	if (block = block_lookup(opasm, label), block != NULL) {
		return block;
	}

	instr = op_instr_new(JVST_OP_INVALID);
	instr->u.ecode = ecode;
	return add_block(opasm, instr, "invalid_%d", ecode);
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
	case JVST_OP_FRAME:
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
		fprintf(stderr, "op %s is not a branch\n", jvst_op_name(op));
		abort();

	}

	fprintf(stderr, "unknown op %d\n", op);
	abort();

emit_branch:
	instr = op_instr_new(op);
	instr->u.branch.label = block->label;
	instr->u.branch.dest = block;

	*opasm->ipp = instr;
	opasm->ipp = &instr->next;

	return instr;
}

static struct jvst_op_instr *
emit_cond(struct op_assembler *opasm, enum jvst_vm_op op, 
	struct jvst_op_arg a0, struct jvst_op_arg a1,
	struct jvst_op_block *btrue, struct jvst_op_block *bfalse)
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
	case JVST_OP_FRAME:
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
		fprintf(stderr, "op %s is not a conditional\n", jvst_op_name(op));
		abort();

	}

	fprintf(stderr, "unknown op %d\n", op);
	abort();

emit_cond:
	instr = op_instr_new(op);
	instr->u.args[0] = a0;
	instr->u.args[1] = a1;
	*opasm->ipp = instr;
	opasm->ipp = &instr->next;

	emit_branch(opasm, JVST_OP_CBT, btrue);
	emit_branch(opasm, JVST_OP_BR, bfalse);

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
	struct jvst_op_instr **ipp;
	struct jvst_op_block *b, **bpp, *ordered, *opp;

	// Scan through branches in each block.  If the branch forms a chain (points
	// to another branch), follow the chain to the end and replace the original
	// branch with the final destination
	//
	// The original branch can be conditional, but the chain must be
	// unconditional.
	for (b=proc->blocks; b != NULL; b = b->next) {
		struct jvst_op_instr *instr;

		for(instr = b->ilist; instr != NULL; instr = instr->next) {
			struct jvst_op_block *dst;

			switch (instr->op) {
			case JVST_OP_BR:
			case JVST_OP_CBT:
			case JVST_OP_CBF:
				instr->u.branch.dest  = branch_chain_dest(instr->u.branch.dest);
				instr->u.branch.label = instr->u.branch.dest->label;
				break;

			default:
				/* nop */
				break;
			}
		}
	}

	// Mark all blocks as unvisited.  Then mark reachable blocks.
	// Then eliminate unreachable blocks.
	for (b=proc->blocks; b != NULL; b = b->next) {
		b->work = 0;
	}
	mark_reachable(proc->blocks);

	for (bpp=&proc->blocks; *bpp != NULL; ) {
		if ((*bpp)->work) {
			bpp = &(*bpp)->next;
			continue;
		}

		// unreachable, remove block
		*bpp = (*bpp)->next;
	}

	proc->blocks = resort_blocks(proc->blocks);

	// Combine blocks into a single instruction list...
	ipp = &proc->ilist;
	for (b=proc->blocks; b != NULL; b = b->next) {
		struct jvst_op_instr *i0, *i1;

		assert(b->ilast == NULL);

		i0 = b->ilist;
		i1 = instr_last(i0);

		assert(i0 != NULL);
		i0->label = b->label;

		b->ilast = i1;
		*ipp = i0;
		ipp = &i1->next;
	}

	// Simplify the instruction list
	// 1. Any branches to the next instruction are removed
	for (ipp = &proc->ilist; *ipp != NULL; ) {
		switch ((*ipp)->op) {
		case JVST_OP_BR:
		case JVST_OP_CBT:
		case JVST_OP_CBF:
			assert((*ipp)->u.branch.dest != NULL);
			if ((*ipp)->u.branch.dest->ilist == (*ipp)->next) {
				// branch to the next instruction... remove
				*ipp = (*ipp)->next;
				continue;
			}
			break;

		default:
			/* nop */
			break;
		}

		ipp = &(*ipp)->next;
	}
}

static void
op_assemble_seq(struct op_assembler *opasm, struct jvst_ir_stmt *stmt_list)
{
	struct jvst_ir_stmt *stmt;

	for (stmt = stmt_list; stmt != NULL; stmt = stmt->next) {
		op_assemble(opasm, stmt);
	}
}

struct jvst_op_proc *
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

	frame_opasm.currproc = proc;
	frame_opasm.bpp = &proc->blocks;

	block = add_block(&frame_opasm, NULL, "entry");
	frame_opasm.ipp = &block->ilist;

	// XXX - allocate storage for floats, dfas, splits
	op_assemble_seq(&frame_opasm, top->u.frame.stmts);

	op_finish_proc(proc);

	opasm->procpp = frame_opasm.procpp;

	return proc;
}

static struct jvst_op_block LOOP_BLOCK;

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
	*opasm->bpp = block;
	opasm->bpp = &block->next;

	block_opasm = *opasm;
	block_opasm.ipp = &block->ilist;

	// XXX - allocate storage for floats, dfas, splits
	op_assemble_seq(&block_opasm, top);

	if (bnext == &LOOP_BLOCK) {
		emit_branch(&block_opasm, JVST_OP_BR, block);
	} else if (bnext != NULL) {
		emit_branch(&block_opasm, JVST_OP_BR, bnext);
	}

	opasm->nlbl = block_opasm.nlbl;
	opasm->ntmp = block_opasm.ntmp;
	opasm->bpp  = block_opasm.bpp;
	opasm->procpp = block_opasm.procpp;

	return block;
}

enum { ARG_NONE, ARG_BOOL, ARG_FLOAT, ARG_INT };

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
		return ARG_INT;

	case JVST_VM_ARG_TNUM:
	case JVST_VM_ARG_FLOAT:
		return ARG_FLOAT;
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
			*opasm->ipp = instr;
			opasm->ipp = &instr->next;
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
			*opasm->ipp = instr;
			opasm->ipp = &instr->next;
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

			*opasm->ipp = instr;
			opasm->ipp = &instr->next;
			return ireg;
		}

	case JVST_IR_EXPR_BOOL:
	case JVST_IR_EXPR_BCOUNT:
	case JVST_IR_EXPR_BTEST:
	case JVST_IR_EXPR_BTESTALL:
	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTONE:
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
	case JVST_IR_EXPR_SPLIT:
		fprintf(stderr, "%s:%d (%s) expression %s is not an argument\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(arg->type));
		abort();
	}
}

static struct jvst_op_instr *
emit_cmp(struct op_assembler *opasm, struct jvst_ir_expr *expr, 
	struct jvst_op_arg a0, struct jvst_op_arg a1,
	struct jvst_op_block *btrue, struct jvst_op_block *bfalse)
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
	case JVST_IR_EXPR_SIZE:
	case JVST_IR_EXPR_TOK_TYPE:
	case JVST_IR_EXPR_TOK_NUM:
	case JVST_IR_EXPR_TOK_COMPLETE:
	case JVST_IR_EXPR_TOK_LEN:
	case JVST_IR_EXPR_COUNT:
	case JVST_IR_EXPR_BCOUNT:
	case JVST_IR_EXPR_SPLIT:
		fprintf(stderr, "%s:%d (%s) IR expression %s is not a comparison\n",
			__FILE__, __LINE__, __func__, jvst_ir_expr_type_name(expr->type));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown IR expression %d\n",
		__FILE__, __LINE__, __func__, expr->type);
	abort();

emit:
	return emit_cond(opasm, op, a0, a1, btrue, bfalse);
}

static void
op_assemble_cond(struct op_assembler *opasm, struct jvst_ir_expr *cond,
	struct jvst_op_block *btrue, struct jvst_op_block *bfalse)
{
	switch (cond->type) {
	case JVST_IR_EXPR_NONE:
		fprintf(stderr, "%s:%d (%s) invalid NONE expression\n",
			__FILE__, __LINE__, __func__);
		abort();

	case JVST_IR_EXPR_ISTOK:
		emit_cond(opasm, JVST_OP_IEQ,
			arg_special(JVST_VM_ARG_TT), arg_tt(cond->u.istok.tok_type),
			btrue, bfalse);
		return;

	case JVST_IR_EXPR_ISINT:
		emit_cond(opasm, JVST_OP_FINT,
			arg_special(JVST_VM_ARG_TNUM), arg_none(),
			btrue, bfalse);
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
			emit_cmp(opasm, cond, a0,a1, btrue, bfalse);
		}
		return;

	case JVST_IR_EXPR_BTESTALL:
		{
			struct jvst_ir_stmt *bv;
			uint64_t mask;
			size_t nb;
			int64_t cidx;
			struct jvst_op_arg ireg0, ireg1, slot;
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

			if (nb == 64) {
				mask = ~(uint64_t)0;
			} else {
				mask = (((uint64_t)1) << nb) - 1;
			}

			// emit mask constant and load
			cidx = proc_add_uconst(opasm, mask);
			ireg0 = arg_itmp(opasm);
			instr = op_instr_new(JVST_OP_ILOAD);
			instr->u.args[0] = ireg0;
			instr->u.args[1] = arg_const(cidx);
			*opasm->ipp = instr;
			opasm->ipp = &instr->next;

			// emit slot load
			ireg1 = arg_itmp(opasm);
			instr = op_instr_new(JVST_OP_ILOAD);
			instr->u.args[0] = ireg1;
			instr->u.args[1] = arg_slot(bv->u.bitvec.frame_off);
			*opasm->ipp = instr;
			opasm->ipp = &instr->next;

			// emit AND
			instr = op_instr_new(JVST_OP_BAND);
			instr->u.args[0] = ireg1;
			instr->u.args[1] = ireg0;
			*opasm->ipp = instr;
			opasm->ipp = &instr->next;

			// emit test
			emit_cond(opasm, JVST_OP_IEQ, ireg1, ireg0, btrue, bfalse);
		}
		return;

	case JVST_IR_EXPR_BOOL:

	case JVST_IR_EXPR_NUM:
	case JVST_IR_EXPR_SIZE:

	case JVST_IR_EXPR_TOK_TYPE:
	case JVST_IR_EXPR_TOK_NUM:
	case JVST_IR_EXPR_TOK_COMPLETE:
	case JVST_IR_EXPR_TOK_LEN:

	case JVST_IR_EXPR_COUNT:
	case JVST_IR_EXPR_BCOUNT:
	case JVST_IR_EXPR_BTEST:
	case JVST_IR_EXPR_BTESTANY:
	case JVST_IR_EXPR_BTESTONE:

	case JVST_IR_EXPR_AND:
	case JVST_IR_EXPR_OR:
	case JVST_IR_EXPR_NOT:
	case JVST_IR_EXPR_SPLIT:
		fprintf(stderr, "%s:%d (%s) expression %s not yet supported\n",
				__FILE__, __LINE__, __func__,
				jvst_ir_expr_type_name(cond->type));
		abort();
	}

	fprintf(stderr, "%s:%d (%s) unknown expression type %d\n",
		__FILE__, __LINE__, __func__, cond->type);
	abort();
}

static void
op_assemble_if(struct op_assembler *opasm, struct jvst_ir_stmt *stmt)
{
	struct jvst_op_block *btrue, *bfalse, **condpp, *bjoin;

	// block for rejoining execution...
	bjoin = op_assemble_block(opasm, NULL, "rejoin", NULL);
	bjoin->ilist = op_instr_new(JVST_OP_NOP);

	// assemble true/false blocks
	btrue  = op_assemble_block(opasm, stmt->u.if_.br_true, NULL, bjoin);
	bfalse = op_assemble_block(opasm, stmt->u.if_.br_false, NULL, bjoin);

	// XXX - how to handle statements after if, eg in a SEQ block?
	//       does this case come up?

	// assemble conditional...
	op_assemble_cond(opasm, stmt->u.if_.cond, btrue, bfalse);

	opasm->ipp = &bjoin->ilist;
}

static void
op_assemble_loop(struct op_assembler *opasm, struct jvst_ir_stmt *loop)
{
	struct jvst_op_block *loop_block, *loop_end;
	struct jvst_op_instr **ipp, *nop;

	loop_end = op_assemble_block(opasm, NULL, "loop_end", NULL);
	loop->data = loop_end;
	/*
	// to be overwritten!
	nop = op_instr_new(JVST_OP_NOP);
	loop_end = add_block(opasm, nop, "loop_end%s", &loop_block->label[4]);
	*/

	loop_block = op_assemble_block(opasm, loop->u.loop.stmts, "loop", &LOOP_BLOCK);
	snprintf(loop_block->label, sizeof loop_block->label, "loop_%s", &loop_end->label[9]);

	emit_branch(opasm, JVST_OP_BR, loop_block);

	/*
	for(ipp = &loop_block->ilist; *ipp != NULL; ipp = &(*ipp)->next) {
		continue;
	}

	*ipp = op_instr_new(JVST_OP_BR);
	(*ipp)->u.branch.label = loop_block->label;
	(*ipp)->u.branch.dest = loop_block;
	*/

	opasm->ipp = &loop_end->ilist;
	loop->data = NULL;
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
				*opasm->ipp = instr;
				opasm->ipp = &instr->next;
			}
		}
		return;

	case JVST_IR_STMT_TOKEN:
		instr = op_instr_new(JVST_OP_TOKEN);
		*opasm->ipp = instr;
		opasm->ipp = &instr->next;
		return;

	case JVST_IR_STMT_CONSUME:
		instr = op_instr_new(JVST_OP_CONSUME);
		*opasm->ipp = instr;
		opasm->ipp = &instr->next;
		return;

	case JVST_IR_STMT_VALID:
		block = add_valid_block(opasm);
		emit_branch(opasm, JVST_OP_BR, block);
		return;

	case JVST_IR_STMT_INVALID:
		block = add_invalid_block(opasm, stmt->u.invalid.code);
		emit_branch(opasm, JVST_OP_BR, block);
		return;

	case JVST_IR_STMT_IF:
		op_assemble_if(opasm, stmt);
		return;

	case JVST_IR_STMT_SEQ:
		op_assemble_seq(opasm, stmt->u.stmt_list);
		return;

	case JVST_IR_STMT_LOOP:
		op_assemble_loop(opasm, stmt);
		return;

	case JVST_IR_STMT_BREAK:
		{
			struct jvst_ir_stmt *loop;
			struct jvst_op_block *loop_block;

			loop = stmt->u.break_.loop;
			assert(loop != NULL);
			assert(loop->data != NULL);

			loop_block = loop->data;
			emit_branch(opasm, JVST_OP_BR, loop_block);
		}
		return;

	case JVST_IR_STMT_MATCH:
		op_assemble_match(opasm, stmt);
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
			*opasm->ipp = instr;
			opasm->ipp = &instr->next;
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
			*opasm->ipp = instr;
			opasm->ipp = &instr->next;
		}
		return;

	case JVST_IR_STMT_COUNTER:
	case JVST_IR_STMT_MATCHER:
	case JVST_IR_STMT_BITVECTOR:
	case JVST_IR_STMT_BCLEAR:
	case JVST_IR_STMT_DECR:
	case JVST_IR_STMT_SPLITVEC:
		fprintf(stderr, "%s:%d (%s) IR statement %s not yet implemented\n",
			__FILE__, __LINE__, __func__, jvst_ir_stmt_type_name(stmt->type));
		abort();
	}

	fprintf(stderr, "unknown IR statement %d\n", stmt->type);
	abort();
}

struct jvst_op_program *
jvst_op_assemble(struct jvst_ir_stmt *stmt)
{
	struct op_assembler opasm = { 0 };
	struct jvst_op_proc *proc;
	size_t i;

	opasm.prog = op_prog_new(NULL);
	opasm.procpp = &opasm.prog->procs;

	op_assemble(&opasm, stmt);

	// Number procedures
	for(i=0, proc = opasm.prog->procs; proc != NULL; i++, proc=proc->next) {
		proc->proc_index = i;
	}

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
