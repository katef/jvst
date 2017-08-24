#include "validate_vm.h"

#include <assert.h>
#include <ctype.h>
#include <inttypes.h>
#include <limits.h>
#include <math.h>
#include <stdarg.h>
#include <stdio.h>
#include <stddef.h>
#include <string.h>

#include "xalloc.h"
#include "sjp_testing.h"
#include "validate_ir.h"  // XXX - this is for INVALID codes, which should be moved!

#define DEBUG_OPCODES 1		// displays opcodes and the current frame's stack

// XXX - replace with something better at some point
//       (maybe a longjmp to an error handler?)
#define PANIC(vm, ecode, errmsg) \
	do { fprintf(stderr, "PANIC (code=%d): %s\n", (ecode), (errmsg)); \
		jvst_vm_dumpstate(vm); abort(); } while(0)

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
	case JVST_OP_MOVE: 	return "MOVE";
	case JVST_OP_INCR:      return "INCR";
	case JVST_OP_BSET:      return "BSET";
	case JVST_OP_BAND:      return "BAND";
	case JVST_OP_VALID:     return "VALID";
	case JVST_OP_INVALID:   return "INVALID";
	}

	fprintf(stderr, "Unknown OP %d\n", op);
	abort();
}

static const char *
argname(uint16_t arg, char buf[static 16]) {
	if (jvst_vm_arg_isslot(arg)) {
		int slot = jvst_vm_arg_toslot(arg);
		switch (slot) {
		// case JVST_VM_PPC: 	snprintf(buf, 16, "%%PPC"); break;
		// case JVST_VM_PFP:	snprintf(buf, 16, "%%PFP"); break;
		case JVST_VM_TT:	snprintf(buf, 16, "%%TT"); break;
		case JVST_VM_TNUM:	snprintf(buf, 16, "%%TN"); break;
		case JVST_VM_TLEN:	snprintf(buf, 16, "%%TL"); break;
		case JVST_VM_M:		snprintf(buf, 16, "%%M"); break;
		default:
			snprintf(buf, 16, "%%R%d", slot - JVST_VM_NUMREG);
			break;
		}
	} else {
		snprintf(buf, 16, "$%d", jvst_vm_arg_tolit(arg));
	}
	return buf;
}

static void
vm_dump_opcode(struct sbuf *buf, uint32_t pc, uint32_t c, int indent)
{
	const char *opname;
	uint32_t barg;
	long br;
	enum jvst_vm_op op;
	uint16_t a,b;

	sbuf_indent(buf, indent);

	op = jvst_vm_decode_op(c);

	opname = jvst_op_name(op);
	switch (op) {
	case JVST_OP_BR:
	case JVST_OP_CBT:
	case JVST_OP_CBF:
	case JVST_OP_CALL:
		barg = jvst_vm_decode_barg(c);
		br = jvst_vm_tobarg(barg);
		sbuf_snprintf(buf, "%05" PRIu32 "\t0x%08" PRIx32 "\t%s\t%-5ld\n",
			pc, c, opname, br);
		break;

	default:
		{
			char astr[16], bstr[16];
			a = jvst_vm_decode_arg0(c);
			b = jvst_vm_decode_arg1(c);
			sbuf_snprintf(buf,
				"%05" PRIu32 "\t0x%08" PRIx32 "\t%s\t%s, %s\n",
				pc, c, opname, argname(a,astr), argname(b,bstr));
		}
	}
}

static void
vm_dump(struct sbuf *buf, const struct jvst_vm_program *prog, int indent)
{
	size_t i,n;

	sbuf_indent(buf, indent);
	sbuf_snprintf(buf, ".DATA\n");

	if (prog->nfloat > 0) {
		for (i=0; i < prog->nfloat; i++) {
			sbuf_indent(buf, indent+2);
			sbuf_snprintf(buf, "FLOAT(%zu)\t%g\n", i, prog->fdata[i]);
		}

		sbuf_snprintf(buf, "\n");
	}

	if (prog->nconst > 0) {
		for (i=0; i < prog->nconst; i++) {
			sbuf_indent(buf, indent+2);
			sbuf_snprintf(buf, "CONST(%zu)\t%" PRId64 "\t%" PRIu64 "\n",
					i, prog->cdata[i], (uint64_t) prog->cdata[i]);
		}

		sbuf_snprintf(buf, "\n");
	}

	if (prog->nsplit > 0) {
		for (i=0; i < prog->nsplit; i++) {
			uint32_t si,si0,si1,c;
			si0 = prog->sdata[i];
			si1 = prog->sdata[i+1];

			sbuf_indent(buf, indent+2);
			sbuf_snprintf(buf, "SPLIT(%" PRIu32 ")\t", i);
			for (c=0, si = si0; si < si1; c++, si++) {
				uint32_t off,pinstr;

				off = prog->sdata[si];
				sbuf_snprintf(buf, " %" PRIu32, off);

				if (c >= 6 && i < prog->nsplit-1) {
					sbuf_snprintf(buf, "\n");
					sbuf_indent(buf, indent+2);
					sbuf_snprintf(buf, "\t\t");
					c = 0;
				}
			}

			sbuf_snprintf(buf, "\n");
		}

		sbuf_snprintf(buf, "\n");
	}

	if (prog->ndfa > 0) {
		for (i=0; i < prog->ndfa; i++) {
			sbuf_indent(buf, indent+2);
			sbuf_snprintf(buf, "DFA(%zu)\n", i);
		}

		sbuf_snprintf(buf, "\n");
	}

	sbuf_indent(buf, indent);
	sbuf_snprintf(buf, ".CODE\n");

	n = prog->ncode;
	for (i=0; i < n; i++) {
		uint32_t c;
		c = prog->code[i];

		vm_dump_opcode(buf, i, c, indent);
	}
}

int
jvst_vm_program_dump(const struct jvst_vm_program *prog, char *buf, size_t nb)
{
	struct sbuf b = {
	    .buf = buf, .cap = nb, .len = 0, .np = 0,
	};

	vm_dump(&b, prog, 0);
	sbuf_snprintf(&b, "\n");
	return (b.len < b.cap) ? 0 : -1;
}

void
jvst_vm_program_print(FILE *f, const struct jvst_vm_program *prog)
{
	size_t i;
	// FIXME: gross hack
	char buf[65536] = {0}; // 64K

	jvst_vm_program_dump(prog, buf, sizeof buf);
	for (i=0; i < 72; i++) {
		fprintf(f, "-");
	}
	fprintf(f, "\n");
	fprintf(f, "%s\n", buf);
}

void
jvst_vm_program_debug(const struct jvst_vm_program *prog)
{
	jvst_vm_program_print(stderr,prog);
}

size_t
jvst_vm_dfa_init(struct jvst_vm_dfa *dfa, size_t nstates, size_t nedges, size_t nends)
{
	size_t nelts;
	int *elts;

	nelts = (nstates+1) + 2*nedges + 2*nends;
	elts = xmalloc(nelts * sizeof *elts);

	dfa->nstates = nstates;
	dfa->nedges  = nedges;
	dfa->nends   = nends;

	dfa->offs = elts;
	dfa->transitions = dfa->offs + (nstates+1);
	dfa->endstates = dfa->transitions  + 2*nedges;

	return nelts;
}

void
jvst_vm_dfa_copy(struct jvst_vm_dfa *dst, const struct jvst_vm_dfa *src)
{
	(void) jvst_vm_dfa_init(dst, src->nstates, src->nedges, src->nends);

	memcpy(dst->offs, src->offs, (src->nstates+1)*sizeof src->offs[0]);
	memcpy(dst->transitions, src->transitions, 2*src->nedges * sizeof src->transitions[0]);
	memcpy(dst->endstates, src->endstates, 2*src->nends * sizeof src->endstates[0]);
}

void
jvst_vm_dfa_finalize(struct jvst_vm_dfa *dfa)
{
	static struct jvst_vm_dfa zero = { 0 };
	// arrays within the dfa were allocated as a single chunk, so
	// this frees them
	free(dfa->offs);
	*dfa = zero;
}

static int
twoint_binary_search(const int *restrict list, int i0, int i1, int key)
{
	fprintf(stderr, "binary search in range [%d,%d] for %d (%c)\n",
		i0,i1,key,isprint(key) ? key : ' ');
	while (i0 <= i1) {
		int mid,mkey;
		mid = (i0 + i1)/2;
		mkey = list[2*mid];
		fprintf(stderr, "  i0 = %d, i1 = %d, mid = %d, mkey = %d (%c)\n",
			i0,i1,mid,mkey, isprint(mkey) ? mkey : ' ');
		if (mkey == key) {
			return mid;
		}

		if (mkey < key) {
			i0 = mid+1;
		} else {
			i1 = mid-1;
		}
		fprintf(stderr, "  new: i0 = %d, i1 = %d\n", i0,i1);
	}

	return -1;
}

static int
dfa_find_edge(const struct jvst_vm_dfa *dfa, int i0, int i1, int edge)
{
	int ind;

	// currently a binary search.  would an interpolating search
	// make sense?
	ind = twoint_binary_search(dfa->transitions, i0,i1, edge);

	if (ind < 0) {
		return JVST_VM_DFA_NOMATCH;
	}

	assert(ind >= i0 && ind <= i1);
	return dfa->transitions[2*ind+1];
}

int
jvst_vm_dfa_run(const struct jvst_vm_dfa *dfa, int st0, const char *buf, size_t n)
{
	size_t i;
	int st;

	if (st0 < 0) {
		return st0;
	}

	if ((size_t)st0 >= dfa->nstates) {
		return JVST_VM_DFA_BADSTATE;
	}

	st = st0;
	for (i=0; i < n; i++) {
		int i0,i1,edge;
		edge = (unsigned char)buf[i];
		i0 = dfa->offs[st];
		i1 = dfa->offs[st+1]-1;
		st = dfa_find_edge(dfa, i0,i1, edge);
		if (st < 0) {
			break;
		}
	}

	return st;
}

bool
jvst_vm_dfa_endstate(const struct jvst_vm_dfa *dfa, int st1, int *datap)
{
	int ind;

	if (st1 < 0 || (size_t)st1 >= dfa->nstates) {
		return st1;
	}

	ind = twoint_binary_search(dfa->endstates, 0, dfa->nends-1, st1);
	if (ind < 0) {
		return false;
	}

	assert(ind >= 0 && (size_t)ind < dfa->nends);
	if (datap != NULL) {
		*datap = dfa->endstates[2*ind+1];
	}

	return true;
}

void
jvst_vm_program_free(struct jvst_vm_program *prog)
{
	size_t i;
	assert(prog != NULL);
	free(prog->fdata);
	free(prog->cdata);
	free(prog->sdata);

	for (i=0; i < prog->ndfa; i++) {
		jvst_vm_dfa_finalize(&prog->dfas[i]);
	}
	free(prog->dfas);

	free(prog->code);
	free(prog);
}

enum { VM_DEFAULT_STACK = 1024  };   // 8 bytes per stack element, so default to 16K stack
enum { VM_STACK_BUFFER = 64     };   // in resize, minimum amount of extra space
enum { VM_DEFAULT_MAXSPLIT = 16 };

void
jvst_vm_init_defaults(struct jvst_vm *vm, struct jvst_vm_program *prog)
{
	static struct jvst_vm zero = { 0 };

	*vm = zero;

	vm->prog = prog;

	vm->maxstack = VM_DEFAULT_STACK;
	vm->stack = xmalloc(vm->maxstack * sizeof vm->stack[0]);

	vm->nsplit = 0;
	vm->maxsplit = VM_DEFAULT_MAXSPLIT;
	vm->splits = xmalloc(vm->maxsplit * sizeof vm->splits[0]);

	vm->r_flag = 0;
	vm->r_pc = 0;
	vm->r_fp = 0;
	vm->r_sp = 0;

	(void)sjp_parser_init(&vm->parser, &vm->pstack[0], ARRAYLEN(vm->pstack), &vm->pbuf[0],
			      ARRAYLEN(vm->pbuf));
}

void
jvst_vm_finalize(struct jvst_vm *vm)
{
	size_t i;

	static struct jvst_vm zero = { 0 };
	free(vm->stack);

	for (i=0; i < vm->nsplit; i++) {
		jvst_vm_finalize(&vm->splits[i]);
	}
	free(vm->splits);

	*vm = zero;
}

static void
vm_dumpregs(struct sbuf *buf, const struct jvst_vm *vm)
{
	sbuf_snprintf(buf, "PC=%" PRIu32 " FP=%" PRIu32 " SP=%" PRIu32 " FLAG=%" PRId64 "\n",
		vm->r_pc, vm->r_fp, vm->r_sp, vm->r_flag);
}

static void
vm_dumpstack(FILE *f, const struct jvst_vm *vm)
{
	uint32_t fp,sp,i;

	fp = vm->r_fp;
	sp = vm->r_sp;
	if (fp > 0) {
		fprintf(f, "[%5d] %" PRId64 "\t(PPC)\n", fp-2, vm->stack[fp-2].i);
		fprintf(f, "[%5d] %" PRId64 "\t(PFP)\n", fp-1, vm->stack[fp-1].i);
		fprintf(f, "---\n");
	}
	for (i=fp; i < sp; i++) {
		if (i == fp+1) {
			fprintf(f, "[%5d] %f\n", i, vm->stack[i].f);
		} else {
			fprintf(f, "[%5d] %" PRId64 "\n", i, vm->stack[i].i);
		}
	}
	fprintf(f, "\n");
}

void
jvst_vm_dumpstate(struct jvst_vm *vm)
{
	uint32_t i, fp,sp;
	char cbuf[128];
	struct sbuf buf = { .buf = cbuf, .cap = sizeof cbuf, .len = 0, .np = 0 };

	fprintf(stderr, "--- VM state ---\n");
	jvst_vm_program_debug(vm->prog);
	vm_dumpregs(&buf, vm);
	fprintf(stderr, "\n%s\n", buf.buf);
	
	fprintf(stderr, "stack frame:\n");

	vm_dumpstack(stderr,vm);
}

static void
resize_stack(struct jvst_vm *vm, size_t newlen)
{
	size_t newmax;

	if (newlen < vm->maxstack) {
		return;
	}

	newmax = vm->maxstack;
	if (newmax < VM_DEFAULT_STACK) {
		newmax = VM_DEFAULT_STACK;
	} else if (newmax < 16384) {
		newmax *= 2;
	} else {
		newmax += newmax/4;
	}

	if (newmax < newlen) {
		newmax = newlen + VM_STACK_BUFFER;
	}

	vm->stack = xrealloc(vm->stack, newmax * sizeof vm->stack[0]);
	vm->maxstack = newmax;
}

static inline union jvst_vm_stackval *
vm_slotptr(struct jvst_vm *vm, uint32_t fp, uint32_t arg)
{
	int slot;

	assert(jvst_vm_arg_isslot(arg));
	slot = jvst_vm_arg_toslot(arg);
	if (fp+slot > vm->r_sp) {
		// XXX - better error code!
		PANIC(vm, -1, "slot exceeded stack");
	}

	return &vm->stack[fp+slot];
}

static inline uint64_t
vm_uval(struct jvst_vm *vm, uint32_t fp, uint32_t arg)
{
	int slot;

	if (jvst_vm_arg_islit(arg)) {
		return jvst_vm_arg_tolit(arg);
	}

	return vm_slotptr(vm,fp,arg)->u;
}

static inline int64_t
vm_ival(struct jvst_vm *vm, uint32_t fp, uint32_t arg)
{
	int slot;

	if (jvst_vm_arg_islit(arg)) {
		return jvst_vm_arg_tolit(arg);
	}

	return vm_slotptr(vm,fp,arg)->i;
}

static inline double *
vm_fvalptr(struct jvst_vm *vm, uint32_t fp, uint32_t arg)
{
	int slot;

	if (jvst_vm_arg_islit(arg)) {
		// XXX - better error code!
		PANIC(vm, -1, "literal arg to float compare");
	}

	return &vm_slotptr(vm,fp,arg)->f;
}

static inline int
iopdiff(struct jvst_vm *vm, uint32_t fp, uint32_t opcode)
{
	uint32_t a,b;
	int64_t va,vb;

	a = jvst_vm_decode_arg0(opcode);
	b = jvst_vm_decode_arg1(opcode);

	va = vm_ival(vm, fp, a);
	vb = vm_ival(vm, fp, b);

	return va-vb;
}

static inline int
fopdiff(struct jvst_vm *vm, uint32_t fp, uint32_t opcode)
{
	uint32_t a,b;
	double va,vb;

	a = jvst_vm_decode_arg0(opcode);
	b = jvst_vm_decode_arg1(opcode);

	va = vm_fvalptr(vm, fp, a)[0];
	vb = vm_fvalptr(vm, fp, b)[0];

	va -= vb;
	if (va > 0) {
		return 1;
	} else if (va < 0) {
		return -1;
	} else {
		return 0;
	}
}

static inline int
has_partial_token(struct jvst_vm *vm)
{
	return (sjp_parser_state(&vm->parser) == SJP_PARSER_PARTIAL);
}

static int
next_token(struct jvst_vm *vm)
{
	uint32_t fp = vm->r_fp;
	int ret;

	assert(vm->r_sp >= fp + JVST_VM_NUMREG);

	if (!has_partial_token(vm)) {
		vm->stack[fp+JVST_VM_TT  ].i = 0;
		vm->stack[fp+JVST_VM_TNUM].f = 0.0;
		vm->stack[fp+JVST_VM_TLEN].i = 0;
	}

	ret = sjp_parser_next(&vm->parser, &vm->evt);
	if (SJP_ERROR(ret)) {
		return ret;
	}

	vm->consumed = 0;

	vm->stack[fp+JVST_VM_TT].i = vm->evt.type;
	vm->stack[fp+JVST_VM_TLEN].i += vm->evt.n;
	if (vm->evt.type == SJP_NUMBER) {
		vm->stack[fp+JVST_VM_TNUM].f = vm->evt.d;
	}

	return ret;
}

static int
consume_partial_token(struct jvst_vm *vm)
{
	int ret;

retry:
	ret = sjp_parser_next(&vm->parser, &vm->evt);
	if (ret == SJP_PARTIAL) {
		goto retry;
	}

	return ret;
}

static int
consume_current_value(struct jvst_vm *vm)
{
	int ret;

	if (vm->consumed) {
		return SJP_OK;
	}

	if (has_partial_token(vm)) {
		ret = consume_partial_token(vm);

		if (ret != SJP_OK) {
			return ret;
		}
	}

	for (;;) {
		if (vm->nobj == 0 && vm->narr == 0) {
			vm->consumed = 1;
			return SJP_OK;
		}

		for(;;) {
			ret = sjp_parser_next(&vm->parser, &vm->evt);
			if (ret != SJP_PARTIAL) {
				break;
			}
		}

		if (ret != SJP_OK) {
			return ret;
		}

		switch (vm->evt.type) {
		case SJP_NONE:
		case SJP_NULL:
		case SJP_TRUE:
		case SJP_FALSE:
		case SJP_STRING:
		case SJP_NUMBER: break;

		case SJP_OBJECT_BEG: vm->nobj++; break;
		case SJP_OBJECT_END: vm->nobj--; break;
		case SJP_ARRAY_BEG:  vm->narr++; break; 
		case SJP_ARRAY_END:  vm->narr--; break;
		}
	}
}

static void
vm_dumpevt(struct sbuf *buf, const struct jvst_vm *vm)
{
	size_t n;
	sbuf_snprintf(buf, "type=%s n=%zu text=\"",
		evt2name(vm->evt.type),
		vm->evt.n);
	n = buf->cap - buf->len;
	if (vm->evt.n+2 < n) {
		memcpy(&buf->buf[buf->len], vm->evt.text, vm->evt.n);
		buf->len += vm->evt.n;
		buf->buf[buf->len++] = '"';
		buf->buf[buf->len++] = 0;
	} else {
		const char trailing[] = "...\"";
		size_t nc = n - sizeof trailing;
		memcpy(&buf->buf[buf->len], vm->evt.text, nc);
		buf->len += nc;
		memcpy(&buf->buf[buf->len], trailing, sizeof trailing);
		buf->len += sizeof trailing;
	}
}

static inline void
debug_op(struct jvst_vm *vm, uint32_t pc, uint32_t opcode)
{
	char cbuf[128];
	struct sbuf buf = { .buf = cbuf, .cap = sizeof(cbuf), .len = 0, .np = 0 };

	vm_dump_opcode(&buf, pc, opcode, 0);
	fprintf(stderr, "INSTR> %s", buf.buf);

	buf.len = 0;
	buf.np = 0;
	vm_dumpevt(&buf, vm);
	fprintf(stderr, "EVT  > %s\n", buf.buf);

	buf.len = 0;
	buf.np = 0;
	vm_dumpregs(&buf, vm);
	fprintf(stderr, "REGS > %s", buf.buf);
	vm_dumpstack(stderr, vm);
}

/* MATCH semantics:
 *
 * Works with the current string token, which may be a partial token.
 * MATCH will complete the token.
 *
 * MATCH will beginning matching against whatever text is present, so
 * it's usually a bug to call MATCH if any of the bits of the string
 * have been consumed.  For example, if the token was originally a
 * partial token and has subsequently been completed, then the initial
 * data is lost and MATCH will start halfway in.
 */
static int
vm_match(struct jvst_vm *vm, const struct jvst_vm_dfa *dfa)
{
	int ret, st, result;

	if (vm->evt.type != SJP_STRING) {
		PANIC(vm, -1, "MATCH called on a non-string token");
	}

	if (vm->consumed) {
		PANIC(vm, -1, "MATCH called on a consumed token");
	}

	ret = SJP_OK;
	st = vm->dfa_st;
	for(;;) {
		st = jvst_vm_dfa_run(dfa, st, vm->evt.text, vm->evt.n);
		if (!has_partial_token(vm)) {
			break;
		}

		ret = sjp_parser_next(&vm->parser, &vm->evt);
		if (SJP_ERROR(ret)) {
			vm->error = ret;
			return JVST_INVALID;
		}

		if (vm->evt.n == 0) {
			break;
		}
	}

	if (ret != SJP_OK) {
		vm->dfa_st = st;
		return ret;
	}

	result = -1;
	if (st == JVST_VM_DFA_NOMATCH || !jvst_vm_dfa_endstate(dfa, st, &result)) {
		result = 0;
	}
	assert(result >= 0);

	// reset state for next MATCH instruction
	vm->dfa_st = 0;
	vm->consumed = 1;

	vm->stack[vm->r_fp + JVST_VM_M].i = result;
	return SJP_OK;
}

#if DEBUG_OPCODES
#  define DEBUG_OP(vm,pc,opcode) debug_op((vm),(pc),(opcode))
#else
#  define DEBUG_OP(vm,pc,opcode) do{}while(0)
#endif /* DEBUG */

#define NEXT do{ vm->r_pc = ++pc; goto loop; } while(0)
#define BRANCH(newpc) do { pc += (newpc); vm->r_pc = pc; goto loop; } while(0)
static enum jvst_result
vm_run(struct jvst_vm *vm)
{
	uint32_t opcode, pc, fp, sp;
	int64_t flag;
	uint32_t *code;
	size_t ncode;

	enum jvst_vm_op op;
	int ret;

	code  = vm->prog->code;
	ncode = vm->prog->ncode;

	pc = vm->r_pc;
	fp = vm->r_fp;
	sp = vm->r_sp;
	flag = vm->r_flag;

	ret = JVST_INVALID;

loop:
	assert(pc >= 0);  // safety in case type is changed

	// bounds check pc
	if (pc > ncode) {
		vm->error = JVST_INVALID_VM_BAD_PC;
		ret = JVST_INVALID;
		goto finish;
	}

	opcode = code[pc];
	op = jvst_vm_decode_op(opcode);
	DEBUG_OP(vm, pc, opcode);
#if 0
	{
		static char buf[256];
		fgets(buf, sizeof buf, stdin);
	}
#endif /* 0 */

	switch (op) {
	case JVST_OP_NOP:
		NEXT;

	case JVST_OP_PROC:
		{
			uint32_t a;
			int i,n,nsl;
			a = jvst_vm_decode_arg0(opcode);
			assert(jvst_vm_arg_islit(a));

			nsl = jvst_vm_arg_tolit(a);
			if (nsl < 0) {
				// XXX - better error messages
				vm->error = JVST_INVALID_VM_INVALID_ARG;
				ret = JVST_INVALID;
				goto finish;
			}

			// allocate extra slots for "registers"
			n = nsl + JVST_VM_NUMREG;

			// setup frame
			fp = sp;

			// allocate stack slots
			resize_stack(vm, sp+n);
			for (i=0; i < n; i++) {
				vm->stack[sp++].u = 0;
			}

			vm->r_fp = fp;
			vm->r_sp = sp;
		}
		NEXT;

	/* integer comparisons */
	case JVST_OP_ILT:
		flag = iopdiff(vm, fp, opcode) < 0;
		NEXT;

	case JVST_OP_ILE:
		flag = iopdiff(vm, fp, opcode) <= 0;
		NEXT;

	case JVST_OP_IEQ:
		flag = iopdiff(vm, fp, opcode) == 0;
		NEXT;

	case JVST_OP_IGE:
		flag = iopdiff(vm, fp, opcode) >= 0;
		NEXT;

	case JVST_OP_IGT:
		flag = iopdiff(vm, fp, opcode) > 0;
		NEXT;

	case JVST_OP_INEQ:
		flag = iopdiff(vm, fp, opcode) != 0;
		NEXT;

	/* floating point comparisons */
	case JVST_OP_FLT:
		flag = fopdiff(vm, fp, opcode) < 0;
		NEXT;

	case JVST_OP_FLE:
		flag = fopdiff(vm, fp, opcode) <= 0;
		NEXT;

	case JVST_OP_FEQ:
		flag = fopdiff(vm, fp, opcode) == 0;
		NEXT;

	case JVST_OP_FGE:
		flag = fopdiff(vm, fp, opcode) >= 0;
		NEXT;

	case JVST_OP_FGT:
		flag = fopdiff(vm, fp, opcode) > 0;
		NEXT;

	case JVST_OP_FNEQ:
		flag = fopdiff(vm, fp, opcode) != 0;
		NEXT;

	case JVST_OP_FINT:
		{
			double v;
			uint32_t arg0;
			int slot;

			arg0 = jvst_vm_decode_arg0(opcode);
			assert(jvst_vm_arg_isslot(arg0));

			v = vm_fvalptr(vm, fp, arg0)[0];
			flag = isfinite(v) && (v == ceil(v));
		}
		NEXT;

	case JVST_OP_CBF:
	case JVST_OP_CBT:
		if (!!flag != (op == JVST_OP_CBT)) {
			NEXT;
		}

		/* fallthrough */

	case JVST_OP_BR:
		{
			uint32_t barg;
			long br;
			barg = jvst_vm_decode_barg(opcode);
			BRANCH(jvst_vm_tobarg(barg));
		}

	case JVST_OP_TOKEN:
		// read entire token, set the various token values
		ret = next_token(vm);
		if (SJP_ERROR(ret)) {
			vm->error = ret;
			ret = JVST_INVALID;
			goto finish;
		}
		if (ret == SJP_MORE && vm->evt.type == SJP_NONE) {
			ret = JVST_MORE;
			goto finish;
		}
		NEXT;

	case JVST_OP_CONSUME:
		{
			int ret;

			if (vm->consumed) {
				ret = next_token(vm);
				if (SJP_ERROR(ret)) {
					vm->error = ret;
					ret = JVST_INVALID;
					goto finish;
				}

				if (ret == SJP_OK) {
					if (vm->evt.type == SJP_OBJECT_BEG) {
						vm ->nobj++;
					} else if (vm->evt.type == SJP_ARRAY_BEG) {
						vm ->narr++;
					}
				}
			}

			ret = consume_current_value(vm);
			if (SJP_ERROR(ret)) {
				vm->error = ret;
				ret = JVST_INVALID;
				goto finish;
			}

			if (ret == SJP_MORE) {
				return ret;
			}
		}
		NEXT;

	case JVST_OP_VALID:
		// if not already eating an object/array, and current
		// value is an OBJECT_BEG or ARRAY_BEG, eat the
		// object/array
		if (vm->nobj == 0 && vm->narr == 0) {
			if (vm->evt.type == SJP_OBJECT_BEG) {
				vm->nobj++;
			} else if (vm->evt.type == SJP_ARRAY_BEG) {
				vm->narr++;
			}
		}

		// consume token, then return to previous frame or, if top of
		// stack, return JVST_VALID
		ret = consume_current_value(vm);
		if (ret == SJP_MORE) {
			ret = JVST_MORE;
			goto finish;
		}
		if (ret != SJP_OK) {
			ret = JVST_INVALID;
			vm->error = ret;	// sjp errors are negative
			goto finish;
		}

		// top of stack!
		if (fp == 0) {
			vm->r_pc = pc = 0;
			ret = JVST_VALID;
			goto finish;
		}

		vm->r_sp = sp = fp-2;
		vm->r_pc = pc = vm->stack[fp-2].u;
		vm->r_fp = fp = vm->stack[fp-1].u;
		NEXT; // pc points to CALL, continue with next instruction

	case JVST_OP_INVALID:
		{
			uint32_t arg0;
			int ecode;

			arg0 = jvst_vm_decode_arg0(opcode);
			assert(jvst_vm_arg_islit(arg0));

			vm->error = vm_ival(vm, fp, arg0);
			assert(vm->error != 0);
			ret = JVST_INVALID;
			goto finish;
		}

	case JVST_OP_MOVE:
		{
			double v;
			uint32_t a0,a1;

			a0 = jvst_vm_decode_arg0(opcode);
			a1 = jvst_vm_decode_arg1(opcode);

			assert(jvst_vm_arg_isslot(a0));

			if (jvst_vm_arg_islit(a1)) {
				int lit = jvst_vm_arg_tolit(a1);
				vm_slotptr(vm,fp,a0)->i = lit;
			} else {
				union jvst_vm_stackval *s0, *s1;
				s0 = vm_slotptr(vm,fp,a0);
				s1 = vm_slotptr(vm,fp,a1);
				memcpy(s0,s1,sizeof(*s0));
			}
		}
		NEXT;

	case JVST_OP_FLOAD:
	case JVST_OP_ILOAD:
		{
			uint32_t a0,a1;
			union jvst_vm_stackval *slot;
			int ind;

			a0 = jvst_vm_decode_arg0(opcode);
			a1 = jvst_vm_decode_arg1(opcode);

			assert(jvst_vm_arg_isslot(a0));
			assert(jvst_vm_arg_islit(a1));
			slot = vm_slotptr(vm, fp, a0);
			ind = jvst_vm_arg_tolit(a1);

			if (op == JVST_OP_FLOAD) {
				if (ind < 0 || (size_t)ind > vm->prog->nfloat) {
					PANIC(vm, -1, "invalid float pool index");
				}

				slot->f = vm->prog->fdata[ind];
			} else {
				if (ind < 0 || (size_t)ind > vm->prog->nconst) {
					PANIC(vm, -1, "invalid const pool index");
				}

				slot->i = vm->prog->cdata[ind];
			}
		}
		NEXT;

	case JVST_OP_INCR:
		{
			uint32_t a0,a1;
			union jvst_vm_stackval *slot;
			int delta;

			a0 = jvst_vm_decode_arg0(opcode);
			a1 = jvst_vm_decode_arg1(opcode);

			assert(jvst_vm_arg_isslot(a0));

			slot = vm_slotptr(vm, fp, a0);
			delta = vm_ival(vm, fp, a1);
			slot->i += delta;
		}
		NEXT;

	case JVST_OP_MATCH:
		{
			uint32_t a0;
			int dfa_ind;
			const struct jvst_vm_dfa *dfa;

			a0 = jvst_vm_decode_arg0(opcode);
			dfa_ind = vm_ival(vm, fp, a0);

			if (dfa_ind < 0 || (size_t)dfa_ind >= vm->prog->ndfa) {
				PANIC(vm, -1, "MATCH called with invalid DFA");
			}

			dfa = &vm->prog->dfas[dfa_ind];
			assert(dfa != NULL);

			ret = vm_match(vm, dfa);
			if (ret != JVST_VALID) {
				goto finish;
			}
		}
		NEXT;

	case JVST_OP_CALL:
		{
			uint32_t barg;
			long br;
			barg = jvst_vm_decode_barg(opcode);
			br = jvst_vm_tobarg(barg);

			assert(pc+br >= 0 && (size_t)(pc+br) < vm->prog->ncode);
			assert(jvst_vm_decode_op(vm->prog->code[pc+br]) == JVST_OP_PROC);

			resize_stack(vm, sp+2);
			vm->stack[sp+0].u = pc;
			vm->stack[sp+1].u = fp;

			sp += 2;
			vm->r_fp = fp;
			vm->r_sp = sp;

			BRANCH(br);
		}

	case JVST_OP_BSET:
		{
			uint32_t a0,a1;
			union jvst_vm_stackval *slot;
			int bit;

			a0 = jvst_vm_decode_arg0(opcode);
			a1 = jvst_vm_decode_arg1(opcode);

			assert(jvst_vm_arg_isslot(a0));

			slot = vm_slotptr(vm, fp, a0);
			bit = vm_ival(vm, fp, a1);

			if (bit < 0 || bit >= 64) {
				PANIC(vm, -1, "BSET called with invalid bit");
			}

			slot->u |= (1<<bit);
		}
		NEXT;

	case JVST_OP_BAND:
		{
			uint32_t a0,a1;
			union jvst_vm_stackval *slot;
			uint64_t mask;

			a0 = jvst_vm_decode_arg0(opcode);
			a1 = jvst_vm_decode_arg1(opcode);

			assert(jvst_vm_arg_isslot(a0));

			slot = vm_slotptr(vm, fp, a0);
			mask = vm_uval(vm, fp, a1);

			slot->u &= mask;
		}
		NEXT;

	case JVST_OP_SPLIT:
	case JVST_OP_SPLITV:
		fprintf(stderr, "%s:%d (%s) op %s not yet implemented\n",
			__FILE__, __LINE__, __func__, jvst_op_name(op));
		abort();
	}

	vm->error = JVST_INVALID_VM_INVALID_OP;
	return JVST_INVALID;

finish:
	vm->r_pc = pc;
	vm->r_fp = fp;
	vm->r_sp = sp;
	vm->r_flag = flag;
	return ret;
}
#undef NEXT
#undef BRANCH
#undef DEBUG_OP

enum jvst_result
jvst_vm_more(struct jvst_vm *vm, char *data, size_t n)
{
	if (vm->error) {
		return JVST_INVALID;
	}

	sjp_parser_more(&vm->parser, data, n);
	return vm_run(vm);
}

enum jvst_result
jvst_vm_close(struct jvst_vm *vm)
{
	int st,ret;

	if (vm->r_pc != 0) {
		char buf[2] = " ";
		// FIXME: this is a dumb hack to deal with numbers The problem is
		// this: if the number is adjacent to the end of the stream, the lexer
		// won't know this until it's closed.  So it returns a SJP_MORE value.
		// This is fine, but we don't deal with it very well.  So, append
		// a trailing space and try to let the validation clean up.  Then
		// close everything...
		//
		if (ret = jvst_vm_more(vm, buf, 1), JVST_IS_INVALID(ret)) {
			return ret;
		}
	}

	ret = sjp_parser_close(&vm->parser);

	if (SJP_ERROR(ret)) {
		vm->error = JVST_INVALID_JSON;
		return JVST_INVALID;
	}

	return (vm->error == 0) ? JVST_VALID : JVST_INVALID;
}



/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
