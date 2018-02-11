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
#include "debug.h"

#define DEBUG_OPCODES (debug & DEBUG_VMOP)	// displays opcodes and the current frame's stack
#define DEBUG_STEP    0				// instruction-by-instruction execution of the VM
#define DEBUG_TOKENS  (debug & DEBUG_VMTOK)	// displays tokens as they're read
#define DEBUG_BSEARCH 0				// debugs DFA binary search
#define DEBUG_SPLITV  0				// debugs how SPLITV sets its result masks

// XXX - replace with something better at some point
//       (maybe a longjmp to an error handler?)
#define PANIC(vm, ecode, errmsg) \
	do { fprintf(stderr, "%s:%d (%s) PANIC (code=%d): %s\n",  \
		__FILE__, __LINE__, __func__, (ecode), (errmsg)); \
		jvst_vm_dumpstate(vm); abort(); } while(0)

#define NOT_YET_IMPLEMENTED(op) do { \
	fprintf(stderr, "%s:%d (%s) op %s not yet implemented\n", \
		__FILE__, __LINE__, __func__, jvst_op_name((op)));  \
	abort(); } while(0)

const char *
jvst_op_name(enum jvst_vm_op op)
{
	switch (op) {
	case JVST_OP_NOP:	return "NOP";
	case JVST_OP_PROC:	return "PROC";
	case JVST_OP_ICMP:      return "ICMP";
	case JVST_OP_FCMP:      return "FCMP";
	case JVST_OP_FINT:      return "FINT";
	case JVST_OP_JMP:       return "JMP";
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
	case JVST_OP_RETURN:    return "RETURN";
	case JVST_OP_UNIQUE:	return "UNIQUE";
	}

	fprintf(stderr, "Unknown OP %d\n", op);
	abort();
}

const char *
jvst_vm_br_cond_name(enum jvst_vm_br_cond brc)
{
	switch (brc) {
	case 0x00: return "NV";
	case 0x01: return "LT";
	case 0x02: return "GT";
	case 0x03: return "NE";
	case 0x04: return "EQ";
	case 0x05: return "LE";
	case 0x06: return "GE";
	case 0x07: return "AL";
	default:
	   fprintf(stderr, "%s:%d (%s) invalid JMP argument 0x%02x\n",
		   __FILE__, __LINE__, __func__, (unsigned int)brc);
	   abort();
	}
}

static const char *
stackname(uint32_t slot, char buf[static 16])
{
	switch (slot) {
	case JVST_VM_TT:
		snprintf(buf, 16, "%%TT");
		break;

	case JVST_VM_TNUM:
		snprintf(buf, 16, "%%TN");
		break;

	case JVST_VM_TLEN:
		snprintf(buf, 16, "%%TL");
		break;

	case JVST_VM_M:
		snprintf(buf, 16, "%%M");
		break;

	default:
		snprintf(buf, 16, "%%R%d", slot - JVST_VM_NUMREG);
		break;
	}

	return buf;
}

static const char *
argname(uint16_t arg, char buf[static 16])
{
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
	enum jvst_vm_op op;
	uint16_t a,b;

	sbuf_indent(buf, indent);

	op = jvst_vm_decode_op(c);

	opname = jvst_op_name(op);
	switch (op) {
	case JVST_OP_JMP:
	case JVST_OP_CALL:
		{
			enum jvst_vm_br_cond brc;
			uint32_t barg;
			long br;

			barg = jvst_vm_decode_barg(c);
			brc  = jvst_vm_decode_bcond(c);
			br = jvst_vm_tobarg(barg);
			sbuf_snprintf(buf, "%05" PRIu32 "\t0x%08" PRIx32 "\t%s\t%3s %-5ld\n",
				pc, c, opname, 
				op == JVST_OP_JMP ? jvst_vm_br_cond_name(brc) : "",
				br);
		}
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
			uint32_t si,si0,si1,c, soff;
			si0 = prog->sdata[i];
			si1 = prog->sdata[i+1];

			soff = prog->nsplit+1;

			sbuf_indent(buf, indent+2);
			sbuf_snprintf(buf, "SPLIT(%" PRIu32 ")\t", i);
			for (c=0, si = si0; si < si1; c++, si++) {
				uint32_t off,pinstr;

				off = prog->sdata[soff+si];
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
#if DEBUG_BSEARCH
	fprintf(stderr, "binary search in range [%d,%d] for %d (%c)\n",
		i0,i1,key,isprint(key) ? key : ' ');
#endif
	while (i0 <= i1) {
		int mid,mkey;
		mid = (i0 + i1)/2;
		mkey = list[2*mid];
#if DEBUG_BSEARCH
		fprintf(stderr, "  i0 = %d, i1 = %d, mid = %d, mkey = %d (%c)\n",
			i0,i1,mid,mkey, isprint(mkey) ? mkey : ' ');
#endif
		if (mkey == key) {
			return mid;
		}

		if (mkey < key) {
			i0 = mid+1;
		} else {
			i1 = mid-1;
		}
#if DEBUG_BSEARCH
		fprintf(stderr, "  new: i0 = %d, i1 = %d\n", i0,i1);
#endif
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
	uint32_t fp,sp,i,n;

	fp = vm->r_fp;
	sp = vm->r_sp;
	if (fp > 0) {
		fprintf(f, "[%5d] %" PRId64 "\t(PPC)\n", fp-2, vm->stack[fp-2].i);
		fprintf(f, "[%5d] %" PRId64 "\t(PFP)\n", fp-1, vm->stack[fp-1].i);
		fprintf(f, "---\n");
	}

	assert(sp >= fp);
	n = sp - fp;
	for (i=0; i < n; i++) {
		char rname[16];
		fprintf(f, "[%5d] %-3s ", fp+i, stackname(i,rname));
		if (i == JVST_VM_TNUM) {
			fprintf(f, "%f\n", vm->stack[i].f);
		} else {
			fprintf(f, "%" PRId64 "\n", vm->stack[i].i);
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
iopcmp(struct jvst_vm *vm, uint32_t fp, uint32_t opcode)
{
	uint32_t a,b;
	int64_t va,vb;

	a = jvst_vm_decode_arg0(opcode);
	b = jvst_vm_decode_arg1(opcode);

	va = vm_ival(vm, fp, a);
	vb = vm_ival(vm, fp, b);

	return (va > vb) - (va < vb);
}

static inline int
fopcmp(struct jvst_vm *vm, uint32_t fp, uint32_t opcode)
{
	uint32_t a,b;
	double va,vb;

	a = jvst_vm_decode_arg0(opcode);
	b = jvst_vm_decode_arg1(opcode);

	va = vm_fvalptr(vm, fp, a)[0];
	vb = vm_fvalptr(vm, fp, b)[0];

	return (va > vb) - (va < vb);
}

static inline int
has_partial_token(struct jvst_vm *vm)
{
	return (vm->pret != SJP_OK);
}

static void
setup_next_token(struct jvst_vm *vm, uint32_t fp)
{
	int ret;

	assert(vm->r_fp == fp);
	assert(vm->r_sp >= fp + JVST_VM_NUMREG);

	if (has_partial_token(vm)) {
		PANIC(vm, -1, "TOKEN called before previous token fully read");
	}
}

static void
load_slots_from_token(struct jvst_vm *vm, uint32_t fp)
{
	vm->stack[fp+JVST_VM_TT  ].i = 0;
	vm->stack[fp+JVST_VM_TNUM].f = 0.0;
	vm->stack[fp+JVST_VM_TLEN].i = 0;

	vm->stack[fp+JVST_VM_TT].i = vm->evt.type;
	if (vm->evt.type == SJP_STRING) {
		vm->stack[fp+JVST_VM_TLEN].i += vm->evt.extra.ncp;
	} else {
		vm->stack[fp+JVST_VM_TLEN].i += vm->evt.n;
	}
	if (vm->evt.type == SJP_NUMBER) {
		vm->stack[fp+JVST_VM_TNUM].f = vm->evt.extra.d;
	}
}

static void
unget_token(struct jvst_vm *vm)
{
	if (vm->tokstate == JVST_VM_TOKEN_BUFFERED) {
		PANIC(vm, -1, "unget TOKEN while token already buffered");
	}

	vm->tokstate = JVST_VM_TOKEN_BUFFERED;
}

static int
next_token(struct jvst_vm *vm, uint32_t fp)
{
	switch (vm->tokstate) {
	case JVST_VM_TOKEN_BUFFERED:
	case JVST_VM_TOKEN_FETCH:
		vm->tokstate = JVST_VM_TOKEN_READY;
		load_slots_from_token(vm,fp);
		return 0;

	case JVST_VM_TOKEN_READY:
	case JVST_VM_TOKEN_CONSUMED:
		vm->tokstate = JVST_VM_TOKEN_FETCH;
		setup_next_token(vm, fp);
		return 1;

	default:
		PANIC(vm, -1, "invalid VM token state");
	}
}

static int
consume_current_value(struct jvst_vm *vm)
{
	int ret;

	if (vm->nobj > 0 || vm->narr > 0) {
		goto eating_object_or_array;
	}

	// consume current value:
	//
	// if nobj == 0 && narr == 0:
	//   1. value is consumed:
	//      set consumed=false, return JVST_NEXT to obtain a new value
	//   2. value is partial:     return JVST_MORE to get more of the
	//                            value
	//
	//   3. value is not partial: if token type is OBJECT_BEG or
	//                            ARRAY_BEG, incr nobj or narr,
	//                            respectively
	//
	//   4. if nobj==0 and narr==0, set consumed to be true and
	//      return JVST_VALID, other continue on to ...
	//
	// if nobj > 0 || narr > 0:
	//   1. if value is partial, return JVST_MORE to get more of it
	//
	//   2. otherwise, if value is:
	//      OBJECT_BEG, nobj++
	//      OBJECT_END, nobj--
	//      ARRAY_BEG,  narr++
	//      ARRAY_END,  narr--
	//
	//   3. if nobj == 0 && narr == 0, return JVST_VALID
	//
	//   4. otherwise return JVST_NEXT

	switch (vm->tokstate) {
	case JVST_VM_TOKEN_BUFFERED:
		// mark buffered value as consumed
		vm->tokstate = JVST_VM_TOKEN_READY;

		/* fallthrough */

	case JVST_VM_TOKEN_READY:
		if (has_partial_token(vm)) {
			return JVST_MORE;
		}

		if (vm->evt.type == SJP_OBJECT_BEG) {
			vm->nobj++;
			return JVST_NEXT;
		} else if (vm->evt.type == SJP_ARRAY_BEG) {
			vm->narr++;
			return JVST_NEXT;
		}

		vm->tokstate = JVST_VM_TOKEN_CONSUMED;
		return JVST_VALID;

	case JVST_VM_TOKEN_CONSUMED:
	case JVST_VM_TOKEN_FETCH:
		vm->tokstate = JVST_VM_TOKEN_READY;
		return JVST_NEXT;

	default:
		PANIC(vm, -1, "invalid VM token state");
	}

eating_object_or_array:
	if (has_partial_token(vm)) {
		return JVST_MORE;
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

	if (vm->nobj == 0 && vm->narr == 0) {
		vm->tokstate = JVST_VM_TOKEN_CONSUMED;
		return JVST_VALID;
	}

	return JVST_NEXT;
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

static const char *
tokstate_name(enum jvst_vm_tokstate st)
{
	switch (st) {
	case JVST_VM_TOKEN_BUFFERED:
		return "BUFFERED";

	case JVST_VM_TOKEN_FETCH:
		return "FETCH";

	case JVST_VM_TOKEN_READY:
		return "READY";

	case JVST_VM_TOKEN_CONSUMED:
		return "CONSUMED";

	default:
		return "UNKNOWN!!!";
	}
}

static void
debug_state(struct jvst_vm *vm)
{
	char cbuf[128];
	struct sbuf buf = { .buf = cbuf, .cap = sizeof(cbuf), .len = 0, .np = 0 };

	vm_dumpevt(&buf, vm);
	fprintf(stderr, "EVT  > %s\n", buf.buf);

	buf.len = 0;
	buf.np = 0;
	vm_dumpregs(&buf, vm);
	fprintf(stderr, "STATE> vm=%p nobj=%zu, narr=%zu, tokstate=%s, error=%d, dfa_st=%d\n",
		(void *)vm, vm->nobj, vm->narr, tokstate_name(vm->tokstate), vm->error, vm->dfa_st);
	fprintf(stderr, "REGS > %s", buf.buf);
	vm_dumpstack(stderr, vm);
}

static void
debug_op(struct jvst_vm *vm, uint32_t pc, uint32_t opcode)
{
	char cbuf[128];
	struct sbuf buf = { .buf = cbuf, .cap = sizeof(cbuf), .len = 0, .np = 0 };

	vm_dump_opcode(&buf, pc, opcode, 0);
	fprintf(stderr, "INSTR> %s", buf.buf);

	debug_state(vm);
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

	if (vm->tokstate != JVST_VM_TOKEN_READY) {
		PANIC(vm, -1, "MATCH op, but token is not READY");
	}

	if (vm->evt.type != SJP_STRING) {
		PANIC(vm, -1, "MATCH op on a non-string token");
	}

	ret = SJP_OK;
	st = jvst_vm_dfa_run(dfa, vm->dfa_st, vm->evt.text, vm->evt.n);
	if (has_partial_token(vm)) {
		return JVST_MORE;
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
	vm->tokstate = JVST_VM_TOKEN_CONSUMED;

	vm->stack[vm->r_fp + JVST_VM_M].i = result;
	return SJP_OK;
}

static enum jvst_result
vm_run_next(struct jvst_vm *vm, enum SJP_RESULT pret, struct sjp_event *evt);

static int
vm_split(struct jvst_vm *vm, int split, union jvst_vm_stackval *slot, int splitv)
{
	uint32_t proc0, proc1, nproc, i, ndone;
	int endstate;

	proc0 = vm->prog->sdata[split+0];
	proc1 = vm->prog->sdata[split+1];
	nproc = proc1-proc0;

	if (vm->nsplit == 0) {
		uint32_t i, off, fp0;

		if (nproc > vm->maxsplit) {
			size_t incr = vm->maxsplit - nproc;
			vm->splits = xenlargevec(vm->splits, &vm->maxsplit, incr, sizeof vm->splits[0]);
		}

		fp0 = vm->r_fp;
		off = vm->prog->nsplit + 1 + proc0;
		for (i=0; i < nproc; i++) {
			jvst_vm_init_defaults(&vm->splits[i], vm->prog);
			vm->splits[i].r_pc = vm->prog->sdata[off + i];

			// split vms inherit the current token state
			vm->splits[i].tokstate = vm->tokstate;
		}

		// SPLIT should leave the current token, if any, consumed
		vm->tokstate = JVST_VM_TOKEN_CONSUMED;
		vm->nsplit = nproc;
	}

	if (vm->nsplit != nproc) {
		// XXX - fixme: better error message!
		PANIC(vm, -1, "SPLIT count and current split do not agree");
	}

	endstate = JVST_INDETERMINATE;
	ndone = 0;
	for (i=0; i < nproc; i++) {
		enum jvst_result ret;

		if (vm->splits[i].prog == NULL) {
			ndone++;
			continue;
		}

		// run vm code
		ret = vm_run_next(&vm->splits[i], vm->pret, &vm->evt);

		switch (ret) {
		case JVST_VALID:
			assert(vm->splits[i].error == 0);
			vm->splits[i].prog = NULL;

			/* fallthrough */

		case JVST_MORE:
		case JVST_NEXT:
			if (endstate != JVST_INDETERMINATE && ret != endstate) {
				PANIC(vm, -1, "internal error: split return of two end states");
			}

			endstate = ret;
			break;

		case JVST_INVALID:
			/* only case where we don't assign an endstate...
			 * splits can return invalid at any time.
			 *
			 * NB: if all splits return invalid, the parsing
			 * stream not reach a consistent place.
			 *
			 * FIXME: This could be a problem with NOT
			 * conditions.  When generating the cnode tree
			 * (or IR?), we need to ensure that there's a
			 * way for the token stream to end up in the
			 * place we expect. This could be either
			 * explicitly coded (ie: finish consuming
			 * string/object/array) or done with a dummy
			 * split whose result we ignore.
			 */
			assert(vm->splits[i].error != 0);
			vm->splits[i].prog = NULL;
			break;
		}

		if (vm->splits[i].prog == NULL) {
			ndone++;
		}
	}

	if (ndone < nproc) {
		if (endstate == JVST_INDETERMINATE) {
			PANIC(vm, -1, "internal error: split not finished, but endstate is INDETERMINATE");
		}

		if (endstate == JVST_VALID) {
			PANIC(vm, -1, "internal error: split not finished, but endstate is VALID");
		}

		return endstate;
	}

	// all splits have finished, endstate should either be
	// INDETERMINATE or VALID.
	if (endstate != JVST_INDETERMINATE && endstate != JVST_VALID) {
			PANIC(vm, -1, "internal error: split finished, endstate is not INDETERMINATE or VALID");
	}

	// all splits have finished.  record valid splits
	if (splitv == 0) {
		// count number of valid splits
		slot->i = 0;
		for (i=0; i < nproc; i++) {
			assert(vm->splits[i].prog == NULL);

			if (vm->splits[i].error == 0) {
				slot->i++;
			}
		}
	} else {
		size_t i, nslots;
		uint64_t mask;
	       
		nslots = nproc / 64 + ((nproc % 64) > 0);

		// zero bits in bitfield
		for (i=0; i < nslots; i++) {
			slot[i].u = 0;
		}

		// set bits in bitfield
		mask = 1;
		for (i=0; i < nproc; i++) {
			size_t sl = i / 64;
#if DEBUG_SPLITV
			{
				size_t bi;
				fprintf(stderr, "SPLITV> i=%zu, slot = %zu, mask = %" PRIx64 ", bf=",
					i, sl, mask);
				for (bi=64; bi > 0; bi--) {
					int b = (slot[sl].u & ((uint64_t)1 << (bi-1))) > 0;
					fprintf(stderr,"%c", b?'1':'0');
				}
				fprintf(stderr,"\n");
			}
#endif /* DEBUG_SPLITV */

			if (vm->splits[i].error == 0) {
				slot[sl].u |= mask;
			}
			mask = mask << 1;
			if (!mask) { mask = 1; }
		}
	}

	// clean up split resources and reset vm->nsplit
	for (i=0; i < nproc; i++) {
		assert(vm->splits[i].prog == NULL);
		jvst_vm_finalize(&vm->splits[i]);
	}
	vm->nsplit = 0;
	return JVST_VALID;
}

#define DEBUG_OP(vm,pc,opcode) do{ if (DEBUG_OPCODES) { debug_op((vm),(pc),(opcode)); } } while(0)

#define NEXT do{ vm->r_pc = ++pc; goto loop; } while(0)
#define BRANCH(newpc) do { pc += (newpc); vm->r_pc = pc; goto loop; } while(0)
static enum jvst_result
vm_run_next(struct jvst_vm *vm, enum SJP_RESULT pret, struct sjp_event *evt)
{
	uint32_t opcode, pc, fp, sp;
	int64_t flag;
	uint32_t *code;
	size_t ncode;

	enum jvst_vm_op op;
	int ret;

	vm->evt = *evt;
	vm->pret = pret;

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
#if DEBUG_STEP
	{
		static char buf[256];
		fgets(buf, sizeof buf, stdin);
	}
#endif

	switch (op) {
	case JVST_OP_NOP:
		NEXT;

	case JVST_OP_PROC:
		{
			uint32_t a, fp0;
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
			fp0 = fp;
			fp = sp;

			// allocate stack slots
			resize_stack(vm, sp+n);
			for (i=0; i < n; i++) {
				vm->stack[sp++].u = 0;
			}

			if (fp0 != fp) {
				// copy registers
				vm->stack[fp+JVST_VM_TT  ].i = vm->stack[fp0+JVST_VM_TT  ].i;
				vm->stack[fp+JVST_VM_TNUM].f = vm->stack[fp0+JVST_VM_TNUM].f;
				vm->stack[fp+JVST_VM_TLEN].i = vm->stack[fp0+JVST_VM_TLEN].i;
				vm->stack[fp+JVST_VM_M   ].i = vm->stack[fp0+JVST_VM_M   ].i;
			} else {
				// load TT / TNUM / TLEN from current token
				load_slots_from_token(vm,fp);
			}

			vm->r_fp = fp;
			vm->r_sp = sp;
		}
		NEXT;

	/* integer comparisons */
	case JVST_OP_ICMP:
		vm->r_flag = flag = iopcmp(vm, fp, opcode);
		NEXT;

	/* floating point comparisons */
	case JVST_OP_FCMP:
		vm->r_flag = flag = fopcmp(vm, fp, opcode);
		NEXT;

	case JVST_OP_FINT:
		{
			double v;
			uint32_t arg0, arg1;
			int slot;

			arg0 = jvst_vm_decode_arg0(opcode);
			arg1 = jvst_vm_decode_arg1(opcode);
			assert(jvst_vm_arg_isslot(arg0));

			v = vm_fvalptr(vm, fp, arg0)[0];
			if (arg1 != 0) {
				double div;

				if (jvst_vm_arg_isslot(arg1)) {
					div = vm_fvalptr(vm, fp, arg1)[0];
				} else {
					div = jvst_vm_arg_tolit(arg1);
				}

				v /= div;
			}

			vm->r_flag = flag = isfinite(v) && (v == ceil(v));
		}
		NEXT;

	case JVST_OP_JMP:
		{
			enum jvst_vm_br_cond brc;
			uint32_t barg;
			int fmask;

			brc = jvst_vm_decode_bcond(opcode);
			if (brc != JVST_VM_BR_ALWAYS) {
				int mask;

				// XXX - can we simplify / eliminate
				// branches?
				mask = (flag<0) | ((flag > 0) << 1) | ((flag == 0) << 2);

				if ((brc & mask) == 0) {
					NEXT;
				}
			}

			barg = jvst_vm_decode_barg(opcode);
			BRANCH(jvst_vm_tobarg(barg));
		}

	case JVST_OP_TOKEN:
		{
			uint32_t arg1;
			int i1;

			arg1 = jvst_vm_decode_arg1(opcode);
			i1 = jvst_vm_arg_tolit(arg1);

			// read next token, set the various token values
			if (i1 == -1) {
				unget_token(vm);
				NEXT;
			}

			if (next_token(vm,fp)) {
				return JVST_NEXT;
			}
			NEXT;
		}

	case JVST_OP_CONSUME:
		{
			int ret;

			ret = consume_current_value(vm);
			if (ret != JVST_VALID) {
				return ret;
			}
		}
		NEXT;

	case JVST_OP_RETURN:
		{
			uint32_t arg0;

			arg0 = jvst_vm_decode_arg0(opcode);
			assert(jvst_vm_arg_islit(arg0));

			if (arg0 != 0) {
				vm->error = vm_ival(vm, fp, arg0);
				assert(vm->error != 0);
				ret = JVST_INVALID;
				goto finish;
			}

			// otherwise VALID return

			// consume token, then return to previous frame or, if top of
			// stack, return JVST_VALID
			ret = consume_current_value(vm);
			if (ret != JVST_VALID && ret != JVST_NEXT) {
				return ret;
			}

			// value consumed... return to previous frame or finish
			// if we're at the top of the stack
			if (fp == 0) {
				vm->r_pc = pc = 0;
				ret = JVST_VALID;
				goto finish;
			}

			vm->r_sp = sp = fp-2;
			vm->r_pc = pc = vm->stack[fp-2].u;
			vm->r_fp = fp = vm->stack[fp-1].u;
			NEXT; // pc points to CALL, continue with next instruction
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
				PANIC(vm, -1, "MATCH op with invalid DFA");
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
				PANIC(vm, -1, "BSET op with invalid bit");
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

	case JVST_OP_SPLITV:
	case JVST_OP_SPLIT:
		{
			uint32_t a0,a1;
			int split;
			union jvst_vm_stackval *slot;

			a0 = jvst_vm_decode_arg0(opcode);
			a1 = jvst_vm_decode_arg1(opcode);

			if (!jvst_vm_arg_isslot(a1)) {
				PANIC(vm, -1, "SPLIT op with non-slot second argument");
			}

			split = vm_ival(vm, fp, a0);
			slot = vm_slotptr(vm, fp, a1);
			if (split < 0 || (size_t)split >= vm->prog->nsplit) {
				PANIC(vm, -1, "SPLIT op with bad split index");
			}

			ret = vm_split(vm,split,slot, (op == JVST_OP_SPLITV));
			if (ret != JVST_VALID) {
				goto finish;
			}
		}
		NEXT;

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
	static struct sjp_event evt_zero = {0};
	struct sjp_event evt = {0};
	enum SJP_RESULT pret;
	int first;

	if (vm->error) {
		return JVST_INVALID;
	}

	sjp_parser_more(&vm->parser, data, n);

	pret = SJP_OK;
	evt.type = SJP_NONE;

	if (!vm->needtok) {
		enum jvst_result ret;

		ret = vm_run_next(vm, pret, &evt);
		if (ret != JVST_NEXT) {
			return ret;
		}
		vm->needtok = 1;
	}

	for (;;) {
		enum jvst_result ret;

		pret = sjp_parser_next(&vm->parser, &evt);
		if (DEBUG_TOKENS) {
			char txt[256];
			size_t n = evt.n;
			if (n < sizeof txt) {
				memcpy(txt, evt.text, n);
				txt[n] = '\0';
			} else {
				n = sizeof txt - 4;
				memcpy(txt, evt.text, n);
				memcpy(&txt[n], "...", 4);
			}

			fprintf(stderr, "<TOKEN> ret=%s event=%s %s\n",
				ret2name(pret), evt2name(evt.type), txt);
		}

		if (SJP_ERROR(pret)) {
			vm->error = pret;
			if (DEBUG_OPCODES) {
				const char *lbeg, *lend, *err, *end;
				size_t i,n,width = 60, padding = 12;
				char buf[128] = { 0 }, *bstart = &buf[0];
				int ellipsis = 0;

				fprintf(stderr, "Error parsing JSON, offset %zu (line %zu, col %zu): %s\n",
					vm->parser.lex.off, vm->parser.lex.line + 1,
					vm->parser.lex.off - vm->parser.lex.lbeg + 1,
					ret2name(pret));
				fprintf(stderr, "line: ");

				lbeg = &vm->parser.lex.data[vm->parser.lex.lbeg];
				err  = &vm->parser.lex.data[vm->parser.lex.off];
				end = &vm->parser.lex.data[vm->parser.lex.sz];
				lend = memchr(lbeg, '\n', end-lbeg);
				if (lend == NULL) {
					lend = end;
				}

				if (lend-lbeg >= (ptrdiff_t) sizeof buf) {
					const char *emin, *emax;
					emin = lbeg;
					if (err-lbeg > (ptrdiff_t) padding) {
						emin = err-padding;
						ellipsis |= 0x1;
					}

					emax = lend;
					if (lend-err > (ptrdiff_t) width) {
						lend = err+width;
						ellipsis |= 0x2;
					}

					assert(lend-lbeg < (ptrdiff_t) sizeof buf);
				}

				memcpy(&buf[0], lbeg, lend-lbeg);
				if (ellipsis & 0x1) {
					fprintf(stderr, "...");
				}
				fprintf(stderr, "%s", buf);
				if (ellipsis & 0x2) {
					fprintf(stderr, "...");
				}
				fprintf(stderr, "\n");

				fprintf(stderr, "      ");
				n = err - lbeg;
				for (i=0; i < n; i++) {
					buf[i] = ' ';
				}
				buf[n] = '^';
				buf[n+1] = '\0';

				fprintf(stderr,"%s\n",buf);
				fprintf(stderr, "\n");

				debug_state(vm);
			}

			return JVST_INVALID;
		}

		// XXX - handle EOS here?
		// FIXME: handle pret == SJP_PARTIAL!

		if (pret == SJP_MORE && evt.type == SJP_TOK_NONE) {
			// need more...
			return JVST_MORE;
		}

		if (pret == SJP_OK && evt.type == SJP_TOK_NONE) {
			// stream has closed
			if (vm->r_pc == 0 && vm->r_fp == 0) {
				return JVST_VALID;
			}
			return JVST_INVALID;
		}

		vm->needtok = 0;
		ret = vm_run_next(vm, pret, &evt);
		if (ret != JVST_NEXT) {
			return ret;
		}
		vm->needtok = 1;
	}
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
