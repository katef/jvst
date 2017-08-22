#include "validate_vm.h"

#include <assert.h>
#include <inttypes.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <stddef.h>
#include <string.h>

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
		case JVST_VM_PPC: 	snprintf(buf, 16, "%%PPC"); break;
		case JVST_VM_PFP:	snprintf(buf, 16, "%%PFP"); break;
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

void
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
		const char *opname;
		uint32_t c,barg;
		long br;
		enum jvst_vm_op op;
		uint16_t a,b;

		c = prog->code[i];
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

			/*
			sbuf_snprintf(buf, "%05zu\t0x%08" PRIx32 "\t0x%02x 0x%-7" PRIx32 "   \t%s\t%-5ld\n",
				i, c, (unsigned int)op, br, opname, br);
			*/
			sbuf_snprintf(buf, "%05zu\t0x%08" PRIx32 "\t%s\t%-5ld\n",
				i, c, opname, br);
			break;

		default:
			{
				char astr[16], bstr[16];
				a = jvst_vm_decode_arg0(c);
				b = jvst_vm_decode_arg1(c);
				/*
				sbuf_snprintf(buf,
					"%05zu\t0x%08" PRIx32 "\t0x%02x 0x%-4" PRIx16 " 0x%-4" PRIx16 "\t%s\t%s, %s\n",
						i, c, (unsigned int)op, a,b, opname, argname(a,astr), argname(b,bstr));
				*/
				sbuf_snprintf(buf,
					"%05zu\t0x%08" PRIx32 "\t%s\t%s, %s\n",
						i, c, opname, argname(a,astr), argname(b,bstr));
			}
		}
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

void
jvst_vm_program_free(struct jvst_vm_program *prog)
{
	// XXX - free stuff!
	(void)prog;
}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
