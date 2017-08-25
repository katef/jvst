#ifndef VALIDATE_OP_H
#define VALIDATE_OP_H

#include <stdlib.h>

#include "validate_ir.h"
#include "validate_vm.h"

/* What follows is for assembling the opcodes */
enum jvst_op_arg_type {
	// Special read-only registers (cannot be set via a load)
	JVST_VM_ARG_NONE,	// Empty/omitted arg

	JVST_VM_ARG_TT,		// type of current token
	JVST_VM_ARG_TNUM,	// floating point value of current token (if %TT is $NUMBER)
	JVST_VM_ARG_TLEN,	// length of current token (if %TT is $STRING)

	JVST_VM_ARG_M,		// Match case register

	// Slots on the stack
	JVST_VM_ARG_SLOT,

	// Item in the constant pool
	JVST_VM_ARG_POOL,

	// Integer literal values
	JVST_VM_ARG_TOKTYPE,
	JVST_VM_ARG_CONST,

	// Branch destinations
	JVST_VM_ARG_INSTR,
	JVST_VM_ARG_LABEL,

	// Call and split destinations
	JVST_VM_ARG_CALL,
};

struct jvst_op_proc;
struct jvst_op_instr;

struct jvst_op_arg {
	enum jvst_op_arg_type type;
	union {
		int64_t index;
		struct jvst_op_instr *dest;
		struct jvst_op_proc *proc;
		const char *label;
	} u;
};

struct jvst_op_instr {
	struct jvst_op_instr *next;
	struct jvst_op_arg args[2];
	const char *label;
	uint32_t code_off;

	enum jvst_vm_op op;
};

// Instruction data... for assembling the opcodes
struct jvst_op_proc {
	struct jvst_op_proc *next;		// list of all procs
	struct jvst_op_proc *split_next;	// list of procs involved in a split
	uint32_t code_off;

	size_t proc_index;

	size_t nslots;
	size_t temp_off;

	// struct jvst_op_block *blocks;

	struct jvst_op_instr *ilist;

	char label[64];
};

struct jvst_op_program {
	struct jvst_op_proc *procs;

	size_t nfloat;
	double *fdata;

	size_t nconst;
	int64_t *cdata;

	size_t ndfa;
	struct jvst_vm_dfa *dfas;

	size_t nsplit;
	size_t *splitmax;
	struct jvst_op_proc **splits;
};

struct jvst_ir_stmt;

struct jvst_op_program *
jvst_op_assemble(struct jvst_ir_stmt *stmt);

struct jvst_op_program *
jvst_op_optimize(struct jvst_op_program *prog);

int
jvst_op_dump(struct jvst_op_program *prog, char *buf, size_t nb);

void
jvst_op_print(struct jvst_op_program *prog);

struct jvst_vm_program *
jvst_op_encode(struct jvst_op_program *prog);

struct jvst_vm_program *
jvst_ir_assemble(struct jvst_ir_stmt *prog);

void
jvst_op_build_vm_dfa(struct fsm *fsm, struct jvst_vm_dfa *dfa);

void
jvst_vm_dfa_debug(struct jvst_vm_dfa *dfa);

#endif /* VALIDATE_OP_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
