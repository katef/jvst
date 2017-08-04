#ifndef VALIDATE_OP_H
#define VALIDATE_OP_H

#include <stdlib.h>

#include "validate_ir.h"
#include "validate_vm.h"

/* What follows is for assembling the opcodes */
enum jvst_op_arg_type {
	// Special read-only registers (cannot be set via a load)
	JVST_VM_ARG_NONE,	// Empty/omitted arg

	JVST_VM_ARG_FLAG,	// Comparison flag
	JVST_VM_ARG_PC,		// Program counter

	JVST_VM_ARG_TT,		// type of current token
	JVST_VM_ARG_TNUM,	// floating point value of current token (if %TT is $NUMBER)
	JVST_VM_ARG_TLEN,	// length of current token (if %TT is $STRING)
	JVST_VM_ARG_TCOMPLETE,	// 1 if the curernt token is complete, 0 if it is a partial token

	JVST_VM_ARG_M,		// Match case register

	// Scratchpad registers (can be set via a load)
	JVST_VM_ARG_INT,	// integer or size register
	JVST_VM_ARG_FLOAT,	// double precision floating point register

	// Slots on the stack
	JVST_VM_ARG_SLOT,

	// Item in the constant pool
	JVST_VM_ARG_POOL,

	// Integer literal values
	JVST_VM_ARG_TOKTYPE,
	JVST_VM_ARG_CONST,
};

struct jvst_op_arg {
	enum jvst_op_arg_type type;
	int64_t index;
};

struct jvst_op_proc;
struct jvst_op_block;

struct jvst_op_instr {
	struct jvst_op_instr *next;

	enum jvst_vm_op op;
	const char *label;

	union {
		struct jvst_op_arg args[2];

		struct {
			const char *label;
			struct jvst_op_block *dest;
		} branch;

		struct {
			size_t proc_index;
			struct jvst_op_proc *dest;
		} call;

		enum jvst_invalid_code ecode;
	} u;
};

struct jvst_op_block {
	struct jvst_op_block *next;
	struct jvst_op_instr *ilist;
	struct jvst_op_instr *ilast;

	int work;
	char label[128];
};

// Instruction data... for assembling the opcodes
struct jvst_op_proc {
	struct jvst_op_proc *next;		// list of all procs
	struct jvst_op_proc *split_next;	// list of procs involved in a split

	size_t proc_index;

	size_t nfloat;
	double *fdata;

	size_t nconst;
	int64_t *cdata;

	size_t ndfa;
	struct fsm **dfas;

	size_t nsplit;
	struct jvst_op_proc **splits;

	size_t nslots;

	struct jvst_op_block *blocks;

	struct jvst_op_instr *ilist;

	char label[64];
};

struct jvst_op_program {
	struct jvst_op_proc *procs;
};

struct jvst_ir_stmt;

struct jvst_op_program *
jvst_op_assemble(struct jvst_ir_stmt *stmt);

struct jvst_op_program *
jvst_op_optimize(struct jvst_op_program *prog);

const char *
jvst_op_name(enum jvst_vm_op op);

int
jvst_op_dump(struct jvst_op_program *prog, char *buf, size_t nb);

void
jvst_op_print(struct jvst_op_program *prog);

void
jvst_op_block_debug(struct jvst_op_block *blk);

#endif /* VALIDATE_OP_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
