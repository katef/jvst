#ifndef VALIDATE_OP_H
#define VALIDATE_OP_H

#include <stdlib.h>

#include "validate_ir.h"

enum jvst_vm_op {
	JVST_OP_NOP	= 0,
	JVST_OP_FRAME,		// FRAME N sets up a call frame and reserves N 64-bit slots on the call stack
	// JVST_OP_PUSH,		// PUSH N -- reserve N 64-bit slots on the call stack

	// Integer comparison operators.  Args may be either integer registers or immediate constants
	JVST_OP_ILT,
	JVST_OP_ILE,
	JVST_OP_IEQ,
	JVST_OP_IGE,
	JVST_OP_IGT,
	JVST_OP_INEQ,

	// Floating point comparison operators.  Args must be floating point registers
	JVST_OP_FLT,
	JVST_OP_FLE,
	JVST_OP_FEQ,
	JVST_OP_FGE,
	JVST_OP_FGT,
	JVST_OP_FNEQ,

	JVST_OP_FINT,		// Checks if a float is an integer.  args: reg.  result: isnormal(reg) && (reg == ceil(reg)).

	JVST_OP_BR,		// Unconditional branch
	JVST_OP_CBT,		// Conditional branch on true
	JVST_OP_CBF,		// Conditional branch on false

	JVST_OP_CALL,		// Calls into another proc.  Control will continue at the next 
				// instruction if the proc returns VALID.

	JVST_OP_SPLIT,		// SPLIT(split_ind, reg)
	JVST_OP_SPLITV,		// SPLITV(split_ind, slot0)

	JVST_OP_TOKEN,		// Loads the next token
	JVST_OP_CONSUME,	// Consumes the next value, including objects and arrays

	JVST_OP_MATCH,		// Matches the current string token: MATCH(dfa_index)

	// Loads proc constants into registers
	JVST_OP_FLOAD,		// Loads a float: FLOAD(const_index)
	JVST_OP_ILOAD,		// Loads a size/int: ILOAD(const_index)

	JVST_OP_INCR,		// Increments a register or slot: INCR(reg_slotA)

	JVST_OP_BSET,		// Sets a bit. BSET(reg_slotA,bit)
	JVST_OP_BTEST,		// Tests a bit: BTEST(reg_slotA,bit)

	JVST_OP_BAND,		// Bitwise-AND: BAND(regA,reg_slotB)  regA = regA & reg_slotB

	JVST_OP_VALID,		// Consumes the current token and returns a VALID result for the current proc.
				// If the current token in $OBJECT_BEG or $ARRAY_BEG, consumes the entire object/array.
	JVST_OP_INVALID,	// Raises an INVALID result: INVALID(errcode)
};

enum jvst_vm_register {
	JVST_VM_NONE = 0,	// Empty/omitted value

	JVST_VM_FLAG,		// Comparison flag
	JVST_VM_PC,		// Program counter register (read-only)
	JVST_VM_BP,		// stack base pointer
	JVST_VM_SP,		// current stack pointer

	JVST_VM_TT,		// type of current token
	JVST_VM_TNUM,		// floating point value of current token (if %TT is $NUMBER)
	JVST_VM_TLEN,		// length of current token (if %TT is $STRING)
	JVST_VM_TCOMPLETE,	// 1 if the curernt token is complete, 0 if it is a partial token

	JVST_VM_M,		// Match case register

	JVST_VM_IPREFIX = 1<<14,
	JVST_VM_FPREFIX = 1<<15,
	JVST_VM_SPREFIX = (1<<14)|(1<<15),
};


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

	// Integer constant
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
