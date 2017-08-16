#ifndef VALIDATE_VM_H
#define VALIDATE_VM_H

#include <assert.h>
#include <stdint.h>
#include <stdio.h>

#include "jvst_macros.h"
#include "validate_sbuf.h"

#include "sjp_parser.h"

enum jvst_vm_register {
	JVST_VM_NONE = 0,	// Empty/omitted value

	JVST_VM_FLAG,		// Comparison flag
	JVST_VM_PC,		// Program counter register (read-only)
	JVST_VM_FP,		// stack frame pointer
	JVST_VM_SP,		// current stack pointer

	JVST_VM_TT,		// type of current token
	JVST_VM_TNUM,		// floating point value of current token (if %TT is $NUMBER)
	JVST_VM_TLEN,		// length of current token (if %TT is $STRING)
	JVST_VM_TCOMPLETE,	// 1 if the curernt token is complete, 0 if it is a partial token

	JVST_VM_M,		// Match case register

	JVST_VM_IREG0,		// integer registers
	JVST_VM_IREG1,
	JVST_VM_IREG2,
	JVST_VM_IREG3,
	JVST_VM_IREG4,
	JVST_VM_IREG5,
	JVST_VM_IREG6,
	JVST_VM_IREG7,

	JVST_VM_FREG0,		// floating point registers
	JVST_VM_FREG1,
	JVST_VM_FREG2,
	JVST_VM_FREG3,
	JVST_VM_FREG4,
	JVST_VM_FREG5,
	JVST_VM_FREG6,
	JVST_VM_FREG7,

};

enum jvst_vm_op {
	JVST_OP_NOP	= 0,
	JVST_OP_PROC,		// FRAME N sets up a call frame and reserves N 64-bit slots on the call stack
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

	JVST_OP_SPLIT,		// SPLIT(split_ind, iregO)
	JVST_OP_SPLITV,		// SPLITV(split_ind, slot0)

	JVST_OP_TOKEN,		// Loads the next token
	JVST_OP_CONSUME,	// Consumes the next value, including objects and arrays

	JVST_OP_MATCH,		// Matches the current string token: MATCH(dfa_index)

	// Loads proc constants into registers
	JVST_OP_FLOAD,		// Loads a float: FLOAD(fregO,const_index)	fregO = fconsts[const_index]
	JVST_OP_ILOAD,		// Loads a size/int: ILOAD(iregO,const_or_slot) iregO = slot[ind] or iregO = iconsts[ind]

	JVST_OP_MOVE,		// Moves a slot to another slot

	JVST_OP_INCR,		// Increments a slot: INCR(ind,reg_or_const)	slot[ind] = slot[ind] + reg_or_const

	JVST_OP_BSET,		// Sets a bit. BSET(slotA,bit)
	JVST_OP_BTEST,		// Tests a bit: BTEST(slotA,bit)

	JVST_OP_BAND,		// Bitwise-AND: BAND(regA,reg_slotB)  regA = regA & reg_slotB

	JVST_OP_VALID,		// Consumes the current token and returns a VALID result for the current proc.
				// If the current token in $OBJECT_BEG or $ARRAY_BEG, consumes the entire object/array.
	JVST_OP_INVALID,	// Raises an INVALID result: INVALID(errcode)
};

#define JVST_OP_MAX JVST_OP_INVALID

/* VM opcode encoding:
 * 
 * Each non-branching opcode is a fixed 32-bits, encoded as follows:
 *
 * 01234567890123456789012345678901
 * IIIIIAAAAAAAAAAAAABBBBBBBBBBBBBB
 *
 * I - instruction
 * A - first argument (13 bits, 14th bit is implicitly 0)
 * B - second argument (14 bits)
 *
 * Arguments are 14-bits that specify registers with offsets, constant
 * pool values, or small literal integers
 *
 * 01234567890123
 * 000RRRRR000000	register R
 * 001SSSSSSSSSS0	slot S
 * 01IIIIIIIIIII0	const pool index I
 * 1VVVVVVVVVVVVS	literal value V, with sign bit S
 *
 * Slots are positive and stored on the VM stack relative to %FP.
 * Currently 1024 slots are allowed in a single proc.
 *
 * V  - bits associated with the value
 * F  - first flag bit
 * L  - second flag bit
 * S  - value "sign" bit (for constants)
 *
 * FF - 00 register
 * 	01 slot
 * 	10 literal
 * 	11 const pool
 *
 * Special encoding for branch instructions:
 *
 * 01234567890123456789012345678901
 * IIIIIAAAAAAAAAAAAAAAAAAAAAAAAAAS
 *
 * Single argument for the branch address, which is a signed 27-bit
 * number.
 */

static inline enum jvst_vm_op
jvst_vm_decode_op(uint32_t op)
{
	STATIC_ASSERT(JVST_OP_MAX <= 0x20, opcodes_fit_in_five_bits);
	return (enum jvst_vm_op)(op & 0x1f);
}

static inline uint32_t
jvst_vm_decode_arg0(uint32_t op)
{
	return (op >> 5) & 0x1fff;
}

static inline uint32_t
jvst_vm_decode_arg1(uint32_t op)
{
	return (op >> 18) & 0x3fff;
}

static inline uint32_t
jvst_vm_decode_barg(uint32_t op)
{
	return (op >> 5) & 0x7ffffff;
}

static inline int
jvst_vm_arg_isreg(uint32_t arg)
{
	return ((arg & 7) == 0) && ((arg >> 3) < 32);
}

static inline int
jvst_vm_arg_isslot(uint32_t arg)
{
	return (arg & 7) == 4;
}

static inline int
jvst_vm_arg_ispool(uint32_t arg)
{
	return (arg & 3) == 2;
}

static inline int
jvst_vm_arg_islit(uint32_t arg)
{
	return (arg & 1) == 1;
}

static inline uint32_t
jvst_vm_arg_reg(enum jvst_vm_register r)
{
	assert((int)r >= 0 && (int)r < 32);
	return ((uint32_t)r) << 3;
}

static inline enum jvst_vm_register
jvst_vm_arg_toreg(uint32_t arg)
{
	return (arg >> 3);
}

static inline uint32_t
jvst_vm_arg_slot(int sl)
{
	return ((uint32_t)sl << 3) | 0x4;
}

static inline int
jvst_vm_arg_toslot(uint32_t arg)
{
	return (arg >> 3);
}

static inline uint32_t
jvst_vm_arg_pool(int p)
{
	return ((uint32_t)p << 2) | 0x2;
}

static inline int
jvst_vm_arg_topool(uint32_t arg)
{
	return (arg >> 2);
}

enum {
	JVST_VM_MINLIT  = -(1<<12),
	JVST_VM_MAXLIT  = (1<<12)-1,
	JVST_VM_LITMASK = (1<<13)-1,
	JVST_VM_LITSIGN = (1<<12),
};

static inline uint32_t
jvst_vm_arg_lit(int p)
{
	uint32_t raw;

	assert(p >= JVST_VM_MINLIT);
	assert(p <= JVST_VM_MAXLIT);

	raw = (uint32_t)p & JVST_VM_LITMASK;
	return (raw<<1) | 1;
}

static inline int
jvst_vm_arg_tolit(uint32_t arg)
{
	int v = arg>>1;
	return (v & JVST_VM_LITSIGN) ? -((v-1) ^ JVST_VM_LITMASK) : v;
}

enum {
	JVST_VM_BARG_MIN  = -(1<<26),
	JVST_VM_BARG_MAX  = (1<<26)-1,
	JVST_VM_BARG_MASK = (1<<27)-1,
	JVST_VM_BARG_SIGN = (1<<26),
};

static inline uint32_t
jvst_vm_barg(long p)
{
	uint32_t raw;

	assert(p >= JVST_VM_BARG_MIN);
	assert(p <= JVST_VM_BARG_MAX);

	return (uint32_t)p & JVST_VM_BARG_MASK;
}

static inline long
jvst_vm_tobarg(uint32_t arg)
{
	int32_t v = arg;
	return (v & JVST_VM_BARG_SIGN) ? -((v-1) ^ JVST_VM_BARG_MASK) : v;
}

struct jvst_vm_dfa {
	size_t nstates;
	size_t nends;

	int *offs;
	int *transitions;
	int *endstates;
};

struct jvst_vm_program {
	size_t nfloat;
	size_t nconst;
	size_t nsplits;
	size_t ndfas;

	double  *fdata;
	int64_t *cdata;
	uint32_t *sdata;

	struct jvst_vm_dfa *dfas;

	uint32_t code[];
};

struct jvst_vm_program *
jvst_vm_readfile(FILE *f);

struct jvst_vm_program *
jvst_vm_readbuf(const unsigned char *buf, size_t n);

int
jvst_vm_writefile(FILE *f, const struct jvst_vm_program *prog);

int
jvst_vm_writebuf(struct sbuf *buf, const struct jvst_vm_program *prog);

void
jvst_vm_dump(FILE *f, const struct jvst_vm_program *prog);

void
jvst_vm_print(const struct jvst_vm_program *prog);

struct jvst_vm {
	struct jvst_vm_program *prog;
	size_t maxstack;
	uint64_t *stack;

	// builtin registers
	uint32_t pc;
	uint32_t m;
	uint32_t fp;
	uint32_t sp;
	uint32_t ireg[8];
	double   freg[8];

	struct sjp_parser parser;
};


#endif /* VALIDATE_VM_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
