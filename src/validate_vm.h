#ifndef VALIDATE_VM_H
#define VALIDATE_VM_H

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

#include "jvst_macros.h"
#include "validate.h"
#include "validate_sbuf.h"

#include "sjp_parser.h"

// Registers are just slots that are always allocated at the top of the stack framae
enum jvst_vm_register {
	// values used to return from a CALL
	JVST_VM_TT,		// type of current token
	JVST_VM_TNUM,		// floating point value of current token (if %TT is $NUMBER)
	JVST_VM_TLEN,		// length of current token (if %TT is $STRING)
	JVST_VM_M,		// Match case register
};
#define JVST_VM_NUMREG (JVST_VM_M+1)

enum jvst_vm_op {
	JVST_OP_NOP	= 0,
	JVST_OP_PROC,		// FRAME N sets up a call frame and reserves N 64-bit slots on the call stack

	// Integer and float comparisons.  xCMP(slot, slot_or_const)
	// These set the FLAGS register to:
	// 	-1	arg0 < arg1
	// 	 0	arg0 = arg1
	// 	+1	arg0 > arg1
	//
	JVST_OP_ICMP,
	JVST_OP_FCMP,

	JVST_OP_FINT,		// Checks if a float value in a slot is an integer.
				// args: slot.  result: isnormal(reg) && (reg == ceil(reg)).
				// FLAGS should have a non-zero value on success, a zero value on failure.

	JVST_OP_JMP,		// Branch, the branch interprets the FLAGS register based on the condition arg:
				// 
				// Arg	FlagBits	Value	Behavior
				// NV   000             0       Never jump (NOP)
				// LT	001		1	Jump if FLAGS <  0
				// LE	101		5	Jump if FLAGS <= 0
				// EQ	100		4	Jump if FLAGS == 0
				// GE	110		6	Jump if FLAGS >= 0
				// GT	010		2	Jump if FLAGS >  0
				// NE	011		3	Jump if FLAGS >  0
				// UC	111		7	Unconditional (ignores FLAGS)
				//
				// If the leading bit is set, the test
				// is negated.

	JVST_OP_CALL,		// Calls into another proc.  Control will continue at the next 
				// instruction if the proc returns VALID.

	JVST_OP_SPLIT,		// SPLIT(split_ind, slot)
	JVST_OP_SPLITV,		// SPLITV(split_ind, slot0)

	JVST_OP_TOKEN,		// Loads the next token
	JVST_OP_CONSUME,	// Consumes the next value, including objects and arrays

	JVST_OP_MATCH,		// Matches the current string token: MATCH(dfa_index)

	// Loads proc constants into registers
	JVST_OP_FLOAD,		// Loads a float: FLOAD(fregO,const_index)	fregO = fconsts[const_index]
	JVST_OP_ILOAD,		// Loads a size/int: ILOAD(iregO,const_or_slot) slotO = iconsts[ind]

	JVST_OP_MOVE,		// Moves a slot to another slot

	JVST_OP_INCR,		// Increments a slot: INCR(ind,reg_or_const)	slot[ind] = slot[ind] + reg_or_const

	JVST_OP_BSET,		// Sets a bit. BSET(slotA,bit)

	JVST_OP_BAND,		// Bitwise-AND: BAND(regA,reg_slotB)  regA = regA & reg_slotB

	JVST_OP_RETURN,		// Returns VALID or raises an INVALID result.  INVALID results have an error code.

	JVST_OP_UNIQUE,		// Initializes UNIQUE data, finalizes UNIQUE data, or evaluates for UNIQUE
};

#define JVST_OP_MAX JVST_OP_RETURN

enum jvst_vm_br_cond {
	JVST_VM_BR_NEVER  = 0,           // bits: 000
	JVST_VM_BR_LT     = 0x01,        //       001
	JVST_VM_BR_LE     = 0x04 | 0x01, //       101
	JVST_VM_BR_EQ     = 0x04,        //       101
	JVST_VM_BR_GE     = 0x04 | 0x02, //       110
	JVST_VM_BR_GT     = 0x02,        //       010
	JVST_VM_BR_NE     = 0x01 | 0x02, //       011
	JVST_VM_BR_ALWAYS = 0x07,        // bits: 111
};

enum jvst_vm_unique_arg {
	JVST_VM_UNIQUE_INIT  = 0,
	JVST_VM_UNIQUE_EVAL  = 1,
	JVST_VM_UNIQUE_FINAL = 2,
};

/* VM opcode encoding:
 * 
 * Each non-branching opcode is a fixed 32-bits, encoded as follows:
 *
 * 01234567890123456789012345678901
 * IIIIIAAAAAAAAAAAAABBBBBBBBBBBBBB
 *
 * I - instruction
 * A - first argument (13 bits)
 * B - second argument (14 bits)
 *
 * Arguments are 13-bits that specify slots, small integer constants, or indexes into a
 * constant pool
 *
 * For FLOAD and ILOAD, A must be a slot and B must be an index into the constant
 * pool.
 *
 * For all other non-branching instructions, A and B can be either a slot or a constant
 *
 * 01234567890123
 * 0VVVVVVVVVVVVS	literal value V, with sign bit S
 * 1LLLLLLLLLLLLL	slot offset L (used for slots or temporaries)
 * 1IIIIIIIIIIIII	const pool index I
 *
 * Slots are positive and stored on the VM stack relative to %FP.
 * Currently 4096 slots are allowed in a single proc.
 *
 * V  - bits associated with the value
 * S  - value "sign" bit (for constants)
 *
 * Special encoding for branch instructions:
 *
 * 01234567890123456789012345678901
 * IIIIICCCAAAAAAAAAAAAAAAAAAAAAAAS
 *
 * Two arguments, a 3-bit condition (C) and a signed 24-bit branch
 * address (A)
 */

const char *
jvst_op_name(enum jvst_vm_op op);

const char *
jvst_vm_br_cond_name(enum jvst_vm_br_cond brc);

static inline enum jvst_vm_op
jvst_vm_decode_op(uint32_t op)
{
	STATIC_ASSERT(JVST_OP_MAX < 0x20, opcodes_fit_in_six_bits);
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

#define VMLIT(x)      (jvst_vm_arg_lit((x)))
#define VMSLOT(x)     (jvst_vm_arg_slot(JVST_VM_NUMREG + (x)))
#define VMREG(x)      (jvst_vm_arg_slot((x)))
#define VMOP(op,a,b)  (jvst_vm_encode2((op), (a), (b)))
#define VMBR(op,cond,addr) (jvst_vm_encodeb((op), (cond), (addr)))

static inline uint32_t
jvst_vm_decode_barg(uint32_t op)
{
	return (op >> 8) & 0xffffff;
}

static inline uint32_t
jvst_vm_decode_bcond(uint32_t op)
{
	return (op >> 5) & 0x7;
}

static inline int
jvst_vm_arg_isslot(uint32_t arg)
{
	return (arg & 1);
}

static inline int
jvst_vm_arg_ispool(uint32_t arg)
{
	return (arg & 1);
}

static inline int
jvst_vm_arg_islit(uint32_t arg)
{
	return (arg & 1) == 0;
}

static inline uint32_t
jvst_vm_arg_slot(int sl)
{
	return ((uint32_t)sl << 1) | 1;
}

static inline int
jvst_vm_arg_toslot(uint32_t arg)
{
	return (arg >> 1);
}

static inline uint32_t
jvst_vm_arg_pool(int p)
{
	return ((uint32_t)p << 1);
}

static inline int
jvst_vm_arg_topool(uint32_t arg)
{
	return (arg >> 1);
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
	return (raw<<1);
}

static inline int
jvst_vm_arg_tolit(uint32_t arg)
{
	int v = arg>>1;
	return (v & JVST_VM_LITSIGN) ? -((v-1) ^ JVST_VM_LITMASK) : v;
}

enum {
	JVST_VM_BARG_MIN  = -(1<<23),
	JVST_VM_BARG_MAX  = (1<<23)-1,
	JVST_VM_BARG_MASK = (1<<24)-1,
	JVST_VM_BARG_SIGN = (1<<23),
};

static inline uint32_t
jvst_vm_barg(long p)
{
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

static inline uint32_t
jvst_vm_encodeb(enum jvst_vm_op op, enum jvst_vm_br_cond brc, long rel)
{
	return (uint32_t)op | ((brc & 0x7) << 5) | (jvst_vm_barg(rel) << 8);
}

static inline uint32_t
jvst_vm_encode2(enum jvst_vm_op op, uint16_t a, uint16_t b)
{
	return (uint32_t)op | ((uint32_t)a << 5) | ((uint32_t)b << 18);
}

struct jvst_vm_dfa {
	size_t nstates;
	size_t nedges;
	size_t nends;

	int *offs;
	int *transitions;
	int *endstates;
};

size_t
jvst_vm_dfa_init(struct jvst_vm_dfa *dfa, size_t nstates, size_t nedges, size_t nends);

void
jvst_vm_dfa_copy(struct jvst_vm_dfa *dst, const struct jvst_vm_dfa *src);

enum {
	JVST_VM_DFA_START    =  0,
	JVST_VM_DFA_NOMATCH  = -1,
	JVST_VM_DFA_BADSTATE = -2,
};

/* Runs the DFA on the input in buf, starting with state st0.  Returns
 * the DFA state after consuming all input in buf, or
 * JVST_VM_DFA_NOMATCH if the DFA cannot match the input.
 *
 * The starting state is always zero.  st0 can be passed a value of
 * JVST_VM_DFA_NOMATCH as well, in which case the function will just
 * return.  If st0 is not a valid state or JVST_VM_DFA_NOMATCH, then
 * JVST_VM_DFA_BADSTATE will be returned.
 */
int
jvst_vm_dfa_run(const struct jvst_vm_dfa *dfa, int st0, const char *buf, size_t n);


/* Returns if st1 is a valid end state of the DFA.  If st1 is a valid
 * end state and datap is not NULL, *datap is set to the value
 * associated with the end state.
 */
bool
jvst_vm_dfa_endstate(const struct jvst_vm_dfa *dfa, int st1, int *datap);

void
jvst_vm_dfa_finalize(struct jvst_vm_dfa *dfa);

struct jvst_vm_program {
	size_t ncode;

	size_t nfloat;
	size_t nconst;
	size_t nsplit;
	size_t ndfa;

	double  *fdata;
	int64_t *cdata;
	uint32_t *sdata;
	struct jvst_vm_dfa *dfas;

	uint32_t *code;
};

struct jvst_vm_program *
jvst_vm_readfile(FILE *f);

struct jvst_vm_program *
jvst_vm_readbuf(const unsigned char *buf, size_t n);

int
jvst_vm_writefile(FILE *f, const struct jvst_vm_program *prog);

int
jvst_vm_program_writebuf(struct sbuf *buf, const struct jvst_vm_program *prog);

void
jvst_vm_program_print(FILE *f, const struct jvst_vm_program *prog);

int
jvst_vm_program_dump(const struct jvst_vm_program *prog, char *buf, size_t nb);

void
jvst_vm_program_debug(const struct jvst_vm_program *prog);

void
jvst_vm_program_free(struct jvst_vm_program *prog);


enum {
	JVST_VM_PARSER_STKSIZE = 4096,
	JVST_VM_PARSER_BUFSIZE = 4096,
};

enum jvst_vm_tokstate {
	JVST_VM_TOKEN_CONSUMED,
	JVST_VM_TOKEN_FETCH,
	JVST_VM_TOKEN_READY,
	JVST_VM_TOKEN_BUFFERED,
};

union jvst_vm_stackval {
	int64_t  i;
	uint64_t u;
	double   f;
};

struct jvst_vm_unique;

struct jvst_vm {
	struct jvst_vm_program *prog;

	size_t maxstack;
	union jvst_vm_stackval *stack;

	size_t nsplit;
	size_t maxsplit;
	struct jvst_vm *splits;

	// for consuming nested structures
	size_t nobj;
	size_t narr;

	struct sjp_parser parser;
	struct sjp_event evt;

	// machine state registers, when active they aren't stored on
	// the stack
	int64_t  r_flag;
	uint32_t r_pc;
	uint32_t r_fp;
	uint32_t r_sp;

	enum SJP_RESULT pret;
	int error;
	int dfa_st;
	enum jvst_vm_tokstate tokstate;
	int needtok;  // flag if the next call to vm_run_next should have a token

	char pstack[JVST_VM_PARSER_STKSIZE];
	char pbuf[JVST_VM_PARSER_BUFSIZE];

	struct jvst_vm_unique *uniq;
};

void
jvst_vm_init_defaults(struct jvst_vm *vm, struct jvst_vm_program *prog);

enum jvst_result
jvst_vm_more(struct jvst_vm *vm, char *data, size_t n);

enum jvst_result
jvst_vm_close(struct jvst_vm *vm);

void
jvst_vm_finalize(struct jvst_vm *vm);

void
jvst_vm_dumpstate(struct jvst_vm *vm);

#endif /* VALIDATE_VM_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
