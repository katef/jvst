#ifndef JVST_VALIDATE_IR_H
#define JVST_VALIDATE_IR_H

#include <stdint.h>

#include "sjp_parser.h"

// IR has two components: statements and expressions

// Statements
enum jvst_ir_stmt_type {
	JVST_IR_STMT_INVALID	= -1,	// INVALID(code,mesg) returns that current frame is invalid with an error message

	JVST_IR_STMT_NOP	=  0,	// nop statement.  does nothing.
	JVST_IR_STMT_VALID,		// returns that frame is valid, stops further execution of the frame.

	JVST_IR_STMT_IF,		// IF(expr<bool>, child1, child2).  if expr is true, evaluates form1, otherwise child2.
	JVST_IR_STMT_LOOP,		// LOOP(name, stmt...).  Executes children in a loop.  To exit, either evaluate 
					//                 VALID/INVALID or JUMP to a label outside of the loop.

	JVST_IR_STMT_SEQ,		// Children must be statements.  Runs sequence.

	JVST_IR_STMT_BREAK,		// BREAK(name). Exits named loop.

	JVST_IR_STMT_TOKEN,		// requests the next token
	JVST_IR_STMT_CONSUME,		// consumes the next value, including whole objects and arrays

	JVST_IR_STMT_FRAME,		// sets up a new frame

	JVST_IR_STMT_COUNTER,		// allocates a named counter in the current frame
	JVST_IR_STMT_MATCHER,		// allocates a named matcher state in the current frame
	JVST_IR_STMT_BITVECTOR,		// allocates a bitvector in the current frame

	JVST_IR_STMT_BSET,		// sets a bit in a bitmask
	JVST_IR_STMT_BCLEAR,		// sets a bit in a bitmask
	JVST_IR_STMT_INCR,		// increments a counter
	JVST_IR_STMT_DECR,		// increments a counter

	JVST_IR_STMT_MATCH,		// matches a string token against a matcher.
					// the matcher must be declared at the
					// start of the frame
					//
					// MATCH children should be MCASE nodes

};

// expressions
enum jvst_ir_expr_type {
	JVST_IR_EXPR_NONE = 0,

	// literal values
	JVST_IR_EXPR_NUM,		// literal number
	JVST_IR_EXPR_SIZE,		// literal size
	JVST_IR_EXPR_BOOL,		// literal boolean

	JVST_IR_EXPR_TOK_TYPE,		// tok:  token type of the current token
	JVST_IR_EXPR_TOK_NUM,		// num:  number value of the current token
	JVST_IR_EXPR_TOK_COMPLETE,	// bool: is the token complete?
	JVST_IR_EXPR_TOK_LEN,		// size: length of current token

	JVST_IR_EXPR_COUNT, 		// counter value.  args: index; result: size
	JVST_IR_EXPR_BTEST,		// tests if a bit is set.  args: (bvec<index>,bit<index>); result: bool

	JVST_IR_EXPR_ISTOK,		// tests curernt token type.  args: tok_type; result: bool

	// logical AND/OR operators.  args: (bool, bool); result: bool
	JVST_IR_EXPR_AND,
	JVST_IR_EXPR_OR,

	// logical NOT operator.  arg: bool; result: bool
	JVST_IR_EXPR_NOT,

	// comparison operators.  args: (size,size) or (num,num); result: bool
	// for the below operators, the arguments are OP(A,B)
	JVST_IR_EXPR_NE,		// A != B
	JVST_IR_EXPR_LT,		// A <  B
	JVST_IR_EXPR_LE,		// A <= B
	JVST_IR_EXPR_EQ,		// A == B
	JVST_IR_EXPR_GE,		// A >= B
	JVST_IR_EXPR_GT,		// A >  B

	JVST_IR_EXPR_ISINT,		// tests if number is an integer.  arg: num; result: bool

	JVST_IR_EXPR_SPLIT,		// SPLITs the validator.  each sub-validator moves in lock-step.
					// children must be FRAMEs.  result is the number of FRAMEs that
					// return valid.
};

enum jvst_invalid_code {
	JVST_INVALID_UNEXPECTED_TOKEN = 0x0001,
	JVST_INVALID_NOT_INTEGER      = 0x0002,
	JVST_INVALID_NUMBER           = 0x0003,
};

const char *
jvst_invalid_msg(enum jvst_invalid_code code);

struct jvst_ir_expr;
struct jvst_ir_label;

struct jvst_ir_mcase {
	struct jvst_ir_mcase *next;
	size_t which;
	struct jvst_ir_stmt *stmt;
};

struct jvst_ir_frame {
	struct jvst_ir_stmt *counters;
	struct jvst_ir_stmt *matchers;
	struct jvst_ir_stmt *stmts;
	size_t nloops;
	size_t nmatchers;
};

struct jvst_ir_stmt {
	enum jvst_ir_stmt_type type;

	struct jvst_ir_stmt *next;
	struct jvst_ir_stmt *parent;

	union {
		struct {
			int code;
			const char *msg;
		} invalid;

		struct {
			struct jvst_ir_expr *cond;
			struct jvst_ir_stmt *br_true;
			struct jvst_ir_stmt *br_false;
		} if_;

		struct jvst_ir_stmt *stmt_list;

		struct {
			const char *name;
			size_t ind;
			struct jvst_ir_stmt *loop;
		} break_;

		struct {
			const char *name;
			size_t ind;
			struct jvst_ir_stmt *stmts;
		} loop;

		struct jvst_ir_frame frame;

		struct {
			struct jvst_ir_label *label;
			struct jvst_ir_frame *frame;
			size_t ind;
		} counter;

		struct {
			struct fsm *dfa;
			const char *name;
			size_t ind;
		} matcher;

		struct {
			struct jvst_ir_label *label;
			struct jvst_ir_frame *frame;
			size_t ind;
		} bitvector;

		size_t index;

		struct {
			struct fsm *dfa;
			const char *name;
			size_t ind;
			struct jvst_ir_mcase *cases;
			struct jvst_ir_stmt  *default_case;
		} match;
	} u;
};

struct jvst_ir_expr {
	enum jvst_ir_expr_type type;

	union {
		// literals
		double vnum;
		size_t vsize;
		int vbool;

		struct {
			size_t counter;
		} count;

		struct {
			size_t bvec;
			size_t bit_index;
		} btest;

		struct {
			enum SJP_EVENT tok_type;
		} istok;

		struct {
			struct jvst_ir_expr *left;
			struct jvst_ir_expr *right;
		} and_or;

		struct jvst_ir_expr *not_;

		struct {
			struct jvst_ir_expr *left;
			struct jvst_ir_expr *right;
		} cmp;

		struct {
			struct jvst_ir_expr *arg;
		} isint;

		struct {
			struct jvst_ir_stmt *frames;
		} split;
	} u;
};

struct jvst_cnode;

struct jvst_ir_stmt *
jvst_ir_translate(struct jvst_cnode *ctree);

int
jvst_ir_dump(struct jvst_ir_stmt *ir, char *buf, size_t nb);

const char *
jvst_ir_expr_type_name(enum jvst_ir_expr_type type);

const char *
jvst_ir_stmt_type_name(enum jvst_ir_stmt_type type);

#endif /* JVST_VALIDATE_IR_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
