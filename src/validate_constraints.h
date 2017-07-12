#ifndef VALIDATE_CONSTRAINTS_H
#define VALIDATE_CONSTRAINTS_H

#include "sjp_parser.h"
#include "ast.h"

#define MODULE_NAME VALIDATE_CONSTRAINTS

/* simplified tree of validation constraints
 *
 * This differs from the AST as follows:
 *
 * 1. Nodes are either control, token-switch, or constraint.
 *
 *    a) Control nodes: logical (AND/OR/NOT) with children, or
 *       VALID/INVALID leaf nodes
 *
 *    b) Token-switch: nine children corresponding to the event types of
 *       the SJP parser
 *
 *    c) Constraint: each constraint node is for a particular type
 *       (null/true/false, string, number, object, array) and specifies
 *       validation constraints for that specific type.
 *
 * 2. There is one validation constraint per constraint node.
 *
 */

enum jvst_cnode_rangeflags {
	JVST_CNODE_RANGE_MIN      = (1 << 0),
	JVST_CNODE_RANGE_MAX      = (1 << 1),
	JVST_CNODE_RANGE_EXCL_MIN = (1 << 2),
	JVST_CNODE_RANGE_EXCL_MAX = (1 << 3),
};

enum jvst_cnode_type {
	/* Control nodes */
	JVST_CNODE_INVALID = 0, // node always returns invalid
	JVST_CNODE_VALID,       // node always returns valid

	JVST_CNODE_AND, // requires all nodes to be valid
	JVST_CNODE_OR,  // requires at least one node to be valid
	JVST_CNODE_XOR, // requires exactly one node to be valid
	JVST_CNODE_NOT,

	/* Token-switch node */
	JVST_CNODE_SWITCH,

	/* range for string lengths, number of object properties, number of
	 * array items */
	JVST_CNODE_COUNT_RANGE,

	/* Constraint nodes */
	JVST_CNODE_STR_MATCH,

	JVST_CNODE_NUM_RANGE,
	JVST_CNODE_NUM_INTEGER,

	JVST_CNODE_OBJ_PROP_SET,
	JVST_CNODE_OBJ_PROP_MATCH,

	JVST_CNODE_OBJ_REQUIRED,
	// JVST_CNODE_OBJ_REQMASK,
	// JVST_CNODE_OBJ_REQBIT,

	JVST_CNODE_ARR_ITEM,
	JVST_CNODE_ARR_ADDITIONAL,
	JVST_CNODE_ARR_UNIQUE,

	// Nodes used in optimization/simplification to reduce the
	// complexity of matching.
	//
	// After a DFA is created, MATCH_SWITCH holds the overall
	// matching, while MATCH_CASE holds the unique matching
	// endstates
	JVST_CNODE_MATCH_SWITCH,
	JVST_CNODE_MATCH_CASE,
};

struct jvst_cnode_matchset {
	struct jvst_cnode_matchset *next;
	struct ast_regexp match;
};

struct jvst_cnode {
	enum jvst_cnode_type type;

	struct jvst_cnode *next;

	union {
		/* type switch node */
		struct jvst_cnode *sw[SJP_EVENT_MAX];

		/* control nodes */
		struct jvst_cnode *ctrl;

		/* constraint for string length, array length,
		 * number of object properties
		 */
		struct {
			size_t min;
			size_t max; // 0 indicates no upper bound
		} counts;

		/* for string pattern matching or matching string sets */
		struct ast_regexp str_match;

		/* for number ranges */
		struct {
			enum jvst_cnode_rangeflags flags;
			double min;
			double max;
		} num_range;

		/* support for required properties */
		struct ast_string_set *required;

		struct jvst_cnode *prop_set;

		/* object property constraints */
		struct {
			struct ast_regexp match;
			struct jvst_cnode *constraint;
		} prop_match;

		// for array item and additional_item constraints
		struct jvst_cnode *arr_item;

		/* Nodes used for simplifying property matching */
		struct {
			struct jvst_cnode *default_case;
			struct jvst_cnode *cases;
			struct fsm *dfa;
			struct fsm_options *opts;
		} mswitch;

		struct {
			struct jvst_cnode_matchset *matchset;
			struct jvst_cnode *constraint;

			// temp storage used in duplication
			struct jvst_cnode *tmp;
		} mcase;

		/* Nodes used for simplifying required properties */
		/*
		struct {
			size_t nbits;
		} reqmask;

		struct {
			size_t bit;
		} reqbit;
		*/

	} u;
};

struct jvst_cnode *
jvst_cnode_alloc(enum jvst_cnode_type type);

void
jvst_cnode_free(struct jvst_cnode *n);

void
jvst_cnode_free_tree(struct jvst_cnode *n);

const char *
jvst_cnode_type_name(enum jvst_cnode_type type);

// Translates the AST into a contraint tree and optimizes the constraint
// tree
struct jvst_cnode *
jvst_cnode_from_ast(struct ast_schema *ast);

// Just do a raw translation without doing any optimization of the
// constraint tree
struct jvst_cnode *
jvst_cnode_translate_ast(struct ast_schema *ast);

// Optimize the cnode tree.  Returns a new tree.
struct jvst_cnode *
jvst_cnode_optimize(struct jvst_cnode *tree);

// Writes a textual represetnation of the cnode into the buffer,
// returns 0 if the representation fit, non-zero otherwise
int
jvst_cnode_dump(struct jvst_cnode *node, char *buf, size_t nb);

// for debugging, prints node to stderr
void
jvst_cnode_print(struct jvst_cnode *node);

#undef MODULE_NAME

#endif /* VALIDATE_CONSTRAINTS_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */

