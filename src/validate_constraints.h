#ifndef VALIDATE_CONSTRAINTS_H
#define VALIDATE_CONSTRAINTS_H

#include <stdio.h>

#include "sjp_parser.h"
#include "ast.h"
#include "idtbl.h"

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

	/* ranges for string lengths, number of object properties, number of
	 * array items */
	JVST_CNODE_LENGTH_RANGE,
	JVST_CNODE_PROP_RANGE,
	JVST_CNODE_ITEM_RANGE,

	/* Constraint nodes */
	JVST_CNODE_STR_MATCH,

	JVST_CNODE_NUM_RANGE,
	JVST_CNODE_NUM_INTEGER,
	JVST_CNODE_NUM_MULTIPLE_OF,

	JVST_CNODE_OBJ_PROP_SET,
	JVST_CNODE_OBJ_PROP_MATCH,
	JVST_CNODE_OBJ_PROP_DEFAULT,
	JVST_CNODE_OBJ_PROP_NAMES,

	JVST_CNODE_OBJ_REQUIRED,

	JVST_CNODE_ARR_ITEM,
	JVST_CNODE_ARR_ADDITIONAL,
	JVST_CNODE_ARR_UNIQUE,
	JVST_CNODE_ARR_CONTAINS,

	JVST_CNODE_REF,

	// The following node types are only present after
	// canonification.

	// During first pass at canonification, transform REQUIRED nodes
	// into REQMASK/REQBIT nodes
	JVST_CNODE_OBJ_REQMASK,
	JVST_CNODE_OBJ_REQBIT,

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
			size_t max;

			unsigned upper:1; // indicates if max is an upper bound
		} counts;

		/* for string pattern matching or matching string sets */
		struct ast_regexp str_match;

		/* for number ranges */
		struct {
			enum jvst_cnode_rangeflags flags;
			double min;
			double max;
		} num_range;

		/* for multipleOf constraints */
		double multiple_of;

		/* support for required properties */
		struct ast_string_set *required;

		struct jvst_cnode *prop_set;

		/* object property constraints */
		struct {
			struct ast_regexp match;
			struct jvst_cnode *constraint;
		} prop_match;

		struct jvst_cnode *prop_default;
		struct jvst_cnode *prop_names;

		/* Nodes used for simplifying property matching */
		struct {
			struct jvst_cnode *dft_case;
			struct jvst_cnode *cases;

			struct fsm *dfa;
			struct fsm_options *opts;
		} mswitch;

		struct {
			struct jvst_cnode_matchset *matchset;
			struct jvst_cnode *name_constraint;
			struct jvst_cnode *value_constraint;

			// temp storage used in duplication
			void *tmp;

			unsigned collected:1;
			unsigned copied:1;
		} mcase;

		/* Nodes used for simplifying required properties */
		struct {
			size_t nbits;
		} reqmask;

		struct {
			// XXX - do we need to refer to parent to keep
			//       the bit numbering consistent?
			//
			//       consider: two ANDed REQUIRED nodes.
			//       we *could* require them to be merged
			//       before transforming them into
			//       reqmask/reqbit nodes.  This would
			//       require splitting the canonify stage
			//       into two parts.
			size_t bit;
		} reqbit;

		// for array item and additional_item constraints
		struct jvst_cnode *items;

		// for array contains constraint
		struct jvst_cnode *contains;

		struct json_string ref;
	} u;
};

struct jvst_id_table;

struct jvst_cnode *
jvst_cnode_alloc(enum jvst_cnode_type type);

void
jvst_cnode_free(struct jvst_cnode *n);

void
jvst_cnode_free_tree(struct jvst_cnode *n);

const char *
jvst_cnode_type_name(enum jvst_cnode_type type);

// Translates the AST into a contraint tree, first simplifying and
// canonifying the constraint tree
struct jvst_cnode *
jvst_cnode_from_ast(const struct ast_schema *ast);

// Just do a raw translation without doing any optimization of the
// constraint tree
//
// If tbl is not NULL, builds an id -> cnode table.
struct jvst_cnode_forest *
jvst_cnode_translate_ast_with_ids(const struct ast_schema *ast);

// Backwards-compatible version of the above while we migrate code/tests
struct jvst_cnode *
jvst_cnode_translate_ast(const struct ast_schema *ast);

// Simplfies the cnode tree.  Returns a new tree.
struct jvst_cnode *
jvst_cnode_simplify(struct jvst_cnode *tree);

// Canonifies the cnode tree.  Returns a new tree.
struct jvst_cnode *
jvst_cnode_canonify(struct jvst_cnode *tree);

// Writes a textual represetnation of the cnode into the buffer,
// returns 0 if the representation fit, non-zero otherwise
int
jvst_cnode_dump(struct jvst_cnode *node, char *buf, size_t nb);

// for debugging, prints node to stderr
void
jvst_cnode_print(FILE *f, struct jvst_cnode *node);

// for debugging, prints node to stderr
void
jvst_cnode_debug(struct jvst_cnode *node);

struct jvst_id_table;

struct jvst_id_table *
jvst_id_table_new(void);

void
jvst_id_table_delete(struct jvst_id_table *tbl);

struct jvst_cnode *
jvst_id_table_lookup(struct jvst_id_table *tbl, struct json_string s);

struct jvst_cnode *
jvst_id_table_lookup_cstr(struct jvst_id_table *tbl, const char *s);

struct jvst_cnode *
jvst_id_table_lookup_with_len(struct jvst_id_table *tbl, const char *s, size_t n);

struct jvst_cnode_forest {
	size_t len;
	size_t cap;
	struct jvst_cnode **trees;
	struct jvst_id_table *all_ids;
	struct jvst_id_table *ref_ids;
};

struct jvst_cnode_forest *
jvst_cnode_forest_new(void);

void
jvst_cnode_forest_delete(struct jvst_cnode_forest *forest);

void
jvst_cnode_forest_initialize(struct jvst_cnode_forest *forest);

void
jvst_cnode_forest_finalize(struct jvst_cnode_forest *forest);

void
jvst_cnode_forest_add_tree(struct jvst_cnode_forest *forest, struct jvst_cnode *tree);

#endif /* VALIDATE_CONSTRAINTS_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */

