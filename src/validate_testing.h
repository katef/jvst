#ifndef TESTING_H
#define TESTING_H

#include "sjp_parser.h"

#include "jdom.h"
#include "ast.h"

#include "validate_constraints.h"
#include "validate_ir.h"

extern int ntest;
extern int nfail;
extern int nskipped;

struct arena_info {
	size_t nschema;
	size_t nprop;
	size_t nstr;
	size_t npnames;
	size_t nset;

	/* cnode related */
	size_t ncnode;
	size_t nmatchsets;

        /* IR related */
        size_t nstmt;
        size_t nexpr;
	size_t nmcases;
};

struct ast_schema *
empty_schema(void);

struct ast_schema *
newschema(struct arena_info *A, int types);

struct ast_schema *
newschema_p(struct arena_info *A, int types, ...);

struct json_string
newstr(const char *s);

struct ast_string_set *
stringset(struct arena_info *A, ...);

struct ast_schema_set *
schema_set(struct arena_info *A, ...);

size_t
schema_set_count(struct ast_schema_set *s);

struct ast_property_schema *
newprops(struct arena_info *A, ...);

struct ast_property_names *
newpropnames(struct arena_info *A, ...);

struct jvst_cnode *
newcnode(struct arena_info *A, enum jvst_cnode_type type);

struct jvst_cnode *
newcnode_switch(struct arena_info *A, int isvalid, ...);

struct jvst_cnode *
newcnode_prop_match(struct arena_info *A, enum re_dialect dialect, const char *pat,
		    struct jvst_cnode *constraint);

struct jvst_cnode *
newcnode_propset(struct arena_info *A, ...);

struct jvst_cnode *
newcnode_bool(struct arena_info *A, enum jvst_cnode_type type, ...);

struct jvst_cnode *
newcnode_range(struct arena_info *A, enum jvst_cnode_rangeflags flags, double min, double max);

struct jvst_cnode *
newcnode_counts(struct arena_info *A, size_t min, size_t max);

struct jvst_cnode *
newcnode_valid(void);

struct jvst_cnode *
newcnode_invalid(void);

struct jvst_cnode *
newcnode_required(struct arena_info *A, struct ast_string_set *sset);

struct jvst_cnode *
newcnode_mswitch(struct arena_info *A, struct jvst_cnode *dft, ...);

struct jvst_cnode *
newcnode_mcase(struct arena_info *A, struct jvst_cnode_matchset *mset,
	struct jvst_cnode *constraint);

struct jvst_cnode_matchset *
newmatchset(struct arena_info *A, ...);


/* IR-related */
struct jvst_ir_stmt *
newir_stmt(struct arena_info *A, enum jvst_ir_stmt_type type);

struct jvst_ir_expr *
newir_expr(struct arena_info *A, enum jvst_ir_expr_type type);

struct jvst_ir_stmt *
newir_invalid(struct arena_info *A, int code, const char *msg);

struct jvst_ir_stmt *
newir_frame(struct arena_info *A, ...);

struct jvst_ir_stmt *
newir_seq(struct arena_info *A, ...);

struct jvst_ir_stmt *
newir_loop(struct arena_info *A, const char *loopname, size_t ind, ...);

struct jvst_ir_stmt *
newir_break(struct arena_info *A, const char *loopname, size_t ind);

struct jvst_ir_stmt *
newir_if(struct arena_info *A, struct jvst_ir_expr *cond,
	struct jvst_ir_stmt *br_true, struct jvst_ir_stmt *br_false);

struct jvst_ir_stmt *
newir_matcher(struct arena_info *A, size_t ind, const char *name);

struct jvst_ir_stmt *
newir_match(struct arena_info *A, size_t ind, ...);

struct jvst_ir_mcase *
newir_case(struct arena_info *A, size_t ind, struct jvst_cnode_matchset *mset, struct jvst_ir_stmt *frame);

struct jvst_ir_expr *
newir_istok(struct arena_info *A, enum SJP_EVENT tt);

struct jvst_ir_expr *
newir_isint(struct arena_info *A, struct jvst_ir_expr *arg);

struct jvst_ir_expr *
newir_op(struct arena_info *A, enum jvst_ir_expr_type op,
		struct jvst_ir_expr *left,
		struct jvst_ir_expr *right);

struct jvst_ir_expr *
newir_num(struct arena_info *A, double num);

const char *
jvst_ret2name(int ret);

int
report_tests(void);

#endif /* TESTING_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
