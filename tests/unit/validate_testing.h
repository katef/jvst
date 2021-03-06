#ifndef TESTING_H
#define TESTING_H

#include <stdio.h>

#include "sjp_parser.h"

#include "jdom.h"
#include "ast.h"

#include "validate_constraints.h"
#include "validate_ir.h"
#include "validate_op.h"

extern int ntest;
extern int nfail;
extern int nskipped;

struct arena_info {
	size_t nschema;
	size_t nprop;
	size_t nstr;
	size_t npnames;
	size_t nset;

	/* json value related, for const/enum tests */
	size_t njson;
	size_t njsonelt;  // json array elements
	size_t njsonprop; // json object properties
	size_t nvset;

	/* cnode related */
	size_t ncnode;
	size_t nmatchsets;
	size_t nids;

        /* IR related */
        size_t nstmt;
        size_t nexpr;
	size_t nmcases;
	size_t nsplitinds;

	size_t nirpairs;

	/* OP related */
	size_t nprog;
	size_t nproc;
	size_t ninstr;
	size_t nfloat;
	size_t nconst;
	size_t nsplit;
	size_t nsplitoff;

	size_t nvmprog;
	size_t nvmcode;
};

struct id_pair {
	struct id_pair *next;
	const char *id;
	struct jvst_cnode *cnode;
};

struct ir_pair {
	struct ir_pair *next;
	const char *id;
	struct jvst_ir_stmt *ir;
};


/** AST related **/

struct ast_schema *
empty_schema(struct arena_info *A);

struct ast_schema *
true_schema(struct arena_info *A);

struct ast_schema *
false_schema(struct arena_info *A);

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

struct ast_property_schema *
newpatternprops(struct arena_info *A, ...);

struct ast_property_names *
newpropnames(struct arena_info *A, ...);


/** JSON values **/
struct json_value *
newjson_num(struct arena_info *A, double x);

struct json_value *
newjson_str(struct arena_info *A, const char *s);

struct json_value *
newjson_array(struct arena_info *A, ...);

struct json_value *
newjson_object(struct arena_info *A, ...);

struct json_value *
newjson_bool(struct arena_info *A, int b);

struct json_value *
newjson_null(struct arena_info *A);


/** cnodes related **/

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
newcnode_prop_default(struct arena_info *A, struct jvst_cnode *dft); 

struct jvst_cnode *
newcnode_propnames(struct arena_info *A, struct jvst_cnode *tree);

struct jvst_cnode *
newcnode_bool(struct arena_info *A, enum jvst_cnode_type type, ...);

struct jvst_cnode *
newcnode_range(struct arena_info *A, enum jvst_cnode_rangeflags flags, double min, double max);

struct jvst_cnode *
newcnode_multiple_of(struct arena_info *A, double divisor);

struct jvst_cnode *
newcnode_counts(struct arena_info *A, enum jvst_cnode_type type,
	size_t min, size_t max, bool upper);

struct jvst_cnode *
newcnode_strmatch(struct arena_info *A, enum re_dialect dialect, const char *pat);

struct jvst_cnode *
newcnode_items(struct arena_info *A, struct jvst_cnode *additional, ...);

struct jvst_cnode *
newcnode_contains(struct arena_info *A, struct jvst_cnode *top);

struct jvst_cnode *
newcnode_valid(void);

struct jvst_cnode *
newcnode_invalid(void);

struct jvst_cnode *
newcnode_required(struct arena_info *A, struct ast_string_set *sset);

struct jvst_cnode *
newcnode_reqmask(struct arena_info *A, size_t nbits);

struct jvst_cnode *
newcnode_reqbit(struct arena_info *A, size_t bit);

extern const struct jvst_cnode *const mswitch_str_constraints;

struct jvst_cnode *
newcnode_mswitch(struct arena_info *A, struct jvst_cnode *dft, ...);

struct jvst_cnode *
newcnode_mcase(struct arena_info *A, struct jvst_cnode_matchset *mset,
	struct jvst_cnode *vconstraint);

struct jvst_cnode_matchset *
newmatchset(struct arena_info *A, ...);

struct jvst_cnode *
newcnode_ref(struct arena_info *A, const char *id);

/** cnode id related **/
struct id_pair *
new_idpair(struct arena_info *A, const char *id, struct jvst_cnode *ctree);

struct id_pair *
new_idpair_manyids(struct arena_info *A, struct jvst_cnode *ctree, ...);

struct id_pair *
new_idpairs(struct id_pair *first, ...);


/** IR-related **/

extern const struct jvst_ir_stmt *const frameindex;
extern const struct jvst_ir_stmt *const splitlist;

struct jvst_ir_stmt *
newir_stmt(struct arena_info *A, enum jvst_ir_stmt_type type);

struct jvst_ir_expr *
newir_expr(struct arena_info *A, enum jvst_ir_expr_type type);

struct jvst_ir_stmt *
newir_invalid(struct arena_info *A, int code, const char *msg);

struct jvst_ir_stmt *
newir_frame(struct arena_info *A, ...);

struct jvst_ir_stmt *
newir_program(struct arena_info *A, ...);

struct jvst_ir_stmt *
newir_seq(struct arena_info *A, ...);

struct jvst_ir_stmt *
newir_block(struct arena_info *A, size_t lind, const char *prefix, ...);

struct jvst_ir_stmt *
newir_loop(struct arena_info *A, const char *loopname, size_t ind, ...);

struct jvst_ir_stmt *
newir_break(struct arena_info *A, const char *loopname, size_t ind);

struct jvst_ir_stmt *
newir_if(struct arena_info *A, struct jvst_ir_expr *cond,
	struct jvst_ir_stmt *br_true, struct jvst_ir_stmt *br_false);

struct jvst_ir_stmt *
newir_counter(struct arena_info *A, size_t ind, const char *label);

struct jvst_ir_stmt *
newir_matcher(struct arena_info *A, size_t ind, const char *name);

struct jvst_ir_stmt *
newir_bitvec(struct arena_info *A, size_t ind, const char *label, size_t nbits);

struct jvst_ir_stmt *
newir_match(struct arena_info *A, size_t ind, ...);

struct jvst_ir_stmt *
newir_splitlist(struct arena_info *A, size_t ind, size_t n, ...);

struct jvst_ir_stmt *
newir_splitvec(struct arena_info *A, size_t ind, const char *label, ...);

struct jvst_ir_stmt *
newir_incr(struct arena_info *A, size_t ind, const char *label);

struct jvst_ir_stmt *
newir_bitop(struct arena_info *A, enum jvst_ir_stmt_type op, size_t ind, const char *label, size_t bit);

struct jvst_ir_stmt *
newir_branch(struct arena_info *A, size_t lind, const char *prefix);

struct jvst_ir_stmt *
newir_cbranch(struct arena_info *A, struct jvst_ir_expr *cond,
	size_t tind, const char *tprefix,
	size_t find, const char *fprefix);

struct jvst_ir_stmt *
newir_move(struct arena_info *A, struct jvst_ir_expr *tmp, struct jvst_ir_expr *expr);

struct jvst_ir_stmt *
newir_call(struct arena_info *A, size_t frame_ind);

struct jvst_ir_stmt *
newir_callid(struct arena_info *A, const char *id);

struct ir_pair *
new_irpair(struct arena_info *A, const char *id, struct jvst_ir_stmt *ir);

struct ir_pair *
new_irpairs(struct arena_info *A, ...);

struct jvst_ir_mcase *
newir_case(struct arena_info *A, size_t ind, struct jvst_cnode_matchset *mset, struct jvst_ir_stmt *frame);

struct jvst_ir_expr *
newir_istok(struct arena_info *A, enum SJP_EVENT tt);

struct jvst_ir_expr *
newir_isint(struct arena_info *A, struct jvst_ir_expr *arg);

struct jvst_ir_expr *
newir_multiple_of(struct arena_info *A, struct jvst_ir_expr *arg, double divisor);

struct jvst_ir_expr *
newir_op(struct arena_info *A, enum jvst_ir_expr_type op,
		struct jvst_ir_expr *left,
		struct jvst_ir_expr *right);

struct jvst_ir_expr *
newir_num(struct arena_info *A, double num);

struct jvst_ir_expr *
newir_size(struct arena_info *A, size_t sz);

struct jvst_ir_expr *
newir_count(struct arena_info *A, size_t ind, const char *label);

struct jvst_ir_expr *
newir_btest(struct arena_info *A, size_t ind, const char *label, size_t b);

struct jvst_ir_expr *
newir_btestall(struct arena_info *A, size_t ind, const char *label, size_t b0, size_t b1);

struct jvst_ir_expr *
newir_btestany(struct arena_info *A, size_t ind, const char *label, size_t b0, size_t b1);

struct jvst_ir_expr *
newir_split(struct arena_info *A, ...);

struct jvst_ir_expr *
newir_ftemp(struct arena_info *A, size_t ind);

struct jvst_ir_expr *
newir_itemp(struct arena_info *A, size_t ind);

struct jvst_ir_expr *
newir_slot(struct arena_info *A, size_t ind);

struct jvst_ir_expr *
newir_eseq(struct arena_info *A, struct jvst_ir_stmt *stmt, struct jvst_ir_expr *expr);

struct jvst_ir_expr *
newir_ematch(struct arena_info *A, size_t mind);


/* OP related */

struct jvst_op_program *
newop_program(struct arena_info *A, ...);

struct jvst_op_proc *
newop_proc(struct arena_info *A, ...);

struct jvst_op_instr *
newop_instr(struct arena_info *A, enum jvst_vm_op op);

struct jvst_op_instr *
newop_cmp(struct arena_info *A, enum jvst_vm_op op,
	struct jvst_op_arg arg1, struct jvst_op_arg arg2);

struct jvst_op_instr *
newop_load(struct arena_info *A, enum jvst_vm_op op,
	struct jvst_op_arg arg1, struct jvst_op_arg arg2);

struct jvst_op_instr *
newop_br(struct arena_info *A, enum jvst_vm_br_cond brc, const char *label);

struct jvst_op_instr *
newop_match(struct arena_info *A, int64_t dfa);

struct jvst_op_instr *
newop_call(struct arena_info *A, struct jvst_op_arg dest);

struct jvst_op_instr *
newop_incr(struct arena_info *A, size_t slot);

struct jvst_op_instr *
newop_return(struct arena_info *A, enum jvst_invalid_code ecode);

struct jvst_op_instr *
newop_bitop(struct arena_info *A, enum jvst_vm_op op, int frame_off, int bit);

struct jvst_op_instr *
newop_instr2(struct arena_info *A, enum jvst_vm_op op,
	struct jvst_op_arg arg1, struct jvst_op_arg arg2);

extern const struct jvst_op_instr *const oplabel;
extern const struct jvst_op_instr *const opslots;
extern const struct jvst_op_proc *const opfloat;
extern const struct jvst_op_proc *const opconst;
extern const struct jvst_op_proc *const opsplit;
extern const struct jvst_op_proc *const opdfa;

static inline struct jvst_op_arg 
oparg_make(enum jvst_op_arg_type type, int64_t ind) {
	struct jvst_op_arg arg = { 
		.type = type,
		.u = { .index = ind },
	};
	return arg;
}

static inline struct jvst_op_arg 
oparg_none(void) { return oparg_make(JVST_VM_ARG_NONE,0); }

static inline struct jvst_op_arg 
oparg_tt(void) { return oparg_make(JVST_VM_ARG_TT,0); }

static inline struct jvst_op_arg 
oparg_tnum(void) { return oparg_make(JVST_VM_ARG_TNUM,0); }

static inline struct jvst_op_arg 
oparg_m(void) { return oparg_make(JVST_VM_ARG_M,0); }

static inline struct jvst_op_arg 
oparg_lit(int64_t v) { return oparg_make(JVST_VM_ARG_CONST,v); }

static inline struct jvst_op_arg 
oparg_tok(enum SJP_EVENT evt) { return oparg_make(JVST_VM_ARG_TOKTYPE,evt); }

static inline struct jvst_op_arg 
oparg_slot(int n) { return oparg_make(JVST_VM_ARG_SLOT,n); }


/* VM opcode related */
enum {
	VM_END    = -1,
	VM_LABEL  = -2,
	VM_FLOATS = -3,
	VM_DFA    = -4,
	VM_SPLIT  = -5,
};

struct jvst_vm_program *
newvm_program(struct arena_info *A, ...);

const char *
jvst_ret2name(int ret);

int
report_tests(void);

void
buffer_diff(FILE *f, const char *buf1, const char *buf2, size_t n);

void
print_buffer_with_lines(FILE *f, const char *buf, size_t n);

int
cnode_trees_equal(const char *fname, struct jvst_cnode *n1, struct jvst_cnode *n2);

#endif /* TESTING_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
