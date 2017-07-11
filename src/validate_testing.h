#ifndef TESTING_H
#define TESTING_H

#include "jdom.h"
#include "ast.h"
#include "validate_constraints.h"

extern int ntest;
extern int nfail;

struct arena_info {
	size_t nschema;
	size_t nprop;
	size_t nstr;
	size_t npnames;
	size_t nset;
	size_t ncnode;
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

const char *
jvst_ret2name(int ret);

static inline int
report_tests(void)
{
	printf("%d tests, %d failures\n", ntest, nfail);
	if (nfail == 0 && ntest > 0) {
		return EXIT_SUCCESS;
	}
	return EXIT_FAILURE;
}

#endif /* TESTING_H */
