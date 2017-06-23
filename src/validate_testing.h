#ifndef TESTING_H
#define TESTING_H

#include "jdom.h"
#include "ast.h"

#define MODULE_NAME TESTING

int ntest;
int nfail;

struct arena_info {
  size_t nschema;
  size_t nprop;
  size_t nstr;
  size_t nset;
};

struct ast_schema *empty_schema(void);
struct ast_schema *newschema(struct arena_info *A, int types);
struct ast_schema *newschema_p(struct arena_info *A, int types, ...);

struct json_string newstr(const char *s);
struct ast_string_set *stringset(struct arena_info *A, ...);
struct ast_schema_set *schema_set(struct arena_info *A, ...);
size_t schema_set_count(struct ast_schema_set *s);
struct ast_property_schema *newprops(struct arena_info *A, ...);

const char *jvst_ret2name(int ret);

#undef MODULE_NAME

#endif /* TESTING_H */

