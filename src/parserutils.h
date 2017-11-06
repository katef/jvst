#ifndef PARSERUTILS_H
#define PARSERUTILS_H

#include <uriparser/Uri.h>

#include "ast.h"
#include "jdom.h"


struct path_element {
  UriUriA *base_id;
  int isnum;
  union {
    size_t num;
    struct json_string str;
  } u;
};

struct path {
  size_t len;
  size_t cap;

  struct path_element *items;
};

struct path_element *push_element(struct path *p);
struct path_element *peek_element(struct path *p);

void path_push_empty(struct path *p);
void path_push_str(struct path *p, struct json_string s);
void path_push_num_zero(struct path *p);
void path_push_num_next(struct path *p);

void path_pop(struct path *p);

struct json_string path_ref(struct path *path, struct json_string ref);

void path_set_baseid(struct path_element *ptop, struct path_element *pnode, struct json_string baseid);

void path_add_all_ids(struct path *path, struct ast_schema *ast);
char *build_fragment(size_t *lenp, struct path_element *pbeg, struct path_element *pend);

#endif /* PARSERUTILS_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */

