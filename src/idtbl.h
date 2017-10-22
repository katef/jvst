#ifndef IDTBL_H
#define IDTBL_H

#include "jdom.h"

struct jvst_id_table;
struct jvst_cnode;

struct jvst_id_table *
jvst_id_table_new(void);

void
jvst_id_table_delete(struct jvst_id_table *tbl);

int
jvst_id_table_add(struct jvst_id_table *tbl, struct json_string id, struct jvst_cnode *ctree);

struct jvst_cnode *
jvst_id_table_lookup(struct jvst_id_table *tbl, struct json_string s);

struct jvst_cnode *
jvst_id_table_lookup_cstr(struct jvst_id_table *tbl, const char *s);

struct jvst_cnode *
jvst_id_table_lookup_with_len(struct jvst_id_table *tbl, const char *s, size_t n);

void
jvst_id_table_dump_ids(struct jvst_id_table *tbl);

#endif /* IDTBL_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
