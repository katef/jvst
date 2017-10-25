#ifndef IDTBL_H
#define IDTBL_H

#include "jdom.h"

/* cnode id table */

struct jvst_cnode;
struct jvst_cnode_id_table;

struct jvst_cnode_id_table *
jvst_cnode_id_table_new(void);

void
jvst_cnode_id_table_delete(struct jvst_cnode_id_table *tbl);

int
jvst_cnode_id_table_add(struct jvst_cnode_id_table *tbl, struct json_string id, struct jvst_cnode *ctree);

int
jvst_cnode_id_table_set(struct jvst_cnode_id_table *tbl, struct json_string id, struct jvst_cnode *ctree);

struct jvst_cnode *
jvst_cnode_id_table_lookup(struct jvst_cnode_id_table *tbl, struct json_string s);

struct jvst_cnode *
jvst_cnode_id_table_lookup_cstr(struct jvst_cnode_id_table *tbl, const char *s);

struct jvst_cnode *
jvst_cnode_id_table_lookup_with_len(struct jvst_cnode_id_table *tbl, const char *s, size_t n);

int
jvst_cnode_id_table_foreach(struct jvst_cnode_id_table *tbl,
	int (*each)(void *, struct json_string *, struct jvst_cnode **ctreep),
	void *opaque);

size_t
jvst_cnode_id_table_nbuckets(struct jvst_cnode_id_table *tbl);

float
jvst_cnode_id_table_maxload(struct jvst_cnode_id_table *tbl);

// for debugging
void
jvst_cnode_id_table_dump_ids(struct jvst_cnode_id_table *tbl);


/* IR id table */

struct jvst_ir_stmt;
struct jvst_ir_id_table;

struct jvst_ir_id_table *
jvst_ir_id_table_new(void);

void
jvst_ir_id_table_delete(struct jvst_ir_id_table *tbl);

int
jvst_ir_id_table_add(struct jvst_ir_id_table *tbl, struct json_string id, struct jvst_ir_stmt *ir);

int
jvst_ir_id_table_set(struct jvst_ir_id_table *tbl, struct json_string id, struct jvst_ir_stmt *ir);

struct jvst_ir_stmt *
jvst_ir_id_table_lookup(struct jvst_ir_id_table *tbl, struct json_string s);

struct jvst_ir_stmt *
jvst_ir_id_table_lookup_cstr(struct jvst_ir_id_table *tbl, const char *s);

struct jvst_ir_stmt *
jvst_ir_id_table_lookup_with_len(struct jvst_ir_id_table *tbl, const char *s, size_t n);

int
jvst_ir_id_table_foreach(struct jvst_ir_id_table *tbl,
	int (*each)(void *, struct json_string *, struct jvst_ir_stmt **ctreep),
	void *opaque);

size_t
jvst_ir_id_table_nbuckets(struct jvst_ir_id_table *tbl);

float
jvst_ir_id_table_maxload(struct jvst_ir_id_table *tbl);

#endif /* IDTBL_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
