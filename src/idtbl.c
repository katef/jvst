#include "idtbl.h"

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include "hmap.h"
#include "xxhash.h"

// TODO - this parameter should be tuned for performance
enum { IDTBL_INITIAL_NBUCKETS = 256 };
#define IDTBL_MAXLOAD 0.65f

struct jvst_id_table {
	// XXX - add initialize/finalize to hmap so we can store this as
	// a value instead of a pointer
	struct hmap *map;
};

static uint64_t json_string_hash(void *opaque, const void *k)
{
	const struct json_string *sk = k;

	(void)opaque; // unused

	// XXX - use non-zero seed? (third arg)
	return XXH64(sk->s, sk->len, 0);
}

static int json_string_equals(void *opaque, const void *k1, const void *k2)
{
	const struct json_string *sk1 = k1, *sk2 = k2;
	int cmp;

	(void)opaque; // unused

	return (sk1->len == sk2->len) &&
		((sk1->len > 0) || (memcmp(sk1->s, sk2->s, sk1->len) == 0));
}

struct jvst_id_table *
jvst_id_table_new(void)
{
	static const struct jvst_id_table zero;
	struct jvst_id_table *tbl;

	tbl = malloc(sizeof *tbl);
	*tbl = zero;

	tbl->map = hmap_create(IDTBL_INITIAL_NBUCKETS, IDTBL_MAXLOAD, NULL,
		json_string_hash, json_string_equals);

	return tbl;
}

int
jvst_id_table_add(struct jvst_id_table *tbl, struct json_string id, struct jvst_cnode *ctree)
{
	static const struct json_string zero;
	struct json_string *key;

	assert(tbl != NULL);
	assert(tbl->map != NULL);

	key = malloc(sizeof *key);
	*key = zero;

	if (id.len > 0) {
		char *s = malloc(id.len);
		memcpy(s, id.s, id.len);
		key->s = s;
		key->len = id.len;
	}

	return hmap_setptr(tbl->map, key, ctree);
}

int
jvst_id_table_set(struct jvst_id_table *tbl, struct json_string id, struct jvst_cnode *ctree)
{
	union hmap_value *v;

	v = hmap_get(tbl->map, &id);
	if (v == NULL) {
		return 0;
	}

	v->p = ctree;
	return 1;
}

void
jvst_id_table_delete(struct jvst_id_table *tbl)
{
	void *k;
	struct hmap_iter it;

	// iterate over keys, freeing keys.  the ID table makes a
	// duplicate copy of each key.
	for (k = hmap_iter_first(tbl->map, &it); k != NULL; k = hmap_iter_next(&it)) {
		struct json_string *str = k;
		free((void *)str->s);
		free(str);
	}

	// free the table.  values are collected by the usual cnode
	// garbage collection machinery
	hmap_free(tbl->map);
	free(tbl);
}

struct jvst_cnode *
jvst_id_table_lookup(struct jvst_id_table *tbl, struct json_string s)
{
	struct jvst_cnode *n;

	assert(tbl != NULL);
	assert(tbl->map != NULL);

	return hmap_getptr(tbl->map, &s);
}

struct jvst_cnode *
jvst_id_table_lookup_cstr(struct jvst_id_table *tbl, const char *s)
{
	assert(s != NULL);
	return jvst_id_table_lookup_with_len(tbl, s, strlen(s));
}

struct jvst_cnode *
jvst_id_table_lookup_with_len(struct jvst_id_table *tbl, const char *s, size_t n)
{
	struct json_string str = { .s = s, .len = n };
	assert(s != NULL);
	return jvst_id_table_lookup(tbl, str);
}

int
jvst_id_table_foreach(struct jvst_id_table *tbl,
	int (*each)(void *, struct json_string *, struct jvst_cnode **ctreep),
	void *opaque)
{
	struct hmap_iter it;
	struct json_string *k;

	for (k = hmap_iter_first(tbl->map, &it); k != NULL; k = hmap_iter_next(&it)) {
		struct jvst_cnode *vn;

		vn = it.v.p;
		// XXX - cast is slightly non-portable
		if (!each(opaque, k, &vn)) {
			return 0;
		}

		// update the value if it has changed
		if (vn != it.v.p) {
			union hmap_value *v;
			v = hmap_iter_fetch(&it);
			v->p = vn;
		}
	}

	return 1;
}

void
jvst_cnode_debug(struct jvst_cnode *node);

void
jvst_id_table_dump_ids(struct jvst_id_table *tbl)
{
	void *k;
	struct hmap_iter it;

	// iterate over keys, freeing keys.  the ID table makes a
	// duplicate copy of each key.
	for (k = hmap_iter_first(tbl->map, &it); k != NULL; k = hmap_iter_next(&it)) {
		struct json_string *str = k;
		struct jvst_cnode *ctree = it.v.p;
		fprintf(stderr, "ID: %.*s\n", (int)str->len, str->s);
		jvst_cnode_debug(ctree);
	}
}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
