#include <assert.h>
#include <stdlib.h>
#include <string.h>

#include "hmap.h"

#include "xxhash.h"

// XXX - fix this!  We need to seed hash functions securely from a crng
enum { HASH_SEED = 0x5432da };

struct hmap_khb {
	uint64_t hash;
	void *key;
};

static int
hmap_set_inner(struct hmap *m, unsigned long h, void *k, union hmap_value v)
{
	size_t i,n, b;
	void *opaque;
	int (*equals)(void *, const void *, const void *);

	assert(m != NULL);

	n      = m->nbuckets;
	opaque = m->opaque;
        equals = m->equals;

	b = h % n;
	for (i=0; i < n; i++) {
		if (m->khb[b].hash == 0 && m->khb[b].key == NULL) {
			goto set_item;
		}

		if (m->khb[b].hash == h && equals(opaque, m->khb[b].key, k)) {
			goto set_item;
		}

		if (++b >= n) {
			b = 0;
		}

	}

	assert(!"unreachable");
	return 0;

set_item:
	m->khb[b].hash = h;
	m->khb[b].key = k;
	m->vb[b] = v;
	m->nitems++;

	return 1;
}

static int
hmap_rehash(struct hmap *m)
{
	size_t i, n, ni, nbuckets, old_nbuckets;
	struct hmap_khb *khb;
	union hmap_value *vb, *old_vb;
	struct hmap_khb *old_khb;

	khb = NULL;
	vb  = NULL;

	nbuckets = (m->khb == NULL) ? m->nbuckets : 2*m->nbuckets;
	khb = malloc(nbuckets * sizeof khb[0]);
	if (khb == NULL) {
		goto error;
	}

	vb = malloc(nbuckets * sizeof vb[0]);
	if (vb == NULL) {
		goto error;
	}

	for (i=0; i < nbuckets; i++) {
		khb[i].hash = 0;
		khb[i].key  = NULL;
		vb[i].p = NULL;
	}

	old_khb = m->khb;
	old_vb  = m->vb;
	ni      = m->nitems;
        old_nbuckets = m->nbuckets;

	m->khb      = khb;
	m->vb       = vb;
	m->nbuckets = nbuckets;
	m->nitems   = 0;
	m->nthresh  = nbuckets * m->maxload;

	assert(m->nthresh > ni);

	if (!old_khb) {
		goto finish;
	}

	for (n=old_nbuckets, i=0; i < n; i++) {
		if (old_khb[i].key == NULL) {
			continue;
		}

		hmap_set_inner(m, old_khb[i].hash, old_khb[i].key, old_vb[i]);
	}

	assert(m->nitems == ni);

finish:
	free(old_khb);
	free(old_vb);

	return 1;

error:
	free(khb);
	free(vb);
	return 0;
}

int
hmap_set(struct hmap *m, void *k, union hmap_value v)
{
	unsigned long h;

	assert(m != NULL);

	if (m->nitems >= m->nthresh) {
		if (!hmap_rehash(m)) {
			return 0;
		}
	}

	h = m->hash(m->opaque, k);
	return hmap_set_inner(m, h, k, v);
}

int
hmap_setptr(struct hmap *m, void *k, void *v)
{
	union hmap_value vt;
	vt.p = v;
	return hmap_set(m, k, vt);
}

int
hmap_setint(struct hmap *m, void *k, int64_t i)
{
	union hmap_value vt;
	vt.i = i;
	return hmap_set(m, k, vt);
}

int
hmap_setuint(struct hmap *m, void *k, uint64_t u)
{
	union hmap_value vt;
	vt.u = u;
	return hmap_set(m, k, vt);
}

struct hmap *
hmap_create(size_t nbuckets, float maxload, void *opaque,
	uint64_t (*hash)(void *, const void *),
	int (*equals)(void *opaque, const void *k1, const void *k2))
{
	struct hmap *m;
	size_t i;

	m = malloc(sizeof *m);
	if (m == NULL) {
		goto error;
		return NULL;
	}

	m->khb = NULL;
	m->vb  = NULL;

	m->khb = malloc(nbuckets * sizeof m->khb[0]);
	if (m->khb == NULL) {
		goto error;
	}

	m->vb = malloc(nbuckets * sizeof m->vb[0]);
	if (m->vb == NULL) {
		goto error;
	}

	for (i=0; i < nbuckets; i++) {
		m->khb[i].hash = 0;
		m->khb[i].key  = NULL;

		m->vb[i].p = NULL;
	}

	m->nitems   = 0;
	m->nbuckets = nbuckets;
	m->nthresh  = nbuckets * maxload;
	m->maxload  = maxload;

	m->opaque = opaque;
	m->hash   = hash;
	m->equals = equals;

	return m;

error:
	hmap_free(m);
	return NULL;
}

void
hmap_free(struct hmap *m)
{
	if (m == NULL) {
		return;
	}

	free(m->khb);
	free(m->vb);
	free(m);
}

union hmap_value *
hmap_get(const struct hmap *m, const void *k)
{
	unsigned long h = m->hash(m->opaque, k);
	size_t b = h % m->nbuckets;
	for (;;) {
		if (m->khb[b].hash == 0 && m->khb[b].key == NULL) {
			/* empty bucket... cannot find value */
			return NULL;
		}

		if (m->khb[b].hash == h) {
			if (m->equals(m->opaque, m->khb[b].key, k)) {
				return &m->vb[b];
			}
		}

		if (++b >= m->nbuckets) {
			b = 0;
		}
	}
}

void *
hmap_getptr(const struct hmap *m, const void *k)
{
	union hmap_value *v;

	v = hmap_get(m,k);
	return (v != NULL) ? v->p : NULL;
}

int64_t
hmap_getint(const struct hmap *m, const void *k)
{
	union hmap_value *v;

	v = hmap_get(m,k);
	return (v != NULL) ? v->i : 0;
}

uint64_t
hmap_getuint(const struct hmap *m, const void *k)
{
	union hmap_value *v;

	v = hmap_get(m,k);
	return (v != NULL) ? v->u : 0;
}

int
hmap_foreach(const struct hmap *m, void *opaque, int (*callback)(const void *k, union hmap_value v, void *opaque))
{
	size_t i,n;

	for (n=m->nbuckets, i=0; i < n; i++) {
		if (m->khb[i].key == NULL) {
			continue;
		}
		if (!callback(m->khb[i].key, m->vb[i], opaque)) {
			return 0;
		}
	}

	return 1;
}

static void *
next_bucket(struct hmap_iter *it)
{
	size_t i,n;
	const struct hmap *m;

	m = it->m;
	n = m->nbuckets;
	for(i = it->i; i < n; i++) {
		if (m->khb[i].key == NULL) {
			continue;
		}

		it->i = i+1;
		it->k = m->khb[i].key;
		it->v = m->vb[i];

		return it->k;
	}

	it->k = NULL;
	it->v.p = NULL;
	return NULL;
}

void *
hmap_iter_first(const struct hmap *m, struct hmap_iter *it)
{
	it->m = m;
	it->i = 0;
	it->k = NULL;
	it->v.p = NULL;

	return next_bucket(it);
}

void *
hmap_iter_next(struct hmap_iter *it)
{
	return next_bucket(it);
}

uint64_t
hash_string(void *opaque, const void *key)
{
	size_t len;
	(void)opaque;

	len = strlen((char *)key);  // ugh
	return (uint64_t)XXH64(key, len, HASH_SEED); // XXX - FIX SEED!
}

uint64_t
hash_pointer(void *opaque, const void *key)
{
	unsigned char v[sizeof key];

	(void)opaque;
	memcpy(v, &key, sizeof key);
	return (uint64_t)XXH64(v, sizeof v, HASH_SEED); // XXX - FIX SEED!
}

static int
equals_string(void *dummy, const void *a, const void *b)
{
	(void)dummy;
	assert(a != NULL);
	assert(b != NULL);

	return strcmp(a,b) == 0;
}

struct hmap *
hmap_create_string(size_t nbuckets, float maxload)
{
	return hmap_create(nbuckets, maxload, NULL,
		hash_string, equals_string);
}

static int
equals_pointer(void *dummy, const void *a, const void *b)
{
	(void)dummy;

	return a == b;
}

struct hmap *
hmap_create_pointer(size_t nbuckets, float maxload)
{
	return hmap_create(nbuckets, maxload, NULL,
		hash_pointer, equals_pointer);
}
