/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#define _POSIX_C_SOURCE 200809L

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "xalloc.h"

void *
xrealloc(void *p, size_t sz)
{
	void *q;

	/* This is legal and frees p, but confusing; use free() instead */
	assert(sz != 0);

	q = realloc(p, sz);
	if (q == NULL) {
		perror("xrealloc");
		abort();
	}

	return q;
}

char *
xstrndup(const char *s, size_t n)
{
	char *new;

	assert(s != NULL);

	new = strndup(s, n);
	if (new == NULL) {
		perror("xstrndup");
		abort();
	}

	return new;
}

void *
xmalloc(size_t n)
{
	void *p;
	if (p = malloc(n), p == NULL) {
		perror("malloc");
		abort();
	}

	return p;
}

void *
xcalloc(size_t count, size_t sz)
{
	void *p;
	if (p = calloc(count, sz), p == NULL) {
		perror("malloc");
		abort();
	}

	return p;
}

void *
xenlargevec(void *orig, size_t *np, size_t incr, size_t width)
{
	size_t newmax;

	if (incr == 0) {
		return orig;
	}

	newmax = *np + incr;

	if (newmax < 4) {
		newmax = 4;
	} else if (newmax < 2048) {
		newmax *= 2;
	} else {
		newmax += newmax/4;
	}

	assert(newmax > *np + incr);

	*np = newmax;
	return xrealloc(orig, newmax * width);
}

