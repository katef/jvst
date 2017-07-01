/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#ifndef JVST_XALLOC_H
#define JVST_XALLOC_H

void *
xrealloc(void *p, size_t sz);

char *
xstrndup(const char *s, size_t n);

void *
xmalloc(size_t n);

void *
xcalloc(size_t count, size_t sz);

#endif

