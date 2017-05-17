/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#define _POSIX_C_SOURCE 200809L

#include <string.h>

#include "xalloc.h"

char *
xstrndup(const char *s, size_t n)
{
	char *new;

	new = strndup(s, n);
	if (new == NULL) {
		perror("xstrndup");
		abort();
	}

	return new;
}

