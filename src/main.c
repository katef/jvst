/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#define _POSIX_C_SOURCE 2

#include <unistd.h>

#include <assert.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

#include "sjp_lexer.h"

#include "debug.h"
#include "parser.h"
#include "jdom.h"
#include "ast.h"
#include "xalloc.h"

unsigned debug;

static char *
readfile(FILE *f, size_t *np)
{
	size_t sz, n;
	char *p;

	assert(f != NULL);

	p  = NULL;
	sz = 0;
	n  = 0;

	for (;;) {
		size_t r;

		assert(n <= sz);
		if (n + BUFSIZ >= sz) {
			sz += BUFSIZ;
			p = xrealloc(p, sz);
		}

		r = fread(p + n, 1, sz - n, f);
		if (r == 0) {
			break;
		}

		n += r;
	}

	if (ferror(f)) {
		free(p);
		return NULL;
	}

	assert(n < sz);
	p[n] = '\0';

	if (np != NULL) {
		*np = n;
	}

	return p;
}

static int
debug_flags(const char *s)
{
	int v;

	assert(s != NULL);

	v = 1;

	for ( ; *s != '\0'; s++) {
		int e;

		switch (*s) {
		case '+': v = 1; continue;
		case '-': v = 0; continue;

		case 'a': e = ~0U;         break;
		case 's': e = DEBUG_SJP;   break;
		case 'l': e = DEBUG_LEX;   break;
		case 'c': e = DEBUG_ACT;   break;

		default:
			fprintf(stderr, "-d: unrecognised flag '%c'\n", *s);
			return -1;
		}

		if (v) {
			debug |=  e;
		} else {
			debug &= ~e;
		}
	}

	return 0;
}


int
main(int argc, char *argv[])
{
	static const struct ast_schema ast_default;
	struct ast_schema ast = ast_default;
	struct sjp_lexer l;
	size_t n;
	char *p;
	int r;

	{
		int c;

		while (c = getopt(argc, argv, "d:"), c != -1) {
			switch (c) {
			case 'd':
				if (-1 == debug_flags(optarg)) {
					goto usage;
				}
				break;

			default:
				goto usage;
			}
		}

		argc -= optind;
		argv += optind;
	}

	sjp_lexer_init(&l);

	/* TODO: until sjp gets various streamed IO interfaces */
	p = readfile(stdin, &n);
	if (p == NULL) {
		perror("readfile");
		exit(EXIT_FAILURE);
	}

	sjp_lexer_more(&l, p, n);

	parse(&l, &ast);

	ast_dump(stdout, &ast);

	r = sjp_lexer_close(&l);
	if (SJP_ERROR(r)) {
		fprintf(stderr, "sjp error B: %d\n", r); /* TODO */
		exit(EXIT_FAILURE);
	}

	return 0;

usage:

	fprintf(stderr, "usage: jvst [-d +-aslc]\n");

	return 1;
}

