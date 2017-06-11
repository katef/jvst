/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include "sjp_lexer.h"

#include "parser.h"
#include "jdom.h"
#include "ast.h"
#include "xalloc.h"

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

int
main(void)
{
	static const struct ast_schema ast_default;
	struct ast_schema ast = ast_default;
	struct sjp_lexer l;
	size_t n;
	char *p;
	int r;

	sjp_lexer_init(&l);

	/* TODO: until sjp gets various streamed IO interfaces */
	p = readfile(stdin, &n);
	if (p == NULL) {
		perror("readfile");
		exit(EXIT_FAILURE);
	}

	sjp_lexer_more(&l, p, n);

	parse(&l, &ast);

	for (;;) {
		struct sjp_token t;

		r = sjp_lexer_token(&l, &t);
		if (SJP_ERROR(r)) {
			fprintf(stderr, "sjp error A: %d, tok->n=%zu\n", r, t.n); /* TODO */
			exit(EXIT_FAILURE);
		}

		if (t.type == SJP_TOK_NONE) {
			break;
		}

		fprintf(stderr, "r=%d, t=%d '%.*s'\n", r, t.type, (int) t.n, t.value);
	}

	r = sjp_lexer_close(&l);
	if (SJP_ERROR(r)) {
		fprintf(stderr, "sjp error B: %d\n", r); /* TODO */
		exit(EXIT_FAILURE);
	}

	return 0;
}

