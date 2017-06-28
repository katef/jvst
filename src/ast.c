/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <limits.h>
#include <string.h>
#include <stdio.h>

#include "sjp_lexer.h"

#include "jdom.h"
#include "ast.h"

static void
dump_schema(FILE *f, const struct ast_schema *ast)
{
	assert(f != NULL);
	assert(ast != NULL);

	fprintf(f, "_%p [ label = <<TABLE border='0' VALIGN='TOP'>\n", (void *) ast);

	if ((ast->kws & KWS_VALUE)) {
		fprintf(f, "<TR>");
		fprintf(f, "<TD align='left'>value</TD>");
		fprintf(f, "<TD align='left'>");
		/* TODO */
		fprintf(f, "</TD>");
		fprintf(f, "</TR>");
	}

	if ((ast->kws & KWS_MULTIPLE_OF)) {
		fprintf(f, "<TR>");
		fprintf(f, "<TD align='left'>multiple_of</TD>");
		fprintf(f, "<TD align='left'>%f</TD>", ast->multiple_of);
		fprintf(f, "</TR>");
	}

	if ((ast->kws & KWS_MAXIMUM)) {
		fprintf(f, "<TR>");
		fprintf(f, "<TD align='left'>maximum</TD>");
		fprintf(f, "<TD align='left'>%s %f</TD>",
			ast->exclusive_maximum ? "&gt;" : "&gt;=",
			ast->maximum);
		fprintf(f, "</TR>");
	}

	if ((ast->kws & KWS_MINIMUM)) {
		fprintf(f, "<TR>");
		fprintf(f, "<TD align='left'>minimum</TD>");
		fprintf(f, "<TD align='left'>%s %f</TD>",
			ast->exclusive_minimum ? "&lt;" : "&lt;=",
			ast->minimum);
		fprintf(f, "</TR>");
	}

	if ((ast->kws & KWS_MINMAX_LENGTH)) {
	}

	if ((ast->kws & KWS_MINMAX_ITEMS)) {
	}

	if ((ast->kws & KWS_MINMAX_PROPERTIES)) {
	}

	if (ast->types != 0) {
		unsigned v;

		fprintf(f, "<TR>");
		fprintf(f, "<TD align='left'>types</TD>");
		fprintf(f, "<TD align='left'>");
		for (v = ast->types; v != 0; v &= v - 1) {
			fprintf(f, "%s%s",
				type_name(v & -v),
				(v & v - 1) != 0 ? ", " : "");
		}
		fprintf(f, "</TD>");
		fprintf(f, "</TR>");
	}
	fprintf(f, "</TABLE>> ];\n");
}

void
ast_dump(FILE *f, const struct ast_schema *ast)
{
	assert(f != NULL);
	assert(ast != NULL);

	fprintf(f, "digraph G {\n");
	fprintf(f, "\tnode [ shape = Mrecord ];\n");

	dump_schema(f, ast);

	fprintf(f, "}\n");
	fprintf(f, "\n");
}

