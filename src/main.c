/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include <stdlib.h>

#include "parser.h"
#include "json.h"
#include "jdom.h"
#include "ast.h"

int main(void) {
	json_stream json;
	struct ast_schema ast = { 0 };

	json_open_stream(&json, stdin);

	parse(&json, &ast);
	if (json_get_error(&json)) {
		fprintf(stderr, "%s\n", json_get_error(&json));
		exit(EXIT_FAILURE);
	}

	fprintf(stderr, "$schema: %s\n", ast.schema.s);
	fprintf(stderr, "$id: %s\n", ast.id.s);

	json_close(&json);

	return 0;
}

