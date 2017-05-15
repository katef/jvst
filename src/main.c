/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include <stdlib.h>

#include "parser.h"
#include "json.h"

int main(void) {
	json_stream json;

	json_open_stream(&json, stdin);

	parse(&json);
	if (json_get_error(&json)) {
		fprintf(stderr, "%s\n", json_get_error(&json));
		exit(EXIT_FAILURE);
	}

	json_close(&json);

	return 0;
}

