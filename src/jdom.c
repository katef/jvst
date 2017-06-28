/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <string.h>

#include "jdom.h"

static struct {
	const char *s;
	enum json_valuetype t;
} a[] = {
	{ "object",  JSON_VALUE_OBJECT  },
	{ "array",   JSON_VALUE_ARRAY   },
	{ "string",  JSON_VALUE_STRING  },
	{ "number",  JSON_VALUE_NUMBER  },
	{ "integer", JSON_VALUE_INTEGER },
	{ "boolean", JSON_VALUE_BOOL    },
	{ "null",    JSON_VALUE_NULL    },
	{ "any",     ~0U                }
};

int
json_strcmp(const struct json_string *str, const char *s)
{
	size_t z;

	assert(str != NULL);
	assert(s != NULL);

	z = strlen(s);

	if (str->len < z) {
		return -1;
	}

	if (str->len > z) {
		return +1;
	}

	return memcmp(str->s, s, z);
}

enum json_valuetype
type_lookup(const struct json_string *str)
{
	size_t i;

	assert(str != NULL);
	assert(str->s != NULL);

	for (i = 0; i < sizeof a / sizeof *a; i++) {
		if (0 == json_strcmp(str, a[i].s)) {
			return a[i].t;
		}
	}

	return 0;
}

const char *
type_name(enum json_valuetype t)
{
	size_t i;

	for (i = 0; i < sizeof a / sizeof *a; i++) {
		if (a[i].t == t) {
			return a[i].s;
		}
	}

	return "?";
}

