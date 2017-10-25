/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#ifndef JVST_JDOM_H
#define JVST_JDOM_H

#include <stdbool.h>
#include <stdlib.h>

enum json_valuetype {
	JSON_VALUE_OBJECT   = 1 << 0,
	JSON_VALUE_ARRAY    = 1 << 1,
	JSON_VALUE_STRING   = 1 << 2,
	JSON_VALUE_NUMBER   = 1 << 3,
	JSON_VALUE_INTEGER  = 1 << 4,
	JSON_VALUE_BOOL     = 1 << 5,
	JSON_VALUE_NULL     = 1 << 6
};

typedef double json_number;

struct json_string {
	const char *s;
	size_t len;
};

struct json_value {
	enum json_valuetype type;
	union {
		struct json_property *obj;
		struct json_element *arr;
		struct json_string str;
		json_number n;
		bool v;
	} u;
};

/* ordered list, duplicate keys, hetereogenous */
struct json_property {
	struct json_string name;
	struct json_value value;
	struct json_property *next;
};

/* ordered list, hetereogenous */
struct json_element {
	struct json_value value;
	struct json_element *next;
};

int
json_strcmp(const struct json_string *str, const char *s);

struct json_string
json_strdup(const struct json_string s);

struct json_string
json_new_cstr(const char *s);

struct json_string
json_new_str(const char *s, size_t len);

void
json_str_free(struct json_string s);

enum json_valuetype
type_lookup(const struct json_string *str);

const char *
type_name(enum json_valuetype t);

#endif

