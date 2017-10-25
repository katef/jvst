/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <string.h>

#include "kw.h"
#include "jdom.h"

static struct {
	const char *s;
	enum kw k;
} a[] = {
	{ "$schema",              KW_SCHEMA                },
	{ "$ref",                 KW_REF                   },
	{ "id",                   KW_ID                    },
	{ "$id",                  KW_ID                    },

	{ "multipleOf",           KW_MULTIPLE_OF           },
	{ "maximum",              KW_MAXIMUM               },
	{ "exclusiveMaximum",     KW_EXCLUSIVE_MAXIMUM     },
	{ "minimum",              KW_MINIMUM               },
	{ "exclusiveMinimum",     KW_EXCLUSIVE_MINIMUM     },
	{ "maxLength",            KW_MAX_LENGTH            },
	{ "minLength",            KW_MIN_LENGTH            },
	{ "pattern",              KW_PATTERN               },
	{ "items",                KW_ITEMS                 },
	{ "additionalItems",      KW_ADDITIONAL_ITEMS      },
	{ "maxItems",             KW_MAX_ITEMS             },
	{ "minItems",             KW_MIN_ITEMS             },
	{ "uniqueItems",          KW_UNIQUE_ITEMS          },
	{ "contains",             KW_CONTAINS              },
	{ "maxProperties",        KW_MAX_PROPERTIES        },
	{ "minProperties",        KW_MIN_PROPERTIES        },
	{ "required",             KW_REQUIRED              },
	{ "properties",           KW_PROPERTIES            },
	{ "patternProperties",    KW_PATTERN_PROPERTIES    },
	{ "additionalProperties", KW_ADDITIONAL_PROPERTIES },
	{ "dependencies",         KW_DEPENDENCIES          },
	{ "propertyNames",        KW_PROPERTY_NAMES        },

	{ "enum",                 KW_ENUM                  },
	{ "const",                KW_CONST                 },
	{ "type",                 KW_TYPE                  },
	{ "allOf",                KW_ALL_OF                },
	{ "anyOf",                KW_ANY_OF                },
	{ "oneOf",                KW_ONE_OF                },
	{ "not",                  KW_NOT                   },

	/* metadata */
	{ "title",                KW_TITLE                 },
	{ "definitions",          KW_DEFINITIONS           },
	{ "description",          KW_DESCRIPTION           },
	{ "default",              KW_DEFAULT               },
	{ "examples",             KW_EXAMPLES              }
};

enum kw
kw_lookup(const struct json_string *str)
{
	size_t i;

	assert(str != NULL);
	assert(str->s != NULL);

	for (i = 0; i < sizeof a / sizeof *a; i++) {
		if (0 == json_strcmp(str, a[i].s)) {
			return a[i].k;
		}
	}

	return 0;
}

const char *
kw_name(enum kw k)
{
	size_t i;

	for (i = 0; i < sizeof a / sizeof *a; i++) {
		if (a[i].k == k) {
			return a[i].s;
		}
	}

	return "?";
}

