#include "validate_testing.h"

#include <string.h>
#include <stdarg.h>

#include "jvst_macros.h"

#include "validate.h"
#include "validate_testing.h"
#include "validate_constraints.h"

int ntest;
int nfail;

enum { NUM_TEST_THINGS = 1024 };

// arena allocators to make it easy to programmatically set up a schema
static struct ast_schema ar_schema[NUM_TEST_THINGS];
static struct ast_property_schema ar_props[NUM_TEST_THINGS];
static struct ast_string_set ar_stringsets[NUM_TEST_THINGS];
static struct ast_property_names ar_propnames[NUM_TEST_THINGS];
static struct ast_schema_set ar_schemasets[NUM_TEST_THINGS];
static struct jvst_cnode ar_cnodes[NUM_TEST_THINGS];

// Returns a constant empty schema
struct ast_schema *
empty_schema(void)
{
	static struct ast_schema empty = {0};
	return &empty;
}

struct json_string
newstr(const char *s)
{
	struct json_string str = {.s = s, .len = strlen(s)};
	return str;
}

static struct ast_string_set *
stringset_alloc(struct arena_info *A)
{
	struct ast_string_set *elt;
	size_t i, max;

	max = ARRAYLEN(ar_stringsets);
	i   = A->nstr++;
	if (A->nstr >= max) {
		fprintf(stderr, "too many string sets: %zu max\n", max);
		abort();
	}

	elt = &ar_stringsets[i];
	memset(elt, 0, sizeof *elt);

	return elt;
}

struct ast_string_set *
stringset(struct arena_info *A, ...)
{
	struct ast_string_set *ss = NULL, **ssp = &ss;
	va_list args;

	va_start(args, A);
	for (;;) {
		struct ast_string_set *elt;
		struct json_string str;
		const char *s;
		size_t i;

		if (s = va_arg(args, const char *), s == NULL) {
			break;
		}

		elt      = stringset_alloc(A);
		elt->str = newstr(s);
		*ssp     = elt;
		ssp      = &elt->next;
	}
	va_end(args);

	return ss;
}

struct ast_schema_set *
schema_set(struct arena_info *A, ...)
{
	struct ast_schema_set *sset, **sp;
	struct ast_schema *s;
	size_t max;
	va_list args;

	va_start(args, A);

	sset = NULL;
	sp   = &sset;
	max  = sizeof ar_schemasets / sizeof ar_schemasets[0];
	while (s = va_arg(args, struct ast_schema *), s != NULL) {
		struct ast_schema_set *elt;
		size_t i;

		i = A->nset++;
		if (A->nset >= max) {
			fprintf(stderr, "too many schema sets: %zu max\n", max);
			abort();
		}

		elt = &ar_schemasets[i];
		memset(elt, 0, sizeof *elt);
		elt->schema = s;
		*sp	 = elt;
		sp	  = &elt->next;
	}

	va_end(args);

	return sset;
}

size_t
schema_set_count(struct ast_schema_set *s)
{
	size_t n;
	for (n = 0; s != NULL; s = s->next, n++) {
		continue;
	}

	return n;
}

struct ast_property_names *
newpropnames(struct arena_info *A, ...)
{
	size_t i, max;
	struct ast_property_names *pnames, **pp;
	va_list args;

	pnames = NULL;
	pp     = &pnames;

	va_start(args, A);
	for (;;) {
		const char *n;
		struct ast_string_set *set;

		n = va_arg(args, const char *);
		if (n == NULL) {
			break;
		}

		set = va_arg(args, struct ast_string_set *);
		i   = A->npnames++;
		max = ARRAYLEN(ar_propnames);
		if (A->nschema >= max) {
			fprintf(stderr, "too many schema: %zu max\n", max);
			abort();
		}

		*pp = &ar_propnames[i];
		memset(*pp, 0, sizeof **pp);
		(*pp)->set	     = set;
		(*pp)->pattern.dialect = RE_LITERAL;
		(*pp)->pattern.str     = newstr(n);
		(*pp)->pattern.fsm     = NULL;

		pp = &(*pp)->next;
	}
	va_end(args);

	return pnames;
}

struct ast_schema *
newschema(struct arena_info *A, int types)
{
	size_t i, max;
	struct ast_schema *s;

	i   = A->nschema++;
	max = sizeof ar_schema / sizeof ar_schema[0];
	if (A->nschema >= max) {
		fprintf(stderr, "too many schema: %zu max\n", max);
		abort();
	}

	s = &ar_schema[i];
	memset(s, 0, sizeof *s);
	s->types = types;
	return s;
}

struct ast_schema *
newschema_p(struct arena_info *A, int types, ...)
{
	size_t i, max;
	struct ast_schema *s;
	const char *pname;
	va_list args;

	i   = A->nschema++;
	max = ARRAYLEN(ar_schema);
	if (A->nschema >= max) {
		fprintf(stderr, "too many schema: %zu max\n", max);
		abort();
	}

	s = &ar_schema[i];
	memset(s, 0, sizeof *s);
	s->types = types;

	va_start(args, types);
	for (;;) {
		pname = va_arg(args, const char *);
		if (pname == NULL) {
			break;
		}

		// big dumb if-else chain gets the job done...
		if (strcmp(pname, "minProperties") == 0) {
			s->kws |= KWS_MINMAX_PROPERTIES;
			s->min_properties = va_arg(args, ast_count);
		} else if (strcmp(pname, "maxProperties") == 0) {
			s->kws |= KWS_MINMAX_PROPERTIES;
			s->max_properties = va_arg(args, ast_count);
		} else if (strcmp(pname, "properties") == 0) {
			s->properties.set = va_arg(args, struct ast_property_schema *);
		} else if (strcmp(pname, "required") == 0) {
			s->required.set = va_arg(args, struct ast_string_set *);
		} else if (strcmp(pname, "minimum") == 0) {
			s->kws |= KWS_MINIMUM;
			s->minimum = va_arg(args, double);
		} else if (strcmp(pname, "dep_strings") == 0) {
			s->dependencies_strings.set = va_arg(args, struct ast_property_names *);
		} else if (strcmp(pname, "dep_schema") == 0) {
			s->dependencies_schema.set = va_arg(args, struct ast_property_schema *);
		} else if (strcmp(pname, "anyOf") == 0) {
			struct ast_schema_set *sset;
			sset = va_arg(args, struct ast_schema_set *);
			s->some_of.set = sset;
			s->some_of.min = 1;
			s->some_of.max = schema_set_count(sset);
		} else if (strcmp(pname, "allOf") == 0) {
			struct ast_schema_set *sset;
			sset = va_arg(args, struct ast_schema_set *);
			s->some_of.set = sset;
			s->some_of.min = schema_set_count(sset);
			s->some_of.max = s->some_of.min;
		} else if (strcmp(pname, "oneOf") == 0) {
			struct ast_schema_set *sset;
			sset = va_arg(args, struct ast_schema_set *);
			s->some_of.set = sset;
			s->some_of.min = 1;
			s->some_of.max = 1;
		} else {
			// okay to abort() a test if the test writer forgot to add a
			// property to the big dumb if-else chain
			fprintf(stderr, "unsupported schema property '%s'\n", pname);
			abort();
		}
	}
	va_end(args);

	return s;
}

struct ast_property_schema *
newprops(struct arena_info *A, ...)
{
	struct ast_property_schema *props = NULL;
	struct ast_property_schema **pp   = &props;
	size_t max			  = sizeof ar_props / sizeof ar_props[0];
	va_list args;

	va_start(args, A);

	for (;;) {
		const char *name;
		struct ast_schema *schema;
		struct ast_property_schema *p;
		size_t i;

		name = va_arg(args, const char *);
		if (name == NULL) {
			break;
		}

		i = A->nprop++;
		if (A->nprop >= max) {
			fprintf(stderr, "too many properties: %zu max\n", max);
			abort();
		}

		p = &ar_props[i];
		memset(p, 0, sizeof *p);

		p->pattern.str     = newstr(name);
		p->pattern.dialect = RE_LITERAL;
		p->schema	  = va_arg(args, struct ast_schema *);

		*pp = p;
		pp  = &p->next;
	}

	va_end(args);

	return props;
}

const char *
jvst_ret2name(int ret)
{
	switch (ret) {
	case JVST_INVALID:
		return "INVALID";
	case JVST_VALID:
		return "VALID";
	case JVST_MORE:
		return "MORE";
	default:
		return "UNKNOWN";
	}
}

struct jvst_cnode *
newcnode_valid(void)
{
	static struct jvst_cnode n = {.type = JVST_CNODE_VALID};
	return &n;
}

struct jvst_cnode *
newcnode_invalid(void)
{
	static struct jvst_cnode n = {.type = JVST_CNODE_INVALID};
	return &n;
}

struct jvst_cnode *
newcnode(struct arena_info *A, enum jvst_cnode_type type)
{
	size_t i, max;
	struct jvst_cnode *node;
	const char *pname;
	va_list args;

	i   = A->ncnode++;
	max = ARRAYLEN(ar_cnodes);
	if (A->ncnode >= max) {
		fprintf(stderr, "too many cnodes: %zu max\n", max);
		abort();
	}

	node = &ar_cnodes[i];
	memset(node, 0, sizeof *node);
	node->type = type;

	return node;
}

struct jvst_cnode *
newcnode_switch(struct arena_info *A, int isvalid, ...)
{
	struct jvst_cnode *node;
	size_t i;
	va_list args;

	node = newcnode(A, JVST_CNODE_SWITCH);
	for (i = 0; i < SJP_EVENT_MAX; i++) {
		node->u.sw[i] = isvalid ? newcnode_valid() : newcnode_invalid();
	}

	// ARRAY_END and OBJECT_END should not be valid by default...
	node->u.sw[SJP_ARRAY_END]  = newcnode_invalid();
	node->u.sw[SJP_OBJECT_END] = newcnode_invalid();

	va_start(args, isvalid);
	for (;;) {
		enum SJP_EVENT evt;
		struct jvst_cnode *child;

		evt = va_arg(args, enum SJP_EVENT);
		if (evt == SJP_NONE) {
			break;
		}

		if (evt >= SJP_EVENT_MAX) {
			fprintf(stderr, "invalid event %d\n", evt);
			abort();
		}

		child		= va_arg(args, struct jvst_cnode *);
		node->u.sw[evt] = child;
	}
	va_end(args);

	return node;
}

struct jvst_cnode *
newcnode_bool(struct arena_info *A, enum jvst_cnode_type type, ...)
{
	struct jvst_cnode *node, **pp;
	va_list args;

	if ((type != JVST_CNODE_AND) && (type != JVST_CNODE_OR) && (type != JVST_CNODE_XOR)) {
		fprintf(stderr, "invalid cnode type for %s: %d\n", __func__, type);
		abort();
	}

	node = newcnode(A, type);
	pp   = &node->u.ctrl;
	*pp  = NULL;

	va_start(args, type);
	for (;;) {
		struct jvst_cnode *child;

		child = va_arg(args, struct jvst_cnode *);
		if (child == NULL) {
			break;
		}

		*pp = child;
		pp  = &child->next;
	}
	va_end(args);

	return node;
}

struct jvst_cnode *
newcnode_propset(struct arena_info *A, ...)
{
	struct jvst_cnode *node, **mlp;
	va_list args;

	node = newcnode(A, JVST_CNODE_OBJ_PROP_SET);
	mlp  = &node->u.prop_set;
	*mlp = NULL;

	va_start(args, A);
	for (;;) {
		struct jvst_cnode *match;
		match = va_arg(args, struct jvst_cnode *);
		if (match == NULL) {
			break;
		}
		*mlp = match;
		mlp  = &(*mlp)->next;
	}
	va_end(args);

	return node;
}

struct jvst_cnode *
newcnode_prop_match(struct arena_info *A, enum re_dialect dialect, const char *pat,
		    struct jvst_cnode *constraint)
{
	struct jvst_cnode *node;

	node = newcnode(A, JVST_CNODE_OBJ_PROP_MATCH);

	node->u.prop_match.match.dialect = dialect;
	node->u.prop_match.match.str     = newstr(pat);
	node->u.prop_match.match.fsm     = NULL;
	node->u.prop_match.constraint    = constraint;

	return node;
}

struct jvst_cnode *
newcnode_range(struct arena_info *A, enum jvst_cnode_rangeflags flags, double min, double max)
{
	struct jvst_cnode *node, **pp;
	node			= newcnode(A, JVST_CNODE_NUM_RANGE);
	node->u.num_range.flags = flags;
	node->u.num_range.min   = min;
	node->u.num_range.max   = max;
	return node;
}

struct jvst_cnode *
newcnode_counts(struct arena_info *A, size_t min, size_t max)
{
	struct jvst_cnode *node, **pp;
	node		   = newcnode(A, JVST_CNODE_COUNT_RANGE);
	node->u.counts.min = min;
	node->u.counts.max = max;
	return node;
}

struct jvst_cnode *
newcnode_required(struct arena_info *A, struct ast_string_set *sset)
{
	struct ast_string_set **spp;
	struct jvst_cnode *node;
	va_list args;

	node		 = newcnode(A, JVST_CNODE_OBJ_REQUIRED);
	node->u.required = sset;

	return node;
}
