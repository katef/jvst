#include "validate_constraints.h"

#include <assert.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

#include <adt/set.h>
#include <fsm/bool.h>
#include <fsm/fsm.h>
#include <fsm/out.h>
#include <fsm/options.h>
#include <fsm/pred.h>
#include <fsm/walk.h>
#include <re/re.h>

#include "xalloc.h"

#include "jvst_macros.h"
#include "sjp_testing.h"
#include "validate_sbuf.h"

#define SHOULD_NOT_REACH()							\
	do {									\
		fprintf(stderr, "SHOULD NOT REACH %s, line %d (function %s)\n",	\
			__FILE__, __LINE__, __func__);				\
		abort();							\
	} while (0)

enum {
	JVST_CNODE_CHUNKSIZE = 1024,
	JVST_CNODE_NUMROOTS  = 32,
};

enum {
	MARKSIZE = JVST_CNODE_CHUNKSIZE / CHAR_BIT +
		(JVST_CNODE_CHUNKSIZE % CHAR_BIT) ? 1 : 0,
};

struct jvst_cnode_pool {
	struct jvst_cnode_pool *next;
	struct jvst_cnode items[JVST_CNODE_CHUNKSIZE];
	unsigned char marks[MARKSIZE];
};

/* XXX - should these be global vars?  also, not thread safe. */
static struct jvst_cnode_pool *pool = NULL;
static struct jvst_cnode *freelist  = NULL;
static size_t pool_item	= 0;

struct jvst_strset_pool {
	struct jvst_strset_pool *next;
	struct ast_string_set items[JVST_CNODE_CHUNKSIZE];
	unsigned char marks[MARKSIZE];
};

static struct {
	struct jvst_strset_pool *head;
	size_t top;
	struct ast_string_set *freelist;
} strset_pool;

static struct jvst_cnode *roots[JVST_CNODE_NUMROOTS] = {NULL};
static int nroots				     = 0;

static struct ast_string_set *
cnode_strset_alloc(void)
{
	struct jvst_strset_pool *p;

	if (strset_pool.head == NULL) {
		goto new_pool;
	}

	// first try bump allocation
	if (strset_pool.top < ARRAYLEN(strset_pool.head->items)) {
		return &strset_pool.head->items[pool_item++];
	}

	// next try the free list
	if (strset_pool.freelist != NULL) {
		struct ast_string_set *sset;
		sset		     = strset_pool.freelist;
		strset_pool.freelist = strset_pool.freelist->next;
		return sset;
	}

new_pool:
	// fall back to allocating a new pool
	p = xmalloc(sizeof *p);
	p->next = strset_pool.head;
	strset_pool.head = p;
	strset_pool.top  = 1;
	return &p->items[0];
}

static struct ast_string_set *
cnode_strset(struct json_string str, struct ast_string_set *next)
{
	struct ast_string_set *sset;
	sset = cnode_strset_alloc();
	sset->str  = str;
	sset->next = next;
	return sset;
}

static struct ast_string_set *
cnode_strset_copy(struct ast_string_set *orig)
{
	struct ast_string_set *head, **hpp;
	head = NULL;
	hpp  = &head;
	for (; orig != NULL; orig = orig->next) {
		*hpp = cnode_strset(orig->str, NULL);
		hpp  = &(*hpp)->next;
	}

	return head;
}

struct cnode_matchset_pool {
	struct cnode_matchset_pool *next;
	struct jvst_cnode_matchset items[JVST_CNODE_CHUNKSIZE];
	unsigned char marks[MARKSIZE];
};

static struct {
	struct cnode_matchset_pool *head;
	size_t top;
	struct jvst_cnode_matchset *freelist;
} matchset_pool;

static struct jvst_cnode_matchset *
cnode_matchset_alloc(void)
{
	struct cnode_matchset_pool *pool;

	if (matchset_pool.head == NULL) {
		goto new_pool;
	}

	// first try bump allocation
	if (matchset_pool.top < ARRAYLEN(matchset_pool.head->items)) {
		return &matchset_pool.head->items[pool_item++];
	}

	// next try the free list
	if (matchset_pool.freelist != NULL) {
		struct jvst_cnode_matchset *ms;
		ms = matchset_pool.freelist;
		matchset_pool.freelist = ms->next;
		return ms;
	}

new_pool:
	// fall back to allocating a new pool
	pool = xmalloc(sizeof *pool);
	pool->next = matchset_pool.head;
	matchset_pool.head = pool;
	matchset_pool.top  = 1;
	return &pool->items[0];
}

static struct jvst_cnode_matchset *
cnode_matchset_new(struct ast_regexp match, struct jvst_cnode_matchset *next)
{
	struct jvst_cnode_matchset *ms;
	ms = cnode_matchset_alloc();
	memset(ms, 0, sizeof *ms);
	ms->match = match;
	ms->next = next;
	return ms;
}

void
json_string_finalize(struct json_string *s)
{
	// XXX - implement
	(void)s;
}

static struct jvst_cnode *
cnode_new(void)
{
	struct jvst_cnode_pool *p;

	if (pool == NULL) {
		goto new_pool;
	}

	// first try bump allocation
	if (pool_item < ARRAYLEN(pool->items)) {
		return &pool->items[pool_item++];
	}

	// next try the free list
	if (freelist != NULL) {
		struct jvst_cnode *n = freelist;
		freelist	     = freelist->next;
		return n;
	}

new_pool:
	// fall back to allocating a new pool
	p = xmalloc(sizeof *p);
	p->next = pool;
	pool = p;
	pool_item = 1;
	return &p->items[0];
}

struct jvst_cnode *
jvst_cnode_alloc(enum jvst_cnode_type type)
{
	struct jvst_cnode *n;
	n = cnode_new();
	memset(n, 0, sizeof *n);
	n->type = type;
	n->next = NULL;
	return n;
}

static struct jvst_cnode *
cnode_new_switch(int allvalid)
{
	size_t i, n;
	enum jvst_cnode_type type;
	struct jvst_cnode *node, *v, *inv;

	node = jvst_cnode_alloc(JVST_CNODE_SWITCH);
	type = allvalid ? JVST_CNODE_VALID : JVST_CNODE_INVALID;

	for (i = 0, n = ARRAYLEN(node->u.sw); i < n; i++) {
		node->u.sw[i] = jvst_cnode_alloc(type);
	}

	// ARRAY_END and OBJECT_END are always invalid
	if (allvalid) {
		node->u.sw[SJP_ARRAY_END]  = jvst_cnode_alloc(JVST_CNODE_INVALID);
		node->u.sw[SJP_OBJECT_END] = jvst_cnode_alloc(JVST_CNODE_INVALID);
	}

	return node;
}

static struct jvst_cnode *
cnode_new_mcase(struct jvst_cnode_matchset *ms, struct jvst_cnode *constraint)
{
	struct jvst_cnode *node;

	node = jvst_cnode_alloc(JVST_CNODE_MATCH_CASE);
	node->u.mcase.matchset = ms;
	node->u.mcase.constraint = constraint;

	return node;
}

void
jvst_cnode_free(struct jvst_cnode *n)
{
	// simple logic: add back to freelist
	memset(n, 0, sizeof *n);
	n->next  = freelist;
	freelist = n;
}

void
jvst_cnode_free_tree(struct jvst_cnode *root)
{
	struct jvst_cnode *node, *next;
	size_t i, n;

	for (node = root; node != NULL; node = next) {
		next = node->next;

		switch (node->type) {
		case JVST_CNODE_INVALID:
		case JVST_CNODE_VALID:
			break;

		case JVST_CNODE_AND:
		case JVST_CNODE_OR:
		case JVST_CNODE_XOR:
		case JVST_CNODE_NOT:
			jvst_cnode_free_tree(node->u.ctrl);
			break;

		case JVST_CNODE_SWITCH:
			for (i = 0, n = ARRAYLEN(node->u.sw); i < n; i++) {
				if (node->u.sw[i] != NULL) {
					jvst_cnode_free_tree(node->u.sw[i]);
				}
			}
			break;

		/* constrains with no child nodes */
		case JVST_CNODE_NUM_INTEGER:
		case JVST_CNODE_NUM_RANGE:
		case JVST_CNODE_COUNT_RANGE:
		case JVST_CNODE_ARR_UNIQUE:
			break;

		case JVST_CNODE_STR_MATCH:
			// XXX - need to handle FSM cleanup
			// pool FSMs?  ref count them?
			//
			// be lazy about it, keep references to temporaries,
			// recreate the fsm from scratch when we're done and delete
			// the temporaries?
			break;

		case JVST_CNODE_OBJ_PROP_MATCH:
			// XXX - ensure that fsm is torn down
			// do we pool FSMs?  check if they're ref counted.
			assert(node->u.prop_match.constraint != NULL);
			jvst_cnode_free_tree(node->u.prop_match.constraint);
			break;

		case JVST_CNODE_ARR_ITEM:
		case JVST_CNODE_ARR_ADDITIONAL:
			if (node->u.arr_item != NULL) {
				jvst_cnode_free_tree(node->u.arr_item);
			}
			break;

		default:
			SHOULD_NOT_REACH();
		}

		// now free the node
		jvst_cnode_free(node);
	}
}

const char *
jvst_cnode_type_name(enum jvst_cnode_type type)
{
	switch (type) {
	case JVST_CNODE_INVALID:
		return "INVALID";
	case JVST_CNODE_VALID:
		return "VALID";
	case JVST_CNODE_AND:
		return "AND";
	case JVST_CNODE_OR:
		return "OR";
	case JVST_CNODE_XOR:
		return "XOR";
	case JVST_CNODE_NOT:
		return "NOT";
	case JVST_CNODE_SWITCH:
		return "SWITCH";
	case JVST_CNODE_COUNT_RANGE:
		return "COUNT_RANGE";
	case JVST_CNODE_STR_MATCH:
		return "STR_MATCH";
	case JVST_CNODE_NUM_RANGE:
		return "NUM_RANGE";
	case JVST_CNODE_NUM_INTEGER:
		return "NUM_INTEGER";
	case JVST_CNODE_OBJ_PROP_SET:
		return "OBJ_PROP_SET";
	case JVST_CNODE_OBJ_PROP_MATCH:
		return "OBJ_PROP_MATCH";
	case JVST_CNODE_OBJ_REQUIRED:
		return "OBJ_REQUIRED";
	case JVST_CNODE_ARR_ITEM:
		return "ARR_ITEM";
	case JVST_CNODE_ARR_ADDITIONAL:
		return "ARR_ADDITIONAL";
	case JVST_CNODE_ARR_UNIQUE:
		return "ARR_UNIQUE";

	default:
		fprintf(stderr, "unknown cnode type %d\n", type);
		abort();
	}
}

void
jvst_cnode_matchset_dump(struct jvst_cnode_matchset *ms, struct sbuf *buf, int indent)
{
	char str[256] = {0};
	size_t n;

	sbuf_indent(buf, indent);
	sbuf_snprintf(buf, "P[");
	switch (ms->match.dialect) {
	case RE_LIKE:
		sbuf_snprintf(buf, "LIKE");
		break;

	case RE_LITERAL:
		sbuf_snprintf(buf, "LITERAL");
		break;

	case RE_GLOB:
		sbuf_snprintf(buf, "GLOB");
		break;

	case RE_NATIVE:
		sbuf_snprintf(buf, "NATIVE");
		break;

	default:
		// avoid ??( trigraph by splitting
		// "???(..." into "???" and "(..."
		sbuf_snprintf(buf, "???" "(%d)", ms->match.dialect);
		break;
	}

	n = ms->match.str.len;
	if (n < sizeof str) {
		memcpy(str, ms->match.str.s, n);
	} else {
		memcpy(str, ms->match.str.s, sizeof str - 4);
		memcpy(str + sizeof str - 4, "...", 4);
	}

	sbuf_snprintf(buf, ", \"%s\"]", str);
}

// returns number of bytes written
static void
jvst_cnode_dump_inner(struct jvst_cnode *node, struct sbuf *buf, int indent)
{
	const char *op = NULL;

	if (node == NULL) {
		sbuf_snprintf(buf, "<null>");
		return;
	}

	switch (node->type) {
	case JVST_CNODE_INVALID:
	case JVST_CNODE_VALID:
		sbuf_snprintf(buf, (node->type == JVST_CNODE_VALID) ? "VALID" : "INVALID");
		return;

	case JVST_CNODE_SWITCH:
		{
			size_t i, n;

			sbuf_snprintf(buf, "SWITCH(\n");
			n = ARRAYLEN(node->u.sw);
			for (i = 0; i < n; i++) {
				sbuf_indent(buf, indent + 2);
				sbuf_snprintf(buf, "%-10s : ", evt2name(i));
				jvst_cnode_dump_inner(node->u.sw[i], buf, indent + 2);
				if (i < n - 1) {
					sbuf_snprintf(buf, ",\n");
				} else {
					sbuf_snprintf(buf, "\n");
					sbuf_indent(buf, indent);
					sbuf_snprintf(buf, ")");
				}
			}
		}
		break;

	case JVST_CNODE_NUM_INTEGER:
		sbuf_snprintf(buf, "IS_INTEGER");
		break;

	case JVST_CNODE_NUM_RANGE:
		sbuf_snprintf(buf, "NUM_RANGE(");
		if (node->u.num_range.flags & JVST_CNODE_RANGE_EXCL_MIN) {
			sbuf_snprintf(buf, "%g < ", node->u.num_range.min);
		} else if (node->u.num_range.flags & JVST_CNODE_RANGE_MIN) {
			sbuf_snprintf(buf, "%g <= ", node->u.num_range.min);
		}

		sbuf_snprintf(buf, "x");

		if (node->u.num_range.flags & JVST_CNODE_RANGE_EXCL_MAX) {
			sbuf_snprintf(buf, " < %g", node->u.num_range.max);
		} else if (node->u.num_range.flags & JVST_CNODE_RANGE_MAX) {
			sbuf_snprintf(buf, " <= %g", node->u.num_range.max);
		}

		sbuf_snprintf(buf, ")");
		break;

	case JVST_CNODE_AND:
		op = "AND";
		goto and_or_xor;

	case JVST_CNODE_OR:
		op = "OR";
		goto and_or_xor;
	/* fallthrough */

	case JVST_CNODE_XOR:
		op = "XOR";
		goto and_or_xor;

and_or_xor:
		{
			struct jvst_cnode *cond;

			sbuf_snprintf(buf, "%s(\n", op);
			for (cond = node->u.ctrl; cond != NULL; cond = cond->next) {
				sbuf_indent(buf, indent + 2);
				jvst_cnode_dump_inner(cond, buf, indent + 2);
				if (cond->next) {
					sbuf_snprintf(buf, ",\n");
				} else {
					sbuf_snprintf(buf, "\n");
					sbuf_indent(buf, indent);
					sbuf_snprintf(buf, ")");
				}
			}
		}
		break;

	case JVST_CNODE_OBJ_PROP_SET:
		{
			struct jvst_cnode *prop;

			sbuf_snprintf(buf, "PROP_SET(\n");
			for (prop = node->u.prop_set; prop != NULL; prop = prop->next) {
				sbuf_indent(buf, indent + 2);
				jvst_cnode_dump_inner(prop, buf, indent + 2);
				if (prop->next) {
					sbuf_snprintf(buf, ",\n");
				} else {
					sbuf_snprintf(buf, "\n");
					sbuf_indent(buf, indent);
					sbuf_snprintf(buf, ")");
				}
			}
		}
		break;

	case JVST_CNODE_OBJ_PROP_MATCH:
		{
			char match[256] = {0};
			if (node->u.prop_match.match.str.len >= sizeof match) {
				memcpy(match, node->u.prop_match.match.str.s, sizeof match - 4);
				match[sizeof match - 4] = '.';
				match[sizeof match - 3] = '.';
				match[sizeof match - 2] = '.';
			} else {
				memcpy(match, node->u.prop_match.match.str.s,
						node->u.prop_match.match.str.len);
			}

			sbuf_snprintf(buf, "PROP_MATCH(\n");
			sbuf_indent(buf, indent + 2);
			{
				char *prefix = "";
				char delim   = '/';
				switch (node->u.prop_match.match.dialect) {
					case RE_LIKE:
						prefix = "L";
						break;
					case RE_LITERAL:
						delim = '"';
						break;

					case RE_GLOB:
						prefix = "G";
						break;
					case RE_NATIVE:
						break;
					default:
						prefix = "???";
						break;
				}
				sbuf_snprintf(buf, "%s%c%s%c,\n", prefix, delim, match, delim);
				sbuf_indent(buf, indent + 2);
				jvst_cnode_dump_inner(node->u.prop_match.constraint, buf, indent + 2);
				sbuf_snprintf(buf, "\n");
				sbuf_indent(buf, indent);
				sbuf_snprintf(buf, ")");
			}
		}
		break;

	case JVST_CNODE_COUNT_RANGE:
		sbuf_snprintf(buf, "COUNT_RANGE(");
		if (node->u.counts.min > 0) {
			sbuf_snprintf(buf, "%zu <= ", node->u.counts.min);
		}

		sbuf_snprintf(buf, "x");

		if (node->u.counts.max > 0) {
			sbuf_snprintf(buf, "<= %zu", node->u.counts.min);
		}

		sbuf_snprintf(buf, ")");
		break;

	case JVST_CNODE_OBJ_REQUIRED:
		{
			struct ast_string_set *ss;

			sbuf_snprintf(buf, "REQUIRED(\n");
			for (ss = node->u.required; ss != NULL; ss = ss->next) {
				char str[256] = {0};
				size_t n;

				n = ss->str.len;
				if (n < sizeof str) {
					memcpy(str, ss->str.s, n);
				} else {
					memcpy(str, ss->str.s, sizeof str - 4);
					memcpy(str + sizeof str - 4, "...", 4);
				}

				sbuf_indent(buf, indent + 2);
				sbuf_snprintf(buf, "\"%s\"%s\n", str, (ss->next != NULL) ? "," : "");
			}
			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		break;

	case JVST_CNODE_MATCH_SWITCH:
		{
			struct jvst_cnode *c;

			sbuf_snprintf(buf, "MATCH_SWITCH(\n");
			if (node->u.mswitch.default_case != NULL) {
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "DEFAULT[\n");

				sbuf_indent(buf, indent+4);
				jvst_cnode_dump_inner(node->u.mswitch.default_case, buf, indent + 4);
				sbuf_snprintf(buf, "\n");

				sbuf_indent(buf, indent+2);
				if (node->u.mswitch.cases != NULL) {
					sbuf_snprintf(buf, "],\n");
				} else {
					sbuf_snprintf(buf, "]\n");
				}
			}

			for (c = node->u.mswitch.cases; c != NULL; c = c->next) {
				assert(c->type == JVST_CNODE_MATCH_CASE);
				sbuf_indent(buf, indent+2);
				jvst_cnode_dump_inner(c, buf, indent+2);
				if (c->next != NULL) {
					sbuf_snprintf(buf, ",\n");
				} else {
					sbuf_snprintf(buf, "\n");
				}
			}
			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		break;

	case JVST_CNODE_MATCH_CASE:
		{
			struct jvst_cnode_matchset *ms;

			sbuf_snprintf(buf, "MATCH_SWITCH(\n");
			assert(node->u.mcase.matchset != NULL);

			for (ms = node->u.mcase.matchset; ms != NULL; ms = ms->next) {
				jvst_cnode_matchset_dump(ms, buf, indent+2);
				sbuf_snprintf(buf, ",\n");
			}

			sbuf_indent(buf, indent+2);
			jvst_cnode_dump_inner(node->u.mcase.constraint, buf, indent+2);
			sbuf_snprintf(buf, "\n");

			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		break;

	case JVST_CNODE_NOT:
	case JVST_CNODE_STR_MATCH:
	case JVST_CNODE_ARR_ITEM:
	case JVST_CNODE_ARR_ADDITIONAL:
	case JVST_CNODE_ARR_UNIQUE:
		fprintf(stderr, "**not implemented**\n");
		abort();
	}
}

int
jvst_cnode_dump(struct jvst_cnode *node, char *buf, size_t nb);

void
jvst_cnode_print(struct jvst_cnode *node)
{
	// FIXME: gross hack
	char buf[65536] = {0}; // 64K

	jvst_cnode_dump(node, buf, sizeof buf);
	fprintf(stderr, "%s\n", buf);
}

int
jvst_cnode_dump(struct jvst_cnode *node, char *buf, size_t nb)
{
	struct sbuf b = {
	    .buf = buf, .cap = nb, .len = 0, .np = 0,
	};

	jvst_cnode_dump_inner(node, &b, 0);
	return (b.len < b.cap) ? 0 : -1;
}

// Translates the AST into a contraint tree and simplifys the constraint
// tree
struct jvst_cnode *
jvst_cnode_from_ast(struct ast_schema *ast);

// Just do a raw translation without doing any optimization of the
// constraint tree
struct jvst_cnode *
jvst_cnode_translate_ast(struct ast_schema *ast)
{
	struct jvst_cnode *node;
	enum json_valuetype types;

	assert(ast != NULL);
	types = ast->types;

	// TODO - implement ast->some_of.set != NULL logic
	// top is a switch
	if (types == 0) {
		node = cnode_new_switch(true);
	} else {
		struct jvst_cnode *valid;

		node  = cnode_new_switch(false);
		valid = jvst_cnode_alloc(JVST_CNODE_VALID);

		if (types & JSON_VALUE_OBJECT) {
			node->u.sw[SJP_OBJECT_BEG] = valid;
		}

		if (types & JSON_VALUE_ARRAY) {
			node->u.sw[SJP_ARRAY_BEG] = valid;
		}

		if (types & JSON_VALUE_STRING) {
			node->u.sw[SJP_STRING] = valid;
		}

		if (types & JSON_VALUE_STRING) {
			node->u.sw[SJP_STRING] = valid;
		}

		if (types & JSON_VALUE_NUMBER) {
			node->u.sw[SJP_NUMBER] = valid;
		}

		if (types & JSON_VALUE_INTEGER) {
			node->u.sw[SJP_NUMBER] = jvst_cnode_alloc(JVST_CNODE_NUM_INTEGER);
		}

		if (types & JSON_VALUE_BOOL) {
			node->u.sw[SJP_TRUE]  = valid;
			node->u.sw[SJP_FALSE] = valid;
		}

		if (types & JSON_VALUE_NULL) {
			node->u.sw[SJP_NULL] = valid;
		}
	}

	if (ast->kws & (KWS_MINIMUM | KWS_MAXIMUM)) {
		enum jvst_cnode_rangeflags flags = 0;
		double min = 0, max = 0;
		struct jvst_cnode *range, *jxn;

		if (ast->kws & KWS_MINIMUM) {
			flags |= (ast->exclusive_minimum ? JVST_CNODE_RANGE_EXCL_MIN
							 : JVST_CNODE_RANGE_MIN);
			min = ast->minimum;
		}

		if (ast->kws & KWS_MAXIMUM) {
			flags |= (ast->exclusive_maximum ? JVST_CNODE_RANGE_EXCL_MAX
							 : JVST_CNODE_RANGE_MAX);
			max = ast->maximum;
		}

		range = jvst_cnode_alloc(JVST_CNODE_NUM_RANGE);
		range->u.num_range.flags = flags;
		range->u.num_range.min = min;
		range->u.num_range.max = max;

		jxn = jvst_cnode_alloc(JVST_CNODE_AND);
		jxn->u.ctrl = range;
		range->next = node->u.sw[SJP_NUMBER];
		node->u.sw[SJP_NUMBER] = jxn;
	}

	if (ast->properties.set != NULL) {
		struct jvst_cnode **plist, *phead, *prop_set, *top_jxn;
		struct ast_property_schema *pset;

		top_jxn = NULL;
		prop_set = NULL;
		phead = NULL;
		plist = &phead;

		for (pset = ast->properties.set; pset != NULL; pset = pset->next) {
			struct jvst_cnode *pnode;
			pnode = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_MATCH);
			pnode->u.prop_match.match = pset->pattern;
			pnode->u.prop_match.constraint = jvst_cnode_translate_ast(pset->schema);
			*plist = pnode;
			plist = &pnode->next;
		}

		prop_set = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_SET);
		prop_set->u.prop_set = phead;
		assert(phead != NULL);

		top_jxn		= jvst_cnode_alloc(JVST_CNODE_AND);
		top_jxn->u.ctrl = prop_set;
		prop_set->next  = node->u.sw[SJP_OBJECT_BEG];

		node->u.sw[SJP_OBJECT_BEG] = top_jxn;
	}

	if (ast->kws & KWS_MINMAX_PROPERTIES) {
		struct jvst_cnode *range, *jxn;

		range = jvst_cnode_alloc(JVST_CNODE_COUNT_RANGE);
		range->u.counts.min = ast->min_properties;
		range->u.counts.max = ast->max_properties;

		jxn = jvst_cnode_alloc(JVST_CNODE_AND);
		jxn->u.ctrl = range;
		range->next = node->u.sw[SJP_OBJECT_BEG];
		node->u.sw[SJP_OBJECT_BEG] = jxn;
	}

	if (ast->required.set != NULL) {
		struct jvst_cnode *req, *jxn;

		req = jvst_cnode_alloc(JVST_CNODE_OBJ_REQUIRED);
		req->u.required = ast->required.set;

		jxn = jvst_cnode_alloc(JVST_CNODE_AND);
		jxn->u.ctrl = req;
		req->next = node->u.sw[SJP_OBJECT_BEG];
		node->u.sw[SJP_OBJECT_BEG] = jxn;
	}

	if (ast->dependencies_strings.set != NULL) {
		struct ast_property_names *pnames;
		struct jvst_cnode *top_jxn, **tpp;

		top_jxn = jvst_cnode_alloc(JVST_CNODE_AND);
		top_jxn->u.ctrl = NULL;
		tpp = &top_jxn->u.ctrl;

		for (pnames = ast->dependencies_strings.set; pnames != NULL;
		     pnames = pnames->next) {
			struct jvst_cnode *req, *pset, *pm, *jxn;
			struct ast_string_set *strset;

			req = jvst_cnode_alloc(JVST_CNODE_OBJ_REQUIRED);
			// build required stringset for the dependency pair
			assert(pnames->pattern.dialect == RE_LITERAL);
			req->u.required = cnode_strset(pnames->pattern.str, cnode_strset_copy(pnames->set));

			pm = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_MATCH);
			pm->u.prop_match.match = pnames->pattern;
			pm->u.prop_match.constraint = jvst_cnode_alloc(JVST_CNODE_INVALID);

			pset = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_SET);
			pset->u.prop_set = pm;

			req->next = pset;
			jxn = jvst_cnode_alloc(JVST_CNODE_OR);
			jxn->u.ctrl = req;

			*tpp = jxn;
			tpp  = &jxn->next;
		}

		*tpp = node->u.sw[SJP_OBJECT_BEG];
		node->u.sw[SJP_OBJECT_BEG] = top_jxn;
	}

	if (ast->dependencies_schema.set != NULL) {
		struct ast_property_schema *pschema;
		struct jvst_cnode *top_jxn, **tpp;

		top_jxn = jvst_cnode_alloc(JVST_CNODE_AND);
		top_jxn->u.ctrl = node;
		tpp = &node->next;
		node = top_jxn;

		for (pschema = ast->dependencies_schema.set; pschema != NULL;
		     pschema = pschema->next) {
			struct jvst_cnode *jxn, **jpp;
			struct jvst_cnode *sw, *req, *schema, *andjxn, *pm, *pset;
			struct ast_string_set *strset;

			jxn  = jvst_cnode_alloc(JVST_CNODE_OR);
			jpp  = &jxn->u.ctrl;
			*jpp = NULL;

			andjxn = jvst_cnode_alloc(JVST_CNODE_AND);

			req = jvst_cnode_alloc(JVST_CNODE_OBJ_REQUIRED);
			// build required stringset for the dependency pair
			assert(pschema->pattern.dialect == RE_LITERAL);
			req->u.required = cnode_strset(pschema->pattern.str, NULL);

			sw = cnode_new_switch(false);
			sw->u.sw[SJP_OBJECT_BEG] = req;
			andjxn->u.ctrl = sw;
			sw->next = jvst_cnode_translate_ast(pschema->schema);

			*jpp = andjxn;
			jpp  = &(*jpp)->next;

			sw = cnode_new_switch(true);

			pm = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_MATCH);
			pm->u.prop_match.match = pschema->pattern;
			pm->u.prop_match.constraint = jvst_cnode_alloc(JVST_CNODE_INVALID);

			pset = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_SET);
			pset->u.prop_set = pm;

			sw->u.sw[SJP_OBJECT_BEG] = pset;

			*jpp = sw;
			jpp  = &(*jpp)->next;

			*tpp = jxn;
			tpp  = &jxn->next;
		}
	}

	if (ast->some_of.set != NULL) {
		struct jvst_cnode *top_jxn, *some_jxn, **conds;
		struct ast_schema_set *sset;
		enum jvst_cnode_type op = JVST_CNODE_OR;

		if (ast->some_of.min == ast->some_of.max) {
			op = (ast->some_of.min == 1) ? JVST_CNODE_XOR : JVST_CNODE_AND;
		}

		some_jxn = jvst_cnode_alloc(op);
		conds = &some_jxn->u.ctrl;
		some_jxn->u.ctrl = NULL;
		for (sset = ast->some_of.set; sset != NULL; sset = sset->next) {
			struct jvst_cnode *c;
			c = jvst_cnode_translate_ast(sset->schema);
			*conds = c;
			conds = &c->next;
		}

		top_jxn = jvst_cnode_alloc(JVST_CNODE_AND);
		top_jxn->u.ctrl = some_jxn;
		some_jxn->next = node;
		node = top_jxn;
	}

	return node;
}

static struct jvst_cnode *
cnode_deep_copy(struct jvst_cnode *node);

static int
mcase_copier(const struct fsm *dfa, const struct fsm_state *st)
{
	struct jvst_cnode *node, *ndup;

	if (!fsm_isend(dfa, st)) {
		return 1;
	}

	node = fsm_getopaque((struct fsm *)dfa, st);
	assert(node->type == JVST_CNODE_MATCH_CASE);
	assert(node->u.mcase.tmp == NULL);

	ndup = cnode_deep_copy(node);
	node->u.mcase.tmp = ndup;

	fsm_setopaque((struct fsm *)dfa, (struct fsm_state *)st, ndup);

	return 1;
}

static struct jvst_cnode *
cnode_mswitch_copy(struct jvst_cnode *node)
{
	struct jvst_cnode *tree, *mcases, **mcpp;
	struct fsm *dup_fsm;

	tree = jvst_cnode_alloc(JVST_CNODE_MATCH_SWITCH);

	// it would be lovely to copy this but there doesn't seem to be
	// a way to get/set it on the fsm.
	tree->u.mswitch.opts = node->u.mswitch.opts;

	// duplicate FSM
	//
	// XXX - need to determine how we're keeping track of
	// FSMs
	dup_fsm = fsm_clone(node->u.mswitch.dfa);

	tree->u.mswitch.dfa = dup_fsm;

	// copy and collect all opaque states
	fsm_all(dup_fsm, mcase_copier);

	mcpp = &tree->u.mswitch.cases;
	for (mcases = node->u.mswitch.cases; mcases != NULL; mcases = mcases->next) {
		assert(mcases->u.mcase.tmp != NULL);
		*mcpp = mcases->u.mcase.tmp;
		mcases->u.mcase.tmp = NULL;
		mcpp = &(*mcpp)->next;
	}

	assert(node->u.mswitch.default_case != NULL);
	tree->u.mswitch.default_case = cnode_deep_copy(node->u.mswitch.default_case);

	return tree;
}

static struct jvst_cnode *
cnode_deep_copy(struct jvst_cnode *node)
{
	struct jvst_cnode *tree;

	switch (node->type) {
	case JVST_CNODE_INVALID:
	case JVST_CNODE_VALID:
	case JVST_CNODE_NUM_INTEGER:
	case JVST_CNODE_ARR_UNIQUE:
		return jvst_cnode_alloc(node->type);

	case JVST_CNODE_AND:
	case JVST_CNODE_OR:
	case JVST_CNODE_XOR:
	case JVST_CNODE_NOT:
		{
			struct jvst_cnode *ctrl, **cp;
			tree = jvst_cnode_alloc(node->type);
			cp = &tree->u.ctrl;
			for (ctrl = node->u.ctrl; ctrl != NULL; ctrl = ctrl->next) {
				*cp = cnode_deep_copy(ctrl);
				cp = &(*cp)->next;
			}
			return tree;
		}

	case JVST_CNODE_SWITCH:
		{
			size_t i, n;
			tree = jvst_cnode_alloc(node->type);
			for (i = 0, n = ARRAYLEN(node->u.sw); i < n; i++) {
				tree->u.sw[i] = NULL;
				if (node->u.sw[i] != NULL) {
					tree->u.sw[i] = cnode_deep_copy(node->u.sw[i]);
				}
			}
			return tree;
		}

	case JVST_CNODE_NUM_RANGE:
		tree = jvst_cnode_alloc(node->type);
		tree->u.num_range = node->u.num_range;
		return tree;

	case JVST_CNODE_COUNT_RANGE:
		tree	   = jvst_cnode_alloc(node->type);
		tree->u.counts = node->u.counts;
		return tree;

	case JVST_CNODE_STR_MATCH:
		tree = jvst_cnode_alloc(node->type);
		tree->u.str_match = node->u.str_match;
		return tree;

	case JVST_CNODE_OBJ_PROP_SET:
		{
			struct jvst_cnode *prop, **pp;
			tree = jvst_cnode_alloc(node->type);
			pp = &tree->u.prop_set;
			for (prop = node->u.prop_set; prop != NULL; prop = prop->next) {
				*pp = cnode_deep_copy(prop);
				pp  = &(*pp)->next;
			}
			return tree;
		}

	case JVST_CNODE_OBJ_PROP_MATCH:
		tree = jvst_cnode_alloc(node->type);
		tree->u.prop_match.match = node->u.prop_match.match;
		tree->u.prop_match.constraint = cnode_deep_copy(node->u.prop_match.constraint);
		return tree;

	case JVST_CNODE_OBJ_REQUIRED:
		tree = jvst_cnode_alloc(node->type);
		tree->u.required = node->u.required;
		return tree;

	case JVST_CNODE_ARR_ITEM:
		{
			struct jvst_cnode *item, **ip;
			tree = jvst_cnode_alloc(node->type);
			ip = &tree->u.arr_item;
			for (item = node->u.arr_item; item != NULL; item = item->next) {
				*ip = cnode_deep_copy(item);
				ip  = &(*ip)->next;
			}
			return tree;
		}

	case JVST_CNODE_ARR_ADDITIONAL:
		tree = jvst_cnode_alloc(node->type);
		tree->u.arr_item = cnode_deep_copy(node->u.arr_item);
		return tree;

	case JVST_CNODE_MATCH_SWITCH:
		return cnode_mswitch_copy(node);

	case JVST_CNODE_MATCH_CASE:
		{
			struct jvst_cnode_matchset *mset, **mspp;

			tree = jvst_cnode_alloc(JVST_CNODE_MATCH_CASE);
			mspp = &tree->u.mcase.matchset;
			for(mset = node->u.mcase.matchset; mset != NULL; mset = mset->next) {
				*mspp = cnode_matchset_new(mset->match, NULL);
				mspp = &(*mspp)->next;
			}
			tree->u.mcase.constraint = cnode_deep_copy(node->u.mcase.constraint);
			return tree;
		}
	}

	// avoid default case in switch so the compiler can complain if
	// we add new cnode types
	SHOULD_NOT_REACH();
}

struct jvst_cnode *
cnode_list_end(struct jvst_cnode *node)
{
	assert(node != NULL);
	while (node->next != NULL) {
		node = node->next;
	}
	return node;
}

struct jvst_cnode *
cnode_list_prepend(struct jvst_cnode **headp, struct jvst_cnode *node)
{
	assert(headp != NULL);
	node->next = *headp;
	*headp = node;
	return node;
}

struct jvst_cnode *
cnode_list_concat(struct jvst_cnode **headp, struct jvst_cnode *tail)
{
	struct jvst_cnode **hp0;

	hp0 = headp;

	assert(headp != NULL);
	while (*headp != NULL) {
		headp = &(*headp)->next;
	}
	*headp = tail;
	return *hp0;
}

static struct jvst_cnode *
cnode_find_type(struct jvst_cnode *node, enum jvst_cnode_type type)
{
	for (; node != NULL; node = node->next) {
		if (node->type == type) {
			return node;
		}
	}

	return NULL;
}

static struct jvst_cnode *
cnode_simplify_andor_switches(struct jvst_cnode *top)
{
	// check if all nodes are SWITCH nodes.  If they are, combine
	// the switch clauses and simplify

	struct jvst_cnode *node, **pp, *sw;
	size_t i, n;

	for (node = top->u.ctrl; node != NULL; node = node->next) {
		if (node->type != JVST_CNODE_SWITCH) {
			return top;
		}
	}

	// all nodes are switch nodes...
	sw = jvst_cnode_alloc(JVST_CNODE_SWITCH);
	for (i = 0, n = ARRAYLEN(sw->u.sw); i < n; i++) {
		struct jvst_cnode *jxn, **cpp;

		jxn = jvst_cnode_alloc(top->type);
		cpp = &jxn->u.ctrl;

		for (node = top->u.ctrl; node != NULL; node = node->next) {
			assert(node->type == JVST_CNODE_SWITCH);

			*cpp = node->u.sw[i];
			assert((*cpp)->next == NULL);
			cpp = &(*cpp)->next;
		}

		sw->u.sw[i] = jvst_cnode_simplify(jxn);
	}

	return sw;
}

static struct jvst_cnode *
cnode_simplify_and_propsets(struct jvst_cnode *top)
{
	// merges any children that are PROPSET nodes into a single
	// PROPSET that contains all of the PROP_MATCHes.
	struct jvst_cnode *node, *psets, **pspp, **npp, **pmpp, *comb;
	size_t npsets;

	// check how many PROPSET children we have... if less than two,
	// no simplification is necessary
	for (npsets = 0, node = top->u.ctrl; node != NULL; node= node->next) {
		if (node->type == JVST_CNODE_OBJ_PROP_SET) {
			npsets++;
		}
	}

	if (npsets < 2) {
		return top;
	}

	// collect all PROPSET children
	psets = NULL;
	pspp = &psets;
	for (npp = &top->u.ctrl; *npp != NULL; ) {
		if ((*npp)->type != JVST_CNODE_OBJ_PROP_SET) {
			npp = &(*npp)->next;
			continue;
		}

		*pspp = *npp;
		*npp = (*npp)->next;

		pspp = &(*pspp)->next;
		*pspp = NULL;
	}

	// merge all PROP_MATCH cases into one PROPSET
	comb = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_SET);
	pmpp = &comb->u.prop_set;
	for (node=psets; node != NULL; node = node->next) {
		*pmpp = node->u.prop_set;
		for (; *pmpp != NULL; pmpp = &(*pmpp)->next) {
			continue;
		}
	}

	// all children are PROPSETs... return the combined PROPSET
	if (top->u.ctrl == NULL) {
		return comb;
	}

	// add the combined PROPSET to the AND node and return the AND
	// node
	*npp = comb;
	return top;
}

void
cnode_simplify_ctrl_children(struct jvst_cnode *top)
{
	struct jvst_cnode *node, *next, **pp;
	pp = &top->u.ctrl;

	// first optimize child nodes...
	for (node = top->u.ctrl; node != NULL; node = next) {
		next = node->next;
		*pp  = jvst_cnode_simplify(node);
		pp   = &(*pp)->next;
	}
}

void
cnode_simplify_ctrl_combine_like(struct jvst_cnode *top)
{
	struct jvst_cnode *node, *next, **pp;

	// combine subnodes of the same type (ie: AND will combine with
	// AND and OR will combine with OR)
	for (pp = &top->u.ctrl; *pp != NULL; pp = &(*pp)->next) {
		if ((*pp)->type != top->type) {
			continue;
		}

		// save next link
		next = (*pp)->next;
		*pp  = (*pp)->u.ctrl;

		// fast path...
		if (next == NULL) {
			continue;
		}

		while (*pp != NULL) {
			pp = &(*pp)->next;
		}

		*pp = next;
	}
}

static struct jvst_cnode *
cnode_simplify_andor(struct jvst_cnode *top)
{
	struct jvst_cnode *node, *next, **pp;
	enum jvst_cnode_type snt; // short circuit node type
	enum jvst_cnode_type rnt; // remove node type

	cnode_simplify_ctrl_children(top);

	// pass 1: remove VALID/INVALID nodes
	switch (top->type) {
	case JVST_CNODE_AND:
		snt = JVST_CNODE_INVALID;
		rnt = JVST_CNODE_VALID;
		break;

	case JVST_CNODE_OR:
		snt = JVST_CNODE_VALID;
		rnt = JVST_CNODE_INVALID;
		break;

	default:
		SHOULD_NOT_REACH();
	}

	for (pp = &top->u.ctrl; *pp != NULL;) {
		enum jvst_cnode_type nt = (*pp)->type;

		if (nt == snt) {
			(*pp)->next = NULL;
			return *pp;
		}

		if (nt == rnt) {
			*pp = (*pp)->next;
			continue;
		}

		pp = &(*pp)->next;
	}

	// all nodes were valid
	if (top->u.ctrl == NULL) {
		return jvst_cnode_alloc(rnt);
	}

	assert(top->u.ctrl != NULL);
	if (top->u.ctrl->next == NULL) {
		// only one child
		return top->u.ctrl;
	}

	cnode_simplify_ctrl_combine_like(top);

	if (top->type == JVST_CNODE_AND) {
		top = cnode_simplify_and_propsets(top);
	}
	return cnode_simplify_andor_switches(top);
}

static struct jvst_cnode *
cnode_simplify_propset(struct jvst_cnode *tree)
{
	struct jvst_cnode *pm;

	// step 1: iterate over PROP_MATCH nodes and simplify each
	// constraint individually
	for (pm = tree->u.prop_set; pm != NULL; pm=pm->next) {
		pm->u.prop_match.constraint = jvst_cnode_simplify(pm->u.prop_match.constraint);
	}

	return tree;
}

struct jvst_cnode *
jvst_cnode_simplify(struct jvst_cnode *tree)
{
	struct jvst_cnode *node;

	// make a copy
	tree = cnode_deep_copy(tree);

	switch (tree->type) {
	case JVST_CNODE_INVALID:
	case JVST_CNODE_VALID:
	case JVST_CNODE_NUM_INTEGER:
	case JVST_CNODE_ARR_UNIQUE:
		return tree;

	case JVST_CNODE_AND:
	case JVST_CNODE_OR:
		return cnode_simplify_andor(tree);

	case JVST_CNODE_XOR:
		// TODO: basic optimization for XOR
		return tree;

	case JVST_CNODE_NOT:
		// TODO: basic optimizations for NOT
		return tree;

	case JVST_CNODE_SWITCH:
		{
			size_t i, n;
			for (i = 0, n = ARRAYLEN(tree->u.sw); i < n; i++) {
				tree->u.sw[i] = jvst_cnode_simplify(tree->u.sw[i]);
			}
		}
		return tree;

	case JVST_CNODE_OBJ_PROP_SET:
		return cnode_simplify_propset(tree);

	case JVST_CNODE_NUM_RANGE:
	case JVST_CNODE_COUNT_RANGE:
	case JVST_CNODE_STR_MATCH:
	case JVST_CNODE_OBJ_PROP_MATCH:
	case JVST_CNODE_OBJ_REQUIRED:
	case JVST_CNODE_ARR_ITEM:
	case JVST_CNODE_ARR_ADDITIONAL:
	case JVST_CNODE_MATCH_SWITCH:
	case JVST_CNODE_MATCH_CASE:
		// TODO: basic optimization for these nodes
		return tree;
	}

	// avoid default case in switch so the compiler can complain if
	// we add new cnode types
	SHOULD_NOT_REACH();
}

struct json_str_iter {
	struct json_string str;
	size_t off;
};

static int
json_str_getc(void *p)
{
	struct json_str_iter *iter = p;
	unsigned char ch;

	if (iter->off >= iter->str.len) {
		return EOF;
	}

	ch = iter->str.s[iter->off++];
	return ch;
}

static void
merge_mcases(struct set *orig, struct fsm *dfa, struct fsm_state *comb)
{
	struct jvst_cnode *mcase, *jxn, **jpp;
	struct jvst_cnode_matchset **mspp;
	struct fsm_state *st;
	struct set_iter it;
	size_t nstates;

	// first count states to make sure that we need to merge...
	mcase = NULL;
	nstates = 0;

	for (st = set_first(orig, &it); st != NULL; st = set_next(&it)) {
		struct jvst_cnode *c;

		if (!fsm_isend(dfa, st)) {
			continue;
		}

		c = fsm_getopaque(dfa, st);
		assert(c != NULL);

		// allow a fast path if nstates==1
		if (mcase == NULL) {
			mcase = c;
		}

		nstates++;
	}

	if (nstates == 0) {
		return;
	}

	if (nstates == 1) {
		assert(mcase != NULL);
		fsm_setopaque(dfa, comb, mcase);
		return;
	}

	// okay... need to combine things...
	jxn = jvst_cnode_alloc(JVST_CNODE_AND);
	jpp = &jxn->u.ctrl;
	mcase = cnode_new_mcase(NULL, jxn);
	mspp = &mcase->u.mcase.matchset;

	for (st = set_first(orig, &it); st != NULL; st = set_next(&it)) {
		struct jvst_cnode *c;
		struct jvst_cnode_matchset *mset;

		if (!fsm_isend(dfa, st)) {
			continue;
		}

		c = fsm_getopaque(dfa, st);
		assert(c != NULL);

		assert(c->type == JVST_CNODE_MATCH_CASE);
		assert(c->u.mcase.matchset != NULL);

		// XXX - currently don't check for duplicates.
		// Do we need to?
		for (mset = c->u.mcase.matchset; mset != NULL; mset = mset->next) {
			*mspp = cnode_matchset_new(mset->match, NULL);
			mspp = &(*mspp)->next;
		}

		*jpp = cnode_deep_copy(c->u.mcase.constraint);
		jpp = &(*jpp)->next;
	}

	fsm_setopaque(dfa, comb, mcase);
}

static struct jvst_cnode **mcase_collector_head;

static int
mcase_collector(const struct fsm *dfa, const struct fsm_state *st)
{
	struct jvst_cnode *node;

	assert(mcase_collector_head != NULL);
	assert(*mcase_collector_head == NULL);

	if (!fsm_isend(dfa, st)) {
		return 1;
	}

	node = fsm_getopaque((struct fsm *)dfa, st);
	assert(node->type == JVST_CNODE_MATCH_CASE);
	assert(node->next == NULL);

	*mcase_collector_head = node;
	mcase_collector_head = &node->next;

	return 1;
}

static struct jvst_cnode *
cnode_canonify_propset(struct jvst_cnode *top)
{
	struct jvst_cnode *pm, *mcases, *msw, **mcpp;
	struct fsm_options *opts;
	struct fsm *matches;

	// FIXME: this is a leak...
	opts = xmalloc(sizeof *opts);
	*opts = (struct fsm_options) {
		.tidy = false,
		.anonymous_states = false,
		.consolidate_edges = true,
		.fragment = true,
		.comments = true,
		.case_ranges = true,

		.io = FSM_IO_GETC,
		.prefix = NULL,
		.carryopaque = merge_mcases,
	};

	assert(top->type == JVST_CNODE_OBJ_PROP_SET);
	assert(top->u.prop_set != NULL);

	// step 1: construct a FSM from all PROP_MATCH nodes.
	//
	// This involves:
	//
	//  a. create an FSM for each PROP_MATCH node
	//  b. create a MATCH_CASE for each PROP_MATCH node
	//  c. Set the MATCH_CASE as the opaque value for all end states
	//     in the FSM
	//  d. Union the FSM with the previous FSMs.
	matches = NULL;
	for (pm = top->u.prop_set; pm != NULL; pm=pm->next) {
		struct jvst_cnode *cons, *mcase;
		struct jvst_cnode_matchset *mset;
		struct fsm *pat;
		struct json_str_iter siter;
		struct re_err err = { 0 };

		cons = pm->u.prop_match.constraint;
		mset = cnode_matchset_new(pm->u.prop_match.match, NULL);
		mcase = cnode_new_mcase(mset, cons);

		siter.str = pm->u.prop_match.match.str;
		siter.off = 0;

		pat = re_comp(
			pm->u.prop_match.match.dialect,
			json_str_getc,
			&siter,
			opts,
			(enum re_flags)0,
			&err);

		// errors should be checked in parsing
		assert(pat != NULL);

		fsm_setendopaque(pat, mcase);

		if (matches == NULL) {
			matches = pat;
		} else {
			matches = fsm_union(matches, pat);

			// XXX - we can't handle failure states right
			// now...
			assert(matches != NULL);
		}
	}

	// step 2: convert the FSM from an NFA to a DFA.
	//
	// This may involve merging MATCH_CASE nodes.  The rules are
	// fairly simple: combine pattern sets, combine constraints with
	// an AND condition.
	//
	// NB: combining requires copying because different end states
	// may still have the original MATCH_CASE node.

	if (!fsm_determinise(matches)) {
		perror("cannot determinise fsm");
		abort();
	}

	// step 3: collect all MATCH_CASE nodes from the DFA by
	// iterating over the DFA end states.  All MATCH_CASE nodes must
	// be placed into a linked list.
	mcases = NULL;
	mcase_collector_head = &mcases; // XXX - ugly global variable

	fsm_all(matches, mcase_collector);

	// step 5: build the MATCH_SWITCH container to hold the cases
	// and the DFA.  The default case should be VALID.
	msw = jvst_cnode_alloc(JVST_CNODE_MATCH_SWITCH);
	msw->u.mswitch.dfa = matches;
	msw->u.mswitch.opts = opts;
	msw->u.mswitch.cases = mcases;
	msw->u.mswitch.default_case = jvst_cnode_alloc(JVST_CNODE_VALID);

	// step 4: simplify and canonify the constraint of each MATCH_CASE node.
	// 	   We re-simplify the constraints because multiple
	// 	   constraints can be merged.
	for (; mcases != NULL; mcases = mcases->next) {
		struct jvst_cnode *cons;
		cons = jvst_cnode_simplify(mcases->u.mcase.constraint);
		mcases->u.mcase.constraint = jvst_cnode_canonify(cons);
	}

	return msw;
}

struct jvst_cnode *
jvst_cnode_canonify(struct jvst_cnode *tree)
{
	struct jvst_cnode *node;

	// this also makes a copy...
	tree = cnode_deep_copy(tree);

	switch (tree->type) {
	case JVST_CNODE_INVALID:
	case JVST_CNODE_VALID:
	case JVST_CNODE_ARR_UNIQUE:
	case JVST_CNODE_NUM_RANGE:
	case JVST_CNODE_COUNT_RANGE:
		return tree;

	case JVST_CNODE_AND:
	case JVST_CNODE_OR:
	case JVST_CNODE_XOR:
	case JVST_CNODE_NOT:
		{
			struct jvst_cnode *xform = NULL;
			struct jvst_cnode **xpp = &xform;

			for (node = tree->u.ctrl; node != NULL; node = node->next) {
				*xpp = jvst_cnode_canonify(node);
				xpp = &(*xpp)->next;
			}

			tree->u.ctrl = xform;

		}
		return tree;

	case JVST_CNODE_SWITCH:
		{
			size_t i, n;
			for (i = 0, n = ARRAYLEN(tree->u.sw); i < n; i++) {
				tree->u.sw[i] = jvst_cnode_canonify(tree->u.sw[i]);
			}
		}
		return tree;

	case JVST_CNODE_OBJ_PROP_SET:
		return cnode_canonify_propset(tree);

	case JVST_CNODE_NUM_INTEGER:
	case JVST_CNODE_STR_MATCH:
	case JVST_CNODE_OBJ_PROP_MATCH:
	case JVST_CNODE_OBJ_REQUIRED:
	case JVST_CNODE_ARR_ITEM:
	case JVST_CNODE_ARR_ADDITIONAL:
	case JVST_CNODE_MATCH_SWITCH:
	case JVST_CNODE_MATCH_CASE:
		// TODO: basic optimization for these nodes
		return tree;
	}

	// avoid default case in switch so the compiler can complain if
	// we add new cnode types
	SHOULD_NOT_REACH();
}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
