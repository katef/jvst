#include "validate_constraints.h"

#include <assert.h>
#include <stdarg.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

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
#include "hmap.h"

#define WHEREFMT "%s:%d (%s) "
#define WHEREARGS __FILE__, __LINE__, __func__

#define SHOULD_NOT_REACH()					\
	do {							\
		fprintf(stderr, WHEREFMT "SHOULD NOT REACH\n",	\
			WHEREARGS);				\
		abort();					\
	} while (0)

#define NOT_YET_IMPLEMENTED(cnode, oper) do {					\
		fprintf(stderr, WHEREFMT "%s not yet implemented for node %s\n",\
			WHEREARGS, (oper), jvst_cnode_type_name((cnode)->type));\
		abort();							\
	} while (0)

#define UNKNOWN_NODE_TYPE(cnode) do { 				\
	fprintf(stderr, WHEREFMT "unknown node type %s\n",	\
		WHEREARGS, jvst_cnode_type_name((cnode)->type));\
	abort(); } while(0)

#define INVALID_OPERATION(cnode, oper) do {				\
	fprintf(stderr, WHEREFMT "invalid operation %s on %s node \n",  \
			WHEREARGS, jvst_cnode_type_name((cnode)->type), (oper)); \
		abort(); } while (0)

#define DIE(mesg) do {					\
	fprintf(stderr, WHEREFMT mesg, WHEREARGS);	\
	abort(); } while(0)

#define DIEF(mesg,...) do {					\
	fprintf(stderr, WHEREFMT mesg, WHEREARGS, __VA_ARGS__);	\
	abort(); } while(0)

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
		return &strset_pool.head->items[strset_pool.top++];
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
	memset(sset, 0, sizeof *sset);
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
		return &matchset_pool.head->items[matchset_pool.top++];
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
cnode_new_ref(struct json_string id)
{
	struct jvst_cnode *node;

	node = jvst_cnode_alloc(JVST_CNODE_REF);
	node->u.ref = json_strdup(id);

	return node;
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
	node->u.mcase.value_constraint = constraint;

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
		case JVST_CNODE_LENGTH_RANGE:
		case JVST_CNODE_PROP_RANGE:
		case JVST_CNODE_ITEM_RANGE:
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
			if (node->u.items != NULL) {
				jvst_cnode_free_tree(node->u.items);
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
	case JVST_CNODE_LENGTH_RANGE:
		return "LENGTH_RANGE";
	case JVST_CNODE_PROP_RANGE:
		return "PROP_RANGE";
	case JVST_CNODE_ITEM_RANGE:
		return "ITEM_RANGE";
	case JVST_CNODE_STR_MATCH:
		return "STR_MATCH";
	case JVST_CNODE_NUM_RANGE:
		return "NUM_RANGE";
	case JVST_CNODE_NUM_MULTIPLE_OF:
		return "NUM_MULTIPLE_OF";
	case JVST_CNODE_NUM_INTEGER:
		return "NUM_INTEGER";
	case JVST_CNODE_OBJ_PROP_SET:
		return "OBJ_PROP_SET";
	case JVST_CNODE_OBJ_PROP_MATCH:
		return "OBJ_PROP_MATCH";
	case JVST_CNODE_OBJ_PROP_DEFAULT:
		return "OBJ_PROP_DEFAULT";
	case JVST_CNODE_OBJ_PROP_NAMES:
		return "OBJ_PROP_NAMES";
	case JVST_CNODE_OBJ_REQUIRED:
		return "OBJ_REQUIRED";
	case JVST_CNODE_ARR_ITEM:
		return "ARR_ITEM";
	case JVST_CNODE_ARR_ADDITIONAL:
		return "ARR_ADDITIONAL";
	case JVST_CNODE_ARR_CONTAINS:
		return "ARR_CONTAINS";
	case JVST_CNODE_ARR_UNIQUE:
		return "ARR_UNIQUE";
	case JVST_CNODE_OBJ_REQMASK:
		return "OBJ_REQMASK";
	case JVST_CNODE_OBJ_REQBIT:
		return "OBJ_REQBIT";
	case JVST_CNODE_MATCH_SWITCH:
		return "MATCH_SWITCH";
	case JVST_CNODE_MATCH_CASE:
		return "MATCH_CASE";
	case JVST_CNODE_REF:
		return "REF";
	}

	fprintf(stderr, "unknown cnode type %d\n", type);
	abort();
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

static void
regexp_dump(struct sbuf *buf, struct ast_regexp *re)
{
	char *prefix = "";
	char delim   = '/';
	char match[256] = {0};

	if (re->str.len >= sizeof match) {
		memcpy(match, re->str.s, sizeof match - 4);
		match[sizeof match - 4] = '.';
		match[sizeof match - 3] = '.';
		match[sizeof match - 2] = '.';
	} else {
		memcpy(match, re->str.s, re->str.len);
	}

	switch (re->dialect) {
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
	sbuf_snprintf(buf, "%s%c%s%c", prefix, delim, match, delim);
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

	case JVST_CNODE_REF:
		{
			if (node->u.ref.len <= INT_MAX) {
				sbuf_snprintf(buf, "REF( \"%.*s\" )",
					(int)node->u.ref.len, node->u.ref.s);
			} else {
				sbuf_snprintf(buf, "REF( \"%.*s...\" )",
					INT_MAX, node->u.ref.s);
			}
		}
		break;

	case JVST_CNODE_NUM_INTEGER:
		sbuf_snprintf(buf, "IS_INTEGER");
		break;

	case JVST_CNODE_NUM_MULTIPLE_OF:
		sbuf_snprintf(buf, "MULTIPLE_OF(%g)", node->u.multiple_of);
		break;

	case JVST_CNODE_NUM_RANGE:
		{
			enum jvst_cnode_rangeflags flags;
			double min,max;

			flags = node->u.num_range.flags;
			min = node->u.num_range.min;
			max = node->u.num_range.max;

			// special case for equality
			if (min == max && flags == (JVST_CNODE_RANGE_MIN | JVST_CNODE_RANGE_MAX)) {
				goto num_range_equals;
			}

			sbuf_snprintf(buf, "NUM_RANGE(");
			if (flags & JVST_CNODE_RANGE_EXCL_MIN) {
				sbuf_snprintf(buf, "%g < ", node->u.num_range.min);
			} else if (flags & JVST_CNODE_RANGE_MIN) {
				sbuf_snprintf(buf, "%g <= ", node->u.num_range.min);
			}

			sbuf_snprintf(buf, "x");

			if (flags & JVST_CNODE_RANGE_EXCL_MAX) {
				sbuf_snprintf(buf, " < %g", node->u.num_range.max);
			} else if (flags & JVST_CNODE_RANGE_MAX) {
				sbuf_snprintf(buf, " <= %g", node->u.num_range.max);
			}

			sbuf_snprintf(buf, ")");
		}
		break;

num_range_equals:
		{
			double x = node->u.num_range.min;
			assert(node->u.num_range.max == x);
			assert(node->u.num_range.flags == (JVST_CNODE_RANGE_MIN | JVST_CNODE_RANGE_MAX));

			sbuf_snprintf(buf, "NUM_RANGE(x == %g)", x);
		}
		break;

	case JVST_CNODE_NOT:
		op = "NOT";
		assert(node->u.ctrl != NULL);
		assert(node->u.ctrl->next == NULL);  // NOT should have exactly one child
		goto and_or_xor; // FIXME: rename this (also, maybe factor to a function?)

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
		sbuf_snprintf(buf, "PROP_MATCH(\n");
		sbuf_indent(buf, indent + 2);
		regexp_dump(buf, &node->u.prop_match.match);
		sbuf_snprintf(buf, ",\n");

		sbuf_indent(buf, indent + 2);
		jvst_cnode_dump_inner(node->u.prop_match.constraint, buf, indent + 2);
		sbuf_snprintf(buf, "\n");
		sbuf_indent(buf, indent);
		sbuf_snprintf(buf, ")");
		break;

	case JVST_CNODE_OBJ_PROP_DEFAULT:
		sbuf_snprintf(buf, "PROP_DEFAULT(\n");
		sbuf_indent(buf, indent + 2);
		jvst_cnode_dump_inner(node->u.prop_default, buf, indent + 2);
		sbuf_snprintf(buf, "\n");
		sbuf_indent(buf, indent);
		sbuf_snprintf(buf, ")");
		break;

	case JVST_CNODE_OBJ_PROP_NAMES:
		sbuf_snprintf(buf, "PROP_NAMES(\n");
		sbuf_indent(buf, indent + 2);
		jvst_cnode_dump_inner(node->u.prop_names, buf, indent+2);
		sbuf_snprintf(buf, "\n");
		sbuf_indent(buf, indent);
		sbuf_snprintf(buf, ")");
		break;

	case JVST_CNODE_LENGTH_RANGE:
	case JVST_CNODE_PROP_RANGE:
	case JVST_CNODE_ITEM_RANGE:
		sbuf_snprintf(buf, "%s(", jvst_cnode_type_name(node->type));
		if (node->u.counts.min > 0) {
			sbuf_snprintf(buf, "%zu <= ", node->u.counts.min);
		}

		sbuf_snprintf(buf, "x");

		if (node->u.counts.upper > 0) {
			sbuf_snprintf(buf, " <= %zu", node->u.counts.max);
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

	case JVST_CNODE_OBJ_REQMASK:
		sbuf_snprintf(buf, "REQMASK(nbits=%zu)", node->u.reqmask.nbits);
		break;

	case JVST_CNODE_OBJ_REQBIT:
		sbuf_snprintf(buf, "REQBIT(bits=%zu)", node->u.reqbit.bit);
		break;

	case JVST_CNODE_MATCH_SWITCH:
		{
			struct jvst_cnode *c;

			sbuf_snprintf(buf, "MATCH_SWITCH(\n");

			if (node->u.mswitch.dft_case != NULL) {
				struct jvst_cnode *dft;

				dft = node->u.mswitch.dft_case;
				assert(dft->type == JVST_CNODE_MATCH_CASE);

				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "DEFAULT[\n");

				sbuf_indent(buf, indent+4);
				jvst_cnode_dump_inner(dft, buf, indent + 4);
				sbuf_snprintf(buf, "\n");

				sbuf_indent(buf, indent+2);
				if (node->u.mswitch.cases != NULL) {
					sbuf_snprintf(buf, "],\n");
				} else {
					sbuf_snprintf(buf, "]\n");
				}
			} else {
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "DEFAULT[ << WARNING: NO DEFAULT >> ],\n");
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

			sbuf_snprintf(buf, "MATCH_CASE(\n");
			// assert(node->u.mcase.matchset != NULL);

			for (ms = node->u.mcase.matchset; ms != NULL; ms = ms->next) {
				jvst_cnode_matchset_dump(ms, buf, indent+2);
				sbuf_snprintf(buf, ",\n");
			}

			if (node->u.mcase.name_constraint != NULL) {
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "NAME_CONSTRAINT[\n");

				sbuf_indent(buf, indent+4);
				jvst_cnode_dump_inner(node->u.mcase.name_constraint, buf, indent+4);
				sbuf_snprintf(buf, "\n");
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "],\n");
			}

			sbuf_indent(buf, indent+2);
			jvst_cnode_dump_inner(node->u.mcase.value_constraint, buf, indent+2);
			sbuf_snprintf(buf, "\n");
			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		break;

	case JVST_CNODE_STR_MATCH:
		sbuf_snprintf(buf, "STRMATCH(");
		regexp_dump(buf, &node->u.str_match);
		sbuf_snprintf(buf, ")");
		break;

	case JVST_CNODE_ARR_ITEM:
		{
			struct jvst_cnode *it;
			size_t i;

			sbuf_snprintf(buf, "ITEMS(\n");
			i=0;
			for (it = node->u.items; it != NULL; it = it->next) {
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "[ITEM %3zu]\n", i++);
				sbuf_indent(buf, indent+2);
				jvst_cnode_dump_inner(it, buf, indent+2);
				if (it->next) {
					sbuf_snprintf(buf, ",\n");
				} else {
					sbuf_snprintf(buf, "\n");
				}
			}
			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		break;

	case JVST_CNODE_ARR_ADDITIONAL:
		{
			struct jvst_cnode *it;

			sbuf_snprintf(buf, "ADDITIONAL(\n");

			it = node->u.items;
			assert(it->next == NULL);

			sbuf_indent(buf, indent+2);
			jvst_cnode_dump_inner(it, buf, indent+2);
			sbuf_snprintf(buf, "\n");

			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		break;

	case JVST_CNODE_ARR_CONTAINS:
		{
			struct jvst_cnode *it;

			sbuf_snprintf(buf, "CONTAINS(\n");

			it = node->u.contains;
			assert(it->next == NULL);

			sbuf_indent(buf, indent+2);
			jvst_cnode_dump_inner(it, buf, indent+2);
			sbuf_snprintf(buf, "\n");

			sbuf_indent(buf, indent);
			sbuf_snprintf(buf, ")");
		}
		break;

	case JVST_CNODE_ARR_UNIQUE:
		fprintf(stderr, WHEREFMT "**not implemented**\n",
			WHEREARGS);
		abort();
	}
}

int
jvst_cnode_dump(struct jvst_cnode *node, char *buf, size_t nb);

void
jvst_cnode_debug(struct jvst_cnode *node)
{
	jvst_cnode_print(stderr, node);
}

void
jvst_cnode_debug_forest(struct jvst_cnode_forest *ctrees)
{
	jvst_cnode_print_forest(stderr, ctrees);
}

struct cnode_id_pair {
	struct json_string id;
	struct jvst_cnode *ctree;
};

static int
find_ref_name(void *opaque, struct json_string *key, struct jvst_cnode **ctreep)
{
	struct cnode_id_pair *pair = opaque;

	assert(ctreep != NULL);

	if (*ctreep != pair->ctree) {
		return 1; // keep going
	}

	pair->id = *key;

	return 0;
}

void
jvst_cnode_print_forest(FILE *f, struct jvst_cnode_forest *forest)
{
	size_t i;
	static const struct cnode_id_pair zero;

	fprintf(f, "CNODE forest: %zu cnode trees\n", forest->len);

	for (i=0; i < forest->len; i++) {
		struct cnode_id_pair pair = zero;
		pair.ctree = forest->trees[i];

		if (jvst_cnode_id_table_foreach(forest->ref_ids, find_ref_name, &pair) == 0) {
			if (pair.id.len < INT_MAX) {
				fprintf(f, "[ REF: \"%.*s\" ]\n", (int)pair.id.len, pair.id.s);
			} else {
				fprintf(f, "[ REF: \"%.*s...\" ]\n", INT_MAX, pair.id.s);
			}
		} else {
			fprintf(f, "[ REF: UNKNOWN ]\n");
		}

		jvst_cnode_print(f, forest->trees[i]);
		fprintf(f,"\n");
	}
}

void
jvst_cnode_print(FILE *f, struct jvst_cnode *node)
{
	// FIXME: gross hack
	char buf[65536] = {0}; // 64K

	jvst_cnode_dump(node, buf, sizeof buf);
	fprintf(f, "%s\n", buf);
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
jvst_cnode_from_ast(const struct ast_schema *ast)
{
	struct jvst_cnode *translated, *simplified, *canonified;
	translated = jvst_cnode_translate_ast(ast);
	simplified = jvst_cnode_simplify(translated);
	canonified = jvst_cnode_canonify(simplified);
	return canonified;
}

static void
add_ast_constraint(struct jvst_cnode *sw, enum SJP_EVENT evt, struct jvst_cnode *constraint)
{
	struct jvst_cnode *curr, *jxn;
	
	assert(sw != NULL);
	assert(sw->type == JVST_CNODE_SWITCH);

	assert(constraint->next == NULL);

	assert(evt >= 0 && evt < ARRAYLEN(sw->u.sw));

	curr = sw->u.sw[evt];

	// add an AND for this constraint and the current one
	jxn = jvst_cnode_alloc(JVST_CNODE_AND);
	jxn->u.ctrl = constraint;
	constraint->next = curr;
	sw->u.sw[evt] = jxn;
}

static struct jvst_cnode *
cnode_enum_translate(struct json_value *v);

static struct jvst_cnode *
cnode_enum_translate_obj(struct json_value *v)
{
	struct jvst_cnode *jxn, **jpp;
	struct json_property *prop;

	struct ast_string_set *rprops, **rpp;
	struct jvst_cnode *pmatches, **pmpp;

	assert(v != NULL);
	assert(v->type == JSON_VALUE_OBJECT);

	// Need to build three constraints: properties, additional
	// properties, and required.
	//
	// All properties of the object are given const schemas.
	// All properties are required.
	// Any additional property is invalid.

	jxn = jvst_cnode_alloc(JVST_CNODE_AND);
	jpp = &jxn->u.ctrl;
	*jpp = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_DEFAULT);
	(*jpp)->u.prop_default = jvst_cnode_alloc(JVST_CNODE_INVALID);
	jpp = &(*jpp)->next;

	rprops = NULL;
	rpp = &rprops;

	pmatches = NULL;
	pmpp = &pmatches;

	for (prop = v->u.obj; prop != NULL; prop = prop->next) {
		struct ast_string_set *pn;
		struct jvst_cnode *vcons, *pmatch;

		*rpp = cnode_strset(prop->name, NULL);
		rpp = &(*rpp)->next;

		vcons = cnode_enum_translate(&prop->value);
		assert(vcons != NULL);

		pmatch = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_MATCH);
		pmatch->u.prop_match.match.dialect = RE_LITERAL;
		pmatch->u.prop_match.match.str = prop->name;
		pmatch->u.prop_match.constraint = vcons;

		*pmpp = pmatch;
		pmpp = &pmatch->next;
	}

	// if either is non-NULL then both should be non-NULL
	assert((rprops != NULL) == (pmatches != NULL));

	if (rprops != NULL) {
		struct jvst_cnode *req;

		req = jvst_cnode_alloc(JVST_CNODE_OBJ_REQUIRED);
		req->u.required = rprops;

		*jpp = req;
		jpp = &(*jpp)->next;
	}

	if (pmatches != NULL) {
		struct jvst_cnode *pset;
		pset = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_SET);
		pset->u.prop_set = pmatches;
		
		*jpp = pset;
		jpp = &(*jpp)->next;
	}

	return jxn;
}

static struct jvst_cnode *
cnode_enum_translate_arr(struct json_value *v)
{
	struct jvst_cnode *jxn, **jpp;
	struct json_element *elt;
	struct jvst_cnode *items, **ipp;

	assert(v != NULL);
	assert(v->type == JSON_VALUE_ARRAY);

	// Need to build two constraints: items and additional
	// items
	//
	// All items of the array are given const schemas.
	// Any additional item is invalid.

	jxn = jvst_cnode_alloc(JVST_CNODE_AND);
	jpp = &jxn->u.ctrl;

	*jpp = jvst_cnode_alloc(JVST_CNODE_ARR_ADDITIONAL);
	(*jpp)->u.items = cnode_new_switch(0);
	jpp = &(*jpp)->next;

	items = NULL;
	ipp = &items;

	for (elt = v->u.arr; elt != NULL; elt = elt->next) {
		*ipp = cnode_enum_translate(&elt->value);
		ipp = &(*ipp)->next;
	}

	if (items != NULL) {
		struct jvst_cnode *cons;
		cons = jvst_cnode_alloc(JVST_CNODE_ARR_ITEM);
		cons->u.items = items;

		*jpp = cons;
		jpp = &(*jpp)->next;
	}

	return jxn;
}

static struct jvst_cnode *
cnode_enum_translate(struct json_value *v)
{
	struct jvst_cnode *sw;

	sw = cnode_new_switch(0);
	switch (v->type) {
	case JSON_VALUE_ARRAY:
		sw->u.sw[SJP_ARRAY_BEG] = cnode_enum_translate_arr(v);
		return sw;

	case JSON_VALUE_OBJECT:
		sw->u.sw[SJP_OBJECT_BEG] = cnode_enum_translate_obj(v);
		return sw;

	case JSON_VALUE_STRING:
		{
			struct jvst_cnode *scons;

			scons = jvst_cnode_alloc(JVST_CNODE_STR_MATCH);
			scons->u.str_match.dialect = RE_LITERAL;
			scons->u.str_match.str = v->u.str;

			sw->u.sw[SJP_STRING] = scons;
		}
		return sw;

	case JSON_VALUE_NUMBER:
	case JSON_VALUE_INTEGER:
		{
			struct jvst_cnode *neq;
			double x;

			x = v->u.n;

			neq = jvst_cnode_alloc(JVST_CNODE_NUM_RANGE);
			neq->u.num_range.flags = JVST_CNODE_RANGE_MIN|JVST_CNODE_RANGE_MAX;
			neq->u.num_range.min = x;
			neq->u.num_range.max = x;
			sw->u.sw[SJP_NUMBER] = neq;
		}
		return sw;

	case JSON_VALUE_BOOL:
		sw->u.sw[v->u.v ? SJP_TRUE : SJP_FALSE] = jvst_cnode_alloc(JVST_CNODE_VALID);
		return sw;

	case JSON_VALUE_NULL:
		sw->u.sw[SJP_NULL] = jvst_cnode_alloc(JVST_CNODE_VALID);
		return sw;

	default:
		DIEF("unknown JSON type for enum/const: 0x%x\n", v->type);
	}

	return jvst_cnode_alloc(JVST_CNODE_INVALID);
}

static
void add_cnode_ids(struct jvst_cnode_id_table *tbl, const struct ast_schema *ast, struct jvst_cnode *n)
{
	// XXX - better error messages!
	// XXX - better error handling!
	if (!jvst_cnode_id_table_add(tbl, ast->path, n)) {
		fprintf(stderr, "error adding path -> cnode entry to id table\n");
		abort();
	}

	if (ast->id.len > 0) {
		if (!jvst_cnode_id_table_add(tbl, ast->id, n)) {
			fprintf(stderr, "error adding id -> cnode entry to id table\n");
			abort();
		}
	}
}

struct ast_translator {
	struct jvst_cnode_forest forest;

	struct {
		size_t len;
		size_t cap;
		struct jvst_cnode **items;
	} refs;
};

static void
xlator_add_ref(struct ast_translator *xl, struct jvst_cnode *ref)
{
	size_t i;

	assert(ref->type == JVST_CNODE_REF);

	if (xl->refs.len >= xl->refs.cap) {
		xl->refs.items = xenlargevec(xl->refs.items, &xl->refs.cap, 1, sizeof xl->refs.items[0]);
	}

	assert(xl->refs.len < xl->refs.cap);
	xl->refs.items[xl->refs.len++] = ref;
}

static int
xlator_has_root(struct ast_translator *xl, struct jvst_cnode *root)
{
	size_t i,n;

	n = xl->forest.len;

	// XXX - dumb linear scan.  do we need to do more?
	for (i=0; i < n; i++) {
		if (xl->forest.trees[i] == root) {
			return 1;
		}
	}

	return 0;
}

static void
xlator_finalize(struct ast_translator *xl)
{
	if (xl == NULL) {
		return;
	}

	free(xl->refs.items);
}

static void 
xlator_initialize(struct ast_translator *xl)
{
	static const struct ast_translator zero;

	*xl = zero;
	jvst_cnode_forest_initialize(&xl->forest);
}

static void 
xlator_add_tree(struct ast_translator *xl, struct jvst_cnode *tree)
{
	jvst_cnode_forest_add_tree(&xl->forest, tree);
}

// Just do a raw translation without doing any optimization of the
// constraint tree
static struct jvst_cnode *
cnode_translate_ast_with_ids(const struct ast_schema *ast, struct ast_translator *xl)
{
	struct jvst_cnode *node;
	enum json_valuetype types;

	assert(ast != NULL);

	if (ast->kws & KWS_VALUE) {
	       	if (ast->value.type != JSON_VALUE_BOOL) {
			fprintf(stderr, "Invalid JSON value type.  Schemas must be objects or booleans.\n");
			abort();
		}

		node = cnode_new_switch(ast->value.u.v);
		add_cnode_ids(xl->forest.all_ids, ast, node);

		return node;
	}

	// if an object has a "$ref", then all other properties must be
	// ignored
	if (ast->kws & KWS_HAS_REF) {
		assert(ast->ref.len > 0);
		assert(ast->ref.s != NULL);

		node = cnode_new_ref(ast->ref);
		add_cnode_ids(xl->forest.all_ids, ast, node);

		// for first pass, add (id -> NULL) entries to the
		// ref_ids table
		jvst_cnode_id_table_add(xl->forest.ref_ids, ast->ref, NULL);

		// add node the ref list
		xlator_add_ref(xl, node);

		return node;
	}

	if (ast->definitions != NULL) {
		const struct ast_schema_set *def;
		// add definitions to the all_ids table
		for (def = ast->definitions; def != NULL; def = def->next) {
			assert(def->schema != NULL);
			cnode_translate_ast_with_ids(def->schema, xl);
		}
	}

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
		struct jvst_cnode *range;

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

		add_ast_constraint(node, SJP_NUMBER, range);
	}

	if (ast->kws & KWS_MULTIPLE_OF) {
		struct jvst_cnode *multiple_of;
		assert(ast->multiple_of > 0.0);

		multiple_of = jvst_cnode_alloc(JVST_CNODE_NUM_MULTIPLE_OF);
		multiple_of->u.multiple_of = ast->multiple_of;

		add_ast_constraint(node, SJP_NUMBER, multiple_of);
	}

	if (ast->pattern.str.s != NULL) {
		struct jvst_cnode *strmatch, *topjxn;

		strmatch = jvst_cnode_alloc(JVST_CNODE_STR_MATCH);
		// FIXME: I think this will leak!
		strmatch->u.str_match = ast->pattern;

		add_ast_constraint(node, SJP_STRING, strmatch);
	}

	if (ast->kws & (KWS_MIN_LENGTH | KWS_MAX_LENGTH)) {
		struct jvst_cnode *range, *jxn;

		range = jvst_cnode_alloc(JVST_CNODE_LENGTH_RANGE);
		range->u.counts.min = ast->min_length;
		range->u.counts.max = ast->max_length;

		range->u.counts.upper = !!(ast->kws & KWS_MAX_LENGTH);

		add_ast_constraint(node, SJP_STRING, range);
	}

	if (ast->items != NULL) {
		struct jvst_cnode *items_constraint;

		assert(ast->items != NULL);

		if (ast->kws & KWS_SINGLETON_ITEMS) {
			struct jvst_cnode *constraint;

			assert(ast->items->schema != NULL);
			assert(ast->items->next == NULL);

			constraint = cnode_translate_ast_with_ids(ast->items->schema, xl);
			items_constraint = jvst_cnode_alloc(JVST_CNODE_ARR_ADDITIONAL);
			items_constraint->u.items = constraint;
		} else {
			struct jvst_cnode *itemlist, **ilpp;
			struct ast_schema_set *sl;

			itemlist = NULL;
			ilpp = &itemlist;
			for (sl = ast->items; sl != NULL; sl = sl->next) {
				struct jvst_cnode *constraint;

				assert(sl->schema != NULL);

				constraint = cnode_translate_ast_with_ids(sl->schema, xl);
				*ilpp = constraint;
				ilpp = &constraint->next;
			}

			items_constraint = jvst_cnode_alloc(JVST_CNODE_ARR_ITEM);
			items_constraint->u.items = itemlist;
		}

		add_ast_constraint(node, SJP_ARRAY_BEG, items_constraint);
	}

	if (ast->additional_items != NULL && ast->items != NULL && (ast->kws & KWS_SINGLETON_ITEMS) == 0) {
		struct jvst_cnode *constraint, *additional;

		constraint = cnode_translate_ast_with_ids(ast->additional_items, xl);
		additional = jvst_cnode_alloc(JVST_CNODE_ARR_ADDITIONAL);
		additional->u.items = constraint;

		add_ast_constraint(node, SJP_ARRAY_BEG, additional);
	}

	if (ast->contains != NULL) {
		struct jvst_cnode *constraint, *contains;

		constraint = cnode_translate_ast_with_ids(ast->contains, xl);
		contains = jvst_cnode_alloc(JVST_CNODE_ARR_CONTAINS);
		contains->u.contains = constraint;

		add_ast_constraint(node, SJP_ARRAY_BEG, contains);
	}

	if (ast->kws & (KWS_MIN_ITEMS | KWS_MAX_ITEMS)) {
		struct jvst_cnode *range, *jxn;

		range = jvst_cnode_alloc(JVST_CNODE_ITEM_RANGE);
		range->u.counts.min = ast->min_items;
		range->u.counts.max = ast->max_items;

		range->u.counts.upper = !!(ast->kws & KWS_MAX_ITEMS);

		add_ast_constraint(node, SJP_ARRAY_BEG, range);
	}

	if (ast->properties.set != NULL) {
		struct jvst_cnode **plist, *phead, *prop_set;
		struct ast_property_schema *pset;

		prop_set = NULL;
		phead = NULL;
		plist = &phead;

		for (pset = ast->properties.set; pset != NULL; pset = pset->next) {
			struct jvst_cnode *pnode;
			pnode = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_MATCH);
			// FIXME: I think this will leak!
			pnode->u.prop_match.match = pset->pattern;
			pnode->u.prop_match.constraint = cnode_translate_ast_with_ids(pset->schema, xl);
			*plist = pnode;
			plist = &pnode->next;
		}

		prop_set = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_SET);
		prop_set->u.prop_set = phead;
		assert(phead != NULL);

		add_ast_constraint(node, SJP_OBJECT_BEG, prop_set);
	}

	if (ast->additional_properties != NULL) {
		struct jvst_cnode *constraint, *pdft;

		constraint = cnode_translate_ast_with_ids(ast->additional_properties, xl);
		assert(constraint != NULL);
		assert(constraint->next == NULL);

		pdft = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_DEFAULT);
		pdft->u.prop_default = constraint;

		add_ast_constraint(node, SJP_OBJECT_BEG, pdft);
	}

	if (ast->property_names != NULL) {
		struct jvst_cnode *constraint;
		struct jvst_cnode *pnames;

		constraint = cnode_translate_ast_with_ids(ast->property_names, xl);

		pnames = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_NAMES);
		pnames->u.prop_names = constraint;

		add_ast_constraint(node, SJP_OBJECT_BEG, pnames);
	}

	if (ast->kws & (KWS_MIN_PROPERTIES | KWS_MAX_PROPERTIES)) {
		struct jvst_cnode *range, *jxn;

		range = jvst_cnode_alloc(JVST_CNODE_PROP_RANGE);
		range->u.counts.min = ast->min_properties;
		range->u.counts.max = ast->max_properties;

		range->u.counts.upper = !!(ast->kws & KWS_MAX_PROPERTIES);

		add_ast_constraint(node, SJP_OBJECT_BEG, range);
	}

	if (ast->required.set != NULL) {
		struct jvst_cnode *req, *jxn;

		req = jvst_cnode_alloc(JVST_CNODE_OBJ_REQUIRED);
		req->u.required = ast->required.set;

		add_ast_constraint(node, SJP_OBJECT_BEG, req);
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

		// FIXME: this assumes that the top node is a switch!
		assert(node->type == JVST_CNODE_SWITCH);
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
			sw->next = cnode_translate_ast_with_ids(pschema->schema, xl);

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
			c = cnode_translate_ast_with_ids(sset->schema, xl);
			*conds = c;
			conds = &c->next;
		}

		top_jxn = jvst_cnode_alloc(JVST_CNODE_AND);
		top_jxn->u.ctrl = some_jxn;
		some_jxn->next = node;
		node = top_jxn;
	}

	if (ast->xenum != NULL) {
		struct ast_value_set *v;
		struct jvst_cnode *top_jxn, *cons, **jpp;

		cons = NULL;
		jpp = &cons;

		for (v=ast->xenum; v != NULL; v = v->next) {
			*jpp = cnode_enum_translate(&v->value);
			jpp = &(*jpp)->next;
		}

		top_jxn = jvst_cnode_alloc(JVST_CNODE_AND);
		assert(cons != NULL);
		if (cons->next == NULL) {
			cons->next = node;
			top_jxn->u.ctrl = cons;
		} else {
			struct jvst_cnode *jxn;

			jxn = jvst_cnode_alloc(JVST_CNODE_OR);
			jxn->u.ctrl = cons;
			jxn->next = node;

			top_jxn->u.ctrl = jxn;
		}

		node = top_jxn;
	}

	add_cnode_ids(xl->forest.all_ids, ast, node);
	return node;
}

static int
cnode_reroot_referred_ids(void *opaque, struct json_string *id, struct jvst_cnode **ctreep)
{
	struct ast_translator *xl;
	struct jvst_cnode *orig, *copy;

	assert(ctreep != NULL);
	assert(*ctreep == NULL);

	xl = opaque;

	orig = jvst_cnode_id_table_lookup(xl->forest.all_ids, *id);

	if (orig == NULL) {
		if (id->len <= INT_MAX) {
			fprintf(stderr, "WARNING: cannot match $ref(%.*s) with a node\n",
				(int)id->len, id->s);
		} else {
			fprintf(stderr, "WARNING: cannot match $ref(%.*s...) with a node\n",
				INT_MAX, id->s);
		}

		// Keep going to report all missing references
		//
		// The dangling reference will be caught in the IR
		// translation and we'll abort then.
		return 1;
	}

	// if it's already a root, we're good
	if (xlator_has_root(xl, orig)) {
		return 1;
	}

	// not already a root... cut it off the tree, make it into a new
	// root, and replace the original node with a REF to the new
	// root.
	//
	// we don't want to descend the tree to find the node's parent,
	// so we make a shallow copy, make that the new root, and
	// convert the original into REF node
	copy = jvst_cnode_alloc(orig->type);
	*copy = *orig;

	// add shallow copy as a new root
	xlator_add_tree(xl,copy);

	// change original value to a REF
	orig->type = JVST_CNODE_REF;
	orig->u.ref = *id;

	// update value in all_ids map
	if (!jvst_cnode_id_table_set(xl->forest.all_ids, *id, copy)) {
		fprintf(stderr, "cannot update ID in table\n");
		abort();
	}

	// update value in ref_ids map
	*ctreep = copy;

	return 1;
}

struct jvst_cnode_forest *
jvst_cnode_translate_ast_with_ids(const struct ast_schema *ast)
{
	struct ast_translator xl;
	struct jvst_cnode_forest *forest;
	struct jvst_cnode *ctree;

	xlator_initialize(&xl);
	ctree = cnode_translate_ast_with_ids(ast, &xl);

	assert(ctree != NULL);

	// add the main tree
	xlator_add_tree(&xl, ctree);

	// now iterate through the entries of the ref_ids table,
	// splitting them into separate trees
	jvst_cnode_id_table_foreach(xl.forest.ref_ids, cnode_reroot_referred_ids, &xl);

	// finally, add the root as a ref
	{
		struct json_string root_id = { .s = "#", .len = 1 };
		jvst_cnode_id_table_add(xl.forest.ref_ids, root_id, ctree);
	}

	forest = malloc(sizeof *forest);
	*forest = xl.forest;

	xlator_finalize(&xl);

	return forest;
}

struct jvst_cnode *
jvst_cnode_translate_ast(const struct ast_schema *ast)
{
	struct jvst_cnode_forest *forest;
	struct jvst_cnode *root;

	forest = jvst_cnode_translate_ast_with_ids(ast);
	if (forest->len == 0) {
		return NULL;
	}

	root = forest->trees[0];

	jvst_cnode_forest_delete(forest);

	return root;
}

static struct jvst_cnode *
cnode_deep_copy(struct jvst_cnode *node);

static int
mcase_update_opaque(const struct fsm *dfa, const struct fsm_state *st, void *opaque)
{
	struct jvst_cnode *node, *ndup;

	(void)opaque;

	if (!fsm_isend(dfa, st)) {
		return 1;
	}

	node = fsm_getopaque((struct fsm *)dfa, st);
	assert(node->type == JVST_CNODE_MATCH_CASE);
	assert(node->u.mcase.tmp != NULL);

	ndup = node->u.mcase.tmp;
	fsm_setopaque((struct fsm *)dfa, (struct fsm_state *)st, ndup);

	return 1;
}

static int print_mcases_walker(const struct fsm *fsm, const struct fsm_state *st, void *opaque)
{
	struct jvst_cnode *cn;

	(void)opaque;
	if (!fsm_isend(fsm,st)) {
		return 1;
	}

	cn = fsm_getopaque((struct fsm *)fsm,(struct fsm_state *)st);
	fprintf(stderr, "fsm=%p, st=%p, cnode=%p\n",
		(void *)fsm, (void *)st, (void *)cn);
	jvst_cnode_debug(cn);
	fprintf(stderr, "tmp=%p collected=%d copied=%d\n",
		cn->u.mcase.tmp,
		cn->u.mcase.collected,
		cn->u.mcase.copied);
	fprintf(stderr, "\n");

	return 1;
}

static void print_mcases(struct fsm *fsm)
{
	fsm_walk_states(fsm, NULL, print_mcases_walker);
}

static void print_mswitch(struct jvst_cnode *node)
{
	struct jvst_cnode *mc;
	size_t i;

	fprintf(stderr, "mcases in dfa\n");
	print_mcases(node->u.mswitch.dfa);

	fprintf(stderr, "mcases in cases list...\n");
	for(i=0,mc = node->u.mswitch.cases; mc != NULL; i++,mc = mc->next) {
		fprintf(stderr, "[%05zu] %p copied? %d  collected? %d  tmp=%p\n",
			i, (void *)mc, mc->u.mcase.copied, mc->u.mcase.collected, mc->u.mcase.tmp);
	}
}

void (*volatile foofunc)(struct jvst_cnode *) = &print_mswitch;

static struct jvst_cnode *
cnode_mswitch_copy(struct jvst_cnode *node)
{
	struct jvst_cnode *tree, *mcases, **mcpp;
	struct fsm *dup_fsm;

	/*
	fprintf(stderr,"---> orig: %p\n", (void *)node);
	print_mswitch(node);
	fprintf(stderr, "\n");
	*/
	tree = jvst_cnode_alloc(JVST_CNODE_MATCH_SWITCH);

	// it would be lovely to copy this but there doesn't seem to be
	// a way to get/set it on the fsm.
	tree->u.mswitch.opts = node->u.mswitch.opts;

	// duplicate FSM
	//
	// XXX - need to determine how we're keeping track of
	// FSMs
	dup_fsm = NULL;
	if (node->u.mswitch.dfa != NULL) {
		dup_fsm = fsm_clone(node->u.mswitch.dfa);
	}

	tree->u.mswitch.dfa = dup_fsm;

	// copy and collect all opaque states
	mcpp = &tree->u.mswitch.cases;
	for (mcases = node->u.mswitch.cases; mcases != NULL; mcases = mcases->next) {
		struct jvst_cnode *mcdup;

		assert(mcases->u.mcase.tmp == NULL);
		assert(!mcases->u.mcase.copied);

		mcdup = cnode_deep_copy(mcases);

		assert(mcdup->u.mcase.tmp == NULL);
		assert(!mcdup->u.mcase.copied);

		mcases->u.mcase.tmp = mcdup;
		mcases->u.mcase.copied = 1;

		*mcpp = mcdup;
		mcpp = &mcdup->next;
	}

	// update the copied DFA
	if (dup_fsm != NULL) {
		fsm_walk_states(dup_fsm, NULL, mcase_update_opaque);
	}

	// all mswitch nodes need a default case!
	assert(node->u.mswitch.dft_case != NULL);
	assert(node->u.mswitch.dft_case->type == JVST_CNODE_MATCH_CASE);
	tree->u.mswitch.dft_case = cnode_deep_copy(node->u.mswitch.dft_case);

	/*
	if (node->u.mswitch.constraints != NULL) {
		tree->u.mswitch.constraints = cnode_deep_copy(node->u.mswitch.constraints);
	}
	*/

	/*
	fprintf(stderr,"---> copy: %p\n", (void *)tree);
	print_mswitch(tree);
	fprintf(stderr, "\n");
	*/
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

	case JVST_CNODE_NUM_MULTIPLE_OF:
		tree = jvst_cnode_alloc(node->type);
		tree->u.multiple_of = node->u.multiple_of;
		return tree;

	case JVST_CNODE_REF:
		tree = jvst_cnode_alloc(node->type);
		tree->u.ref = json_strdup(node->u.ref);
		return tree;

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

	case JVST_CNODE_LENGTH_RANGE:
	case JVST_CNODE_PROP_RANGE:
	case JVST_CNODE_ITEM_RANGE:
		tree = jvst_cnode_alloc(node->type);
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

	case JVST_CNODE_OBJ_PROP_DEFAULT:
		tree = jvst_cnode_alloc(node->type);
		tree->u.prop_default = cnode_deep_copy(node->u.prop_default);
		return tree;

	case JVST_CNODE_OBJ_PROP_NAMES:
		tree = jvst_cnode_alloc(node->type);
		tree->u.prop_names = node->u.prop_names;
		return tree;

	case JVST_CNODE_OBJ_REQUIRED:
		tree = jvst_cnode_alloc(node->type);
		tree->u.required = node->u.required;
		return tree;

	case JVST_CNODE_ARR_ITEM:
		{
			struct jvst_cnode *item, **ip;
			tree = jvst_cnode_alloc(node->type);
			ip = &tree->u.items;
			for (item = node->u.items; item != NULL; item = item->next) {
				*ip = cnode_deep_copy(item);
				ip  = &(*ip)->next;
			}
			return tree;
		}

	case JVST_CNODE_ARR_ADDITIONAL:
		tree = jvst_cnode_alloc(node->type);
		tree->u.items = cnode_deep_copy(node->u.items);
		return tree;

	case JVST_CNODE_ARR_CONTAINS:
		tree = jvst_cnode_alloc(node->type);
		tree->u.contains = cnode_deep_copy(node->u.contains);
		return tree;

	case JVST_CNODE_OBJ_REQMASK:
		tree = jvst_cnode_alloc(JVST_CNODE_OBJ_REQMASK);
		tree->u.reqmask = node->u.reqmask;
		return tree;

	case JVST_CNODE_OBJ_REQBIT:
		tree = jvst_cnode_alloc(JVST_CNODE_OBJ_REQBIT);
		tree->u.reqbit = node->u.reqbit;
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

			if (node->u.mcase.name_constraint) {
				tree->u.mcase.name_constraint = cnode_deep_copy(node->u.mcase.name_constraint);
			}

			tree->u.mcase.value_constraint = cnode_deep_copy(node->u.mcase.value_constraint);
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
cnode_simplify_xor_switches(struct jvst_cnode *top)
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

// merges any children that are PROPSET nodes into a single
// PROPSET that contains all of the PROP_MATCHes.
//
// Collects PROP_DEFAULT nodes, ANDing their constraints, and adds the
// PROP_DEFAULT node as a child of the PROPSET.
//
// Note that if no PROPSET node exists
static struct jvst_cnode *
cnode_simplify_and_propsets(struct jvst_cnode *top)
{
	struct jvst_cnode *comb, *psets, *pdfts, **dftpp, *pnames, **pnpp, **npp;
	size_t npsets, npdfts, npnames;

	// check how many PROPSET children we have... if less than two,
	// no simplification is necessary
	npsets  = 0;
	npdfts  = 0;
	npnames = 0;
	{
		struct jvst_cnode *node;
		for (node = top->u.ctrl; node != NULL; node= node->next) {
			switch (node->type) {
			case JVST_CNODE_OBJ_PROP_SET:
				npsets++;
				break;

			case JVST_CNODE_OBJ_PROP_DEFAULT:
				npdfts++;
				break;

			case JVST_CNODE_OBJ_PROP_NAMES:
				npnames++;
				break;

			default:
				break;
			}
		}
	}

	// If only less than two PROPSETs and no PROP_DEFAULT, return
	if (npsets < 2 && npdfts == 0 && npnames == 0) {
		return top;
	}

	// collect all PROPSET and PROP_DEFAULT children, removing them
	// from the parent's list of nodes.  We keep them in different
	// lists of nodes
	psets = NULL;
	pdfts = NULL;  dftpp = &pdfts;
	pnames = NULL; pnpp  = &pnames;
	{
		struct jvst_cnode **setpp;

		setpp = &psets;
		for (npp = &top->u.ctrl; *npp != NULL; ) {
			switch ((*npp)->type) {
			case JVST_CNODE_OBJ_PROP_SET:
				*setpp = *npp;
				*npp = (*npp)->next;

				setpp = &(*setpp)->next;
				*setpp = NULL;
				break;

			case JVST_CNODE_OBJ_PROP_DEFAULT:
				*dftpp = *npp;
				*npp = (*npp)->next;

				dftpp = &(*dftpp)->next;
				*dftpp = NULL;
				break;

			case JVST_CNODE_OBJ_PROP_NAMES:
				*pnpp = *npp;
				*npp = (*npp)->next;

				pnpp = &(*pnpp)->next;
				*pnpp = NULL;
				break;

			default:
				npp = &(*npp)->next;
				break;
			}
		}
	}

	// merge all PROP_MATCH cases into one PROPSET.
	//
	// PROPSET nodes can have PROP_MATCH and PROP_DEFAULT children.
	// We want to combine the PROP_MATCH children into a single
	// PROP_SET node, and to add the PROP_DEFAULT children to the
	// dftpp list so we can process all the PROP_DEFAULT children
	// together.
	comb = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_SET);
	{
		struct jvst_cnode *node, **pmpp;

		pmpp = &comb->u.prop_set;
		for (node=psets; node != NULL; node = node->next) {
			assert(node->u.prop_set != NULL);
			assert(node->type == JVST_CNODE_OBJ_PROP_SET);
			assert(node->u.prop_set->type == JVST_CNODE_OBJ_PROP_MATCH ||
				node->u.prop_set->type == JVST_CNODE_OBJ_PROP_NAMES ||
				node->u.prop_set->type == JVST_CNODE_OBJ_PROP_DEFAULT);

			*pmpp = node->u.prop_set;
			while (*pmpp != NULL) {
				switch ((*pmpp)->type) {
				case JVST_CNODE_OBJ_PROP_DEFAULT:
					// add node to dftpp list and
					// remove from pmpp list
					*dftpp = *pmpp;
					*pmpp = (*pmpp)->next;
					dftpp = &(*dftpp)->next;
					*dftpp = NULL;
					break;

				case JVST_CNODE_OBJ_PROP_NAMES:
					// add node to pnpp list and
					// remove from pmpp list
					*pnpp = *pmpp;
					*pmpp = (*pmpp)->next;
					pnpp = &(*pnpp)->next;
					*pnpp = NULL;
					break;

				case JVST_CNODE_OBJ_PROP_MATCH:
					pmpp = &(*pmpp)->next;
					break;
					
				default:
					UNKNOWN_NODE_TYPE(*pmpp);
				}
			}
		}
	}

	// combine constraints for all PROP_DEFAULT nodes into a single
	// PROP_DEFAULT node.  We combine the constraints by ANDing them
	// together.
	//
	// Add the resulting PROP_DEFAULT node to the combined PROPSET
	// node.
	if (pdfts != NULL) {
		struct jvst_cnode *comb_dft;

		if (pdfts->next == NULL) {
			comb_dft = pdfts;
		} else {
			struct jvst_cnode *node, *jxn, **jpp;

			jxn = jvst_cnode_alloc(JVST_CNODE_AND);
			jpp = &jxn->u.ctrl;
			for (node = pdfts; node != NULL; node = node->next) {
				assert(node->u.prop_default != NULL);
				assert(node->u.prop_default->next == NULL);

				*jpp = node->u.prop_default;
				jpp = &(*jpp)->next;
			}

			assert(jxn->u.ctrl != NULL);
			assert(jxn->u.ctrl->next != NULL); // should have at least two constraints!

			comb_dft = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_DEFAULT);
			comb_dft->u.prop_default = jvst_cnode_simplify(jxn);
		}

		// prepend to combine PROPSET list
		assert(comb_dft->next == NULL);
		comb_dft->next = comb->u.prop_set;
		comb->u.prop_set = comb_dft;
	}

	// Add PROP_NAMES node to the PROPSET.  There should be at most
	// one PROP_NAMES node.
	if (pnames != NULL) {
		if (pnames->next != NULL) {
			DIE("multiple PROP_NAMES nodes not supported\n");
		}

		pnames->next = comb->u.prop_set;
		comb->u.prop_set = pnames;
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

static struct jvst_cnode *
cnode_simplify_and_required(struct jvst_cnode *top)
{
	// merges any children that are REQUIRED nodes into a single
	// REQUIRED that contains all of the required elements.
	//
	// XXX - Currently does not eliminate duplicated required names.
	//       The DFA construction will do this, but we could also do
	//       this here if it helped with performance.
	struct jvst_cnode *node, *reqs, **rpp, **npp, *comb;
	struct ast_string_set **sspp;
	size_t nreqs;

	// check how many REQUIRED children we have... if less than two,
	// no simplification is necessary
	for (nreqs = 0, node = top->u.ctrl; node != NULL; node= node->next) {
		if (node->type == JVST_CNODE_OBJ_REQUIRED) {
			nreqs++;
		}
	}

	if (nreqs < 2) {
		return top;
	}

	// collect all REQUIRED children
	reqs = NULL;
	rpp = &reqs;
	for (npp = &top->u.ctrl; *npp != NULL; ) {
		if ((*npp)->type != JVST_CNODE_OBJ_REQUIRED) {
			npp = &(*npp)->next;
			continue;
		}

		*rpp = *npp;
		*npp = (*npp)->next;

		rpp = &(*rpp)->next;
		*rpp = NULL;
	}

	// merge all REQUIRED cases into one REQUIRED set
	comb = jvst_cnode_alloc(JVST_CNODE_OBJ_REQUIRED);
	sspp = &comb->u.required;
	for (node=reqs; node != NULL; node = node->next) {
		*sspp = cnode_strset_copy(node->u.required);
		for (; *sspp != NULL; sspp = &(*sspp)->next) {
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
	struct jvst_cnode *node, *next, *newlist, **pp;

	assert(top != NULL);
	assert(top->type == JVST_CNODE_AND || top->type == JVST_CNODE_OR);
	assert(top->u.ctrl != NULL);

	// combine subnodes of the same type (ie: AND will combine with
	// AND and OR will combine with OR)
	newlist = NULL;
	pp = &newlist;
	for (node = top->u.ctrl; node != NULL; node = next) {
		next = node->next;

		if (node->type != top->type) {
			*pp = node;
			pp = &node->next;
			continue;
		}

		assert(node->u.ctrl != NULL);

		*pp = node->u.ctrl;
		while (*pp != NULL) {
			pp = &(*pp)->next;
		}
	}

	top->u.ctrl = newlist;
}

static struct jvst_cnode *
cnode_or_constraints(struct jvst_cnode *c1, struct jvst_cnode *c2)
{
	struct jvst_cnode *jxn;

	assert(c1 != NULL);
	assert(c2 != NULL);

	assert(c1->next == NULL);
	assert(c2->next == NULL);

	if (c1->type == JVST_CNODE_VALID) {
		return c1;
	}

	if (c1->type == JVST_CNODE_INVALID) {
		return c2;
	}

	if (c2->type == JVST_CNODE_VALID) {
		return c2;
	}

	if (c2->type == JVST_CNODE_INVALID) {
		return c1;
	}

	jxn = jvst_cnode_alloc(JVST_CNODE_OR);
	c1->next = c2;
	jxn->u.ctrl = c1;

	return jvst_cnode_simplify(jxn);
}

static struct jvst_cnode *
cnode_xor_constraints(struct jvst_cnode *c1, struct jvst_cnode *c2)
{
	struct jvst_cnode *jxn;

	assert(c1 != NULL);
	assert(c2 != NULL);

	assert(c1->next == NULL);
	assert(c2->next == NULL);

	if (c1->type == JVST_CNODE_INVALID) {
		return c2;
	}

	if (c2->type == JVST_CNODE_INVALID) {
		return c1;
	}

	if (c1->type == JVST_CNODE_VALID && c2->type == JVST_CNODE_VALID) {
		return jvst_cnode_alloc(JVST_CNODE_INVALID);
	}

	jxn = jvst_cnode_alloc(JVST_CNODE_XOR);
	c1->next = c2;
	jxn->u.ctrl = c1;

	return jvst_cnode_simplify(jxn);
}

static struct jvst_cnode *
cnode_and_constraints(struct jvst_cnode *c1, struct jvst_cnode *c2)
{
	struct jvst_cnode *jxn;

	assert(c1 != NULL);
	assert(c2 != NULL);

	assert(c1->next == NULL);
	assert(c2->next == NULL);

	if (c1->type == JVST_CNODE_VALID) {
		return c2;
	}

	if (c1->type == JVST_CNODE_INVALID) {
		return c1;
	}

	if (c2->type == JVST_CNODE_VALID) {
		return c1;
	}

	if (c2->type == JVST_CNODE_INVALID) {
		return c2;
	}

	jxn = jvst_cnode_alloc(JVST_CNODE_AND);
	c1->next = c2;
	jxn->u.ctrl = c1;

	return jvst_cnode_simplify(jxn);
}

static struct jvst_cnode *cnode_jxn_constraints(struct jvst_cnode *c1, struct jvst_cnode *c2, enum jvst_cnode_type jxntype)
{
	switch (jxntype) {
	case JVST_CNODE_AND:
		return cnode_and_constraints(c1,c2);

	case JVST_CNODE_OR:
		return cnode_or_constraints(c1,c2);

	case JVST_CNODE_XOR:
		return cnode_xor_constraints(c1,c2);

	default:
		DIEF("combining constraints with %s not yet implemented\n",
			jvst_cnode_type_name(jxntype));
	}
}

static void
collect_mcases(struct fsm *dfa, struct jvst_cnode **mcpp);

static struct jvst_cnode *
mcase_list_jxn_with_default(struct jvst_cnode *mcases, struct jvst_cnode *dft, struct fsm *dfa, enum jvst_cnode_type jxntype)
{
	struct jvst_cnode *vcons, *ncons, *c, *new_cases, **ncpp;

	assert(dft->type == JVST_CNODE_MATCH_CASE);

	ncons = dft->u.mcase.name_constraint;
	vcons = dft->u.mcase.value_constraint;

	// safe to ignore VALID name constraint
	if (ncons != NULL && ncons->type == JVST_CNODE_VALID) {
		ncons = NULL;
	}

	// fast exit for AND and OR jxn types: default cases that won't change anything
	// (no or always VALID name constraints and always VALID default constriants)
	if (jxntype == JVST_CNODE_AND || jxntype == JVST_CNODE_OR) {
		if (ncons == NULL && vcons->type == JVST_CNODE_VALID) {
			return mcases;
		}
	}

	new_cases = NULL;
	ncpp = &new_cases;
	for (c = mcases; c != NULL; c = c->next) {
		struct jvst_cnode *nc, *vdft;
		assert(c->type == JVST_CNODE_MATCH_CASE);

		nc = cnode_deep_copy(c);

		if (ncons != NULL) {
			struct jvst_cnode *nnc;
			nnc = cnode_deep_copy(ncons);
			assert(nnc->type != JVST_CNODE_MATCH_CASE);

		       if (nc->u.mcase.name_constraint == NULL) {
			       nc->u.mcase.name_constraint = nnc;
		       } else {
			       assert(nc->u.mcase.name_constraint->type != JVST_CNODE_MATCH_CASE);

			       nc->u.mcase.name_constraint = 
				       cnode_jxn_constraints(nc->u.mcase.name_constraint, nnc, jxntype);
		       }
		}

		vdft = cnode_deep_copy(vcons);
		nc->u.mcase.value_constraint = cnode_jxn_constraints(nc->u.mcase.value_constraint, vdft, jxntype);

		// so the dfa can be updated with the revised MATCH_CASE
		// nodes
		c->u.mcase.tmp = nc;

		*ncpp = nc;
		ncpp = &nc->next;
	}

	// update states in the dfa
	fsm_walk_states(dfa, NULL, mcase_update_opaque);

	// reset the tmp fields
	for (c = mcases; c != NULL; c = c->next) {
		assert(c->type == JVST_CNODE_MATCH_CASE);
		assert(c->u.mcase.tmp != NULL);
		c->u.mcase.tmp = NULL;
	}

	return new_cases;
}

static struct jvst_cnode *
dfa_jxn_cases_with_default(struct fsm *dfa, struct jvst_cnode *dft, enum jvst_cnode_type jxntype)
{
	struct jvst_cnode *cases;

	cases = NULL;
	collect_mcases(dfa, &cases);

	return mcase_list_jxn_with_default(cases, dft, dfa, jxntype);
}

static struct jvst_cnode *
mswitch_jxn_cases_with_default(struct jvst_cnode *msw, struct jvst_cnode *dft, enum jvst_cnode_type jxntype)
{
	struct jvst_cnode *vcons, *ncons, *c, *new_cases, **ncpp;

	new_cases = mcase_list_jxn_with_default(msw->u.mswitch.cases, dft, msw->u.mswitch.dfa, jxntype);
	msw->u.mswitch.cases = new_cases;

	return msw;
}

static int
matchset_cmp(const void *p0, const void *p1)
{
	const struct jvst_cnode_matchset *const *ms0, *const *ms1;
	int diff;
	size_t n0, n1, nsm;

	ms0 = p0;
	ms1 = p1;

	diff = (*ms0)->match.dialect - (*ms1)->match.dialect;
	if (diff != 0) {
		return diff;
	}

	n0 = (*ms0)->match.str.len;
	n1 = (*ms1)->match.str.len;
	nsm = n0;
	if (nsm > n1) {
		nsm = n1;
	}

	diff = memcmp((*ms0)->match.str.s, (*ms1)->match.str.s, nsm);
	if ((diff != 0) || (n0 == n1)) {
		return diff;
	}

	return (n0 < n1) ? -1 : 1;
}

static void
sort_matchset(struct jvst_cnode_matchset **mspp)
{
	struct jvst_cnode_matchset *ms, **msv;
	struct jvst_cnode_matchset *msv0[16];
	size_t i,n;

	for (n=0, ms = *mspp; ms != NULL; n++, ms = ms->next) {
		continue;
	}

	if (n < 2) {
		return;
	}

	if (n <= ARRAYLEN(msv0)) {
		msv = msv0;
	} else {
		msv = xmalloc(n * sizeof *msv);
	}

	for (i=0, ms=*mspp; ms != NULL; i++, ms=ms->next) {
		msv[i] = ms;
	}

	qsort(msv, n, sizeof *msv, matchset_cmp);

	for (i=0; i < n; i++) {
		*mspp = msv[i];
		mspp = &(*mspp)->next;
		*mspp = NULL;
	}

	if (msv != msv0) {
		free(msv);
	}
}

static int
mcase_cmp(const void *p0, const void *p1)
{
	const struct jvst_cnode *const *c0, *const *c1;
	const struct jvst_cnode_matchset *ms0, *ms1;
	c0 = p0;
	c1 = p1;

	ms0 = (*c0)->u.mcase.matchset;
	ms1 = (*c1)->u.mcase.matchset;
	for(; (ms0 != NULL) || (ms1 != NULL); ms0=ms0->next, ms1=ms1->next) {
		int diff;

		if (ms0 == ms1) {
			return 0;
		}

		if (ms0 == NULL) {
			return -1;
		}

		if (ms1 == NULL) {
			return 1;
		}

		diff = matchset_cmp(&ms0,&ms1);
		if (diff != 0) {
			return diff;
		}
	}

	if ((ms0 == NULL) && (ms1 == NULL)) {
		return 0;
	}

	return (ms0 == NULL) ? -1 : 1;
}

static void
sort_mcases(struct jvst_cnode **mcpp)
{
	struct jvst_cnode *mc, **mcv;
	size_t i,n;
	struct jvst_cnode *mcv0[16] = { 0 };

	assert(mcpp != NULL);

	for (n=0, mc = *mcpp; mc != NULL; n++, mc = mc->next) {
		sort_matchset(&mc->u.mcase.matchset);
	}

	if (n < 2) {
		return;
	}

	if (n <= ARRAYLEN(mcv0)) {
		mcv = mcv0;
	} else {
		mcv = xmalloc(n * sizeof *mcv);
	}

	for (i=0, mc = *mcpp; mc != NULL; i++, mc = mc->next) {
		mcv[i] = mc;
	}

	qsort(mcv, n, sizeof *mcv, mcase_cmp);

	for (i=0; i < n; i++) {
		*mcpp = mcv[i];
		mcpp = &(*mcpp)->next;
		*mcpp = NULL;
	}

	if (mcv != mcv0) {
		free(mcv);
	}
}

struct mcase_collector {
	struct jvst_cnode **mcpp;
};

static int
mcase_collector(const struct fsm *dfa, const struct fsm_state *st, void *opaque)
{
	struct jvst_cnode *node;
	struct mcase_collector *collector;

	collector = opaque;
	assert(collector->mcpp != NULL);
	assert(*collector->mcpp == NULL);

	if (!fsm_isend(dfa, st)) {
		return 1;
	}

	node = fsm_getopaque((struct fsm *)dfa, st);
	assert(node->type == JVST_CNODE_MATCH_CASE);

	if (node->u.mcase.collected) {
		return 1;
	}

	assert(collector->mcpp != &node->next);

	*collector->mcpp = node;
	collector->mcpp = &node->next;
	*collector->mcpp = NULL;

	node->u.mcase.collected = 1;

	return 1;
}

static void
collect_mcases(struct fsm *dfa, struct jvst_cnode **mcpp)
{
	struct mcase_collector collector;
	struct jvst_cnode *n, **it;

	assert(mcpp != NULL);

	collector.mcpp = mcpp;
	*collector.mcpp = NULL;

	fsm_walk_states(dfa, &collector, mcase_collector);

	for (it=mcpp; *it != NULL; it = &(*it)->next) {
		assert((*it)->type == JVST_CNODE_MATCH_CASE);

		(*it)->u.mcase.collected = 0;
	}

	sort_mcases(mcpp);
}

static void
merge_mcases_with_and(const struct fsm_state **orig, size_t n,
	struct fsm *dfa, struct fsm_state *comb);

// "non-destructive" intersection
static struct fsm *
intersect_nd(const struct fsm *a, const struct fsm *b, const struct fsm_options *opts)
{
	struct fsm *dfa1, *dfa2;

	assert(opts != NULL);

	// fsm_intersect frees its arguments, so we make copies to
	// preserve the originals
	dfa1 = fsm_clone(a);
	if (!dfa1) {
		return NULL;
	}

	fsm_setoptions(dfa1, opts);

	dfa2 = fsm_clone(b);
	if (!dfa2) {
		fsm_free(dfa1);
		return NULL;
	}

	fsm_setoptions(dfa2, opts);

	return fsm_intersect(dfa1,dfa2);
}

// subtract(a, b) = intersect(a, complement(b)).
// sets the opaque value of end states of complement(b) to opaque_compl
static struct fsm *
subtract_nd(const struct fsm *a, const struct fsm *b, const struct fsm_options *opts)
{
	struct fsm *dfa1, *dfa2;

	assert(opts != NULL);

	// fsm_intersect frees its arguments, so we make copies to
	// preserve the originals
	dfa1 = fsm_clone(a);
	if (!dfa1) {
		return NULL;
	}

	fsm_setoptions(dfa1, opts);

	dfa2 = fsm_clone(b);
	if (!dfa2) {
		fsm_free(dfa1);
		return NULL;
	}

	fsm_setoptions(dfa2, opts);

	return fsm_subtract(dfa1,dfa2);
}

static void
merge_mcases_with_or(const struct fsm_state **orig, size_t n,
	struct fsm *dfa, struct fsm_state *comb);

static void
merge_mcases_with_xor(const struct fsm_state **orig, size_t n,
	struct fsm *dfa, struct fsm_state *comb);

static void
mcase_add_name_constraint(struct jvst_cnode *c, struct jvst_cnode *name_cons)
{
	struct jvst_cnode *top_jxn, *jxn;

	// sanity assertions
	assert(c != NULL);
	assert(c->type == JVST_CNODE_MATCH_CASE);
	assert(c->u.mcase.value_constraint != NULL);
	assert(c->u.mcase.value_constraint->next == NULL);

	assert(name_cons != NULL);
	assert(name_cons->type != JVST_CNODE_MATCH_CASE);

	// ASSUMPTION: name_cons is simplified!
	jxn = cnode_deep_copy(name_cons);

	if (c->u.mcase.name_constraint == NULL) {
		// NB: cjxn (and thus jxn) are already simplified
		c->u.mcase.name_constraint = jxn;
	} else {
		struct jvst_cnode *top_jxn;

		// We can do a better job of not overallocating nodes
		// here!
		top_jxn = jvst_cnode_alloc(JVST_CNODE_AND);
		top_jxn->u.ctrl = jxn;
		jxn->next = c->u.mcase.name_constraint;

		c->u.mcase.name_constraint = jvst_cnode_simplify(top_jxn);
		assert(c->u.mcase.name_constraint->type != JVST_CNODE_MATCH_CASE);
	}
}

static struct jvst_cnode *
merge_mswitches(struct jvst_cnode *mswlst, enum jvst_cnode_type jxntype)
{
	struct jvst_cnode *n, *msw;
	void (*mergefunc)(const struct fsm_state **, size_t, struct fsm *, struct fsm_state *);

	static const int dbg = 0;

	assert(mswlst != NULL);
	assert(mswlst->type == JVST_CNODE_MATCH_SWITCH);

	switch (jxntype) {
	case JVST_CNODE_AND:
		mergefunc = merge_mcases_with_and;
		break;

	case JVST_CNODE_OR:
		mergefunc = merge_mcases_with_or;
		break;

	case JVST_CNODE_XOR:
		mergefunc = merge_mcases_with_xor;
		break;

	default:
		DIEF("merging mswitches combined with %s not yet implemented\n",
			jvst_cnode_type_name(jxntype));
	}

	if (mswlst->next == NULL) {
		return mswlst;
	}

	msw = cnode_deep_copy(mswlst);
	for (n = mswlst->next; n != NULL; n = n->next) {
		assert(n->type == JVST_CNODE_MATCH_SWITCH);

		if (msw->u.mswitch.cases != NULL && n->u.mswitch.cases != NULL) {
			struct fsm *dfa1, *dfa2, *both, *only1, *only2, *combined;
			const struct fsm_options *orig_opts;
			struct fsm_options opts;
			struct jvst_cnode *mc1, *mc2;

			// Combining match_switch nodes with OR
			//
			// Let the non-default cases for DFA1 be:
			//   A_1, A_2, ... A_M, and the default case be A_0.
			//
			// Similarly, let the non-default cases for DFA2 be:
			//   B_1, B_2, ... B_N, and the default case be B_0.
			//
			// First focus on something that matches case A_1.  There are two possibilities:
			//
			//   1. It also matches some non-default case in DFA2: say B_k
			//   2. It matches the default case in DFA2: B_0
			//
			// If it matches B_k, then the combined constraint is:
			//   OR(A_1, B_k).
			//
			// If it matches the default case, the combine constraint is:
			//   OR(A_1, B_0).
			//
			// We have four general situations:
			//
			//   1. Matches non-default in DFA1 and non-default in DFA2
			//
			//      The combined states are given by intersect(DFA1,DFA2)
			//
			//   2. Matches non-default in DFA1 and default in DFA2
			//
			//      The combined states are given by subtract(DFA1,DFA2)
			//   
			//   3. Matches default in DFA1 and non-default in DFA2
			//
			//      The combined states are given by subtract(DFA2,DFA1)
			//   
			//   4. Matches default in DFA1 and default in DFA2
			//
			//      Indicates that nothing above has been matched.
			//
			// Thus we need:
			//   both  = intersect(DFA1,DFA2)
			//   only1 = subtract(DFA1,DFA2)
			//   only2 = subtract(DFA2,DFA1)
			//
			//   combined = union(both, only1, only2)
			//
			// In all of these cases, we need the opaque values to be merged
			// correctly.

			dfa1 = msw->u.mswitch.dfa;
			dfa2 = n->u.mswitch.dfa;

			orig_opts = fsm_getoptions(dfa1);
			opts = *orig_opts;
			opts.carryopaque = mergefunc;
			opts.tidy = false;

			// both = DFA1 & DFA2
			both = intersect_nd(dfa1,dfa2,&opts);
			if (!both) {
				perror("intersecting (dfa1 & dfa2)");
				abort();
			}

			if (dbg) {
				fprintf(stderr, "\n---> both <---\n");
				fsm_print(both, stderr, FSM_OUT_FSM);
			}

			// only1 = DFA2 - DFA1
			only1 = subtract_nd(dfa1,dfa2,&opts);
			if (!only1) {
				perror("subtracting (DFA1 - DFA2)");
				abort();
			}

			mc2 = cnode_deep_copy(n->u.mswitch.dft_case);
			dfa_jxn_cases_with_default(only1, mc2, jxntype);

			if (dbg) {
				fprintf(stderr, "\n---> only1 <---\n");
				fsm_print(only1, stderr, FSM_OUT_FSM);
			}

			// only2 = DFA2 - DFA1
			only2 = subtract_nd(dfa2,dfa1,&opts);
			if (!only2) {
				perror("subtracting (DFA2 - DFA1)");
				abort();
			}

			/*
			if (!fsm_minimise(only2)) {
				perror("minimizing (DFA2 - DFA1)");
				abort();
			}
			*/

			mc1 = cnode_deep_copy(msw->u.mswitch.dft_case);
			dfa_jxn_cases_with_default(only2, mc1, jxntype);

			if (dbg) {
				fprintf(stderr, "\n---> only2 <---\n");
				fsm_print(only2, stderr, FSM_OUT_FSM);
			}

			// now union DFA1&DFA2, DFA1-DFA2, and DFA2-DFA1 together
			combined = fsm_union(both, only1);
			if (!combined) {
				perror("unioning (both OR only1)");
				abort();
			}

			combined = fsm_union(combined, only2);
			if (!combined) {
				perror("unioning (combined OR only2)");
				abort();
			}

			if (!fsm_determinise(combined)) {
				perror("determinising union");
				abort();
			}

			if (dbg) {
				fprintf(stderr, "\n---> combined <---\n");
				fsm_print(combined, stderr, FSM_OUT_FSM);
			}

			fsm_setoptions(combined, orig_opts);

			// Finally, gather mcases
			msw->u.mswitch.dfa = combined;
			collect_mcases(combined, &msw->u.mswitch.cases);
		} else if (n->u.mswitch.cases != NULL) {
			assert(msw->u.mswitch.cases == NULL);

			msw->u.mswitch.dfa = fsm_clone(n->u.mswitch.dfa);
			msw->u.mswitch.cases = n->u.mswitch.cases;
			mswitch_jxn_cases_with_default(msw, msw->u.mswitch.dft_case, jxntype);
		} else if (msw->u.mswitch.cases != NULL) {
			// need to AND together msw's default case and
			// each of n's cases
			mswitch_jxn_cases_with_default(msw, n->u.mswitch.dft_case, jxntype);
		}

		assert(msw->u.mswitch.dft_case != NULL);
		assert(msw->u.mswitch.dft_case->type == JVST_CNODE_MATCH_CASE);

		assert(n->u.mswitch.dft_case != NULL);
		assert(n->u.mswitch.dft_case->type == JVST_CNODE_MATCH_CASE);

		if (msw->u.mswitch.dft_case->u.mcase.name_constraint && n->u.mswitch.dft_case->u.mcase.name_constraint) {
			msw->u.mswitch.dft_case->u.mcase.name_constraint = cnode_jxn_constraints(
					msw->u.mswitch.dft_case->u.mcase.name_constraint,
					n->u.mswitch.dft_case->u.mcase.name_constraint,
					jxntype);
		} else if (n->u.mswitch.dft_case->u.mcase.name_constraint) {
			msw->u.mswitch.dft_case->u.mcase.name_constraint = cnode_deep_copy(
				n->u.mswitch.dft_case->u.mcase.name_constraint);
		}

		msw->u.mswitch.dft_case->u.mcase.value_constraint = cnode_jxn_constraints(
				msw->u.mswitch.dft_case->u.mcase.value_constraint,
				n->u.mswitch.dft_case->u.mcase.value_constraint,
				jxntype);
	}

	msw = jvst_cnode_simplify(msw);
	return msw;
}

static struct jvst_cnode *
cnode_simplify_and_mswitch(struct jvst_cnode *top)
{
	struct jvst_cnode *msw, *conds;
	struct jvst_cnode **mswpp, **npp, **cpp;

	assert(top->type == JVST_CNODE_AND);

	// collect all MATCH_SWITCH children and cnodes we want to push
	// into MATCH_SWITCH cases
	msw = NULL;
	mswpp = &msw;

	// conditions that apply to all cases of the match switch.
	// currently this is only string length constraints, and
	// specifically LENGTH_RANGE nodes (other string constraints are
	// rolled into MATCH_SWITCH/MATCH_CASE).
	conds = NULL;
	cpp = &conds;

	for (npp = &top->u.ctrl; *npp != NULL; ) {
		switch ((*npp)->type) {
		case JVST_CNODE_MATCH_SWITCH:
			*mswpp = *npp;
			*npp = (*npp)->next;

			mswpp = &(*mswpp)->next;
			*mswpp = NULL;
			break;

		case JVST_CNODE_LENGTH_RANGE:
			*cpp = *npp;
			*npp = (*npp)->next;

			cpp = &(*cpp)->next;
			*cpp = NULL;
			break;

		default:
			npp = &(*npp)->next;
			continue;
		}
	}

	// no match_switch node, add contraints back to the AND top node
	// and return
	//
	// XXX - revisit this.  should we handle all string constraints
	// through a MATCH_SWITCH, even if it only involves the default
	// case.
	if (msw == NULL) {
		*npp = conds;
		return top;
	}

	// msw = merge_mswitches_with_and(msw);
	msw = merge_mswitches(msw, JVST_CNODE_AND);

	*npp = msw;

	if (conds == NULL) {
		return top;
	}

	// push string conditionals into the constraints field of the
	// MATCH_SWITCH
	//
	// after merging mswitches above, there should be only one
	// mswitch node
	{
		struct jvst_cnode *c, *cjxn;
		cjxn = jvst_cnode_alloc(JVST_CNODE_AND);
		cjxn->u.ctrl = conds;
		cjxn = jvst_cnode_simplify(cjxn);

		assert(cjxn->u.ctrl != NULL);

		for (c = msw->u.mswitch.cases; c != NULL; c = c->next) {
			mcase_add_name_constraint(c, cjxn);
		}

		{ 
			struct jvst_cnode *dft, *top_jxn;
			dft = msw->u.mswitch.dft_case;

			// sanity checks
			assert(dft != NULL);
			assert(dft->type == JVST_CNODE_MATCH_CASE);
			assert(dft->next == NULL);
			assert(cjxn->next == NULL);

			mcase_add_name_constraint(dft, cjxn);
		}
	}

	return top;
}

static struct jvst_cnode *
cnode_simplify_or_xor_mswitch(struct jvst_cnode *top)
{
	struct jvst_cnode *msw, **mswpp, **npp;

	assert(top->type == JVST_CNODE_OR || top->type == JVST_CNODE_XOR);

	// collect all MATCH_SWITCH children and nodes we want to push
	// into MATCH_SWITCH cases
	msw = NULL;
	mswpp = &msw;

	for (npp = &top->u.ctrl; *npp != NULL; ) {
		switch ((*npp)->type) {
		case JVST_CNODE_MATCH_SWITCH:
			*mswpp = *npp;
			*npp = (*npp)->next;

			mswpp = &(*mswpp)->next;
			*mswpp = NULL;
			break;

		default:
			npp = &(*npp)->next;
			continue;
		}
	}

	if (msw != NULL) {
		switch (top->type) {
		case JVST_CNODE_OR:
			msw = merge_mswitches(msw, JVST_CNODE_OR);
			break;

		case JVST_CNODE_XOR:
			msw = merge_mswitches(msw, JVST_CNODE_XOR);
			break;

		default:
			SHOULD_NOT_REACH();
		}

		*npp = msw;
	}

	return top;
}

static struct jvst_cnode *
cnode_simplify_andor_strmatch(struct jvst_cnode *top)
{
	/* TODO: strmatch cases (like propsets) can be combined more
	 * easily than match_switches, so we should try to combine them if they're
	 * AND'd or OR'd:
	 */

	return top;
}

static int
cmp_range_cnodes(const void *pa, const void *pb)
{
	static const size_t no_upper = (size_t)-1;
	struct jvst_cnode *a, *b;
	size_t max_a, max_b;

	a = *((struct jvst_cnode **)pa);
	b = *((struct jvst_cnode **)pb);

	assert(a->type == JVST_CNODE_LENGTH_RANGE ||
		a->type == JVST_CNODE_PROP_RANGE  ||
		a->type == JVST_CNODE_ITEM_RANGE);

	assert(b->type == JVST_CNODE_LENGTH_RANGE ||
		b->type == JVST_CNODE_PROP_RANGE  ||
		b->type == JVST_CNODE_ITEM_RANGE);

	if (a->u.counts.min < b->u.counts.min) {
		return -1;
	}
	
	if (a->u.counts.min > b->u.counts.min) {
		return 1;
	}

	max_a = a->u.counts.upper ? a->u.counts.max : no_upper;
	max_b = b->u.counts.upper ? b->u.counts.max : no_upper;

	if (max_a < max_b) {
		return -1;
	}

	if (max_a > max_b) {
		return 1;
	}

	return 0;
}

static struct jvst_cnode *
cnode_simplify_ored_count_range(struct jvst_cnode *rlist)
{
	enum jvst_cnode_type type;
	struct jvst_cnode *rn, *ret, *jxn, *ccn, **ccnpp;
	struct jvst_cnode *node_buf[4], **node_arr;
	size_t i,n;

	/* ORing is somewhat harder than AND-ing them... ORed expressions
	 * can encompass N disjoint regions.  We want to combine them in an
	 * efficient way.
	 *
	 * To do this, we first collect and sort the nodes by their range.
	 */

	if (rlist == NULL) {
		return NULL;
	}

	type = rlist->type;

	// ensure that the first node is count range
	assert(type == JVST_CNODE_LENGTH_RANGE ||
		type == JVST_CNODE_PROP_RANGE  ||
		type == JVST_CNODE_ITEM_RANGE);

	n=0;
	for (rn=rlist; rn != NULL; rn = rn->next) {
		assert(rn->type == type);
		n++;
	}

	assert(n > 0); // sanity check

	if (n == 1) {
		return rlist;
	}

	if (n <= ARRAYLEN(node_buf)) {
		node_arr = &node_buf[0];
	} else {
		node_arr = malloc(n * sizeof node_arr[0]);
	}

	for (i=0, rn=rlist; rn != NULL; i++, rn = rn->next) {
		assert(i < n);
		assert(rn->type == type);
		node_arr[i] = rn;
	}

	qsort(node_arr, n, sizeof *node_arr, cmp_range_cnodes);

	// Now that the nodes are sorted by range, we traverse the list in
	// the sorted order and combine adjacent nodes if possible.
	//
	// Set the current combined node (CCN) to a copy of node 0.
	// Set i=1.
	//
	// Loop:
	//   If node i overlaps or is adjacent to the CCN, then extend the
	//   range of the CCN to hold both nodes.
	//
	//   Otherwise, copy node i, add the copy to the CCN list, and let
	//   the copy be the CCN.
	//
	//   Set i = i+1.
	//   If i < n, repeat the loop.
	//
	// After the CCN list is built, if it holds one item, return that
	// item.  Otherwise place all items under an OR node and return the
	// OR node.

	ccn = cnode_deep_copy(node_arr[0]);
	ccnpp = &ccn;

	for (i=1; i < n; i++) {
		// special case... if ccn has no upper bounds, it eats the rest of
		// the nodes and we can drop out of the loop
		if (!(*ccnpp)->u.counts.upper) {
			break;
		}

		// if node[i] overlaps or is adjacent to the CCN, extend the
		// max of the ccn to include the max of node[i]
		if (node_arr[i]->u.counts.min <= (*ccnpp)->u.counts.max+1) {
			if (!node_arr[i]->u.counts.upper) {
				(*ccnpp)->u.counts.max = 0;
				(*ccnpp)->u.counts.upper = false;
			} else if (node_arr[i]->u.counts.max > (*ccnpp)->u.counts.max) {
				(*ccnpp)->u.counts.max = node_arr[i]->u.counts.max;
			}

			continue;
		}

		// no overlap, add a copy of node[i] at the end of the
		// CCN list.
		ccnpp = &(*ccnpp)->next;
		*ccnpp = cnode_deep_copy(node_arr[i]);
	}

	assert(ccn != NULL);

	// clean up temporary list if we had to malloc it
	if (&node_arr[0] != &node_buf[0]) {
		free(node_arr);
	}

	if (ccn->next == NULL) {
		// single item, return it
		return ccn;
	}

	jxn = jvst_cnode_alloc(JVST_CNODE_OR);
	jxn->u.ctrl = ccn;
	return jxn;
}

static void
and_range_pair(struct jvst_cnode *lhs, const struct jvst_cnode *rhs)
{
	enum jvst_cnode_type type;

	assert(lhs != NULL);
	assert(rhs != NULL);

	type = lhs->type;

	assert(type == JVST_CNODE_LENGTH_RANGE ||
		type == JVST_CNODE_PROP_RANGE  ||
		type == JVST_CNODE_ITEM_RANGE);

	assert(type == rhs->type);

	if (rhs->u.counts.min > lhs->u.counts.min) {
		lhs->u.counts.min = rhs->u.counts.min;
	}

	if (!rhs->u.counts.upper) {
		return;
	}

	if (!lhs->u.counts.upper) {
		lhs->u.counts.upper = true;
		lhs->u.counts.max = rhs->u.counts.max;
	} else if (rhs->u.counts.max < lhs->u.counts.max) {
		lhs->u.counts.max = rhs->u.counts.max;
	}
}

static struct jvst_cnode *
cnode_simplify_anded_count_range(struct jvst_cnode *rlist)
{
	enum jvst_cnode_type type;
	struct jvst_cnode *rn, *ret;

	if (rlist == NULL) {
		return NULL;
	}

	type = rlist->type;

	// ensure that the first node is count range
	assert(type == JVST_CNODE_LENGTH_RANGE ||
		type == JVST_CNODE_PROP_RANGE  ||
		type == JVST_CNODE_ITEM_RANGE);

	if (rlist->next == NULL) {
		return rlist;
	}

	ret = jvst_cnode_alloc(rlist->type);
	ret->u.counts = rlist->u.counts;

	for (rn=rlist->next; rn != NULL; rn = rn->next) {
		assert(rn->type == type);  // all nodes should be the same type
		and_range_pair(ret, rn);
	}

	if (ret->u.counts.upper && ret->u.counts.max < ret->u.counts.min) {
		ret->type = JVST_CNODE_INVALID;
	}

	return ret;
}

static struct jvst_cnode *
cnode_simplify_count_range(enum jvst_cnode_type type, struct jvst_cnode *rlist)
{
	switch (type) {
	case JVST_CNODE_AND:
		return cnode_simplify_anded_count_range(rlist);

	case JVST_CNODE_OR:
		return cnode_simplify_ored_count_range(rlist);

	default:
		DIEF("cannot simplify count ranges combined with %s node",
			jvst_cnode_type_name(type));
	}

	return rlist;
}

static int
all_children_of_type(struct jvst_cnode *top, enum jvst_cnode_type type)
{
	struct jvst_cnode *n;

	switch (top->type) {
	case JVST_CNODE_AND:
	case JVST_CNODE_OR:
	case JVST_CNODE_XOR:
	case JVST_CNODE_NOT:
		for (n = top->u.ctrl; n != NULL; n = n->next) {
			if (n->type != type) {
				return 0;
			}
		}

		return 1;

	default:
		SHOULD_NOT_REACH();
	}
}

static struct jvst_cnode *
cnode_simplify_and_ored_ranges(enum jvst_cnode_type rtype, struct jvst_cnode *and)
{
	struct jvst_cnode **npp, *nl, **wlpp, *n, *wl;
	size_t nsingle;

	// Try to simplify ANDed ORed ranges...
	//
	// 1. AND(R1, OR(R2,R3))        --> OR(AND(R1,R2), AND(R1,R3))
	// 2. AND(OR(R1,R2), OR(R3,R4)) --> OR(AND(R1,R3), AND(R1,R4), AND(R2,R3), AND(R2,R4))
	// 3. same as (2) with more nodes per OR.
	//
	// First, remove a) any bare node of type rtype
	//               b) any ORed nodes that have only rtype children
	//
	// All removed nodes should be kept on a list.  The non-removed nodes should be
	// kept on a different list.
	//
	// Note that this should be done after AND simplification, so there should be only
	// one bare node of type rtype.
	//
	// Let N_0 = the first item in the list.  Let A_j be each item in the list.
	//
	// Walk the list of removed nodes, attempting to simplify as follows:
	// N_i = AND(N_i-1, A_j), where any ORs are expected:
	//
	//    AND(OR(a_0, a_1, ..., a_m), OR(b_0, b1_, ..., b_n)) -->
	//      OR(AND(a_0,b_0), AND(a_0,b_1), ..., AND(a_0,b_n),
	//         AND(a_1,b_0), AND(a_1,b_1), ..., AND(a_1,b_n),
	//         ...
	//         AND(a_m,b_0), AND(a_m,b_1), ..., AND(a_m,b_n))
	//
	// If either N_i-1 or A_j are single nodes, we treat them as ORs with a single
	// term.
	//

	// TODO: There's a change that this expansion results in a lot more terms than the
	// original.  So we need to keep track of the number of operations in the original
	// and the new versions and choose the one that has the least terms.
	//
	// TODO: Can we be smarter about this if we structure this as a dynamic
	// programming problem?

	// Sanity checks
	assert(and != NULL);
	assert(and->type == JVST_CNODE_AND);
	assert(rtype == JVST_CNODE_LENGTH_RANGE ||
		rtype == JVST_CNODE_PROP_RANGE  ||
		rtype == JVST_CNODE_ITEM_RANGE);

	// Step 1: Build working list by factoring out bare nodes of type rtype and OR
	//         nodes whose children are all type rtype
	wl = NULL;
	wlpp = &wl;

	nsingle = 0;
	for (npp = &and->u.ctrl; *npp != NULL;) {
		if ((*npp)->type == rtype) {
			*wlpp = *npp;
			wlpp = &(*wlpp)->next;
			*npp = (*npp)->next;
			*wlpp = NULL;
			continue;
		}

		if ((*npp)->type == JVST_CNODE_OR && all_children_of_type(*npp, rtype)) {
			*wlpp = *npp;
			wlpp = &(*wlpp)->next;
			*npp = (*npp)->next;
			*wlpp = NULL;
			continue;
		}

		npp = &(*npp)->next;
	}

	// fast exit: no nodes to simplify
	if (wl == NULL) {
		return and;
	}

	// fast exit: only one node, cannot combine
	if (wl->next == NULL) {
		*npp = wl;
		return and;
	}

	// Step 2: Build transformed list by iterating through the working list and
	//         combining terms
	nl = wl;

	for (n = wl->next; n != NULL; n = n->next) {
		struct jvst_cnode *terms1, *terms2, *t1, *t2, *terms3, **t3pp;
		if (nl->type == JVST_CNODE_OR) {
			terms1 = nl->u.ctrl;
		} else if (nl->type == rtype) {
			terms1 = nl;
		} else {
			SHOULD_NOT_REACH();
		}

		if (n->type == JVST_CNODE_OR) {
			terms2 = n->u.ctrl;
		} else if (n->type == rtype) {
			terms2 = n;
		} else {
			SHOULD_NOT_REACH();
		}

		terms3 = NULL;
		t3pp = &terms3;
		for (t1 = terms1; t1 != NULL; t1 = t1->next) {
			struct jvst_cnode **partial;

			assert(t1->type == JVST_CNODE_LENGTH_RANGE ||
				t1->type == JVST_CNODE_PROP_RANGE  ||
				t1->type == JVST_CNODE_ITEM_RANGE);

			for (t2 = terms2; t2 != NULL; t2 = t2->next) {
				struct jvst_cnode *t3;

				assert(t2->type == JVST_CNODE_LENGTH_RANGE ||
					t2->type == JVST_CNODE_PROP_RANGE  ||
					t2->type == JVST_CNODE_ITEM_RANGE);

				assert(t1->type == t2->type);

				t3 = jvst_cnode_alloc(t1->type);
				t3->u.counts = t1->u.counts;
				and_range_pair(t3, t2);

				if (t3->u.counts.upper && t3->u.counts.min > t3->u.counts.max) {
					continue;
				}

				*t3pp = t3;
				t3pp = &t3->next;
			}
		}

		// simplify terms3 list
		if (terms3 != NULL) {
			terms3 = cnode_simplify_ored_count_range(terms3);
		}

		if (terms3 == NULL) {
			nl = NULL;
		} else if (terms3->next == NULL) {
			nl = terms3;
		} else {
			nl = jvst_cnode_alloc(JVST_CNODE_OR);
			nl->u.ctrl = terms3;
		}
	}

	// no term survives, so all are invalid, making the entire AND invalid
	if (nl == NULL) {
		return jvst_cnode_alloc(JVST_CNODE_INVALID);
	}

	*npp = nl;
	return and;
}

static struct jvst_cnode *
cnode_simplify_bool_ranges(struct jvst_cnode *top)
{
	struct jvst_cnode *len_range, **lrpp, *prop_range, **prpp, *item_range, **irpp, **npp;
	enum jvst_cnode_type type;

	assert(top != NULL);

	type = top->type;
	assert(type == JVST_CNODE_AND || type == JVST_CNODE_OR);

	assert(top->u.ctrl != NULL);

	len_range = NULL; lrpp = &len_range;
	prop_range = NULL; prpp = &prop_range;
	item_range = NULL; irpp = &item_range;

	for (npp = &top->u.ctrl; *npp != NULL;) {
		switch ((*npp)->type) {
		case JVST_CNODE_LENGTH_RANGE:
			*lrpp = *npp;
			*npp = (*npp)->next;
			lrpp = &(*lrpp)->next;
			*lrpp = NULL;
			break;

		case JVST_CNODE_PROP_RANGE:
			*prpp = *npp;
			*npp = (*npp)->next;
			prpp = &(*prpp)->next;
			*prpp = NULL;
			break;

		case JVST_CNODE_ITEM_RANGE:
			*irpp = *npp;
			*npp = (*npp)->next;
			irpp = &(*irpp)->next;
			*irpp = NULL;
			break;

		default:
			npp = &(*npp)->next;
			break;
		}
	}

	assert(*npp == NULL);

	if (len_range != NULL) {
		len_range = cnode_simplify_count_range(type,len_range);
		*npp = len_range;
		for(; *npp != NULL; npp = &(*npp)->next) {
			continue;
		}
	}

	if (prop_range != NULL) {
		prop_range = cnode_simplify_count_range(type,prop_range);
		*npp = prop_range;
		for(; *npp != NULL; npp = &(*npp)->next) {
			continue;
		}
	}

	if (item_range != NULL) {
		item_range = cnode_simplify_count_range(type,item_range);
		*npp = item_range;
		for(; *npp != NULL; npp = &(*npp)->next) {
			continue;
		}
	}

	assert(top->u.ctrl != NULL);
	if (top->u.ctrl->next == NULL) {
		// only one item
		return top->u.ctrl;
	}

	if (type == JVST_CNODE_AND) {
		// Now that we've built the simplified AND, try to distribute ANDs over any ORs
		top = cnode_simplify_and_ored_ranges(JVST_CNODE_LENGTH_RANGE, top);
		top = cnode_simplify_and_ored_ranges(JVST_CNODE_PROP_RANGE, top);
		top = cnode_simplify_and_ored_ranges(JVST_CNODE_ITEM_RANGE, top);
	}

	return top;
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

	if (top->type == JVST_CNODE_AND || top->type == JVST_CNODE_OR) {
		top = cnode_simplify_andor_strmatch(top);
	}

	if (top->type == JVST_CNODE_AND) {
		top = cnode_simplify_and_required(top);
	}

	if (top->type == JVST_CNODE_AND || top->type == JVST_CNODE_OR) {
		top = cnode_simplify_bool_ranges(top);
	}

	if ((top->type == JVST_CNODE_AND) || (top->type == JVST_CNODE_OR)) {
		top = cnode_simplify_andor_switches(top);
	}

	/* combine AND'd match_switch nodes, moves any AND'd COUNT_RANGE nodes */
	if (top->type == JVST_CNODE_AND) {
		top = cnode_simplify_and_mswitch(top);
	} else if (top->type == JVST_CNODE_OR) {
		// need to limit when we do this.  otherwise it causes
		// problems...
		//
		// top = cnode_simplify_or_xor_mswitch(top);
	}

	/* XXX - can also combine OR'd match_switch nodes */

	if (top->type == JVST_CNODE_AND || top->type == JVST_CNODE_OR) {
		if (top->u.ctrl->next == NULL) {
			// only one child
			return top->u.ctrl;
		}
	}

	return top;
}

static struct jvst_cnode *
cnode_negate_range(struct jvst_cnode *range)
{
	struct jvst_cnode *ret;

	switch (range->type) {
	case JVST_CNODE_LENGTH_RANGE:
	case JVST_CNODE_PROP_RANGE:
	case JVST_CNODE_ITEM_RANGE:
		// okay
		break;

	default:
		SHOULD_NOT_REACH();
	}

	ret = NULL;
	if (range->u.counts.min > 0) {
		struct jvst_cnode *lower;

		lower = jvst_cnode_alloc(range->type);
		lower->u.counts.min = 0;
		lower->u.counts.max = range->u.counts.min-1;
		lower->u.counts.upper = true;

		ret = lower;
	}

	if (range->u.counts.upper) {
		struct jvst_cnode *upper;

		upper = jvst_cnode_alloc(range->type);
		upper->u.counts.min = range->u.counts.max+1;
		upper->u.counts.max = 0;
		upper->u.counts.upper = false;

		if (ret == NULL) {
			ret = upper;
		} else {
			struct jvst_cnode *jxn;
			jxn = jvst_cnode_alloc(JVST_CNODE_OR);
			ret->next = upper;
			jxn->u.ctrl = ret;
			ret = jxn;
		}
	}

	return ret;
}

static int
cnode_is_range(struct jvst_cnode *n)
{
	if (n->type == JVST_CNODE_LENGTH_RANGE) {
		return 1;
	}

	if (n->type == JVST_CNODE_PROP_RANGE) {
		return 1;
	}

	if (n->type == JVST_CNODE_ITEM_RANGE) {
		return 1;
	}

	return 0;
}

static struct jvst_cnode *
cnode_simplify_xor_ranges(struct jvst_cnode *top)
{
	struct jvst_cnode *lhs, *rhs, *and, *not, *or, *dup, *newlhs;

	// FIXME: we can probably do more efficiently (allocating fewer temporary nodes)
	// FIXME: also, support more than two children!
	// FIXME: also, support control nodes

	assert(top->type == JVST_CNODE_XOR);
	assert(top->u.ctrl != NULL);

	lhs = top->u.ctrl;
	rhs = top->u.ctrl->next;
	if (rhs == NULL) {
		return lhs;
	}

	if (rhs->next != NULL) {
		// XXX - current limitation is two child nodes
		return top;
	}

	if (!cnode_is_range(lhs) || !cnode_is_range(rhs)) {
		return top;
	}

	// construct OR(AND(lhs,NOT(rhs)), AND(NOT(lhs),rhs)) and simplify
	dup = cnode_deep_copy(lhs);
	not = cnode_negate_range(rhs);
	and = jvst_cnode_alloc(JVST_CNODE_AND);
	dup->next = not;
	and->u.ctrl = dup;
	newlhs = jvst_cnode_simplify(and);

	dup = cnode_deep_copy(rhs);
	not = cnode_negate_range(lhs);
	and = jvst_cnode_alloc(JVST_CNODE_AND);
	dup->next = not;
	and->u.ctrl = dup;
	rhs = jvst_cnode_simplify(and);

	or = jvst_cnode_alloc(JVST_CNODE_OR);
	newlhs->next = rhs;
	or->u.ctrl = newlhs;

	return jvst_cnode_simplify(or);
}

static struct jvst_cnode *
cnode_simplify_xor(struct jvst_cnode *top)
{
	struct jvst_cnode *node, *next, **pp;
	size_t num_valid;

	cnode_simplify_ctrl_children(top);

	// pass 1: remove VALID/INVALID nodes
	//
	// We have to handle this differently for XOR than for AND/OR.
	//
	// INVALID nodes are removed.  VALID nodes are removed and counted.
	//
	//   If we have no VALID nodes, then proceed normally.
	// 
	//   If we have one VALID node and any other nodes, then the VALID
	//   node is removed and all the other nodes are placed under and
	//   NOT(OR(...)).
	//
	//   If we have two or more VALID nodes, then the entire XOR becomes
	//   INVALID.
	num_valid = 0;
	for (pp = &top->u.ctrl; *pp != NULL;) {
		switch ((*pp)->type) {
		case JVST_CNODE_INVALID:
			// remove
			*pp = (*pp)->next;
			break;

		case JVST_CNODE_VALID:
			num_valid++;
			// remove
			*pp = (*pp)->next;
			break;

		default:
			pp = &(*pp)->next;
			break;
		}
	}

	switch (num_valid) {
	case 0:
		// normal
		break;

	case 1:
		if (top->u.ctrl == NULL) {
			// no remaining nodes... so VALID
			return jvst_cnode_alloc(JVST_CNODE_VALID);
		} else {
			struct jvst_cnode *not, *or;

			// remaining nodes.  For the XOR to be VALID, none of these
			// nodes may be valid, so replace this construct
			// with a NOT(OR(...))
			//
			// special case: if there's only one remaining node, then the OR
			// isn't necessary

			not = jvst_cnode_alloc(JVST_CNODE_NOT);
			if (top->u.ctrl->next == NULL) {
				not->u.ctrl = top->u.ctrl;
			} else {
				or = jvst_cnode_alloc(JVST_CNODE_OR);
				or->u.ctrl = top->u.ctrl;

				not->u.ctrl = or;
			}

			return jvst_cnode_simplify(not);
		}

	default:
		// more than one... entire XOR is invalid
		return jvst_cnode_alloc(JVST_CNODE_INVALID);
	}

	// all nodes were invalid
	if (top->u.ctrl == NULL) {
		return jvst_cnode_alloc(JVST_CNODE_INVALID);
	}

	assert(top->u.ctrl != NULL);
	if (top->u.ctrl->next == NULL) {
		// only one child
		return top->u.ctrl;
	}

	// XOR semantics are kind of complicated compared to AND and OR.
	// For now we only do a few simplifications.
	if (top->type == JVST_CNODE_XOR) {
		top = cnode_simplify_xor_switches(top);
	}

	if (top->type == JVST_CNODE_XOR) {
		top = cnode_simplify_xor_ranges(top);
	}

	if (top->type == JVST_CNODE_XOR) {
		// need to limit when we do this.  otherwise it causes
		// problems...
		//
		// top = cnode_simplify_or_xor_mswitch(top);
	}

	if (top->type == JVST_CNODE_XOR && top->u.ctrl->next == NULL) {
		// only one child
		return top->u.ctrl;
	}

	return top;
}

static struct jvst_cnode *
cnode_simplify_not_range(struct jvst_cnode *top)
{
	struct jvst_cnode *range;

	assert(top->type == JVST_CNODE_NOT);
	assert(top->u.ctrl != NULL);

	range = top->u.ctrl;
	switch (range->type) {
	case JVST_CNODE_LENGTH_RANGE:
	case JVST_CNODE_PROP_RANGE:
	case JVST_CNODE_ITEM_RANGE:
		// okay
		break;

	default:
		return top;
	}

	return cnode_negate_range(range);
}

static struct jvst_cnode *
cnode_simplify_not_switch(struct jvst_cnode *top)
{
	struct jvst_cnode *sw, *sw0;
	size_t i,n;

	assert(top->type == JVST_CNODE_NOT);
	assert(top->u.ctrl != NULL);

	sw0 = top->u.ctrl;
	if (sw0->type != JVST_CNODE_SWITCH) {
		SHOULD_NOT_REACH();
	}

	sw = jvst_cnode_alloc(JVST_CNODE_SWITCH);
	for (i = 0, n = ARRAYLEN(sw->u.sw); i < n; i++) {
		struct jvst_cnode *not, *n;

		// these are never valid switch cases
		if (i == SJP_ARRAY_END || i == SJP_OBJECT_END) {
			sw->u.sw[i] = jvst_cnode_alloc(JVST_CNODE_INVALID);
			continue;
		}

		not = jvst_cnode_alloc(JVST_CNODE_NOT);
		not->u.ctrl = sw0->u.sw[i];

		sw->u.sw[i] = jvst_cnode_simplify(not);
	}

	return sw;
}

static struct jvst_cnode *
cnode_simplify_not(struct jvst_cnode *top)
{
	assert(top != NULL);
	assert(top->type == JVST_CNODE_NOT);
	assert(top->u.ctrl != NULL);
	assert(top->u.ctrl->next == NULL);

	if (top->u.ctrl->type == JVST_CNODE_SWITCH) {
		// fast exit if then child node is a SWITCH node: the NOT is pushed into
		// each case of the switch, so there's no further simplification to be
		// done on the top node
		return cnode_simplify_not_switch(top);
	}

	// currently simplification of NOT is pretty limited
	if (top->type == JVST_CNODE_NOT) {
		top = cnode_simplify_not_range(top);
	}

	if (top->type == JVST_CNODE_NOT) {
		switch (top->u.ctrl->type) {
		case JVST_CNODE_INVALID:
			return jvst_cnode_alloc(JVST_CNODE_VALID);

		case JVST_CNODE_VALID:
			return jvst_cnode_alloc(JVST_CNODE_INVALID);

		default:
			/* nop */
			break;
		}
	}

	return top;
}

static struct jvst_cnode *
cnode_simplify_propset(struct jvst_cnode *tree)
{
	struct jvst_cnode *pm;

	// step 1: iterate over PROP_MATCH nodes and simplify each
	// constraint individually
	for (pm = tree->u.prop_set; pm != NULL; pm=pm->next) {
		assert(pm != NULL);

		switch (pm->type) {
		case JVST_CNODE_OBJ_PROP_MATCH:
			pm->u.prop_match.constraint = jvst_cnode_simplify(pm->u.prop_match.constraint);
			break;

		case JVST_CNODE_OBJ_PROP_DEFAULT:
			pm->u.prop_default = jvst_cnode_simplify(pm->u.prop_default);
			break;

		case JVST_CNODE_OBJ_PROP_NAMES:
			break;

		default:
			DIEF("%s should not have %s as a child node\n",
				jvst_cnode_type_name(tree->type),
				jvst_cnode_type_name(pm->type));
		}

	}

	return tree;
}

static struct jvst_cnode *
cnode_simplify_list(struct jvst_cnode *items)
{
	struct jvst_cnode *it, *next, *simplified_items, **spp;

	simplified_items = NULL;
	spp = &simplified_items;
	for (it = items; it != NULL; it = next) {
		struct jvst_cnode *simplified;

		next = it->next;

		simplified = jvst_cnode_simplify(it);
		*spp = simplified;
		spp = &(*spp)->next;
		*spp = NULL;
	}

	return simplified_items;
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
	case JVST_CNODE_NUM_MULTIPLE_OF:
	case JVST_CNODE_ARR_UNIQUE:
	case JVST_CNODE_REF:
		return tree;

	case JVST_CNODE_AND:
	case JVST_CNODE_OR:
		return cnode_simplify_andor(tree);

	case JVST_CNODE_XOR:
		return cnode_simplify_xor(tree);

	case JVST_CNODE_NOT:
		// TODO: improve optimizations for NOT
		return cnode_simplify_not(tree);

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

	case JVST_CNODE_OBJ_PROP_DEFAULT:
		{
			struct jvst_cnode *pset;

			// simplify constraint
			tree->u.prop_default = jvst_cnode_simplify(tree->u.prop_default);

			// wrap any bare PROP_DEFAULT nodes in a PROP_SET
			pset = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_SET);
			pset->u.prop_set = tree;
			return pset;
		}

	case JVST_CNODE_OBJ_PROP_NAMES:
		{
			struct jvst_cnode *pset;

			// wrap any bare PROP_NAMES nodes in a PROP_SET
			pset = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_SET);
			pset->u.prop_set = tree;
			return pset;
		}

	case JVST_CNODE_ARR_ITEM:
		assert(tree->u.items != NULL);
		tree->u.items = cnode_simplify_list(tree->u.items);
		return tree;

	case JVST_CNODE_ARR_ADDITIONAL:
		assert(tree->u.items != NULL);
		assert(tree->u.items->next == NULL);
		tree->u.items = cnode_simplify_list(tree->u.items);
		return tree;

	case JVST_CNODE_ARR_CONTAINS:
		assert(tree->u.contains != NULL);
		assert(tree->u.contains->next == NULL);
		tree->u.contains = jvst_cnode_simplify(tree->u.contains);
		return tree;

	case JVST_CNODE_MATCH_SWITCH:
		{
			struct jvst_cnode *mc, *next;

			tree->u.mswitch.dft_case = jvst_cnode_simplify(tree->u.mswitch.dft_case);

			for (mc=tree->u.mswitch.cases; mc != NULL; mc = next) {
				struct jvst_cnode *smc;

				assert(mc->type == JVST_CNODE_MATCH_CASE);
				next = mc->next;

				// FIXME: this is a hack.  what we should do is to rebuild the case list.
				// When we do that, the u.mcase.tmp values aren't kept and this is required
				// when updating FSM nodes.  We need to find a better way to do this!

				smc = jvst_cnode_simplify(mc);
				mc->u.mcase.name_constraint = smc->u.mcase.name_constraint;
				mc->u.mcase.value_constraint = smc->u.mcase.value_constraint;
			}

			return tree;
		}

	case JVST_CNODE_MATCH_CASE:
		if (tree->u.mcase.name_constraint != NULL) {
			tree->u.mcase.name_constraint = jvst_cnode_simplify(tree->u.mcase.name_constraint);

			if (tree->u.mcase.name_constraint->type == JVST_CNODE_VALID) {
				// a VALID name constraint is equivalent to no name constraint
				tree->u.mcase.name_constraint = NULL;
				break;
			} else if (tree->u.mcase.name_constraint->type == JVST_CNODE_INVALID) {
				// an INVALID name constraint makes everything INVALID
				tree->u.mcase.value_constraint = tree->u.mcase.name_constraint;
				tree->u.mcase.name_constraint = NULL;
			}
		}

		tree->u.mcase.value_constraint = jvst_cnode_simplify(tree->u.mcase.value_constraint);

		assert(tree->u.mcase.value_constraint != NULL);
		if (tree->u.mcase.value_constraint->type == JVST_CNODE_INVALID) {
			// an INVALID value constraint makes everything INVALID
			tree->u.mcase.name_constraint = NULL;
		}

		return tree;

	case JVST_CNODE_NUM_RANGE:
	case JVST_CNODE_LENGTH_RANGE:
	case JVST_CNODE_PROP_RANGE:
	case JVST_CNODE_ITEM_RANGE:
	case JVST_CNODE_STR_MATCH:
	case JVST_CNODE_OBJ_PROP_MATCH:
	case JVST_CNODE_OBJ_REQUIRED:
	case JVST_CNODE_OBJ_REQMASK:
	case JVST_CNODE_OBJ_REQBIT:
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

static int 
cmp_mcase_ptr(const void *pa, const void *pb)
{
	const struct jvst_cnode *a, *b;
	ptrdiff_t delta;

	a = *((const struct jvst_cnode **)pa);
	b = *((const struct jvst_cnode **)pb);

	delta = a-b;
	if (delta < 0) {
		return -1;
	}

	if (delta > 0) {
		return 1;
	}

	return 0;
}

static int
cmp_matchsets(const void *pa, const void *pb)
{
	const struct jvst_cnode_matchset *a, *b;
	size_t n;
	int delta;

	a = *((const struct jvst_cnode_matchset **)pa);
	b = *((const struct jvst_cnode_matchset **)pb);

	if (a == b) {
		return 0;
	}

	if (a == NULL) {
		return 1;
	}

	if (b == NULL) {
		return -1;
	}

	n = (a->match.str.len < b->match.str.len) ? a->match.str.len : b->match.str.len;
	delta = memcmp(a->match.str.s, b->match.str.s, n);
	if (delta != 0) {
		return delta;
	}

	if (a->match.str.len < b->match.str.len) {
		return -1;
	}

	if (a->match.str.len > b->match.str.len) {
		return 1;
	}

	return 0;
}

static void
merge_mcases_with_cjxn(const struct fsm_state **orig, size_t n,
	struct fsm *dfa, struct fsm_state *comb, enum jvst_cnode_type cjxn_type)
{
	struct jvst_cnode *mcase, *njxn, **njpp, *vjxn, **vjpp;
	struct jvst_cnode_matchset **mspp;
	struct jvst_cnode *mcases_buf[8] = { 0 }, **mcases;
	struct jvst_cnode_matchset *mset_buf[8] = { 0 }, **msets;
	size_t nstates, nuniq, nmatchsets;
	size_t i,ind;

	switch (cjxn_type) {
	case JVST_CNODE_AND:
	case JVST_CNODE_OR:
	case JVST_CNODE_XOR:
		/* okay */
		break;
	default:
		SHOULD_NOT_REACH();
	}

	// first count states to make sure that we need to merge...
	mcase = NULL;
	nstates = 0;
	nuniq = 0;

	for (i = 0; i < n; i++) {
		struct jvst_cnode *c;

		if (!fsm_isend(dfa, orig[i])) {
			continue;
		}

		c = fsm_getopaque(dfa, orig[i]);
		if (c == NULL) {
			continue;
		}
		// assert(c != NULL);

		// allow a fast path if nstates==1
		if (mcase == NULL) {
			mcase = c;
			nuniq++;
		} else if (mcase != c) {
			nuniq++;
		}

		nstates++;
	}

	if (nstates == 0) {
		return;
	}

	if (nstates == 1 || nuniq == 1) {
		assert(mcase != NULL);
		fsm_setopaque(dfa, comb, mcase);
		return;
	}

	// okay... need to combine things...
	if (nstates <= ARRAYLEN(mcases_buf)) {
		mcases = &mcases_buf[0];
	} else {
		mcases = xcalloc(nstates, sizeof *mcases);
	}

	// gather all the mcases
	for (ind = 0, i = 0; i < n; i++) {
		struct jvst_cnode *c;

		if (!fsm_isend(dfa, orig[i])) {
			continue;
		}

		c = fsm_getopaque(dfa, orig[i]);
		assert(c != NULL);

		assert(c->type == JVST_CNODE_MATCH_CASE);
		// assert(c->u.mcase.matchset != NULL);

		assert(ind < nstates);
		mcases[ind++] = c;
	}

	// sort cases, remove duplicates
	qsort(mcases, nstates, sizeof *mcases, cmp_mcase_ptr);

	njxn = jvst_cnode_alloc(cjxn_type);
	njpp = &njxn->u.ctrl;

	vjxn = jvst_cnode_alloc(cjxn_type);
	vjpp = &vjxn->u.ctrl;

	// XXX: fix cnode_new_mcase to take both name and value
	// constraints
	mcase = cnode_new_mcase(NULL, vjxn);
	mspp = &mcase->u.mcase.matchset;

	nmatchsets = 0;
	for (i=0; i < nstates; i++) {
		struct jvst_cnode_matchset *mset;
		struct jvst_cnode *c;

		if (i > 0 && mcases[i] == mcases[i-1]) {
			continue;
		}

		c = mcases[i];

		// XXX - currently don't check the matchsets for duplicates.
		// Do we need to?
		for (mset = c->u.mcase.matchset; mset != NULL; mset = mset->next) {
			nmatchsets++;
			*mspp = cnode_matchset_new(mset->match, NULL);
			mspp = &(*mspp)->next;
		}

		if (c->u.mcase.name_constraint != NULL) {
			assert(c->u.mcase.name_constraint->type != JVST_CNODE_MATCH_CASE);

			*njpp = cnode_deep_copy(c->u.mcase.name_constraint);
			njpp = &(*njpp)->next;
		}

		assert(c->u.mcase.value_constraint->type != JVST_CNODE_MATCH_CASE);
		*vjpp = cnode_deep_copy(c->u.mcase.value_constraint);
		vjpp = &(*vjpp)->next;
	}

	if (njxn->u.ctrl != NULL) {
		mcase->u.mcase.name_constraint = njxn;
	}

	if (nmatchsets > 1) {
		struct jvst_cnode_matchset *ms;
		size_t i;

		if (nmatchsets <= ARRAYLEN(mset_buf)) {
			msets = &mset_buf[0];
		} else {
			msets = xcalloc(nmatchsets, sizeof *msets);
		}

		i=0;
		for (ms = mcase->u.mcase.matchset; ms != NULL; ms = ms->next) {
			assert(i < nmatchsets);
			msets[i++] = ms;
		}

		assert(i == nmatchsets);

		qsort(msets, nmatchsets, sizeof *msets, cmp_matchsets);

		mspp = &mcase->u.mcase.matchset;
		*mspp = NULL;
		for (i=0; i < nmatchsets; i++) {
			if (i > 0 && cmp_matchsets(&msets[i], &msets[i-1]) == 0) {
				continue;
			}
			*mspp = msets[i];
			mspp = &(*mspp)->next;
			*mspp = NULL;
		}

		if (msets != &mset_buf[0]) {
			free(msets);
		}
	}

	assert(mcase->next == NULL);
	fsm_setopaque(dfa, comb, mcase);

	if (mcases != &mcases_buf[0]) {
		free(mcases);
	}
}

static void
merge_mcases_with_and(const struct fsm_state **orig, size_t n,
	struct fsm *dfa, struct fsm_state *comb)
{
	merge_mcases_with_cjxn(orig, n, dfa, comb, JVST_CNODE_AND);
}

static void
merge_mcases_with_or(const struct fsm_state **orig, size_t n,
	struct fsm *dfa, struct fsm_state *comb)
{
	merge_mcases_with_cjxn(orig, n, dfa, comb, JVST_CNODE_OR);
}

static void
merge_mcases_with_xor(const struct fsm_state **orig, size_t n,
	struct fsm *dfa, struct fsm_state *comb)
{
	merge_mcases_with_cjxn(orig, n, dfa, comb, JVST_CNODE_XOR);
}

static int
fsm_debug_printer(const struct fsm *dfa, const struct fsm_state *st, void *opaque)
{
	struct jvst_cnode *mc;
	static char buf[2048];

	(void)opaque;

	if (!fsm_isend(dfa,st)) {
		return 1;
	}

	mc = fsm_getopaque((struct fsm *)dfa, (struct fsm_state *)st);

	memset(buf,0,sizeof buf);
	if (!fsm_example(dfa, st, buf, sizeof buf)) {
		const char mesg[] = "... too long ...";
		memcpy(buf, mesg, sizeof mesg);
	}

	fprintf(stderr, "graph %p, end state %p, mc = %p\n", (void *)dfa, (void *)st, (void *)mc);
	fprintf(stderr, "  example: %s\n", buf);
	if (mc != NULL) {
		jvst_cnode_debug(mc);
	}

	return 1;
}

// static struct jvst_cnode **mcase_collector_head;

static struct fsm *
mcase_re_compile(struct ast_regexp *re, struct fsm_options *opts, struct jvst_cnode *mcase)
{
	struct fsm *pat;
	struct json_str_iter siter;
	struct re_err err = { 0 };
	char tmp[128], *pbuf;

	siter.str = re->str;
	siter.off = 0;

	pat = re_comp(	re->dialect,
			json_str_getc,
			&siter,
			opts,
			(enum re_flags)0,
			&err);

	if (!fsm_minimise(pat)) {
		perror("minimizing regexp");
		abort();
	}

	if (pat == NULL) {
		goto error;
	}

	fsm_setendopaque(pat, mcase);

	return pat;

error:
	// the match.str field is a json_string, which
	// is length encoded and may not have a
	// terminating NUL character.  Copy it so we can
	// pass it to re_perror.
	if (re->str.len < sizeof tmp) {
		pbuf = &tmp[0];
	} else {
		pbuf = xmalloc(re->str.len+1);
	}

	memcpy(pbuf, re->str.s, re->str.len);
	pbuf[re->str.len] = '\0';

	re_perror(re->dialect, &err, NULL, pbuf);
	if (pbuf != &tmp[0]) {
		free(pbuf);
	}
	abort();
}

static struct jvst_cnode *
cnode_canonify_propset(struct jvst_cnode *top)
{
	struct jvst_cnode *pm, *mcases, *msw, **mcpp, *dft, *names;
	struct fsm_options *opts;
	struct fsm *matches;
	struct mcase_collector collector;
	struct jvst_cnode *names_match;

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
		.carryopaque = NULL,
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
	names = NULL;
	dft = NULL;
	for (pm = top->u.prop_set; pm != NULL; pm=pm->next) {
		struct jvst_cnode *cons, *mcase;
		struct jvst_cnode_matchset *mset;
		struct fsm *pat;

		if (pm->type == JVST_CNODE_OBJ_PROP_DEFAULT) {
			// should have at most one PROP_DEFAULT child
			assert(dft == NULL);
			dft = pm->u.prop_default;
			continue;
		}

		if (pm->type == JVST_CNODE_OBJ_PROP_NAMES) {
			// should have at most one PROP_NAMES child
			assert(names == NULL);
			names = pm;
			continue;
		}

		assert(pm->type == JVST_CNODE_OBJ_PROP_MATCH);

		cons = pm->u.prop_match.constraint;
		mset = cnode_matchset_new(pm->u.prop_match.match, NULL);
		mcase = cnode_new_mcase(mset, cons);
		assert(mcase->next == NULL);

		pat = mcase_re_compile(&pm->u.prop_match.match, opts, mcase);

		if (matches == NULL) {
			matches = pat;
		} else {
			matches = fsm_union(matches, pat);

			// XXX - we can't handle failure states right
			// now...
			assert(matches != NULL);
		}
	}

	// make sure we have a non-NULL default case.
	if (dft == NULL) {
		dft = jvst_cnode_alloc(JVST_CNODE_VALID);
	} else {
		dft = jvst_cnode_simplify(dft);
		dft = jvst_cnode_canonify(dft);
	}

	names_match = NULL;
	// if a PROP_NAMES node is present, we compile its regexp for
	// later processing
	if (names != NULL) {
		struct jvst_cnode *mc, *nametree;

		assert(names->type == JVST_CNODE_OBJ_PROP_NAMES);

		nametree = jvst_cnode_simplify(names->u.prop_names);
		nametree = jvst_cnode_canonify(nametree);

		if (nametree->type == JVST_CNODE_SWITCH) {
			nametree = nametree->u.sw[SJP_STRING];
		}

		switch (nametree->type) {
		case JVST_CNODE_VALID:
			// PROP_NAMES has no constraints on keys...
			// leave names_match = NULL.
			break;

		case JVST_CNODE_INVALID:
			{
				struct fsm *empty;
				struct fsm_state *start;

				// all keys are disallowed, regardless of
				// everything else...
				names_match = jvst_cnode_alloc(JVST_CNODE_MATCH_SWITCH);

				// empty DFA
				empty = fsm_new(opts);
				start = fsm_addstate(empty);
				fsm_setstart(empty,start);

				names_match->u.mswitch.dfa = empty;
				names_match->u.mswitch.dft_case = cnode_new_mcase(NULL,nametree);
			}
			break;

		case JVST_CNODE_MATCH_SWITCH:
			// names_pat = nametree;
			names_match = nametree;
			break;

		default:
			DIEF("PROP_NAMES does not support cnode type %s\n",
				jvst_cnode_type_name(nametree->type));
			break;
		}
	}

	// defer setting carryopaque until we're done compiling the REs
	// into their own DFAs.  each RE gets a unique opaque value for
	// all of its endstates.  When we union the DFAs together, we
	// may need to merge these states, but not during compilation.
	opts->carryopaque = merge_mcases_with_and;

	if (matches != NULL) {
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
	}

	mcases = NULL;
	if (matches != NULL) {
		// step 3: collect all MATCH_CASE nodes from the DFA by
		// iterating over the DFA end states.  All MATCH_CASE nodes must
		// be placed into a linked list.
		//
		// step 4: sort the MATCH_CASE nodes.
		//
		// This keeps the IR output deterministic (useful for testing,
		// possibly other places?).  Currently this could be elided (or
		// put behind an optional flag) if necessary.
		collect_mcases(matches, &mcases);
	}

	// step 5: build the MATCH_SWITCH container to hold the cases
	// and the DFA.  The default case should be VALID.
	msw = jvst_cnode_alloc(JVST_CNODE_MATCH_SWITCH);
	msw->u.mswitch.dfa = matches;
	msw->u.mswitch.opts = opts;
	msw->u.mswitch.cases = mcases;

	// if have a PROP_NAMES node, the default case (non-matching) is
	// INVALID
	msw->u.mswitch.dft_case = cnode_new_mcase(NULL,dft);

	// step 4: simplify and canonify the constraint of each MATCH_CASE node.
	// 	   We re-simplify the constraints because multiple
	// 	   constraints can be merged.
	for (; mcases != NULL; mcases = mcases->next) {
		struct jvst_cnode *ncons, *vcons;
		ncons = mcases->u.mcase.name_constraint;
		if (ncons != NULL) {
			ncons = jvst_cnode_simplify(ncons);
			ncons = jvst_cnode_canonify(ncons);
			mcases->u.mcase.name_constraint = ncons;
		}

		vcons = jvst_cnode_simplify(mcases->u.mcase.value_constraint);
		mcases->u.mcase.value_constraint = jvst_cnode_canonify(vcons);
	}

	if (names_match == NULL) {
		return msw;
	}

	{
		struct jvst_cnode *merged;

		assert(msw->next == NULL);
		assert(names_match->next == NULL);

		msw->next = names_match;
		// merged = merge_mswitches_with_and(msw);
		merged = merge_mswitches(msw, JVST_CNODE_AND);
		return merged;
	}
}

// replaces REQUIRED nodes with REQMASK and REQBIT nodes
//
// XXX - should this be in the translation phase?
static struct jvst_cnode *
cnode_canonify_required(struct jvst_cnode *req)
{
	struct jvst_cnode *jxn, **npp, *mask, *pset;
	struct ast_string_set *rcases;
	size_t nbits;

	assert(req->type == JVST_CNODE_OBJ_REQUIRED);
	assert(req->u.required != NULL);

	jxn = jvst_cnode_alloc(JVST_CNODE_AND);
	npp = &jxn->u.ctrl;

	mask = jvst_cnode_alloc(JVST_CNODE_OBJ_REQMASK);
	*npp = mask;
	npp = &(*npp)->next;

	pset = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_SET);
	*npp = pset;
	npp = &pset->u.prop_set;

	for (nbits=0, rcases = req->u.required; rcases != NULL; nbits++, rcases = rcases->next) {
		struct jvst_cnode *pm, *reqbit;
		pm = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_MATCH);
		pm->u.prop_match.match.dialect = RE_LITERAL;
		pm->u.prop_match.match.str = rcases->str;

		reqbit = jvst_cnode_alloc(JVST_CNODE_OBJ_REQBIT);
		reqbit->u.reqbit.bit = nbits;
		pm->u.prop_match.constraint = reqbit;

		*npp = pm;
		npp = &pm->next;
	}

	mask->u.reqmask.nbits = nbits;
	return jxn;
}

static struct jvst_cnode *
cnode_canonify_strmatch(struct jvst_cnode *top)
{
	struct jvst_cnode *mcase, *msw, *cons;
	struct jvst_cnode_matchset *mset;
	struct fsm_options *opts;
	struct fsm *match;

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
		.carryopaque = NULL,
	};

	assert(top->type == JVST_CNODE_STR_MATCH);
	assert(top->u.str_match.str.s != NULL);

	cons = jvst_cnode_alloc(JVST_CNODE_VALID);
	mset = cnode_matchset_new(top->u.str_match, NULL);
	mcase = cnode_new_mcase(mset, cons);
	assert(mcase->next == NULL);

	match = mcase_re_compile(&top->u.str_match, opts, NULL);

	if (!fsm_determinise(match)) {
		perror("cannot determinise fsm");
		abort();
	}

	fsm_setendopaque(match, mcase);

	// build the MATCH_SWITCH container to hold the case and the
	// DFA.  The default case is INVALID.
	msw = jvst_cnode_alloc(JVST_CNODE_MATCH_SWITCH);
	msw->u.mswitch.dfa = match;
	msw->u.mswitch.opts = opts;
	msw->u.mswitch.cases = mcase;
	msw->u.mswitch.dft_case = cnode_new_mcase(NULL, jvst_cnode_alloc(JVST_CNODE_INVALID));

	return msw;
}

static struct jvst_cnode *
cnode_canonify_pass1(struct jvst_cnode *tree);

// canonifies a list of nodes
static struct jvst_cnode *
cnode_nodelist_canonify_pass1(struct jvst_cnode *nodes)
{
	struct jvst_cnode *result, **rpp, *n, *next;

	result = NULL;
	rpp = &result;
	for (n = nodes; n != NULL; n = next) {
		next = n->next;
		
		*rpp = cnode_canonify_pass1(n);
		rpp = &(*rpp)->next;
		*rpp = NULL;
	}

	return result;
}

// Initial canonification before DFAs are constructed
static struct jvst_cnode *
cnode_canonify_pass1(struct jvst_cnode *tree)
{
	struct jvst_cnode *node;

	// this also makes a copy...
	tree = cnode_deep_copy(tree);

	switch (tree->type) {
	case JVST_CNODE_INVALID:
	case JVST_CNODE_VALID:
	case JVST_CNODE_ARR_UNIQUE:
	case JVST_CNODE_NUM_MULTIPLE_OF:
	case JVST_CNODE_NUM_RANGE:
	case JVST_CNODE_PROP_RANGE:
	case JVST_CNODE_ITEM_RANGE:
	case JVST_CNODE_REF:
		return tree;

	case JVST_CNODE_AND:
	case JVST_CNODE_OR:
	case JVST_CNODE_XOR:
	case JVST_CNODE_NOT:
		tree->u.ctrl = cnode_nodelist_canonify_pass1(tree->u.ctrl);
		return tree;

	case JVST_CNODE_SWITCH:
		{
			size_t i, n;
			for (i = 0, n = ARRAYLEN(tree->u.sw); i < n; i++) {
				tree->u.sw[i] = cnode_canonify_pass1(tree->u.sw[i]);
			}
		}
		return tree;

	case JVST_CNODE_OBJ_PROP_SET:
		{
			for (node=tree->u.prop_set; node != NULL; node = node->next) {
				struct jvst_cnode *cons;

				switch (node->type) {
				case JVST_CNODE_OBJ_PROP_MATCH:
					cons = cnode_canonify_pass1(node->u.prop_match.constraint);
					node->u.prop_match.constraint = cons;
					break;

				case JVST_CNODE_OBJ_PROP_DEFAULT:
					cons = cnode_canonify_pass1(node->u.prop_default);
					node->u.prop_default = cons;
					break;

				case JVST_CNODE_OBJ_PROP_NAMES:
					break;

				default:
					DIEF("%s should not have %s as a child node\n",
						jvst_cnode_type_name(tree->type),
						jvst_cnode_type_name(node->type));
				}
			}

		}
		return tree;

	case JVST_CNODE_OBJ_REQUIRED:
		return cnode_canonify_required(tree);

	case JVST_CNODE_STR_MATCH:
		return cnode_canonify_strmatch(tree);

	case JVST_CNODE_LENGTH_RANGE:
		{
			struct jvst_cnode *msw, *mc, *v;

			msw = jvst_cnode_alloc(JVST_CNODE_MATCH_SWITCH);
			v = jvst_cnode_alloc(JVST_CNODE_VALID);
			mc = cnode_new_mcase(NULL,v);
			mc->u.mcase.name_constraint = tree;
			msw->u.mswitch.dft_case = mc;

			return msw;
		}

	case JVST_CNODE_ARR_ITEM:
	case JVST_CNODE_ARR_ADDITIONAL:
		tree->u.items = cnode_nodelist_canonify_pass1(tree->u.items);
		return tree;

	case JVST_CNODE_ARR_CONTAINS:
		tree->u.items = cnode_nodelist_canonify_pass1(tree->u.items);
		return tree;

	case JVST_CNODE_MATCH_SWITCH:
		{
			struct jvst_cnode *c;
			for (c = tree->u.mswitch.cases; c != NULL; c = c->next) {
				if (c->u.mcase.name_constraint != NULL) {
					c->u.mcase.name_constraint = cnode_canonify_pass1(c->u.mcase.name_constraint);
				}
				c->u.mcase.value_constraint = cnode_canonify_pass1(c->u.mcase.value_constraint);
			}

			c = tree->u.mswitch.dft_case;
			if (c->u.mcase.name_constraint != NULL) {
				c->u.mcase.name_constraint = cnode_canonify_pass1(c->u.mcase.name_constraint);
			}
			c->u.mcase.value_constraint = cnode_canonify_pass1(c->u.mcase.value_constraint);
		}
		return tree;

	case JVST_CNODE_MATCH_CASE:
		SHOULD_NOT_REACH();

	case JVST_CNODE_OBJ_PROP_DEFAULT:
	case JVST_CNODE_OBJ_PROP_NAMES:
	case JVST_CNODE_NUM_INTEGER:
	case JVST_CNODE_OBJ_PROP_MATCH:
	case JVST_CNODE_OBJ_REQMASK:
	case JVST_CNODE_OBJ_REQBIT:
		// TODO: basic optimization for these nodes
		return tree;

	}

	// avoid default case in switch so the compiler can complain if
	// we add new cnode types
	SHOULD_NOT_REACH();
}

static int cnode_cmp(const void *p0, const void *p1)
{
	const struct jvst_cnode *a, *b;
	int delta;

	a = *(const void **)p0;
	b = *(const void **)p1;

	delta = a->type - b->type;
	/*
	fprintf(stderr, "a is %s, b is %s, delta = %d\n", 
		jvst_cnode_type_name(a->type),
		jvst_cnode_type_name(b->type),
		delta);
		*/
	if (delta != 0) {
		return delta;
	}

	// TODO: implement comparison for nodes of the same type!
	return 0;
}

static struct jvst_cnode *
cnode_canonify_pass2(struct jvst_cnode *tree);

// canonifies a list of nodes
static struct jvst_cnode *
cnode_nodelist_canonify_pass2(struct jvst_cnode *nodes)
{
	struct jvst_cnode *result, **rpp, *n, *next;

	result = NULL;
	rpp = &result;
	for (n = nodes; n != NULL; n = next) {
		next = n->next;
		
		*rpp = cnode_canonify_pass2(n);
		rpp = &(*rpp)->next;
		*rpp = NULL;
	}

	return result;
}

static struct jvst_cnode *
cnode_canonify_pass2(struct jvst_cnode *tree)
{
	struct jvst_cnode *node;

	// this also makes a copy...
	tree = cnode_deep_copy(tree);

	switch (tree->type) {
	case JVST_CNODE_INVALID:
	case JVST_CNODE_VALID:
	case JVST_CNODE_ARR_UNIQUE:
	case JVST_CNODE_NUM_MULTIPLE_OF:
	case JVST_CNODE_NUM_RANGE:
	case JVST_CNODE_LENGTH_RANGE:
	case JVST_CNODE_PROP_RANGE:
	case JVST_CNODE_ITEM_RANGE:
	case JVST_CNODE_REF:
		return tree;

	case JVST_CNODE_NOT:
		{
			// NOT should have exactly one child!
			assert(tree->u.ctrl != NULL);
			assert(tree->u.ctrl->next == NULL);

			tree->u.ctrl = cnode_canonify_pass2(tree->u.ctrl);
		}
		return tree;

	case JVST_CNODE_AND:
	case JVST_CNODE_OR:
	case JVST_CNODE_XOR:
		{
			struct jvst_cnode *xform, **xpp, **nlist;
			size_t i, n;

			// AND/OR/XOR should have at least one child
			assert(tree->u.ctrl != NULL);

			// count number of child nodes
			n = 0;
			for (node = tree->u.ctrl; node != NULL; node = node->next) {
				n++;
			}

			// canonify the nodes, store in nlist for now
			nlist = xmalloc(n * sizeof nlist[0]);
			for (i=0, node = tree->u.ctrl; node != NULL; i++, node = node->next) {
				assert(i < n);
				nlist[i] = cnode_canonify_pass2(node);
			}
			assert(i == n);

			// now sort the nodes to keep them in
			// deterministic order.
			//
			// XXX - need to make sure that this correctly
			// sorts nodes of the same type in a
			// deterministic manner
			qsort(nlist, n, sizeof *nlist, cnode_cmp);

			// reform the linked list
			xform = NULL;
			xpp = &xform;
			for (i=0; i < n; i++) {
				*xpp = nlist[i];
				xpp = &nlist[i]->next;
				*xpp = NULL;
			}

			free(nlist);
			tree->u.ctrl = xform;
		}
		return tree;

	case JVST_CNODE_SWITCH:
		{
			size_t i, n;
			for (i = 0, n = ARRAYLEN(tree->u.sw); i < n; i++) {
				tree->u.sw[i] = cnode_canonify_pass2(tree->u.sw[i]);
			}
		}
		return tree;

	case JVST_CNODE_OBJ_PROP_SET:
		{
			struct jvst_cnode *result;
			result = cnode_canonify_propset(tree);
			return cnode_canonify_pass2(result);
		}

	case JVST_CNODE_MATCH_SWITCH:
		{
			struct jvst_cnode *mc, **mcpp;

			tree->u.mswitch.dft_case = cnode_canonify_pass2(tree->u.mswitch.dft_case);

			mc = NULL;
			mcpp = &mc;
			for (node = tree->u.mswitch.cases; node != NULL; node = node->next) {
				struct jvst_cnode *result;

				assert(node->u.mcase.tmp == NULL);

				result = cnode_canonify_pass2(node);
				assert(result != NULL);
				node->u.mcase.tmp = result;
				*mcpp = result;
				mcpp = &(*mcpp)->next;
			}

			*mcpp = NULL;

			// now we have to relabel the states of the
			// fsm...
			//
			// XXX - should we make a copy of the DFA?
			// This could result in a lot of copies...
			if (tree->u.mswitch.dfa != NULL) {
				fsm_walk_states(tree->u.mswitch.dfa, NULL, mcase_update_opaque);
			}

			tree->u.mswitch.cases = mc;
		}
		return tree;

	case JVST_CNODE_MATCH_CASE:
		{
			if (tree->u.mcase.name_constraint != NULL) {
				tree->u.mcase.name_constraint = cnode_canonify_pass2(tree->u.mcase.name_constraint);
			}
			tree->u.mcase.value_constraint = cnode_canonify_pass2(tree->u.mcase.value_constraint);
		}
		return tree;

	case JVST_CNODE_ARR_ITEM:
	case JVST_CNODE_ARR_ADDITIONAL:
		tree->u.items = cnode_nodelist_canonify_pass2(tree->u.items);
		return tree;

	case JVST_CNODE_ARR_CONTAINS:
		tree->u.contains = cnode_nodelist_canonify_pass2(tree->u.contains);
		return tree;

	case JVST_CNODE_NUM_INTEGER:
	case JVST_CNODE_OBJ_REQMASK:
	case JVST_CNODE_OBJ_REQBIT:
		// TODO: basic optimization for these nodes
		return tree;

	case JVST_CNODE_STR_MATCH:
	case JVST_CNODE_OBJ_PROP_DEFAULT:
	case JVST_CNODE_OBJ_PROP_NAMES:
	case JVST_CNODE_OBJ_PROP_MATCH:
	case JVST_CNODE_OBJ_REQUIRED:
		INVALID_OPERATION(tree, "canonization (pass 2)");
	}

	// avoid default case in switch so the compiler can complain if
	// we add new cnode types
	SHOULD_NOT_REACH();
}

struct jvst_cnode *
jvst_cnode_canonify(struct jvst_cnode *tree)
{
	tree = cnode_canonify_pass1(tree);
	tree = jvst_cnode_simplify(tree);
	tree = cnode_canonify_pass2(tree);
	tree = jvst_cnode_simplify(tree);
	return tree;
}

void
jvst_cnode_forest_add_tree(struct jvst_cnode_forest *forest, struct jvst_cnode *tree)
{
	forest->trees = xenlargevec(forest->trees, &forest->cap, 1, sizeof forest->trees[0]);

	assert(forest->cap > 0);
	assert(forest->len < forest->cap);
	forest->trees[forest->len++] = tree;
}

void
jvst_cnode_forest_initialize(struct jvst_cnode_forest *forest)
{
	static const struct jvst_cnode_forest zero;

	*forest = zero;
	forest->all_ids = jvst_cnode_id_table_new();
	forest->ref_ids = jvst_cnode_id_table_new();
}

struct jvst_cnode_forest *
jvst_cnode_forest_new(void)
{
	struct jvst_cnode_forest *forest;

	forest = malloc(sizeof *forest);
	jvst_cnode_forest_initialize(forest);

	return forest;
}

void
jvst_cnode_forest_finalize(struct jvst_cnode_forest *forest)
{
	if (forest == NULL) {
		return;
	}

	jvst_cnode_id_table_delete(forest->all_ids);
	jvst_cnode_id_table_delete(forest->ref_ids);
	free(forest->trees);
}

void
jvst_cnode_forest_delete(struct jvst_cnode_forest *forest)
{
	jvst_cnode_forest_finalize(forest);
	free(forest);
}

static int
cnode_id_update(void *opaque, struct json_string *k, struct jvst_cnode **ctreep)
{
	struct hmap *upds = opaque;

	(void)k;

	assert(ctreep != NULL);
	assert(upds != NULL);

	if (*ctreep != NULL) {
		struct jvst_cnode *ctree_new;
		ctree_new = hmap_getptr(upds, *ctreep);
		assert(ctree_new != NULL);

		*ctreep = ctree_new;
	}

	return 1;
}

static struct jvst_cnode_forest *
cnode_update_forest(struct jvst_cnode_forest *forest, struct jvst_cnode *(*updater)(struct jvst_cnode *))
{
	size_t i,n;
	struct hmap *upds;

	upds = hmap_create_pointer(
			jvst_cnode_id_table_nbuckets(forest->ref_ids),
			jvst_cnode_id_table_maxload(forest->ref_ids));

	n = forest->len;
	for (i = 0; i < n; i++) {
		struct jvst_cnode *cnode;

		cnode = updater(forest->trees[i]);
		if (!hmap_setptr(upds, forest->trees[i], cnode)) {
			fprintf(stderr, "could not add entry to cnode update table\n");
			abort();
		}

		forest->trees[i] = cnode;
	}

	// jvst_cnode_id_table_foreach(forest->all_ids, cnode_id_update, upds);
	jvst_cnode_id_table_foreach(forest->ref_ids, cnode_id_update, upds);

	hmap_free(upds);

	return forest;
}

struct jvst_cnode_forest *
jvst_cnode_simplify_forest(struct jvst_cnode_forest *forest)
{
	return cnode_update_forest(forest, jvst_cnode_simplify);
}

// Canonifies the cnode forest.  Replaces each tree in the forest with a
// canonified one.
struct jvst_cnode_forest *
jvst_cnode_canonify_forest(struct jvst_cnode_forest *forest)
{
	return cnode_update_forest(forest, jvst_cnode_canonify);
}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
