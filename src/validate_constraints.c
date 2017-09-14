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
#if 0
			if (node->u.mswitch.constraints != NULL) {
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "CONSTRAINTS[\n");
				sbuf_indent(buf, indent+4);
				jvst_cnode_dump_inner(node->u.mswitch.constraints, buf, indent + 4);
				sbuf_snprintf(buf, "\n");
				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "],\n");
			}
#endif

			// assert(node->u.mswitch.default_case != NULL);

			if (node->u.mswitch.dft_case != NULL) {
				struct jvst_cnode *dft, *constraint;

				dft = node->u.mswitch.dft_case;
				assert(dft->type == JVST_CNODE_MATCH_CASE);

				constraint = dft->u.mcase.constraint;
				assert(constraint != NULL);

				sbuf_indent(buf, indent+2);
				sbuf_snprintf(buf, "DEFAULT[\n");

				sbuf_indent(buf, indent+4);
				jvst_cnode_dump_inner(constraint, buf, indent + 4);
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

	case JVST_CNODE_NOT:
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

// Just do a raw translation without doing any optimization of the
// constraint tree
struct jvst_cnode *
jvst_cnode_translate_ast(const struct ast_schema *ast)
{
	struct jvst_cnode *node;
	enum json_valuetype types;

	assert(ast != NULL);

	if (ast->kws & KWS_VALUE) {
	       	if (ast->value.type != JSON_VALUE_BOOL) {
			fprintf(stderr, "Invalid JSON value type.  Schemas must be objects or booleans.\n");
			abort();
		}
		return cnode_new_switch(ast->value.u.v);
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

			constraint = jvst_cnode_translate_ast(ast->items->schema);
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

				constraint = jvst_cnode_translate_ast(sl->schema);
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

		constraint = jvst_cnode_translate_ast(ast->additional_items);
		additional = jvst_cnode_alloc(JVST_CNODE_ARR_ADDITIONAL);
		additional->u.items = constraint;

		add_ast_constraint(node, SJP_ARRAY_BEG, additional);
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
			pnode->u.prop_match.constraint = jvst_cnode_translate_ast(pset->schema);
			*plist = pnode;
			plist = &pnode->next;
		}

		prop_set = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_SET);
		prop_set->u.prop_set = phead;
		assert(phead != NULL);

		add_ast_constraint(node, SJP_OBJECT_BEG, prop_set);
	}

	if (ast->additional_properties != NULL) {
		struct jvst_cnode *constraint, **cpp, *pdft;
		struct ast_schema_set *sset;

		constraint = jvst_cnode_translate_ast(ast->additional_properties);
		assert(constraint != NULL);
		assert(constraint->next == NULL);

		pdft = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_DEFAULT);
		pdft->u.prop_default = constraint;

		add_ast_constraint(node, SJP_OBJECT_BEG, pdft);
	}

	if (ast->property_names != NULL) {
		struct jvst_cnode *constraint;
		struct jvst_cnode *pnames;

		constraint = jvst_cnode_translate_ast(ast->property_names);

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

static struct jvst_cnode *
mswitch_and_cases_with_default(struct jvst_cnode *msw, struct jvst_cnode *dft)
{
	struct jvst_cnode *c, *new_cases, **ncpp;

	assert(msw->type == JVST_CNODE_MATCH_SWITCH);

	if (dft->type == JVST_CNODE_VALID) {
		return msw;
	}

	new_cases = NULL;
	ncpp = &new_cases;
	for (c = msw->u.mswitch.cases; c != NULL; c = c->next) {
		struct jvst_cnode *nc, *ndft;
		assert(c->type == JVST_CNODE_MATCH_CASE);

		nc = cnode_deep_copy(c);
		ndft = cnode_deep_copy(dft);

		nc->u.mcase.constraint = cnode_and_constraints(nc->u.mcase.constraint, ndft);

		// the dfa can be updated
		c->u.mcase.tmp = nc;

		*ncpp = nc;
		ncpp = &nc->next;
	}

	fsm_walk_states(msw->u.mswitch.dfa, NULL, mcase_update_opaque);

	// reset the tmp fields
	for (c = msw->u.mswitch.cases; c != NULL; c = c->next) {
		assert(c->type == JVST_CNODE_MATCH_CASE);
		assert(c->u.mcase.tmp != NULL);
		c->u.mcase.tmp = NULL;
	}

	msw->u.mswitch.cases = new_cases;

	return msw;
}

static int matchset_cmp(const void *p0, const void *p1)
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

	assert(node->next == NULL);
	assert(collector->mcpp != &node->next);

	*collector->mcpp = node;
	collector->mcpp = &node->next;
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
merge_mcases(const struct fsm_state **orig, size_t n,
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
subtract_nd(const struct fsm *a, const struct fsm *b, void *opaque_compl, const struct fsm_options *opts)
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

	if (!fsm_complement(dfa2)) {
		fsm_free(dfa1);
		fsm_free(dfa2);
		return NULL;
	}
	fsm_setendopaque(dfa2, opaque_compl);

	return fsm_intersect(dfa1,dfa2);
}

static struct jvst_cnode *
merge_mswitches_with_and(struct jvst_cnode *mswlst)
{
	struct jvst_cnode *n, *msw;

	assert(mswlst != NULL);
	assert(mswlst->type == JVST_CNODE_MATCH_SWITCH);

	if (mswlst->next == NULL) {
		return mswlst;
	}

	msw = cnode_deep_copy(mswlst);
	for (n = mswlst->next; n != NULL; n = n->next) {
		assert(n->type == JVST_CNODE_MATCH_SWITCH);

		if (msw->u.mswitch.cases != NULL && n->u.mswitch.cases != NULL) {
			struct fsm *dfa1, *dfa2, *both, *only1, *only2, *combined;
			const struct fsm_options *opts;
			struct jvst_cnode *mc1, *mc2;

			// Combining match_switch nodes
			//
			// it's an AND operation... this requires a bit of care because of the
			// default case.
			//
			// Let the non-default cases for DFA1 be:
			//   A_1, A_2, ... A_M, and the default case be A_0.
			//
			// Similarly, let the non-default cases for DFA2 be:
			//   B_1, B_2, ... B_N, and the default case be B_0.
			//
			// The intersection of DFA1 and DFA2 will be a set of L cases in DFA1:
			//   A_i1, A_i2, ..., A_iL, 
			// and a set of L cases in DFA2:
			//   B_j1, B_j2, ..., B_jL,
			// where A_i1 has the same end state as B_j1, A_i2 and B_j2, ...,
			// A_iL and B_jL.
			//
			// We want to AND together these cases to give
			//   C_1, C_2, ..., C_L,
			// where C_k = AND(A_ik, B_jk)
			// 
			// This leaves M-L cases in DFA1 that don't match with a case in DFA2
			// and N-L cases in DFA2 that don't match with a case in DFA1.
			//
			// For the M-L cases in DFA1, they should be AND'd with the default case
			// of DFA2.
			//
			// Similarly, for the N-L cases in DFA2, they should be AND'd with the
			// default case in DFA1.
			//
			// Finally, the default case of the combined nodes matches neither DFA1
			// nor DFA2, and should have the default cases for both AND'd together.
			//
			// To find the cases that match both, we need intersect(DFA1, DFA2).
			// To find those that match DFA1 and not DFA2, we need subtract(DFA1, DFA2).
			// To find those that match DFA2 and not DFA1, we need subtract(DFA2, DFA1).
			//
			// In all of these cases, we need the opaque values to be merged
			// correctly.

			dfa1 = msw->u.mswitch.dfa;
			dfa2 = n->u.mswitch.dfa;

			opts = fsm_getoptions(dfa1);
			assert(opts->carryopaque == merge_mcases);

			// both = DFA1 & DFA2
			both = intersect_nd(dfa1,dfa2,opts);
			if (!both) {
				perror("intersecting (dfa1 & dfa2)");
				abort();
			}

			if (!fsm_minimise(both)) {
				perror("minimizing (dfa1 & dfa2)");
				abort();
			}

			// only1 = DFA2 - DFA1
			mc2 = cnode_deep_copy(n->u.mswitch.dft_case);
			only1 = subtract_nd(dfa1,dfa2,mc2,opts);
			if (!only1) {
				perror("subtracting (DFA1 - DFA2)");
				abort();
			}

			if (!fsm_minimise(only1)) {
				perror("minimizing (DFA1 - DFA2)");
				abort();
			}

			// only2 = DFA2 - DFA1
			mc1 = cnode_deep_copy(msw->u.mswitch.dft_case);
			only2 = subtract_nd(dfa2,dfa1,mc1,opts);
			if (!only2) {
				perror("subtracting (DFA2 - DFA1)");
				abort();
			}

			if (!fsm_minimise(only2)) {
				perror("minimizing (DFA2 - DFA1)");
				abort();
			}

			// now union both, only1, and only2 together
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

			// now gather mcases
			msw->u.mswitch.dfa = combined;
			collect_mcases(combined, &msw->u.mswitch.cases);
		} else if (n->u.mswitch.cases != NULL) {
			assert(msw->u.mswitch.cases == NULL);

			msw->u.mswitch.dfa = fsm_clone(n->u.mswitch.dfa);
			msw->u.mswitch.cases = n->u.mswitch.cases;
			mswitch_and_cases_with_default(msw, msw->u.mswitch.dft_case->u.mcase.constraint);
		} else if (msw->u.mswitch.cases != NULL) {
			// need to AND together msw's default case and
			// each of n's cases
			mswitch_and_cases_with_default(msw, n->u.mswitch.dft_case->u.mcase.constraint);
		}

		assert(msw->u.mswitch.dft_case != NULL);
		assert(msw->u.mswitch.dft_case->type == JVST_CNODE_MATCH_CASE);
		msw->u.mswitch.dft_case->u.mcase.constraint = cnode_and_constraints(
				msw->u.mswitch.dft_case->u.mcase.constraint, n->u.mswitch.dft_case->u.mcase.constraint);
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

	// collect all MATCH_SWITCH children and nodes we want to push
	// into MATCH_SWITCH cases
	msw = NULL;
	mswpp = &msw;

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

	// no match_switch node
	if (msw == NULL) {
		*npp = conds;
		return top;
	}

	msw = merge_mswitches_with_and(msw);

	*npp = msw;

	if (conds == NULL) {
		return top;
	}

	// push string conditionals into the constraints field of the
	// MATCH_SWITCH
	//
	// XXX - this is currently the first match_switch node, but
	//       should work fine when we combine multiple match_switch
	//       nodes
	{
		struct jvst_cnode *c, *cjxn;
		cjxn = jvst_cnode_alloc(JVST_CNODE_AND);
		cjxn->u.ctrl = conds;

		assert(cjxn->u.ctrl != NULL);

		for (c = msw->u.mswitch.cases; c != NULL; c = c->next) {
			struct jvst_cnode *top_jxn, *jxn;

			assert(c->u.mcase.constraint != NULL);
			assert(c->u.mcase.constraint->next == NULL);

			// Can do a better job not overallocating nodes
			// here
			jxn = cnode_deep_copy(cjxn);
			top_jxn = jvst_cnode_alloc(JVST_CNODE_AND);
			top_jxn->u.ctrl = jxn;
			jxn->next = c->u.mcase.constraint;

			c->u.mcase.constraint = jvst_cnode_simplify(top_jxn);
		}

		{ 
			struct jvst_cnode *dft, *top_jxn;
			dft = msw->u.mswitch.dft_case;

			assert(dft != NULL);
			assert(dft->type == JVST_CNODE_MATCH_CASE);
			assert(dft->next == NULL);
			assert(cjxn->next == NULL);

			top_jxn = jvst_cnode_alloc(JVST_CNODE_AND);
			top_jxn->u.ctrl = cjxn;
			cjxn->next = dft->u.mcase.constraint;

			msw->u.mswitch.dft_case->u.mcase.constraint = jvst_cnode_simplify(top_jxn);
		}
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

	if ((top->type == JVST_CNODE_AND) || (top->type == JVST_CNODE_OR)) {
		top = cnode_simplify_andor_switches(top);
	}

	/* combine AND'd match_switch nodes, moves any AND'd COUNT_RANGE nodes */
	if (top->type == JVST_CNODE_AND) {
		top = cnode_simplify_and_mswitch(top);
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
	case JVST_CNODE_ARR_ADDITIONAL:
		{
			struct jvst_cnode *it, *next, *simplified_items, **spp;

			simplified_items = NULL;
			spp = &simplified_items;
			for (it = tree->u.items; it != NULL; it = next) {
				struct jvst_cnode *simplified;

				next = it->next;

				simplified = jvst_cnode_simplify(it);
				*spp = simplified;
				spp = &(*spp)->next;
				*spp = NULL;
			}

			tree->u.items = simplified_items;
			return tree;
		}

	case JVST_CNODE_MATCH_SWITCH:
		{
			struct jvst_cnode *mc, *next;

			tree->u.mswitch.dft_case = jvst_cnode_simplify(tree->u.mswitch.dft_case);

			for (mc=tree->u.mswitch.cases; mc != NULL; mc = next) {
				assert(mc->type == JVST_CNODE_MATCH_CASE);
				next = mc->next;
				mc->u.mcase.constraint = jvst_cnode_simplify(mc->u.mcase.constraint);
			}


			return tree;
		}

	case JVST_CNODE_MATCH_CASE:
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
merge_mcases(const struct fsm_state **orig, size_t n,
	struct fsm *dfa, struct fsm_state *comb)
{
	struct jvst_cnode *mcase, *jxn, **jpp;
	struct jvst_cnode_matchset **mspp;
	struct jvst_cnode *mcases_buf[8] = { 0 }, **mcases;
	struct jvst_cnode_matchset *mset_buf[8] = { 0 }, **msets;
	size_t nstates, nuniq, nmatchsets;
	size_t i,ind;

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
		assert(mcase->next == NULL);
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

	jxn = jvst_cnode_alloc(JVST_CNODE_AND);
	jpp = &jxn->u.ctrl;
	mcase = cnode_new_mcase(NULL, jxn);
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

		*jpp = cnode_deep_copy(c->u.mcase.constraint);
		jpp = &(*jpp)->next;
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
	opts->carryopaque = merge_mcases;

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
		struct jvst_cnode *cons;
		cons = jvst_cnode_simplify(mcases->u.mcase.constraint);
		mcases->u.mcase.constraint = jvst_cnode_canonify(cons);
	}

	if (names_match == NULL) {
		return msw;
	}

	{
		struct jvst_cnode *merged;

		assert(msw->next == NULL);
		assert(names_match->next == NULL);

		msw->next = names_match;
		merged = merge_mswitches_with_and(msw);
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
	case JVST_CNODE_NUM_RANGE:
	case JVST_CNODE_PROP_RANGE:
	case JVST_CNODE_ITEM_RANGE:
		return tree;

	case JVST_CNODE_AND:
	case JVST_CNODE_OR:
	case JVST_CNODE_XOR:
	case JVST_CNODE_NOT:
		{
			struct jvst_cnode *xform = NULL;
			struct jvst_cnode **xpp = &xform;

			for (node = tree->u.ctrl; node != NULL; node = node->next) {
				*xpp = cnode_canonify_pass1(node);
				xpp = &(*xpp)->next;
			}

			tree->u.ctrl = xform;

		}
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
			struct jvst_cnode *msw;

			msw = jvst_cnode_alloc(JVST_CNODE_MATCH_SWITCH);
			msw->u.mswitch.dft_case = cnode_new_mcase(NULL,tree);

			return msw;
		}

	case JVST_CNODE_OBJ_PROP_DEFAULT:
	case JVST_CNODE_OBJ_PROP_NAMES:
	case JVST_CNODE_NUM_INTEGER:
	case JVST_CNODE_OBJ_PROP_MATCH:
	case JVST_CNODE_ARR_ITEM:
	case JVST_CNODE_ARR_ADDITIONAL:
	case JVST_CNODE_OBJ_REQMASK:
	case JVST_CNODE_OBJ_REQBIT:
	case JVST_CNODE_MATCH_SWITCH:
	case JVST_CNODE_MATCH_CASE:
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
cnode_canonify_pass2(struct jvst_cnode *tree)
{
	struct jvst_cnode *node;

	// this also makes a copy...
	tree = cnode_deep_copy(tree);

	switch (tree->type) {
	case JVST_CNODE_INVALID:
	case JVST_CNODE_VALID:
	case JVST_CNODE_ARR_UNIQUE:
	case JVST_CNODE_NUM_RANGE:
	case JVST_CNODE_LENGTH_RANGE:
	case JVST_CNODE_PROP_RANGE:
	case JVST_CNODE_ITEM_RANGE:
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
			tree->u.mcase.constraint = cnode_canonify_pass2(tree->u.mcase.constraint);
		}
		return tree;

	case JVST_CNODE_NUM_INTEGER:
	case JVST_CNODE_STR_MATCH:
	case JVST_CNODE_ARR_ITEM:
	case JVST_CNODE_ARR_ADDITIONAL:
	case JVST_CNODE_OBJ_REQMASK:
	case JVST_CNODE_OBJ_REQBIT:
		// TODO: basic optimization for these nodes
		return tree;

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
	return tree;
}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
