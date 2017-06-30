#include "validate_constraints.h"

#include <assert.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

#include "xalloc.h"

#include "jvst_macros.h"
#include "sjp_testing.h"

#define SHOULD_NOT_REACH() do{          \
  fprintf(stderr, "SHOULD NOT REACH %s, line %d (function %s)\n", \
      __FILE__, __LINE__, __func__);    \
  abort();                              \
} while(0)

enum {
  JVST_CNODE_CHUNKSIZE = 1024,
  JVST_CNODE_NUMROOTS  = 32,
};

enum {
  MARKSIZE = JVST_CNODE_CHUNKSIZE / CHAR_BIT + (JVST_CNODE_CHUNKSIZE % CHAR_BIT) ? 1 : 0,
};

struct jvst_cnode_pool {
  struct jvst_cnode_pool *next;
  struct jvst_cnode items[JVST_CNODE_CHUNKSIZE];
  unsigned char marks[MARKSIZE];
};

/* XXX - should these be global vars?  also, not thread safe. */
static struct jvst_cnode_pool *pool = NULL;
static size_t pool_item = 0;
static struct jvst_cnode *freelist = NULL;

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

static struct jvst_cnode *roots[JVST_CNODE_NUMROOTS] = { NULL };
static int nroots = 0;

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
    sset = strset_pool.freelist;
    strset_pool.freelist = strset_pool.freelist->next;
    return sset;
  }

new_pool:
  // fall back to allocating a new pool
  p = xmalloc(sizeof *p);
  p->next = strset_pool.head;
  strset_pool.head = p;
  strset_pool.top = 1;
  return &p->items[0];
}

static struct ast_string_set *
cnode_strset(struct json_string str, struct ast_string_set *next)
{
  struct ast_string_set *sset;
  sset = cnode_strset_alloc();
  sset->str = str;
  sset->next = next;
  return sset;
}

static struct ast_string_set *
cnode_strset_copy(struct ast_string_set *orig)
{
  struct ast_string_set *head, **hpp;
  head = NULL;
  hpp = &head;
  for (; orig != NULL; orig = orig->next) {
    *hpp = cnode_strset(orig->str, NULL);
    hpp = &(*hpp)->next;
  }

  return head;
}

void json_string_finalize(struct json_string *s)
{
  // XXX - implement
  (void)s;
}

static struct jvst_cnode *cnode_new(void)
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
    freelist = freelist->next;
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

struct jvst_cnode *jvst_cnode_alloc(enum JVST_CNODE_TYPE type)
{
  struct jvst_cnode *n;
  n = cnode_new();
  n->type = type;
  n->next = NULL;
  return n;
}

static struct jvst_cnode *cnode_new_switch(int allvalid)
{
  size_t i,n;
  enum JVST_CNODE_TYPE type;
  struct jvst_cnode *node, *v, *inv;

  node = jvst_cnode_alloc(JVST_CNODE_SWITCH);
  type = allvalid ? JVST_CNODE_VALID : JVST_CNODE_INVALID;

  for(i=0, n=ARRAYLEN(node->u.sw); i < n; i++) {
    node->u.sw[i] = jvst_cnode_alloc(type);
  }

  // ARRAY_END and OBJECT_END are always invalid
  if (allvalid) {
    node->u.sw[SJP_ARRAY_END] = jvst_cnode_alloc(JVST_CNODE_INVALID);
    node->u.sw[SJP_OBJECT_END] = jvst_cnode_alloc(JVST_CNODE_INVALID);
  }

  return node;
}

void jvst_cnode_free(struct jvst_cnode *n)
{
  // simple logic: add back to freelist
  memset(n, 0, sizeof *n);
  n->next = freelist;
  freelist = n;
}

void jvst_cnode_free_tree(struct jvst_cnode *root)
{
  struct jvst_cnode *node, *next;
  size_t i,n;

  for(node = root; node != NULL; node = next) {
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
        for (i=0,n=ARRAYLEN(node->u.sw); i < n; i++) {
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

      case JVST_CNODE_OBJ_REQUIRED:
        // XXX - finalize the string set?
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

struct sbuf {
  char *buf;
  size_t cap;
  size_t len;
  size_t np;
};

static int add_indent(struct sbuf *buf, int indent)
{
  int i;
  
  for (i=0; i < indent; i++) {
    if (buf->len >= buf->cap) {
      break;
    }
    buf->buf[buf->len++] = ' ';
  }

  buf->np += indent;

  return indent;
}

static void xsnprintf(struct sbuf *b, const char *fmt, ...)
{
  int ret;
  va_list args;
  char *p;
  size_t nb;

  assert(b->len <= b->cap);

  p = b->buf+b->len;
  nb = b->cap - b->len;

  va_start(args, fmt);
  ret = vsnprintf(p,nb,fmt,args);
  va_end(args);
  if (ret < 0) {
    // FIXME: handle this more gracefully!
    perror("ERROR dumping cnode to a buffer");
    abort();
  }

  if ((size_t)ret <= nb) {
    b->len += ret;
  } else {
    b->len = b->cap;
  }

  b->np += ret;
}



// returns number of bytes written
static void jvst_cnode_dump_inner(struct jvst_cnode *node, struct sbuf *buf, int indent)
{
  const char *op = NULL;

  if (node == NULL) {
    xsnprintf(buf, "<null>");
    return;
  }

  switch (node->type) {
    case JVST_CNODE_INVALID:
    case JVST_CNODE_VALID:
      xsnprintf(buf, (node->type == JVST_CNODE_VALID) ? "VALID" : "INVALID");
      return;

    case JVST_CNODE_SWITCH:
      {
        size_t i,n;

        xsnprintf(buf, "SWITCH(\n");
        n = ARRAYLEN(node->u.sw);
        for (i=0; i < n; i++) {
          add_indent(buf,indent+2);
          xsnprintf(buf,"%-10s : ", evt2name(i));
          jvst_cnode_dump_inner(node->u.sw[i], buf, indent+2);
          if (i < n-1) {
            xsnprintf(buf,",\n");
          } else {
            xsnprintf(buf,"\n");
            add_indent(buf,indent);
            xsnprintf(buf,")");
          }
        }
      }
      break;

    case JVST_CNODE_NUM_INTEGER:
      xsnprintf(buf,"IS_INTEGER");
      break;

    case JVST_CNODE_NUM_RANGE:
      xsnprintf(buf,"NUM_RANGE(");
      if (node->u.num_range.flags & JVST_CNODE_RANGE_EXCL_MIN) {
        xsnprintf(buf,"%g < ", node->u.num_range.min);
      } else if (node->u.num_range.flags & JVST_CNODE_RANGE_MIN) {
        xsnprintf(buf,"%g <= ", node->u.num_range.min);
      }

      xsnprintf(buf,"x");

      if (node->u.num_range.flags & JVST_CNODE_RANGE_EXCL_MAX) {
        xsnprintf(buf," < %g", node->u.num_range.max);
      } else if (node->u.num_range.flags & JVST_CNODE_RANGE_MAX) {
        xsnprintf(buf," <= %g", node->u.num_range.max);
      }

      xsnprintf(buf,")");
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

        xsnprintf(buf, "%s(\n", op);
        for(cond = node->u.ctrl; cond != NULL; cond = cond->next) {
          add_indent(buf,indent+2);
          jvst_cnode_dump_inner(cond, buf, indent+2);
          if (cond->next) {
            xsnprintf(buf,",\n");
          } else {
            xsnprintf(buf,"\n");
            add_indent(buf,indent);
            xsnprintf(buf,")");
          }
        }
      }
      break;

    case JVST_CNODE_OBJ_PROP_SET:
      {
        struct jvst_cnode *prop;

        xsnprintf(buf,"PROP_SET(\n");
        for(prop=node->u.prop_set; prop != NULL; prop = prop->next) {
          add_indent(buf, indent+2);
          jvst_cnode_dump_inner(prop, buf, indent+2);
          if (prop->next) {
            xsnprintf(buf,",\n");
          } else {
            xsnprintf(buf,"\n");
            add_indent(buf,indent);
            xsnprintf(buf,")");
          }
        }
      }
      break;

    case JVST_CNODE_OBJ_PROP_MATCH:
      {
        char match[256] = { 0 };
        if (node->u.prop_match.match.str.len >= sizeof match) {
          memcpy(match, node->u.prop_match.match.str.s, sizeof match - 4);
          match[sizeof match - 4] = '.';
          match[sizeof match - 3] = '.';
          match[sizeof match - 2] = '.';
        } else {
          memcpy(match, node->u.prop_match.match.str.s, node->u.prop_match.match.str.len);
        }

        xsnprintf(buf,"PROP_MATCH(\n");
        add_indent(buf, indent+2);
        {
          char *prefix = "";
          char delim = '/';
          switch (node->u.prop_match.match.dialect) {
            case RE_LIKE:
              prefix="L";
              break;
            case RE_LITERAL:
              delim = '"';
              break;

            case RE_GLOB:
              prefix="G";
              break;
            case RE_NATIVE:
              break;
            default:
              prefix="???";
              break;
          }
          xsnprintf(buf,"%s%c%s%c,\n", prefix,delim,match,delim);
          add_indent(buf, indent+2);
          jvst_cnode_dump_inner(node->u.prop_match.constraint, buf, indent+2);
          xsnprintf(buf,"\n");
          add_indent(buf,indent);
          xsnprintf(buf,")");
        }
      }
      break;

    case JVST_CNODE_COUNT_RANGE:
      xsnprintf(buf,"COUNT_RANGE(");
      if (node->u.counts.min > 0) {
        xsnprintf(buf,"%zu <= ", node->u.counts.min);
      }

      xsnprintf(buf,"x");

      if (node->u.counts.max > 0) {
        xsnprintf(buf,"<= %zu", node->u.counts.min);
      }

      xsnprintf(buf,")");
      break;

    case JVST_CNODE_OBJ_REQUIRED:
      {
        struct ast_string_set *ss;

        xsnprintf(buf,"REQUIRED(\n");
        for (ss = node->u.required; ss != NULL; ss = ss->next) {
          char str[256] = { 0 };
          size_t n;

          n = ss->str.len;
          if (n < sizeof str) {
            memcpy(str, ss->str.s, n);
          } else {
            memcpy(str, ss->str.s, sizeof str - 4);
            memcpy(str + sizeof str - 4, "...", 4);
          }

          add_indent(buf, indent+2);
          xsnprintf(buf,"\"%s\"%s\n", str, (ss->next != NULL) ? "," : "");
        }
        add_indent(buf, indent);
        xsnprintf(buf,")");
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

int jvst_cnode_dump(struct jvst_cnode *node, char *buf, size_t nb);

void jvst_cnode_print(struct jvst_cnode *node)
{
  // FIXME: gross hack
  char buf[65536] = { 0 };  // 64K

  jvst_cnode_dump(node, buf, sizeof buf);
  fprintf(stderr, "%s\n", buf);
}

int jvst_cnode_dump(struct jvst_cnode *node, char *buf, size_t nb)
{
  struct sbuf b = {
    .buf = buf,
    .cap = nb,
    .len = 0,
    .np = 0,
  };

  jvst_cnode_dump_inner(node, &b, 0);
  return (b.len < b.cap) ? 0 : -1;
}

// Translates the AST into a contraint tree and optimizes the constraint
// tree
struct jvst_cnode *jvst_cnode_from_ast(struct ast_schema *ast);

// Just do a raw translation without doing any optimization of the
// constraint tree
struct jvst_cnode *jvst_cnode_translate_ast(struct ast_schema *ast)
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

    node = cnode_new_switch(false);
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
      node->u.sw[SJP_TRUE] = valid;
      node->u.sw[SJP_FALSE] = valid;
    }

    if (types & JSON_VALUE_NULL) {
      node->u.sw[SJP_NULL] = valid;
    }
  }

  if (ast->kws & (KWS_MINIMUM|KWS_MAXIMUM)) {
    enum JVST_CNODE_RANGEFLAGS flags = 0;
    double min = 0, max = 0;
    struct jvst_cnode *range, *jxn;

    if (ast->kws & KWS_MINIMUM) {
      flags |= (ast->exclusive_minimum ? JVST_CNODE_RANGE_EXCL_MIN : JVST_CNODE_RANGE_MIN);
      min = ast->minimum;
    }

    if (ast->kws & KWS_MAXIMUM) {
      flags |= (ast->exclusive_maximum ? JVST_CNODE_RANGE_EXCL_MAX : JVST_CNODE_RANGE_MAX);
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

    top_jxn = prop_set = phead = NULL;
    plist = &phead;

    for(pset = ast->properties.set; pset != NULL; pset = pset->next) {
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

    top_jxn = jvst_cnode_alloc(JVST_CNODE_AND);
    top_jxn->u.ctrl = prop_set;
    prop_set->next = node->u.sw[SJP_OBJECT_BEG];

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

  if (ast->some_of.set != NULL) {
    struct jvst_cnode *top_jxn, *some_jxn, **conds;
    struct ast_schema_set *sset;
    enum JVST_CNODE_TYPE op = JVST_CNODE_OR;

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

static struct jvst_cnode *cnode_deep_copy(struct jvst_cnode *node)
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
        for (ctrl=node->u.ctrl; ctrl != NULL; ctrl = ctrl->next) {
          *cp = cnode_deep_copy(ctrl);
          cp = &(*cp)->next;
        }
        return tree;
      }

    case JVST_CNODE_SWITCH:
      {
        size_t i,n;
        tree = jvst_cnode_alloc(node->type);
        for (i=0,n=ARRAYLEN(node->u.sw); i < n; i++) {
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
        for (prop=node->u.prop_set; prop != NULL; prop = prop->next) {
          *pp = cnode_deep_copy(prop);
          pp = &(*pp)->next;
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
        for (item=node->u.arr_item; item != NULL; item = item->next) {
          *ip = cnode_deep_copy(item);
          ip = &(*ip)->next;
        }
        return tree;
      }

    case JVST_CNODE_ARR_ADDITIONAL:
      tree = jvst_cnode_alloc(node->type);
      tree->u.arr_item = cnode_deep_copy(node->u.arr_item);
      return tree;

    default:
      SHOULD_NOT_REACH();
  }

  // now free the node
  jvst_cnode_free(node);
}

struct jvst_cnode *cnode_list_end(struct jvst_cnode *node)
{
  assert(node != NULL);
  while (node->next != NULL) {
    node = node->next;
  }
  return node;
}

struct jvst_cnode *cnode_list_prepend(struct jvst_cnode **headp, struct jvst_cnode *node)
{
  assert(headp != NULL);
  node->next = *headp;
  *headp = node;
  return node;
}

struct jvst_cnode *cnode_list_concat(struct jvst_cnode **headp, struct jvst_cnode *tail)
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

static struct jvst_cnode *cnode_find_type(struct jvst_cnode *node, enum JVST_CNODE_TYPE type)
{
  for(; node != NULL; node = node->next) {
    if (node->type == type) {
      return node;
    }
  }

  return NULL;
}

static struct jvst_cnode *cnode_optimize_andor_switches(struct jvst_cnode *top)
{
  // check if all nodes are SWITCH nodes.  If they are, combine
  // the switch clauses and simplify

  struct jvst_cnode *node, **pp, *sw;
  size_t i,n;

  for(node=top->u.ctrl; node != NULL; node = node->next) {
    if (node->type != JVST_CNODE_SWITCH) {
      return top;
    }
  }

  // all nodes are switch nodes...
  sw = jvst_cnode_alloc(JVST_CNODE_SWITCH);
  for (i=0, n=ARRAYLEN(sw->u.sw); i < n; i++) {
    struct jvst_cnode *jxn, **cpp;

    jxn = jvst_cnode_alloc(top->type);
    cpp = &jxn->u.ctrl;

    for(node=top->u.ctrl; node != NULL; node = node->next) {
      assert(node->type == JVST_CNODE_SWITCH);

      *cpp = node->u.sw[i];
      assert( (*cpp)->next == NULL );
      cpp = &(*cpp)->next;
    }

    sw->u.sw[i] = jvst_cnode_optimize(jxn);
  }

  return sw;
}

static struct jvst_cnode *cnode_optimize_andor(struct jvst_cnode *top)
{
  struct jvst_cnode *node, *next, **pp;
  pp = &top->u.ctrl;

  // first optimize child nodes...
  for(node=top->u.ctrl; node != NULL; node = next) {
    next = node->next;
    *pp = jvst_cnode_optimize(node);
    pp = &(*pp)->next;
  }

  // pass 1: remove VALID/INVALID nodes
  switch (top->type) {
    case JVST_CNODE_AND:
      for(pp = &top->u.ctrl; *pp != NULL;) {
        switch ((*pp)->type) {
          case JVST_CNODE_INVALID:
            // whole AND becomes invalid
            (*pp)->next = NULL;
            return *pp;

          case JVST_CNODE_VALID:
            // can eliminate VALID from AND
            *pp = (*pp)->next;
            continue;

          default:
            break;
        }

        pp = &(*pp)->next;
      }

      // all nodes were valid
      if (top->u.ctrl == NULL) {
        return jvst_cnode_alloc(JVST_CNODE_VALID);
      }
      break;

    case JVST_CNODE_OR:
      for(pp = &top->u.ctrl; *pp != NULL;) {
        switch ((*pp)->type) {
          case JVST_CNODE_VALID:
            // whole OR becomes valid
            (*pp)->next = NULL;
            return *pp;

          case JVST_CNODE_INVALID:
            // can eliminate INVALID from OR
            *pp = (*pp)->next;
            continue;

          default:
            break;
        }

        pp = &(*pp)->next;
      }

      // all nodes were invalid
      if (top->u.ctrl == NULL) {
        return jvst_cnode_alloc(JVST_CNODE_INVALID);
      }
      break;

    default:
      SHOULD_NOT_REACH();
  }

  assert(top->u.ctrl != NULL);
  if (top->u.ctrl->next == NULL) {
    // only one child
    return top->u.ctrl;
  }

  // pass 2: combine subnodes of the same type (ie: AND will combine
  // with AND and OR will combine with OR)
  for(pp = &top->u.ctrl; *pp != NULL; pp = &(*pp)->next) {
    struct jvst_cnode *head, *tail;

    if ((*pp)->type != top->type) {
      continue;
    }

    // save next link
    next = (*pp)->next;
    *pp = (*pp)->u.ctrl;

    // fast path...
    if (next == NULL) {
      continue;
    }

    while (*pp != NULL) {
      pp = &(*pp)->next;
    }

    *pp = next;
  }

  return cnode_optimize_andor_switches(top);
}

struct jvst_cnode *jvst_cnode_optimize(struct jvst_cnode *tree)
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
      return cnode_optimize_andor(tree);

    case JVST_CNODE_XOR:
      // TODO: basic optimization for XOR
      return tree;

    case JVST_CNODE_NOT:
      // TODO: basic optimizations for NOT
      return tree;

    case JVST_CNODE_SWITCH:
      {
        size_t i,n;
        for(i=0, n=ARRAYLEN(tree->u.sw); i < n; i++) {
          tree->u.sw[i] = jvst_cnode_optimize(tree->u.sw[i]);
        }
      }
      return tree;

    case JVST_CNODE_OBJ_PROP_SET:
    case JVST_CNODE_NUM_RANGE:
    case JVST_CNODE_COUNT_RANGE:
    case JVST_CNODE_STR_MATCH:
    case JVST_CNODE_OBJ_PROP_MATCH:
    case JVST_CNODE_OBJ_REQUIRED:
    case JVST_CNODE_ARR_ITEM:
    case JVST_CNODE_ARR_ADDITIONAL:
      // TODO: basic optimization for these nodes
      return tree;

    default:
      SHOULD_NOT_REACH();
  }
}




