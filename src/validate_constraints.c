#include "validate_constraints.h"

#include <assert.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#include "xalloc.h"

#include "jvst_macros.h"
#include "sjp_testing.h"

#define SHOULD_NOT_REACH() abort()

enum { JVST_CNODE_CHUNKSIZE = 1024 };

struct jvst_cnode_pool {
  struct jvst_cnode_pool *next;
  struct jvst_cnode items[JVST_CNODE_CHUNKSIZE];
};

/* XXX - should these be global vars?  also, not thread safe. */
static struct jvst_cnode_pool *pool = NULL;
static size_t pool_item = 0;
static struct jvst_cnode *freelist = NULL;

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
  struct jvst_cnode *node, *v, *inv;

  node = jvst_cnode_alloc(JVST_CNODE_SWITCH);
  v = inv = jvst_cnode_alloc(JVST_CNODE_INVALID);
  if (allvalid) {
    v = jvst_cnode_alloc(JVST_CNODE_VALID);
  }

  for(i=0, n=ARRAYLEN(node->u.sw); i < n; i++) {
    node->u.sw[i] = v;
  }

  // ARRAY_END and OBJECT_END are always invalid
  if (allvalid) {
    node->u.sw[SJP_ARRAY_END] = inv;
    node->u.sw[SJP_OBJECT_END] = inv;
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
        xsnprintf(buf,"< %g", node->u.num_range.min);
      } else if (node->u.num_range.flags & JVST_CNODE_RANGE_MAX) {
        xsnprintf(buf,"<= %g", node->u.num_range.min);
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
    struct jvst_cnode **plist, *phead, *prop_jxn, *top_jxn;
    struct ast_property_schema *pset;

    top_jxn = prop_jxn = phead = NULL;
    plist = &phead;

    for(pset = ast->properties.set; pset != NULL; pset = pset->next) {
      struct jvst_cnode *pnode;
      pnode = jvst_cnode_alloc(JVST_CNODE_OBJ_PROP_MATCH);
      pnode->u.prop_match.match = pset->pattern;
      pnode->u.prop_match.constraint = jvst_cnode_translate_ast(pset->schema);
      *plist = pnode;
      plist = &pnode->next;
    }

    prop_jxn = jvst_cnode_alloc(JVST_CNODE_OR);
    prop_jxn->u.ctrl = phead;
    assert(phead != NULL);

    top_jxn = jvst_cnode_alloc(JVST_CNODE_AND);
    top_jxn->u.ctrl = prop_jxn;
    prop_jxn->next = node->u.sw[SJP_OBJECT_BEG];

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

