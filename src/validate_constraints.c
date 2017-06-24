#include "validate_constraints.h"

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
      case JVST_CNODE_ARR_UNIQUE:
      case JVST_CNODE_STR_LENRANGE:
      case JVST_CNODE_OBJ_NUMPROP_RANGE:
      case JVST_CNODE_ARR_NUMITEM_RANGE:
        break;

      case JVST_CNODE_STR_MATCH:
        json_string_finalize(&node->u.str_match.pattern);
        if (node->u.str_match.matcher) {
          // XXX - ensure that fsm is torn down
          // do we pool FSMs?  check if they're ref counted.
        }
        break;

      case JVST_CNODE_STR_EQUAL:
        json_string_finalize(&node->u.str_equal);
        break;

      case JVST_CNODE_OBJ_PROPS:
        for (i=0, n=node->u.props.n; i < n; i++) {
          struct jvst_cnode *child;

          json_string_finalize(&node->u.props.names[i]);
          child = &node->u.props.constraints[i];
          if (child != NULL) {
            jvst_cnode_free_tree(child);
          }
        }
        break;

      case JVST_CNODE_OBJ_PROP_MATCH:
        json_string_finalize(&node->u.prop_match.pattern);
        if (node->u.prop_match.matcher != NULL) {
          // XXX - ensure that fsm is torn down
          // do we pool FSMs?  check if they're ref counted.
        }

        if (node->u.prop_match.constraint != NULL) {
          jvst_cnode_free_tree(node->u.prop_match.constraint);
        }
        break;

      case JVST_CNODE_OBJ_REQUIRE:
        for (i=0, n=node->u.required.n; i < n; i++) {
          json_string_finalize(&node->u.required.s[i]);
        }
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

static inline size_t xsnprintf(char *p, size_t sz, const char *fmt, ...)
{
  int ret;
  va_list args;

  va_start(args, fmt);
  if (ret = vsnprintf(p,sz,fmt,args), ret < 0) {
    // FIXME: handle this more gracefully!
    perror("ERROR dumping cnode to a buffer");
    abort();
  }
  va_end(args);

  return (size_t)ret;
}

static int add_indent(char *buf, size_t nb, int indent)
{
  int i;
  
  for (i=0; i < indent && nb > 0; i++, nb--) {
    buf[i] = ' ';
  }

  return indent;
}

// returns number of bytes written
static size_t jvst_cnode_dump_inner(struct jvst_cnode *node, char *buf, size_t nb0, int indent)
{
  size_t nb,np;

  nb = nb0;

  if (node == NULL) {
    np = xsnprintf(buf, nb, "<null>");
    nb -= np;
    goto finished;
  }

  switch (node->type) {
    case JVST_CNODE_INVALID:
    case JVST_CNODE_VALID:
      np = xsnprintf(buf, nb, (node->type == JVST_CNODE_VALID) ? "VALID" : "INVALID");
      nb -= np;
      goto finished;

    case JVST_CNODE_SWITCH:
      {
        size_t i,n;

        if (np = xsnprintf(buf,nb, "SWITCH(\n"), np >= nb) {
          nb -= np;
          goto finished;
        }

        buf += np;
        nb -= np;

        n = ARRAYLEN(node->u.sw);
        for (i=0; i < n; i++) {
          if (np = add_indent(buf,nb,indent+2), np >= nb) {
            nb -= np;
            goto finished;
          }
          buf += np;
          nb -= np;

          if (np = snprintf(buf,nb,"%-10s:", evt2name(i)), np >= nb) {
            nb -= np;
            goto finished;
          }
          buf += np;
          nb -= np;

          if (np = jvst_cnode_dump_inner(node->u.sw[i], buf, nb, indent+2), np > nb) {
            nb -= np;
            goto finished;
          }
          buf += np;
          nb -= np;

          if (np = snprintf(buf,nb,"%c\n", (i < n-1) ? ',' : ')'), np >= nb)  {
            nb -= np;
            goto finished;
          }
          buf += np;
          nb -= np;
        }
      }
      break;

    case JVST_CNODE_AND:
    case JVST_CNODE_OR:
    case JVST_CNODE_XOR:
    case JVST_CNODE_NOT:

    case JVST_CNODE_STR_LENRANGE:
    case JVST_CNODE_STR_MATCH:
    case JVST_CNODE_STR_EQUAL:

    case JVST_CNODE_NUM_RANGE:
    case JVST_CNODE_NUM_INTEGER:

    case JVST_CNODE_OBJ_NUMPROP_RANGE:
    case JVST_CNODE_OBJ_PROPS:
    case JVST_CNODE_OBJ_PROP_MATCH:
    case JVST_CNODE_OBJ_REQUIRE:

    case JVST_CNODE_ARR_NUMITEM_RANGE:
    case JVST_CNODE_ARR_ITEM:
    case JVST_CNODE_ARR_ADDITIONAL:
    case JVST_CNODE_ARR_UNIQUE:
      fprintf(stderr, "**not implemented**\n");
      abort();
  }

finished:
  return nb0 - nb;
}

int jvst_cnode_dump(struct jvst_cnode *node, char *buf, size_t nb)
{
  if (jvst_cnode_dump_inner(node, buf, nb, 0) < nb) {
    return 0;
  }

  return -1;
}

// Translates the AST into a contraint tree and optimizes the constraint
// tree
struct jvst_cnode *jvst_cnode_from_ast(struct ast_schema *ast);

// Just do a raw translation without doing any optimization of the
// constraint tree
struct jvst_cnode *jvst_cnode_translate_ast(struct ast_schema *ast)
{
  struct jvst_cnode *node;

  // TODO - implement ast->some_of.set != NULL logic
  // top is a switch
  node = cnode_new_switch(true);

  (void)ast;

  return node;
}

