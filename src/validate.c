#include "validate.h"

#include <stdio.h>
#include <string.h>

#include <assert.h>

#include "sjp_parser.h"
#include "sjp_testing.h"
#include "ast.h"

#define JVST_VALIDATE_DEBUG 1

#if JVST_VALIDATE_DEBUG
#  define SHOULD_NOT_REACH(v) do{ \
     fprintf(stderr, "\nSHOULD_NOT_REACH() at %s:%d\n", __FILE__, __LINE__); \
     abort(); \
   } while(0)
#else
#  define SHOULD_NOT_REACH(v) return invalid(v);
#endif

#define NCOUNTERS 2

enum JVST_STATE {
  JVST_ST_ERR = -1,

  JVST_ST_VALUE = 0,
  JVST_ST_OBJECT,
  
  JVST_ST_FETCH_PROP,
  JVST_ST_CHECKOBJ,
  JVST_ST_CHECKOBJ1,

  // consumes until the current value is finished
  JVST_ST_EAT_VALUE,
  JVST_ST_EAT_OBJECT,
  JVST_ST_EAT_ARRAY,

  // Used when consuming: valid if no error while consuming
  JVST_ST_VALID,
};

static const char *vst2name(int st)
{
  switch (st) {
    case JVST_ST_ERR:        return "ST_ERR";
    case JVST_ST_VALUE:      return "ST_VALUE";
    case JVST_ST_OBJECT:     return "ST_OBJECT";
    case JVST_ST_FETCH_PROP: return "ST_FETCH_PROP";
    case JVST_ST_EAT_VALUE:  return "ST_EAT_VALUE";
    case JVST_ST_EAT_OBJECT: return "ST_EAT_OBJECT";
    case JVST_ST_EAT_ARRAY:  return "ST_EAT_ARRAY";
    case JVST_ST_VALID:      return "ST_VALID";
    default:                 return "UNKNOWN";
  }
}

static const struct ast_schema empty_schema = {0};

struct jvst_state {
  const struct ast_schema *schema;
  size_t nitems;
  size_t counters[NCOUNTERS];
  enum JVST_STATE state;
};

static void dump_stack(struct jvst_validator *v)
{
  size_t i,n;
  n = v->stop;
  if (n > v->smax) { n = v->smax; }
  fprintf(stderr, "\ntop: %zu, max: %zu\n", v->stop,v->smax);
  for (i=0; i < n; i++) {
    struct jvst_state *sp = &v->sstack[i];

    fprintf(stderr, "[%zu] %-16s %8p %zu %zu %zu\n",
        i, vst2name(sp->state), (void *)sp->schema,
        sp->nitems, sp->counters[0], sp->counters[1]);
  }
  fprintf(stderr, "---\n");
}

static void copycounters(struct jvst_state *dst, const struct jvst_state *src)
{
  size_t i,n;
  dst->nitems = src->nitems;
  n = sizeof dst->counters / sizeof dst->counters[0];
  for (i=0; i < n; i++) {
    dst->counters[i] = src->counters[i];
  }
}

static void zerocounters(struct jvst_state *sp)
{
  size_t i,n;
  sp->nitems = 0;
  n = sizeof sp->counters / sizeof sp->counters[0];
  for (i=0; i < n; i++) {
    sp->counters[i] = 0;
  }
}

void jvst_validate_init_defaults(struct jvst_validator *v, const struct ast_schema *schema)
{
  struct jvst_state zero = { 0 };
  v->schema = schema;

  v->smax = JVST_DEFAULT_STACK_SIZE;
  v->sstack = malloc(v->smax * sizeof *v->sstack);

  v->sstack[0] = zero;
  v->sstack[0].state  = JVST_ST_VALUE;
  v->sstack[0].schema = v->schema;
  v->stop = 1;

  (void)sjp_parser_init(&v->p,
      &v->pstack[0], sizeof v->pstack / sizeof v->pstack[0], 
      &v->pbuf[0], sizeof v->pbuf / sizeof v->pbuf[0]);
}

static int check_type(struct jvst_validator *v, int types, struct sjp_event *ev)
{
  int mask;

  (void)v; // may be unused

  if (types == 0) {
    return JVST_VALID;
  }

  switch (ev->type) {
    case SJP_NONE:
    default:
      SHOULD_NOT_REACH(v);

    case SJP_NULL:
      mask = JSON_VALUE_NULL;
      break;
    case SJP_TRUE:
    case SJP_FALSE:
      mask = JSON_VALUE_BOOL;
      break;

    case SJP_STRING:
      mask = JSON_VALUE_STRING;
      break;

    case SJP_NUMBER:
      // FIXME: handle "integer" constraint correctly
      mask = JSON_VALUE_NUMBER | JSON_VALUE_INTEGER;
      break;

    case SJP_OBJECT_BEG:
      mask = JSON_VALUE_OBJECT;
      break;

    case SJP_ARRAY_BEG:
      mask = JSON_VALUE_ARRAY;
      break;

    case SJP_OBJECT_END:
    case SJP_ARRAY_END:
      return JVST_VALID;
  }

  return (mask & types) ? JVST_VALID : JVST_INVALID;
}

static inline struct jvst_state *getstate(struct jvst_validator *v)
{
  if (v->stop == 0 || v->stop > v->smax) {
    return NULL;
  }

  return &v->sstack[v->stop-1];
}

static inline struct jvst_state *pushstate(struct jvst_validator *v, int st,
    const struct ast_schema *schema)
{
  struct jvst_state *sp;

  if (v->stop >= v->smax) {
    return NULL;
  }

  sp = &v->sstack[v->stop];
  sp->state = st;
  zerocounters(sp);
  if (v->stop > 0 && schema == NULL) {
    sp->schema = v->sstack[v->stop-1].schema;
  } else {
    sp->schema = schema;
  }

  v->stop++;

  return sp;
}

static inline struct jvst_state *newframe(struct jvst_validator *v)
{
  return pushstate(v, JVST_ST_VALUE, NULL);
}

static inline struct jvst_state *returnframe(struct jvst_validator *v)
{
  if (v->stop >= v->smax) {
    return NULL;
  }

  return &v->sstack[v->stop];
}

static inline struct jvst_state *popstate(struct jvst_validator *v)
{
  if (v->stop == 0 || v->stop > v->smax) {
    return NULL;
  }

  return &v->sstack[--v->stop];
}

static int invalid(struct jvst_validator *v)
{
  if (v->stop < v->smax) {
    v->sstack[v->stop].state  = JVST_ST_ERR;
    v->sstack[v->stop].schema = NULL;
  }

  v->stop++; // always increment if v->stop == v->smax to mark as invalid
  return JVST_INVALID;
}

// Finishes consuming a string or number value.  sjp_parser_next should
// have returned SJP_MORE or SJP_PARTIAL.
//
// Caller must push a stack frame on entry.  Initializes the frame if ev
// != NULL.  Pops the top stack frame on exit but leaves the nitems
// count set to allow the caller to retrieve the count.
//
// Only call with ev != NULL the first time.
//
// Returns JVST_MORE if more input is required, JVST_OK if the value
// has been consumed, and JVST_INVALID if an error occurs in
// lexing/parsing the value
//
// For strings, the count returned is the number of bytes (XXX - count
// utf8 characters) and returns them in the nitems field of the top
// stack frame.
//
// For numbers, counts the number of bytes and returns them in the
// nitems field of the top stack frame.
static int eat_value(struct jvst_validator *v, struct sjp_event *ev)
{
  struct jvst_state *sp;
  struct sjp_event evt;
  int ret;

  sp = getstate(v);
  if (ev != NULL) {
    sp->state = JVST_ST_EAT_VALUE;
    sp->nitems = ev->n;
    sp->counters[0] = sp->counters[1] = 0;
  }

  if (sp == NULL) {
    // XXX - this is an internal error and should be reported as such
    return invalid(v);
  }

restart:
  if (ret = sjp_parser_next(&v->p, &evt), SJP_ERROR(ret)) {
    return invalid(v);
  }

  sp->nitems += evt.n;
  switch (ret) {
    case SJP_OK:
      return (popstate(v) != NULL) ? JVST_VALID : JVST_INVALID;

    case SJP_PARTIAL:
      goto restart;

    case SJP_MORE:
      return JVST_MORE;

    default:
      SHOULD_NOT_REACH(v);
  }
}

// Eats an array: consumes all tokens until the array ends.  Call should
// be made after sjp_parser_next returns SJP_ARRAY_BEG or after a whole
// value (not a partial value) has been consumed.
//
// Caller must push a stack frame on entry.  Pops the top stack frame on
// exit, leaving the nitems count set in the return stack frame.
//
// Counts the number of values encountered in the array and returns them
// in the nitems field of the return stack frame.
static int eat_array(struct jvst_validator *v)
{
  struct jvst_state *sp;
  struct sjp_event evt;
  int ret;

  if (sp = getstate(v), sp == NULL) {
    return JVST_INVALID;
  }

  if (sp->state != JVST_ST_EAT_ARRAY) {
    sp->state = JVST_ST_EAT_ARRAY;
    zerocounters(sp);
  }

  for(;;) {
    ret = sjp_parser_next(&v->p, &evt);
    switch (ret) {
      case SJP_MORE:
        return JVST_MORE;

      case SJP_PARTIAL:
        continue;

      case SJP_OK:
        /* nop */
        break;

      default:
        // should be an error
        if (!SJP_ERROR(ret)) {
          SHOULD_NOT_REACH();
        }
        return JVST_INVALID;
    }

    // SJP_OK -- completed token available

    // If we just read an item and we're not in a nested
    // array/object, increment the item count
    if (sp->counters[0] == 0 &&
        sp->counters[1] == 0 &&
        sjp_parser_state(&v->p) == SJP_PARSER_ARR_ITEM) {
      sp->nitems++;
    }

    switch (evt.type) {
      case SJP_OBJECT_BEG:
        sp->counters[0]++;
        break;

      case SJP_OBJECT_END:
        sp->counters[0]--;
        break;

      case SJP_ARRAY_BEG:
        sp->counters[1]++;
        break;

      case SJP_ARRAY_END:
        if (sp->counters[1] == 0) {
          return (popstate(v) != NULL) ? JVST_VALID : JVST_INVALID;
        }
        sp->counters[1]--;
        break;

      default:
        /* nop */
        break;
    }
  }

  SHOULD_NOT_REACH(v);
}

// Eats an object: consumes all tokens until the object ends.  Call should
// be made after sjp_parser_next returns SJP_OBJECTBEG or after a whole
// key-value pair has been consumed.
//
// Caller must push a stack frame on entry.  Pops the top stack frame on
// exit, leaving the nitems count set in the return stack frame.
//
// Counts the number of values encountered in the array and returns them
// in the nitems field of the return stack frame.
static int eat_object(struct jvst_validator *v)
{
  struct jvst_state *sp;
  struct sjp_event evt;
  int ret;

  if (sp = getstate(v), sp == NULL) {
    return JVST_INVALID;
  }

  if (sp->state != JVST_ST_EAT_OBJECT) {
    sp->state = JVST_ST_EAT_OBJECT;
    zerocounters(sp);
  }

  for(;;) {
    ret = sjp_parser_next(&v->p, &evt);
    switch (ret) {
      case SJP_MORE:
        return JVST_MORE;

      case SJP_PARTIAL:
        continue;

      case SJP_OK:
        /* nop */
        break;

      default:
        // should be an error
        if (!SJP_ERROR(ret)) {
          SHOULD_NOT_REACH();
        }
        return JVST_INVALID;
    }

    // SJP_OK -- completed token available

    switch (evt.type) {
      case SJP_OBJECT_BEG:
        sp->counters[0]++;
        break;

      case SJP_OBJECT_END:
        if (sp->counters[0] == 0) {
          return (popstate(v) != NULL) ? JVST_VALID : JVST_INVALID;
        }
        sp->counters[0]--;

      case SJP_ARRAY_BEG:
        sp->counters[1]++;
        break;

      case SJP_ARRAY_END:
        sp->counters[1]--;
        break;

      case SJP_STRING:
        // If we just read a key and we're not in a nested object,
        // increment the number of kv pairs
        if (sp->counters[0] == 0 &&
            sp->counters[1] == 0 &&
            sjp_parser_state(&v->p) == SJP_PARSER_OBJ_KEY) {
          sp->nitems++;
        }

      default:
        /* nop */
        break;
    }
  }

  SHOULD_NOT_REACH(v);
}

static int validate_object(struct jvst_validator *v);

static int validate_value(struct jvst_validator *v)
{
  int ret;
  struct sjp_event evt = {0};
  struct jvst_state *sp;

  ret = sjp_parser_next(&v->p, &evt);

  fprintf(stderr, "[%8s] %s\n", ret2name(ret), evt2name(evt.type));
  if (SJP_ERROR(ret)) {
    return invalid(v);
  }

  if (evt.type == SJP_NONE && ret != SJP_OK) {
    // XXX - double check when a SJP_NONE event should correspond to
    // SJP_OK
    return (ret != SJP_OK) ? JVST_MORE : JVST_INVALID;
  }

  if (sp = getstate(v), sp == NULL) {
    return JVST_INVALID;
  }

  assert(sp->schema != NULL);
  if (check_type(v, sp->schema->types, &evt) == JVST_INVALID) {
    return invalid(v);
  }

  switch (evt.type) {
    case SJP_NONE:
    default:
      SHOULD_NOT_REACH(v);

    case SJP_NULL:
    case SJP_TRUE:
    case SJP_FALSE:
      // XXX - validate the values
      break;

    case SJP_STRING:
    case SJP_NUMBER:
      // XXX - validate the values
      if (ret != SJP_OK) {
        getstate(v)->state = JVST_ST_VALID;
        if (newframe(v) == NULL) {
          return JVST_INVALID;
        }
        return eat_value(v, &evt);
      }
      break;

    case SJP_ARRAY_BEG:
      // XXX - validate the array
      getstate(v)->state = JVST_ST_VALID;
      if (newframe(v) == NULL) {
        return JVST_INVALID;
      }
      return eat_array(v);

    case SJP_OBJECT_BEG:
      return validate_object(v);

    case SJP_OBJECT_END:
    case SJP_ARRAY_END:
      SHOULD_NOT_REACH(v);
  }

  popstate(v);
  return JVST_VALID;
}

enum OBJ_VALIDATION {
  OBJ_PROPERTIES   = 1<<0,

  // constraints that don't require checking individual properties
  OBJ_MINMAX_PROPERTIES = 1<<8,
};

#define CHECK_PROP_MASK 0xff

static const struct ast_schema *match_property(
    struct ast_property_schema *set,
    const char *k,
    size_t n)
{
  for (; set != NULL; set = set->next) {
    const char *sk;
    size_t nsk;
    sk = set->pattern.str.s;
    nsk = set->pattern.str.len;

    if (nsk != n) {
      continue;
    }

    if (memcmp(sk,k,n) != 0) {
      continue;
    }

    return set->schema;
  }

  return NULL;
}

static int validate_object(struct jvst_validator *v)
{
  struct jvst_state *sp;
  const struct ast_schema *schema, *pschema;
  struct sjp_event evt;
  int ret, venum;
  const char *key;
  size_t nkey;

  if (sp = getstate(v), sp == NULL) {
    return JVST_INVALID;
  }

  schema = sp->schema;
  assert(schema != NULL);

  // see what we need to validate...
  venum = 0;
  if (schema->properties.set != NULL) {
    venum |= OBJ_PROPERTIES;
  }

  if (schema->kws & KWS_MINMAX_PROPERTIES) {
    venum |= OBJ_MINMAX_PROPERTIES;
  }

  switch (sp->state) {
    case JVST_ST_OBJECT:
      goto new_prop;

    case JVST_ST_FETCH_PROP:
      goto fetch_prop;

    case JVST_ST_CHECKOBJ1:
      // retrieve eat_object counters from returnframe
      {
        struct jvst_state *rf;
        if (rf  = returnframe(v), rf == NULL) {
          SHOULD_NOT_REACH(v);
        }
        copycounters(sp, rf);
      }
      sp->state = JVST_ST_CHECKOBJ; // necessary?
      /* fallthrough */

    case JVST_ST_CHECKOBJ:
      goto check_obj;

    default:
      /* fast path if we don't have to validate per-property */
      if ((venum & CHECK_PROP_MASK) == 0) {
        getstate(v)->state = (venum == 0) ? JVST_ST_VALID : JVST_ST_CHECKOBJ1;
        if (newframe(v) == NULL) {
          return JVST_INVALID;
        }
        return eat_object(v);
      }

      sp->state = JVST_ST_OBJECT;
      zerocounters(sp);
  }

  // FIXME: currently we limit keys to fit into the kbuf buffer.  This
  // is a limitation of the current dumb approach and hopefully
  // switching to DFA matching we can avoid this
  //
  // FIXME: need to write the sjp_parser buffering code
new_prop:
  sp->state = JVST_ST_FETCH_PROP;
  memset(v->kbuf,0,sizeof v->kbuf);
  sp->counters[0] = 0;

fetch_prop:
  ret = sjp_parser_next(&v->p, &evt);
  switch (ret) {
    case SJP_MORE:
      return JVST_MORE;

    case SJP_PARTIAL:
      if (sp->counters[0] + evt.n > sizeof v->kbuf) {
        // FIXME: need better errors!
        return JVST_INVALID;
      }
      memcpy(&v->kbuf[sp->counters[0]], evt.text, evt.n);
      sp->counters[0] += evt.n;
      goto fetch_prop;

    case SJP_OK:
      if (evt.type == SJP_OBJECT_END) {
        goto check_obj;
      }

      if (sp->counters[0] == 0) {
        key = evt.text;
        nkey = evt.n;
      } else {
        if (sp->counters[0] + evt.n > sizeof v->kbuf) {
          // FIXME: need better errors!
          return JVST_INVALID;
        }

        memcpy(&v->kbuf[sp->counters[0]], evt.text, evt.n);
        sp->counters[0] += evt.n;

        key = v->kbuf;
        nkey = sp->counters[0];
      }
      break;

    default:
      // should be an error
      if (!SJP_ERROR(ret)) {
        SHOULD_NOT_REACH();
      }
      return JVST_INVALID;
  }

  // record items
  sp->nitems++;

  // check property
  pschema = NULL;
  if (schema->properties.set != NULL) {
    pschema = match_property(schema->properties.set, key, nkey);
  }

  if (pschema == NULL) {
    // value is okay...
    pschema = &empty_schema;
  }

  // validate value against schema
  sp->state = JVST_ST_OBJECT;
  if (pushstate(v, JVST_ST_VALUE, pschema) == NULL) {
    // FIXME: better errors!
    return JVST_INVALID;
  }

  return JVST_VALID;

check_obj:
  /* checks like 'required' are not yet implemented */
  if (venum & OBJ_MINMAX_PROPERTIES) {
    if (sp->nitems < schema->min_properties) {
      // XXX - give reason why
      return JVST_INVALID;
    }

    if (schema->max_properties > 0 && sp->nitems > schema->max_properties) {
      // XXX - give reason why
      return JVST_INVALID;
    }
  }

  popstate(v);
  return JVST_VALID;
}

int jvst_validate_more(struct jvst_validator *v, char *data, size_t n)
{
  struct jvst_state *top;

  sjp_parser_more(&v->p, data, n);

  for (;;) {
    int ret;

    dump_stack(v);

    if (top = getstate(v), top == NULL) {
      return JVST_INVALID;
    }

    fprintf(stderr, "--> %zu [%s] schema = %p  nitems = %zu  counters=[%zu %zu]\n",
        v->stop,
        vst2name(top->state),
        (void *)top->schema,
        top->nitems,
        top->counters[0],
        top->counters[1]);

    switch (top->state) {
      case JVST_ST_ERR:
        return invalid(v);

      case JVST_ST_VALUE:
        ret = validate_value(v);
        break;

      case JVST_ST_OBJECT:
      case JVST_ST_FETCH_PROP:
      case JVST_ST_CHECKOBJ:
      case JVST_ST_CHECKOBJ1:
        ret = validate_object(v);
        break;

      case JVST_ST_EAT_VALUE:
        ret = eat_value(v, NULL);
        break;

      case JVST_ST_EAT_OBJECT:
        ret = eat_object(v);
        break;

      case JVST_ST_EAT_ARRAY:
        ret = eat_array(v);
        break;

      case JVST_ST_VALID:
        popstate(v);
        ret = JVST_VALID;
        break;

      default:
        SHOULD_NOT_REACH(v);
    }

    if (JVST_IS_INVALID(ret) || ret == JVST_MORE || v->stop < 1) {
      return ret;
    }
  }
}

int jvst_validate_close(struct jvst_validator *v)
{
  int ret, st;
  struct jvst_state *top;
  char buf[2] = " ";

  if (v->stop > 0) {
    // FIXME: this is a dumb hack to deal with numbers The problem is
    // this: if the number is adjacent to the end of the stream, the lexer
    // won't know this until it's closed.  So it returns a SJP_MORE value.
    // This is fine, but we don't deal with it very well.  So, append
    // a trailing space and try to let the validation clean up.  Then
    // close everything...
    //
    if (ret = jvst_validate_more(v, buf, 1), JVST_IS_INVALID(ret)) {
      return ret;
    }
  }

  st = (v->stop > 0) ? JVST_INVALID : JVST_VALID;

  ret = sjp_parser_close(&v->p);
  free(v->sstack);
  v->sstack = NULL;
  v->stop = v->smax = 0;

  if (SJP_ERROR(ret) || st == JVST_ST_ERR) {
    return JVST_INVALID;
  }
  return JVST_VALID;
}

