#include "validate.h"

#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <inttypes.h>
#include <limits.h>

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
#  define SHOULD_NOT_REACH(v) return INVALID(v, "internal error: SHOULD_NOT_REACH()");
#endif

#define NCOUNTERS 2

#define ARRAYLEN(x) (sizeof (x) / sizeof (x)[0])
#define STRINGIFY0(x) # x
#define STRINGIFY(x) STRINGIFY0(x)
#define SYMCAT0(x,y) x ## y
#define SYMCAT(x,y) SYMCAT0(x,y)
#define SYMCAT3(x,y,z) SYMCAT(SYMCAT(x,y),z)

#ifdef static_assert
#  define STATIC_ASSERT(x,name) static_assert((x),STRINGIFY(name))
#else
#  define STATIC_ASSERT(x,name) struct { char tmp[2*(x)-1]; } SYMCAT3(static_assert_, name, __LINE__)
#endif

#define INVALID(v, ...) invalid((v), __FILE__, __LINE__, __VA_ARGS__)

#define ERR_OVERFLOW() INVALID(v, "too much nesting: stack is exhausted")
#define ERR_UNDERFLOW() INVALID(v, "internal error: stack underflow")
#define ERR_JSON(r) INVALID(v, "error parsing json: %d", r)
#define ERR_ALREADY_ERR() INVALID(v, "validator already encountered an error")

enum JVST_STATE {
  JVST_ST_ERR = -1,

  JVST_ST_VALUE = 0,    // validate a value

  JVST_ST_OBJECT_INIT,  // validate object: initialize validation
  JVST_ST_OBJECT,       // validate object: next property
  JVST_ST_FETCH_PROP,   // validate object: continue fetching property
  JVST_ST_AFTER_VALUE,  // validate object: after previous value
  JVST_ST_CHECKOBJ,     // validate object: check object for consistency
  JVST_ST_CHECKOBJ1,    // validate object: fetch counters from last frame, check for consistency

  // consumes until the current value is finished
  JVST_ST_EAT_VALUE,    // eat a value
  JVST_ST_EAT_OBJECT,   // eat an object
  JVST_ST_EAT_ARRAY,    // eat an array

  JVST_ST_SOMEOF_INIT,  // initialize someof handling
  JVST_ST_SOMEOF_NEXT,  // next token for someof
  JVST_ST_SOMEOF_FINAL, // teardown someof handling

  JVST_ST_VALID,        // valid, consume current token
};

static const char *vst2name(int st)
{
  switch (st) {
    case JVST_ST_ERR:          return "ST_ERR";
    case JVST_ST_VALUE:        return "ST_VALUE";
    case JVST_ST_OBJECT:       return "ST_OBJECT";
    case JVST_ST_FETCH_PROP:   return "ST_FETCH_PROP";
    case JVST_ST_AFTER_VALUE:  return "ST_AFTER_VALUE";
    case JVST_ST_CHECKOBJ:     return "ST_CHECKOBJ";
    case JVST_ST_CHECKOBJ1:    return "ST_CHECKOBJ1";
    case JVST_ST_EAT_VALUE:    return "ST_EAT_VALUE";
    case JVST_ST_EAT_OBJECT:   return "ST_EAT_OBJECT";
    case JVST_ST_EAT_ARRAY:    return "ST_EAT_ARRAY";
    case JVST_ST_SOMEOF_INIT:  return "ST_SOMEOF_INIT";
    case JVST_ST_SOMEOF_NEXT:  return "ST_SOMEOF_NEXT";
    case JVST_ST_SOMEOF_FINAL: return "ST_SOMEOF_FINAL";
    case JVST_ST_VALID:        return "ST_VALID";
    default:                   return "UNKNOWN";
  }
}

static const char *jvst_ret2name(int ret)
{
  switch (ret) {
    case JVST_INVALID:  return "JVST_INVALID";
    case JVST_VALID:    return "JVST_VALID";
    case JVST_MORE:     return "JVST_MORE";
    case JVST_NEXT:     return "JVST_NEXT";
    default:            return "UNKNOWN";
  }
}

static const struct ast_schema empty_schema = {0};

struct validator_split {
  size_t nv;
  struct jvst_validator *vv;
};

struct jvst_state {
  const struct ast_schema *schema;
  size_t nitems;
  size_t counters[NCOUNTERS];
  union {
    uint64_t work[2];
    struct validator_split split;
  } u;
  enum JVST_STATE state;
};

/* counter indices for various sub-machines */
enum CI_OBJ_MACHINES {
  CI_O_NUM_OBJS = 0,
  CI_O_NUM_ARRS = 1,
};

enum CI_ARR_MACHINES {
  CI_A_NUM_OBJS = 0,
  CI_A_NUM_ARRS = 1,
};

/* work indices for various sub-machines */
enum WI_OBJ_MACHINES {
  WI_O_KEYSIZE = 0,
  WI_O_REQBITS = 1,
};

static void dump_stack(struct jvst_validator *v)
{
  size_t i,n;
  n = v->stop;
  if (n > v->smax) { n = v->smax; }
  fprintf(stderr, "\ntop: %zu, max: %zu\n", v->stop,v->smax);
  for (i=0; i < n; i++) {
    size_t ci,nc;
    struct jvst_state *sp = &v->sstack[i];

    fprintf(stderr, "[%zu] %-16s %8p %8zu",
        i, vst2name(sp->state), (void *)sp->schema,
        sp->nitems);

    nc=sizeof sp->counters / sizeof sp->counters[0];
    if (nc > 0) {
      fprintf(stderr," C");
      for (ci=0; ci < nc; ci++) {
        fprintf(stderr, " %8zu", sp->counters[ci]);
      }
    }

    if (nc > 0) {
      fprintf(stderr," W");
      nc=ARRAYLEN(sp->u.work);
      for (ci=0; ci < nc; ci++) {
        fprintf(stderr, " %8" PRIu64, sp->u.work[ci]);
      }
    }
    fprintf(stderr, "\n");
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
  size_t i,nc,nw;
  sp->nitems = 0;
  nc = ARRAYLEN(sp->counters);
  for (i=0; i < nc; i++) {
    sp->counters[i] = 0;
  }

  nw = ARRAYLEN(sp->u.work);
  for (i=0; i < nw; i++) {
    sp->u.work[i] = 0;
  }
}

void jvst_validate_init_defaults(struct jvst_validator *v, const struct ast_schema *schema)
{
  struct jvst_state zero = { 0 };
  STATIC_ASSERT(ARRAYLEN(v->errstack) <= INT_MAX, err_stack_fits_in_etop);

  v->schema = schema;

  v->smax = JVST_DEFAULT_STACK_SIZE;
  v->sstack = malloc(v->smax * sizeof *v->sstack);

  v->sstack[0] = zero;
  v->sstack[0].state  = JVST_ST_VALUE;
  v->sstack[0].schema = v->schema;
  v->stop = 1;

  v->etop = 0;

  (void)sjp_parser_init(&v->p,
      &v->pstack[0], ARRAYLEN(v->pstack),
      &v->pbuf[0], ARRAYLEN(v->pbuf));
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

static int invalid(struct jvst_validator *v, const char *file, int line, const char *fmt, ...)
{
  if (v->stop < v->smax) {
    v->sstack[v->stop].state  = JVST_ST_ERR;
    v->sstack[v->stop].schema = NULL;
  }

  v->stop++; // always increment if v->stop == v->smax to mark as invalid

  STATIC_ASSERT(ARRAYLEN(v->errstack) <= INT_MAX, err_stack_fits_in_etop);
  assert(v->etop >= 0);
  if (v->etop < (int)ARRAYLEN(v->errstack)) {
    va_list args;

    v->errstack[v->etop].file = file;
    v->errstack[v->etop].line = line;

    va_start(args,fmt);
    vsnprintf(v->errstack[v->etop].msg, sizeof v->errstack[v->etop].msg, fmt, args);
    va_end(args);

    v->etop++;
  }

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
static enum JVST_RESULT eat_value(struct jvst_validator *v, enum SJP_RESULT pret, struct sjp_event *evt)
{
  struct jvst_state *sp;

  sp = getstate(v);
  if (sp == NULL) {
    // XXX - this is an internal error and should be reported as such
    return ERR_UNDERFLOW();
  }

  assert(sp->state == JVST_ST_EAT_VALUE);

  if (SJP_ERROR(pret)) {
    return ERR_JSON(pret);
  }

  sp->nitems += evt->n;
  switch (pret) {
    case SJP_OK:
      return (popstate(v) != NULL) ? JVST_VALID : ERR_UNDERFLOW();

    case SJP_PARTIAL:
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
static enum JVST_RESULT eat_array(struct jvst_validator *v, enum SJP_RESULT pret, struct sjp_event *evt)
{
  struct jvst_state *sp;

  if (sp = getstate(v), sp == NULL) {
    return ERR_UNDERFLOW();
  }

  if (sp->state != JVST_ST_EAT_ARRAY) {
    sp->state = JVST_ST_EAT_ARRAY;
    zerocounters(sp);
  }

  switch (pret) {
    case SJP_MORE:
    case SJP_PARTIAL:
      return JVST_MORE;

    case SJP_OK:
      /* nop */
      break;

    default:
      if (SJP_ERROR(pret)) {
        return ERR_JSON(pret);
      }
      // should be a parser error
      SHOULD_NOT_REACH();
  }

  // SJP_OK -- completed token available

  // If we just read an item and we're not in a nested
  // array/object, increment the item count
  if (sp->counters[CI_A_NUM_OBJS] == 0 &&
      sp->counters[CI_A_NUM_ARRS] == 0 &&
      sjp_parser_state(&v->p) == SJP_PARSER_ARR_ITEM) {
    sp->nitems++;
  }

  switch (evt->type) {
    case SJP_OBJECT_BEG:
      sp->counters[CI_A_NUM_OBJS]++;
      break;

    case SJP_OBJECT_END:
      sp->counters[CI_A_NUM_OBJS]--;
      break;

    case SJP_ARRAY_BEG:
      sp->counters[CI_A_NUM_ARRS]++;
      break;

    case SJP_ARRAY_END:
      sp->counters[CI_A_NUM_ARRS]--;
      if (sp->counters[CI_A_NUM_ARRS] == 0) {
        return (popstate(v) != NULL) ? JVST_VALID : ERR_UNDERFLOW();
      }
      break;

    default:
      /* nop */
      break;
  }

  return JVST_NEXT;
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
static enum JVST_RESULT eat_object(struct jvst_validator *v, enum SJP_RESULT pret, struct sjp_event *evt)
{
  struct jvst_state *sp;

  if (sp = getstate(v), sp == NULL) {
    return ERR_UNDERFLOW();
  }

  if (sp->state != JVST_ST_EAT_OBJECT) {
    sp->state = JVST_ST_EAT_OBJECT;
    zerocounters(sp);
  }

  switch (pret) {
    case SJP_MORE:
    case SJP_PARTIAL:
      return JVST_MORE;

    case SJP_OK:
      /* nop */
      break;

    default:
      // should be an error
      if (SJP_ERROR(pret)) {
        return ERR_JSON(pret);
      }
      SHOULD_NOT_REACH();
  }

  // SJP_OK -- completed token available

  switch (evt->type) {
    case SJP_OBJECT_BEG:
      sp->counters[CI_O_NUM_OBJS]++;
      break;

    case SJP_OBJECT_END:
      sp->counters[CI_O_NUM_OBJS]--;
      if (sp->counters[CI_O_NUM_OBJS] == 0) {
        return (popstate(v) != NULL) ? JVST_VALID : ERR_UNDERFLOW();
      }
      break;

    case SJP_ARRAY_BEG:
      sp->counters[CI_O_NUM_ARRS]++;
      break;

    case SJP_ARRAY_END:
      sp->counters[CI_O_NUM_ARRS]--;
      break;

    case SJP_STRING:
      // If we just read a key and we're not in a nested object,
      // increment the number of kv pairs
      if (sp->counters[CI_O_NUM_OBJS] == 1 && // XXX FIXME
          sp->counters[CI_O_NUM_ARRS] == 0 &&
          sjp_parser_state(&v->p) == SJP_PARSER_OBJ_KEY) {
        sp->nitems++;
      }

    default:
      /* nop */
      break;
  }

  return JVST_NEXT;
}

static enum JVST_RESULT validate_object(struct jvst_validator *v, enum SJP_RESULT pret, struct sjp_event *evt);

static inline bool is_valid_type(struct jvst_validator *v, enum json_valuetype mask, enum json_valuetype bits)
{
  (void)v;  // XXX - use to set up a useful error message
  if (mask == 0 || (mask & bits) != 0) {
    return true;
  }

  // XXX - set error message
  // something like: validate_set_error(v, "expected type mask %s but found type %s", mask, bits);
  return false;
}

static enum JVST_RESULT validate_number(struct jvst_validator *v, enum SJP_RESULT pret, struct sjp_event *evt)
{
  struct jvst_state *sp;
  const struct ast_schema *schema;

  (void)pret;

  assert(evt->type == SJP_NUMBER);

  if (sp = getstate(v), sp == NULL) {
    return ERR_UNDERFLOW();
  }
  schema = sp->schema;
  assert(schema != NULL);

  if (schema->kws & KWS_MINIMUM) {
    if (schema->exclusive_minimum) {
      if (evt->d <= schema->minimum) {
        return INVALID(v, "invalid number: %f <= %f", evt->d, schema->minimum);
      }
    } else { // not exclusiveMinimum
      if (evt->d < schema->minimum) {
        return INVALID(v, "invalid number: %f < %f", evt->d, schema->minimum);
      }
    }
  }

  return (popstate(v) != NULL) ? JVST_VALID : ERR_UNDERFLOW();
}

static enum JVST_RESULT validate_integer(struct jvst_validator *v, enum SJP_RESULT pret, struct sjp_event *evt)
{
  double x,cx;

  assert(evt->type == SJP_NUMBER);

  x = evt->d;
  if (x != ceil(x)) {
    // XXX - error: not an integer
    return INVALID(v, "number %f is not an integer", x);
  }

  return validate_number(v,pret,evt);
}

static inline enum JVST_RESULT check_type_priv(struct jvst_validator *v, 
    enum json_valuetype mask, enum json_valuetype bits, const char *file, int line)
{
  if (is_valid_type(v,mask,bits)) {
      return JVST_VALID;
  }

  return invalid(v, file, line, "expected type %d but found %d", mask, bits);
}

static enum JVST_RESULT validate_next_event(struct jvst_validator *v, enum SJP_RESULT pret, struct sjp_event *evt);

static enum JVST_RESULT validate_some_of(struct jvst_validator *v, enum SJP_RESULT pret, struct sjp_event *evt)
{
  struct jvst_state *sp;
  const struct ast_schema *schema;
  struct ast_schema_set *sset;
  struct jvst_validator *vv;
  size_t i,count;

  if (sp = getstate(v), sp == NULL) {
    return ERR_UNDERFLOW();
  }

  schema = sp->schema;
  assert(schema != NULL);

  switch (sp->state) {
    case JVST_ST_SOMEOF_INIT:
      goto init;

    case JVST_ST_SOMEOF_NEXT:
      goto next;

    case JVST_ST_SOMEOF_FINAL:
      goto final;

    default:
      SHOULD_NOT_REACH();
  }

init:
  count = 0;
  for (sset = schema->some_of.set; sset != NULL; sset = sset->next) {
    count++;
  }

  zerocounters(sp);

  // allocate split validators
  vv = malloc(count * sizeof sp->u.split.vv[0]);
  if (vv == NULL) {
    return INVALID(v, "cannot allocate %zu split validators for some_of evaluation", count);
  }
  sp->u.split.vv = vv;
  sp->u.split.nv = count;

  // TODO: bound allocation and split the current stack to keep resource
  // use fixed/minimized
  for (i=0,sset = schema->some_of.set; sset != NULL; sset = sset->next,i++) {
    assert(i < count);
    jvst_validate_init_defaults(&vv[i], sset->schema);
  }
  assert(i == count);

  sp->state = JVST_ST_SOMEOF_NEXT;

  /* fallthrough */

next:
  {
    unsigned num_valid = 0, num_invalid = 0;
    int valid = 0,more = 0;

    vv = sp->u.split.vv;
    count = sp->u.split.nv;

    // feed token to each validator
    for (i=0; i < count; i++) {
      enum JVST_RESULT ret;
      ret = validate_next_event(&vv[i], pret, evt);
      switch (ret) {
        case JVST_INVALID:
          num_invalid++;
          break;

        case JVST_NEXT:
          break;

        case JVST_MORE:
          more = 1;
          break;

        case JVST_VALID:
          valid = 1;
          num_valid++;
          break;

        default:
          SHOULD_NOT_REACH();
      }
    }

    sp->counters[0] = num_valid;
    sp->counters[1] = num_invalid;

    if (valid && more) {
      return INVALID(v, "internal error: split return of both JVST_MORE and JVST_VALID");
    }

    // FIXME: check for overflow!
    if (valid || (num_invalid + schema->some_of.min > count)) {
      sp->state = JVST_ST_SOMEOF_FINAL;
      goto final;
    }
  }
  return JVST_NEXT;

final:
  {
    unsigned num_valid = 0, num_invalid = 0;
    enum JVST_RESULT ret;

    vv = sp->u.split.vv;
    count = sp->u.split.nv;

    // free split validators
    for (i=0; i < count; i++) {
      ret = jvst_validate_close(&vv[i]);
      if (ret == JVST_INVALID) {
        num_invalid++;
      }
    }

    num_valid = count - num_invalid;
    if (num_valid < schema->some_of.min || num_valid > schema->some_of.max) {
      return INVALID(v, "some_of proposition has %zu valid clauses, requires %zu - %zu",
          num_valid, schema->some_of.min, schema->some_of.max);
    }

    return (popstate(v) != NULL) ? JVST_VALID : ERR_UNDERFLOW();
  }

  return JVST_INVALID;
}

#define CHECK_TYPE(v,mask,type) do{ \
  if (check_type_priv((v),(mask),(type), __FILE__, __LINE__) != JVST_VALID) { \
    return JVST_INVALID;            \
  } } while(0)

static enum JVST_RESULT validate_value(struct jvst_validator *v, enum SJP_RESULT pret, struct sjp_event *evt)
{
  struct jvst_state *sp;

  if (sp = getstate(v), sp == NULL) {
    return ERR_UNDERFLOW();
  }

  assert(sp->schema != NULL);

  if (sp->schema->some_of.set != NULL) {
    // XXX - TODO: constraints aside from allOf/anyOf/oneOf
    sp->state = JVST_ST_SOMEOF_INIT;
    return validate_some_of(v, pret, evt);
  }

  // XXX - if condition effectively repeated inside... this seems wrong
  if (evt->type == SJP_NONE && pret != SJP_OK) {
    // XXX - double check when a SJP_NONE event should correspond to
    // SJP_OK
    return (pret != SJP_OK) ? JVST_MORE : JVST_INVALID;
  }

  switch (evt->type) {
    case SJP_NONE:
    default:
      SHOULD_NOT_REACH(v);

    case SJP_NULL:
      CHECK_TYPE(v, sp->schema->types, JSON_VALUE_NULL);
      // XXX - validate the values
      break;

    case SJP_TRUE:
    case SJP_FALSE:
      CHECK_TYPE(v, sp->schema->types, JSON_VALUE_BOOL);
      // XXX - validate the values
      break;

    case SJP_STRING:
      CHECK_TYPE(v, sp->schema->types, JSON_VALUE_STRING);
      // XXX - validate the values
      if (pret != SJP_OK) {
        getstate(v)->state = JVST_ST_VALID;
        if (newframe(v) == NULL) {
          return ERR_OVERFLOW();
        }

        sp->state = JVST_ST_OBJECT;
        sp->nitems = 0;
        zerocounters(sp);
        return eat_value(v, pret, evt);
      }
      break;

    case SJP_NUMBER:
      // XXX - validate the values
      CHECK_TYPE(v, sp->schema->types, JSON_VALUE_NUMBER | JSON_VALUE_INTEGER);
      if (pret != SJP_OK) {
        return JVST_MORE;
        /*
        getstate(v)->state = JVST_ST_VALID;
        if (newframe(v) == NULL) {
          return JVST_INVALID;
        }
        return eat_value(v, &evt);
        */
      }

      if ((sp->schema->types & (JSON_VALUE_NUMBER | JSON_VALUE_INTEGER)) == JSON_VALUE_INTEGER) {
        return validate_integer(v, pret, evt);
      }
      return validate_number(v, pret, evt);

    case SJP_ARRAY_BEG:
      CHECK_TYPE(v, sp->schema->types, JSON_VALUE_ARRAY);
      // XXX - validate the array
      getstate(v)->state = JVST_ST_VALID;
      if (newframe(v) == NULL) {
        return ERR_OVERFLOW();
      }
      return eat_array(v, pret, evt);

    case SJP_OBJECT_BEG:
      CHECK_TYPE(v, sp->schema->types, JSON_VALUE_OBJECT);
      getstate(v)->state = JVST_ST_OBJECT_INIT;
      zerocounters(sp);
      return validate_object(v, pret, evt);

    case SJP_OBJECT_END:
    case SJP_ARRAY_END:
      SHOULD_NOT_REACH(v);
  }

  return (popstate(v) != NULL) ? JVST_VALID : ERR_UNDERFLOW();
}
#undef CHECK_TYPE

enum OBJ_VALIDATION {
  OBJ_PROPERTIES   = 1<<0,
  OBJ_REQUIRED     = 1<<1,

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

static size_t bit_from_set(const struct ast_string_set *ss, const char *k, size_t nk)
{
  size_t b = 1;
  for (; ss != NULL; b = b << 1, ss = ss->next) {
    if (ss->str.len != nk) {
      continue;
    }

    if (memcmp(ss->str.s, k, nk) == 0) {
      return b;
    }
  }

  return 0;
}

static enum JVST_RESULT validate_object(struct jvst_validator *v, enum SJP_RESULT pret, struct sjp_event *evt)
{
  struct jvst_state *sp;
  const struct ast_schema *schema, *pschema;
  int venum;
  const char *key;
  size_t nkey, nreq, reqmask;

  if (sp = getstate(v), sp == NULL) {
    return ERR_UNDERFLOW();
  }

  schema = sp->schema;
  assert(schema != NULL);

  // see what we need to validate...
  venum = 0;
  if (schema->properties.set != NULL) {
    venum |= OBJ_PROPERTIES;
  }

  nreq = 0;
  reqmask = 0;
  if (schema->required.set != NULL) {
    struct ast_string_set *ss;
    size_t full_mask = ~(size_t)0;

    venum |= OBJ_REQUIRED;
    for (ss=schema->required.set; ss != NULL; ss = ss->next) {
      nreq++;
      reqmask = (reqmask << 1) | 1;
      if (reqmask == full_mask) {
        // warn that we currently only support nreq-1 different required
        // fields
        //
        // XXX - need a better way to do this
        // XXX - need to relax the bit-width limitation
        fprintf(stderr, "warning: only %zu different required properties are supported\n",
            nreq-1);
      }
    }
  }

  if (schema->kws & KWS_MINMAX_PROPERTIES) {
    venum |= OBJ_MINMAX_PROPERTIES;
  }

  switch (sp->state) {
    case JVST_ST_OBJECT_INIT:
      goto initialize;

    case JVST_ST_OBJECT:
      goto new_prop;

    case JVST_ST_FETCH_PROP:
      goto fetch_prop;

    case JVST_ST_AFTER_VALUE:
      goto after_value;

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
      SHOULD_NOT_REACH();
  }

initialize:
  /* fast path if we don't have to validate per-property */
  if ((venum & CHECK_PROP_MASK) == 0) {
    getstate(v)->state = (venum == 0) ? JVST_ST_VALID : JVST_ST_CHECKOBJ1;
    if (newframe(v) == NULL) {
      return ERR_OVERFLOW();
    }
    return eat_object(v,pret,evt);
  }

  sp->state = JVST_ST_OBJECT;
  zerocounters(sp);
  return JVST_NEXT;

  // FIXME: currently we limit keys to fit into the kbuf buffer.  This
  // is a limitation of the current dumb approach and hopefully
  // switching to DFA matching we can avoid this
  //
  // FIXME: need to write the sjp_parser buffering code
new_prop:
  sp->state = JVST_ST_FETCH_PROP;
  memset(v->kbuf,0,sizeof v->kbuf);
  sp->u.work[WI_O_KEYSIZE] = 0; // <-- ? XXX FIXME

  /* fallthrough */

fetch_prop:
  // ret = sjp_parser_next(&v->p, &evt);
  switch (pret) {
    case SJP_MORE:
      return JVST_MORE;

    case SJP_PARTIAL:
      if (sp->u.work[WI_O_KEYSIZE] + evt->n > sizeof v->kbuf) {
        // FIXME: need better errors!
        return INVALID(v, "key split across buffers is too long");
      }
      memcpy(&v->kbuf[sp->u.work[WI_O_KEYSIZE]], evt->text, evt->n);
      sp->u.work[WI_O_KEYSIZE] += evt->n;
      return JVST_MORE; // XXX - should this be JVST_NEXT ?

    case SJP_OK:
      if (evt->type == SJP_OBJECT_END) {
        sp->state = JVST_ST_CHECKOBJ;
        goto check_obj;
      }

      if (sp->u.work[WI_O_KEYSIZE] == 0) {
        key = evt->text;
        nkey = evt->n;
      } else {
        size_t ksz = sp->u.work[WI_O_KEYSIZE] + evt->n;
        if (ksz > sizeof v->kbuf) {
          // FIXME: need better errors!
          return INVALID(v, "key split across buffers is too long");
        }

        memcpy(&v->kbuf[sp->u.work[WI_O_KEYSIZE]], evt->text, evt->n);
        sp->u.work[WI_O_KEYSIZE] = ksz; // record this for debugging purposes

        key = v->kbuf;
        nkey = ksz;
      }
      break;

    default:
      if (SJP_ERROR(pret)) {
        return ERR_JSON(pret);
      }
      // should be a parser error
      SHOULD_NOT_REACH();
  }

  // record items
  sp->nitems++;

  if (schema->required.set != NULL) {
    size_t bit;
    bit = bit_from_set(schema->required.set, key, nkey);
    sp->u.work[WI_O_REQBITS] |= bit;
  }

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
  sp->state = JVST_ST_AFTER_VALUE;
  if (pushstate(v, JVST_ST_VALUE, pschema) == NULL) {
    return ERR_OVERFLOW();
  }

  return JVST_NEXT;

after_value:
  sp->state = JVST_ST_OBJECT;
  return JVST_NEXT;

check_obj:
  /* NB: not all checks are implemented */
  if (venum & OBJ_MINMAX_PROPERTIES) {
    if (sp->nitems < schema->min_properties) {
      return INVALID(v, "object has %zu properties, min is %zu", sp->nitems, schema->min_properties);
    }

    if (schema->max_properties > 0 && sp->nitems > schema->max_properties) {
      return INVALID(v, "object has %zu properties, max is %zu", sp->nitems, schema->max_properties);
    }
  }

  /* check for required properties */
  if (venum & OBJ_REQUIRED && sp->u.work[WI_O_REQBITS] != reqmask) {
    // XXX - give a more specific reason (eg: first required property that
    // is missing)
    return INVALID(v, "object is missing required properties");
  }

  return (popstate(v) != NULL) ? JVST_VALID : ERR_UNDERFLOW();
}

static enum JVST_RESULT validate_next_event(struct jvst_validator *v, enum SJP_RESULT pret, struct sjp_event *evt)
{
  struct jvst_state *top;
  int ret;

  char dbgbuf[1024] = {0};
  size_t n = evt->n;
  if (n >= sizeof dbgbuf) {
    n = sizeof dbgbuf - 1;
  }
  memcpy(dbgbuf, evt->text, n);

  fprintf(stderr, "pret = %d (%s)  evt->type = %d (%s)  evt->text = '%s'\n",
      pret, ret2name(pret), evt->type, evt2name(evt->type), dbgbuf);
  dump_stack(v);

  do {
    if (top = getstate(v), top == NULL) {
      return ERR_UNDERFLOW();
    }

    fprintf(stderr, "--> %zu [%s] schema = %p  nitems = %zu  counters=[%zu %zu]  work=[%" PRIu64 " %" PRIu64 "]\n",
        v->stop,
        vst2name(top->state),
        (void *)top->schema,
        top->nitems,
        top->counters[0], top->counters[1],
        top->u.work[0], top->u.work[1]);

    switch (top->state) {
      case JVST_ST_ERR:
        return ERR_ALREADY_ERR();

      case JVST_ST_VALUE:
        ret = validate_value(v, pret, evt);
        break;

      case JVST_ST_OBJECT:
      case JVST_ST_FETCH_PROP:
      case JVST_ST_AFTER_VALUE:
      case JVST_ST_CHECKOBJ:
      case JVST_ST_CHECKOBJ1:
        ret = validate_object(v, pret, evt);
        break;

      case JVST_ST_EAT_VALUE:
        ret = eat_value(v, pret, evt);
        break;

      case JVST_ST_EAT_OBJECT:
        ret = eat_object(v, pret, evt);
        break;

      case JVST_ST_EAT_ARRAY:
        ret = eat_array(v, pret, evt);
        break;

      case JVST_ST_SOMEOF_INIT:
      case JVST_ST_SOMEOF_NEXT:
      case JVST_ST_SOMEOF_FINAL:
        ret = validate_some_of(v, pret, evt);
        break;

      case JVST_ST_VALID:
        ret = (popstate(v) != NULL) ? JVST_VALID : ERR_UNDERFLOW();
        break;

      default:
        SHOULD_NOT_REACH(v);
    }

    fprintf(stderr, "--> event state: %d %s\n", ret, jvst_ret2name(ret));
  } while (ret == JVST_VALID && v->stop > 0);

  return ret;
}

enum JVST_RESULT jvst_validate_more(struct jvst_validator *v, char *data, size_t n)
{
  sjp_parser_more(&v->p, data, n);

  // fast exit if we've already encountered an error...
  if (v->etop > 0) {
    return JVST_INVALID;
  }

  for(;;) {
    struct sjp_event evt = { 0 };
    enum SJP_RESULT pret;
    enum JVST_RESULT ret;

    pret = sjp_parser_next(&v->p, &evt);
#if JVST_VALIDATE_DEBUG
    {
      char txt[256];
      size_t n = evt.n;
      if (n < sizeof txt) {
        memcpy(txt,evt.text,n);
        txt[n] = '\0';
      } else {
        n = sizeof txt - 4;
        memcpy(txt,evt.text,n);
        memcpy(&txt[n], "...", 4);
      }

      fprintf(stderr, "[%-8s] %-16s %s\n", ret2name(pret), evt2name(evt.type), txt);
      if (SJP_ERROR(pret)) {
        return ERR_JSON(pret);
      }
    }
#endif /* JVST_VALIDATE_DEBUG */

    // XXX - handle EOS here?
    // FIXME: handle pret == SJP_PARTIAL!

    if (pret == SJP_MORE && evt.type == SJP_TOK_NONE) {
      // need more...
      return JVST_MORE;
    }

    if (pret == SJP_OK && evt.type == SJP_TOK_NONE) {
      // stream has closed
      return (v->stop > 0) ? JVST_INVALID : JVST_VALID;
    }

    ret = validate_next_event(v, pret, &evt);

    if (ret != JVST_VALID && ret != JVST_NEXT) {
      return ret;
    }
  }
}

enum JVST_RESULT jvst_validate_close(struct jvst_validator *v)
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

  if (SJP_ERROR(ret)) {
    return ERR_JSON(ret);
  }

  if (st == JVST_ST_ERR) {
    return ERR_ALREADY_ERR();
  }

  return JVST_VALID;
}

