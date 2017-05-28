/* Tests to bootstrap validation */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

#include "ast.h"
#include "validate.h"

int ntest;
int nfail;

struct validation_test {
  bool succeeds;
  const char *json;
  struct ast_schema *schema;
};

// arena allocators to make it easy to programmatically set up a schema
static struct ast_schema ar_schema[1024];
static struct ast_property_schema ar_props[1024];

struct arena_info {
  size_t nschema;
  size_t nprop;
};

static struct json_string newstr(const char *s)
{
  struct json_string str = { .s = s, .len = strlen(s) };
  return str;
}

static struct ast_schema *newschema(struct arena_info *A, int types)
{
  size_t i,max;
  struct ast_schema *s;

  i = A->nschema++;
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

static struct ast_property_schema *newprops(struct arena_info *A, ...)
{
  struct ast_property_schema *props = NULL;
  struct ast_property_schema **pp = &props;
  size_t max = sizeof ar_props / sizeof ar_props[0];
  va_list args;

  va_start(args, A);

  for(;;) {
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

    p->pattern.str = newstr(name);
    p->schema = va_arg(args, struct ast_schema *);

    *pp = p;
    pp = &p->next;
  }

  va_end(args);

  return props;
}

static struct ast_schema *empty_schema(void)
{
  static struct ast_schema empty = { 0 };
  return &empty;
}

static const char *jvst_ret2name(int ret)
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

static int run_test(const struct validation_test *t)
{
  struct jvst_validator v;
  size_t n;
  int ret, failed;
  static char buf[4096];

  jvst_validate_init_defaults(&v, t->schema);
  n = strlen(t->json);
  if (n >= sizeof buf) {
    fprintf(stderr, "json exceeds buffer size (%s:%d)\n", __FILE__, __LINE__);
    abort();
  }

  // already checked buffer size
  strcpy(buf, t->json);
  ret = jvst_validate_more(&v, buf, n);
  /*
  fprintf(stderr, "jvst_validate_more(...\"%s\"...) : %s\n",
      buf, jvst_ret2name(ret));
      */
  failed = JVST_IS_INVALID(ret);

  ret = jvst_validate_close(&v);
  /*
  fprintf(stderr, "jvst_validate_close() : %s\n",
      jvst_ret2name(ret));
      */
  failed = failed || JVST_IS_INVALID(ret);

  return !failed;
}

#define RUNTESTS(testlist) runtests(__func__, (testlist))
static void runtests(const char *testname, const struct validation_test tests[])
{
  int i;

  for (i=0; tests[i].json != NULL; i++) {
    bool succ;
    ntest++;

    succ = !!run_test(&tests[i]);
    if (succ != tests[i].succeeds) {
      printf("%s_%d: failed (expected %s but found %s)\n",
          testname, i+1,
          tests[i].succeeds ? "success" : "failure",
          succ ? "success" : "failure");
      nfail++;
    }
  }
}

/* test to get us off the ground */
void test_empty_schema(void)
{
  const struct validation_test tests[] = {
    { true, "{}", empty_schema() },
    { true, "[]", empty_schema() },
    { true, "{ \"foo\" : \"bar\" }", empty_schema() },

    // one to make sure that we're checking for valid json
    { false, "{ 12 : \"bar\" }", empty_schema() },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_type_constraint_number(void)
{
  struct ast_schema schema = {
    .types = JSON_VALUE_NUMBER,
  };

  const struct validation_test tests[] = {
    //  "an integer is a number",
    { true, "1", &schema, },

    //  "a float is a number",
    { true, "1.1", &schema, },

    //  "a string is not a number",
    { false, "\"foo\"", &schema, },

    //  "a string is still not a number, even if it looks like one",
    { false, "\"1\"", &schema, },

    //  "an object is not a number",
    { false, "{}", &schema, },

    //  "an array is not a number",
    { false, "[]", &schema, },

    //  "a boolean is not a number",
    { false, "true", &schema, },

    //  "null is not a number",
    { false, "null", &schema, },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_type_constraint_object(void)
{
  struct ast_schema schema = {
    .types = JSON_VALUE_OBJECT,
  };

  const struct validation_test tests[] = {
    //  "an integer is not an object",
    { false, "1", &schema, },

    //  "a float is not an object",
    { false, "1.1", &schema, },

    //  "a string is not an object",
    { false, "\"foo\"", &schema, },

    //  "an object is an object",
    { true, "{}", &schema, },

    //  "an array is not an object",
    { false, "[]", &schema, },

    //  "a boolean is not an object",
    { false, "true", &schema, },

    //  "null is not an object",
    { false, "null", &schema, },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_type_constraint_properties(void)
{
  struct arena_info A = {0};

  struct ast_schema schema = {
    .properties = {
      .set = newprops(&A,
          "foo", newschema(&A, JSON_VALUE_NUMBER), // XXX - JSON_VALUE_INTEGER
          "bar", newschema(&A, JSON_VALUE_STRING),
          NULL)
    }
  };

  const struct validation_test tests[] = {
    // "description": "both properties present and valid is valid",
    { true, "{\"foo\": 1, \"bar\": \"baz\"}", &schema },

    // "description": "one property invalid is invalid",
    { false, "{\"foo\": 1, \"bar\": {}}", &schema },

    // "description": "both properties invalid is invalid",
    { false, "{\"foo\": [], \"bar\": {}}", &schema },

    // "description": "doesn't invalidate other properties",
    { true, "{\"quux\": []}", &schema },

    // "description": "ignores non-objects",
    { true, "[]", &schema },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

int main(void)
{
  test_empty_schema();
  test_type_constraint_number();
  test_type_constraint_object();

  test_type_constraint_properties();

  printf("%d tests, %d failures\n", ntest, nfail);
}
