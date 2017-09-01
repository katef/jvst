/* Tests to bootstrap validation */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

#include "ast.h"
#include "validate.h"
#include "validate_testing.h"
#include "validate_vm.h"

#define PROTOTYPE 0

struct validation_test {
  bool succeeds;
  const char *json;
  struct ast_schema *schema;
};

static void dump_err_stack(struct jvst_validator *v)
{
  int i;
  fprintf(stderr, "ERROR in validator:\n");
  for (i=0; i < v->etop; i++) {
    fprintf(stderr, "[%2d] %16s:%4d %s\n",
        i,
        v->errstack[i].file,
        v->errstack[i].line,
        v->errstack[i].msg);
  }
}

static int run_prototype_test(const struct validation_test *t)
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

  if (failed && t->succeeds) {
    dump_err_stack(&v);
  }

  ret = jvst_validate_close(&v);
  /*
  fprintf(stderr, "jvst_validate_close() : %s\n",
      jvst_ret2name(ret));
      */
  if (!failed && JVST_IS_INVALID(ret) && t->succeeds) {
    dump_err_stack(&v);
  }

  failed = failed || JVST_IS_INVALID(ret);

  return !failed;
}

static int run_vm_test(const struct validation_test *t)
{
  struct jvst_vm_program *prog;
  struct jvst_vm vm;
  char buf[4096];
  size_t n;
  int ret, failed;

  prog = jvst_compile_schema(t->schema);

  jvst_vm_init_defaults(&vm, prog);
  n = strlen(t->json);
  if (n >= sizeof buf) {
    fprintf(stderr, "json exceeds buffer size (%s:%d)\n", __FILE__, __LINE__);
    abort();
  }

  // already checked buffer size
  strcpy(buf, t->json);
  ret = jvst_vm_more(&vm, buf, n);
  failed = JVST_IS_INVALID(ret);

  if (failed && t->succeeds) {
    jvst_vm_dumpstate(&vm);
  }

  ret = jvst_vm_close(&vm);
  if (!failed && JVST_IS_INVALID(ret) && t->succeeds) {
    jvst_vm_dumpstate(&vm);
  }

  failed = failed || JVST_IS_INVALID(ret);

  jvst_vm_finalize(&vm);
  jvst_vm_program_free(prog);

  return !failed;
}

#define RUNTESTS(testlist) runtests(__func__, (testlist))
static void runtests(const char *testname, const struct validation_test tests[])
{
  int i;

  for (i=0; tests[i].json != NULL; i++) {
    bool succ;
    ntest++;

#if PROTOTYPE
    succ = !!run_prototype_test(&tests[i]);
#else 
    succ = !!run_vm_test(&tests[i]);
#endif

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

    // lots of embedded stuff
    { true, "{ \"foo\" : { \"bar\" : { \"quux\" : [ 1, 2, 3, {}, { \"this\" : [] } ], \"foo\" : [ {}, {}, [ {} ] ] } } }", empty_schema() },

    // one to make sure that we're checking for valid json
    { false, "{ 12 : \"bar\" }", empty_schema() },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_type_integer(void)
{
  struct ast_schema schema = {
    .types = JSON_VALUE_INTEGER,
  };

  const struct validation_test tests[] = {
    // "description": "an integer is an integer",
    { true, "1", &schema },
    { true, "0", &schema },
    { true, "10", &schema },
    { true, "-5", &schema },

    // after shifting decimal places, these are still integers
    { true, "1.1e2", &schema },
    { true, "200e-2", &schema },

    // "description": "a float is not an integer",
    { false, "1.1", &schema },
    { false, "1e-1", &schema },
    { false, "210e-2", &schema },
    { false, "-0.1", &schema },
    { false, "0.1", &schema },
    { false, "-5.7", &schema },

    // "description": "a string is not an integer",
    { false, "\"foo\"", &schema },

    // "description": "a string is still not an integer, even if it looks like one",
    { false, "\"1\"", &schema },

    // "description": "an object is not an integer",
    { false, "{}", &schema },

    // "description": "an array is not an integer",
    { false, "[]", &schema },

    // "description": "a boolean is not an integer",
    { false, "true", &schema },

    // "description": "null is not an integer",
    { false, "null", &schema },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_type_number(void)
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

void test_type_object(void)
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

void test_properties(void)
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

    // "description": "both properties present, but have invalid types
    // (switched types)
    { false, "{\"bar\": 1, \"foo\": \"baz\"}", &schema },

    // "description": "doesn't invalidate other properties",
    { true, "{\"quux\": []}", &schema },

    // "description": "ignores non-objects",
    { true, "[]", &schema },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_minproperties_1(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "minProperties", 1,
      NULL);

  const struct validation_test tests[] = {
    // "description": "longer is valid",
    { true, "{\"foo\": 1, \"bar\": 2}", schema },

    // "description": "exact length is valid",
    { true, "{\"foo\": 1}", schema },

    // "description": "too short is invalid",
    { false, "{}", schema },

    // "description": "ignores non-objects",
    { true, "\"\"", schema },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_minproperties_2(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "minProperties", 1,
      "properties", newprops(&A,
        "foo", newschema(&A, JSON_VALUE_NUMBER), // XXX - JSON_VALUE_INTEGER
        "bar", newschema(&A, JSON_VALUE_STRING),
        NULL),
      NULL);

  const struct validation_test tests[] = {
    // "description": "longer is valid",
    { true, "{\"foo\": 1, \"bar\": \"baz\"}", schema },

    // "description": "satisfies minProperties but not properties"
    { false, "{\"foo\": 1, \"bar\": 2}", schema },

    // "description": "exact length is valid",
    { true, "{\"foo\": 1}", schema },

    // "description": "satisfies minProperties but not properties"
    { false, "{\"bar\": 1}", schema },

    // "description": "satisfies minProperties and properties"
    { true, "{\"bar\": \"baz\"}", schema },

    // "description": "too short is invalid",
    { false, "{}", schema },

    // "description": "ignores non-objects",
    { true, "\"\"", schema },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_minproperties_3(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "minProperties", 1,
      "properties", newprops(&A,
        "foo", newschema_p(&A, JSON_VALUE_OBJECT,
          "minProperties", 1,
          NULL), // XXX - JSON_VALUE_INTEGER
        "bar", newschema(&A, JSON_VALUE_STRING),
        NULL),
      NULL);

  const struct validation_test tests[] = {
    // "description": "longer is valid",
    { true, "{\"baz\": 1, \"bar\": \"baz\"}", schema },

    // "description": "root satisfies minProperties but foo is the wrong type"
    { false, "{\"foo\": 1, \"bar\": \"baz\"}", schema },

    // "description": "root satisfies minProperties but foo does not"
    { false, "{\"foo\": {}, \"bar\": \"baz\"}", schema },

    // "description": "root and foo have valid lengths",
    { true, "{\"foo\": {\"bar\": 3}}", schema },

    // "description": "satisfies minProperties but not properties"
    { false, "{\"bar\": 1}", schema },

    // "description": "satisfies minProperties and properties"
    { true, "{\"bar\": \"baz\"}", schema },

    // "description": "too short is invalid",
    { false, "{}", schema },

    // "description": "ignores non-objects",
    { true, "\"\"", schema },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_maxproperties_1(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "maxProperties", 2,
      NULL);

  const struct validation_test tests[] = {
    // "description": "shorter is valid",
    { true, "{\"foo\": 1}", schema },

    // "description": "exact length is valid",
    { true, "{\"foo\": 1, \"bar\": 2}", schema },

    // "description": "too long is invalid",
    { false, "{\"foo\": 1, \"bar\": 2, \"baz\": 3}", schema },

    // "description": "ignores non-objects",
    { true, "\"foobar\"", schema },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_maxproperties_2(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "maxProperties", 1,
      "properties", newprops(&A,
        "foo", newschema_p(&A, JSON_VALUE_OBJECT,
          "maxProperties", 1,
          NULL), // XXX - JSON_VALUE_INTEGER
        "bar", newschema(&A, JSON_VALUE_STRING),
        NULL),
      NULL);

  const struct validation_test tests[] = {
    // "description": "shorter is valid",
    { true, "{}", schema },

    // "description": "root and foo satisfy maxProperties"
    { true, "{\"foo\": {} }", schema },

    // "description": "root exact length is valid"
    { true, "{\"bar\": \"baz\"}", schema },

    // "description": "root exact length is valid, but bar is wrong type"
    { false, "{\"bar\": 1}", schema },

    // "description": "root has too many properties",
    { false, "{\"baz\": 1, \"bar\": \"baz\"}", schema },

    // "description": "root exact length is valid, shorter foo is valid"
    { true, "{\"foo\": {}}", schema },

    // "description": "root exact length is valid, foo exact length is valid"
    { true, "{\"foo\": { \"bar\" :  1 }}", schema },

    // "description": "root exact length is valid, foo is too long"
    { false, "{\"foo\": { \"bar\" :  1, \"baz\" : \"quux\" }}", schema },

    // "description": "ignores non-objects",
    { true, "\"\"", schema },

    // "description": "ignores non-objects",
    { true, "[]", schema },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_minmaxproperties_1(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "minProperties", 1,
      "maxProperties", 1,
      "properties", newprops(&A,
        "foo", newschema_p(&A, JSON_VALUE_OBJECT,
          "minProperties", 1,
          "maxProperties", 2,
          NULL), // XXX - JSON_VALUE_INTEGER
        "bar", newschema(&A, JSON_VALUE_STRING),
        NULL),
      NULL);

  const struct validation_test tests[] = {
    // "description": "root and foo satisfy min/maxProperties"
    { true, "{\"foo\": { \"bar\" : 17 } }", schema },

    // "description": "root exact length is valid"
    { true, "{\"bar\": \"baz\"}", schema },

    // "description": "root has too few properties",
    { false, "{}", schema },

    // "description": "root exact length is valid, but bar is wrong type"
    { false, "{\"bar\": 1}", schema },

    // "description": "root has too many properties",
    { false, "{\"baz\": 1, \"bar\": \"baz\"}", schema },

    // "description": "root exact length is valid, shorter foo is invalid"
    { false, "{\"foo\": {}}", schema },

    // "description": "root exact length is valid, foo satisfies min/max length"
    { true, "{\"foo\": { \"bar\" :  1 }}", schema },

    // "description": "root exact length is valid, foo satisfies min/max length"
    { true, "{\"foo\": { \"bar\" :  1, \"baz\" : \"quux\" }}", schema },

    // "description": "root exact length is valid, foo is too long"
    { false, "{\"foo\": { \"bar\" :  1, \"baz\" : \"quux\", \"quux\" : 7 }}", schema },

    // "description": "ignores non-objects",
    { true, "\"\"", schema },

    // "description": "ignores non-objects",
    { true, "[]", schema },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_required(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "properties", newprops(&A,
        "foo", empty_schema(),
        "bar", empty_schema(),
        NULL),
      "required", stringset(&A, "foo", NULL),
      NULL);

  const struct validation_test tests[] = {
    // "description": "present required property is valid",
    { true, "{\"foo\": 1}", schema },

    // "description": "non-present required property is invalid",
    { false, "{\"bar\": 1}", schema },

    // "description": "ignores non-objects",
    { true, "12", schema },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_minimum(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "minimum", 1.1,
      NULL);

  const struct validation_test tests[] = {
    // "description": "above the minimum is valid",
    { true, "2.6", schema },

    // "description": "boundary point is valid",
    { true, "1.1", schema },

    // "description": "below the minimum is invalid",
    { false, "0.6", schema },

    // "description": "ignores non-numbers",
    { true, "\"x\"", schema },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_anyof_1(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "anyOf", schema_set(&A, 
        newschema_p(&A, JSON_VALUE_INTEGER, NULL),
        newschema_p(&A, 0, "minimum", 2.0, NULL),
        NULL),
      NULL);

  const struct validation_test tests[] = {
    // "description": "first anyOf valid",
    { true, "1", schema, },
    // "description": "second anyOf valid",
    { true, "2.5", schema, },
    // "description": "both anyOf valid",
    { true, "3", schema, },
    // "description": "neither anyOf valid",
    { false, "1.5", schema, },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_anyof_2(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "anyOf", schema_set(&A, 
        newschema_p(&A, JSON_VALUE_OBJECT,
          "properties", newprops(&A,
            "foo", newschema_p(&A, JSON_VALUE_NUMBER, NULL),
            "bar", newschema_p(&A, JSON_VALUE_STRING, NULL),
            NULL),
          NULL),
        newschema_p(&A, JSON_VALUE_OBJECT,
          "properties", newprops(&A,
            "foo", newschema_p(&A, JSON_VALUE_STRING, NULL),
            "bar", newschema_p(&A, JSON_VALUE_NUMBER, NULL),
            NULL),
          NULL),
        NULL),
      NULL);

  const struct validation_test tests[] = {
    // "description": "empty object should be valid"
    { true, "{}", schema, },

    // "description": "both schemas require an object"
    { false, "1", schema, },

    // "description": "foo is a number"
    { true, "{ \"foo\" : 5 }", schema, },

    // "description": "bar is a string"
    { true, "{ \"bar\" : \"baz\" }", schema, },

    // "description": "foo is a string"
    { true, "{ \"foo\" : \"quux\" }", schema, },

    // "description": "bar is a number"
    { true, "{ \"bar\" : 7 }", schema, },

    // "description": "foo is a number and bar is a string"
    { true, "{ \"bar\" : \"this\", \"foo\" : 0.3 }", schema, },

    // "description": "foo is a string and bar is a number"
    { true, "{ \"foo\" : \"that\", \"bar\" : 0.6 }", schema, },

    // "description": "invalid: foo is a string and bar is a string"
    { false, "{ \"foo\" : \"abc\", \"bar\" : \"def\" }", schema, },

    // "description": "invalid: foo is a number and bar is a number"
    { false, "{ \"foo\" : 4, \"bar\" : 0.25 }", schema, },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_dependencies_1(void)
{
  struct arena_info A = {0};
  // schema: { "dependencies": {"quux": ["foo", "bar"], "this": ["that"]} }
  struct ast_schema *schema = newschema_p(&A, 0,
          "dep_strings", newpropnames(&A,
                           "quux", stringset(&A, "foo", "bar", NULL),
                           "this", stringset(&A, "that", NULL),
                           NULL),
          NULL);

  const struct validation_test tests[] = {
    // "description": "empty object should be valid"
    { true, "{}", schema, },

    // "description": "non-objects are valid"
    { true, "1", schema, },
    { true, "1.1", schema, },
    { true, "[]", schema, },
    { true, "true", schema, },
    { true, "false", schema, },
    { true, "null", schema, },

    // "description": "foo by itself is valid"
    { true, "{ \"foo\" : 5 }", schema, },

    // "description": "bar by itself is valid"
    { true, "{ \"bar\" : \"baz\" }", schema, },

    // "description": "foo and bar by themselves are valid"
    { true, "{ \"foo\" : \"quux\" }", schema, },

    // "description": "quux and foo/bar without bar/foo is invalid"
    { false, "{ \"quux\" : 3, \"foo\" : \"quux\" }", schema, },
    { false, "{ \"quux\" : 3, \"bar\" : true }", schema, },

    // "description": "quux and both foo and bar is valid"
    { true, "{ \"quux\" : 3, \"foo\" : \"this\", \"bar\" : false }", schema, },

    // "description": "that by itself is valid"
    { true, "{ \"that\" : 7 }", schema, },

    // "description": "this with that is valid"
    { true, "{ \"this\" : 5, \"that\" : 0.3 }", schema, },

    // "description": "this without that is invalid"
    { false, "{ \"this\" : 5, \"foo\" : 0.3 }", schema, },

    // "description": "this, that, and quux without both foo and bar is invalid"
    { false, "{ \"this\" : 5, \"that\" : 0.6, \"quux\" : false }", schema, },
    { false, "{ \"this\" : 5, \"that\" : 0.6, \"quux\" : false, \"foo\" : 3 }", schema, },
    { false, "{ \"this\" : 5, \"that\" : 0.6, \"quux\" : false, \"bar\" : [1,2,3] }", schema, },

    // "description": "quux,foo, bar, and this without that is invalid"
    { false, "{ \"this\" : 5, \"foo\" : 0.6, \"quux\" : false, \"bar\" : [1,2,3] }", schema, },

    // "description": "quux,foo,bar, this, and that is valid"
    { true, "{ \"this\" : 5, \"foo\" : 0.6, \"quux\" : false, \"bar\" : [1,2,3], \"that\" : { \"this\" : 5 } }", schema, },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

void test_items_1(void)
{
  struct arena_info A = {0};
  // schema: { "items": { "type": "integer" } }
  struct ast_schema *schema = newschema_p(&A, 0,
      "items_single", newschema(&A, JSON_VALUE_NUMBER),
      NULL);

  const struct validation_test tests[] = {
    // "description": "empty object should be valid"
    { true, "[ 1, 2, 3 ]", schema, },

    { false, "[ 1, \"x\" ]", schema, },

    // "description": "foo by itself is valid"
    { true, "{ \"foo\": \"bar\" }", schema }, 

    { true, "{ \"0\": \"invalid\", \"length\" : 1 }", schema },

    { false, NULL, NULL },
  };

  RUNTESTS(tests);
}

int main(void)
{
  test_empty_schema();

  test_type_integer();
  test_type_number();
  test_type_object();

  test_minimum();

  test_properties();

  test_minproperties_1();
  test_minproperties_2();
  test_minproperties_3();
  test_maxproperties_1();
  test_maxproperties_2();
  test_minmaxproperties_1();

  test_required();

  test_anyof_1();
  test_anyof_2();

  test_dependencies_1();

  test_items_1();

  return report_tests();
}
