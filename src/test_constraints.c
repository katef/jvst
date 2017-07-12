#include "validate_testing.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "jvst_macros.h"

enum TEST_OP {
  STOP = 0,
  TRANSLATE,
  OPTIMIZE,
  BOTH,

  // add specific optimization stages...
  //
};

struct cnode_test {
  enum TEST_OP op;
  struct ast_schema *ast;
  struct jvst_cnode *cnode;
  struct jvst_cnode *expected;
};

static int cnode_trees_equal(const char *fname, struct jvst_cnode *n1, struct jvst_cnode *n2);

static int run_test(const char *fname, const struct cnode_test *t)
{
  struct jvst_cnode *result;

  assert(t->expected != NULL);

  switch (t->op) {
    default:
    case STOP:
      fprintf(stderr, "invalid to call run_test(t) with t->op == %d\n", t->op);
      abort();
      break;

    case TRANSLATE:
      assert(t->ast != NULL);
      result = jvst_cnode_translate_ast(t->ast);
      break;

    case BOTH:
      assert(t->ast != NULL);
      // result = jvst_cnode_from_ast(t->ast);
      fprintf(stderr, "BOTH pass not implemented\n");
      abort();
      break;

    case OPTIMIZE:
      result = jvst_cnode_optimize(t->cnode);
      break;
  }

  // compare result with expected output
  return cnode_trees_equal(fname, result, t->expected);
}

// n1 is actual, n2 is expected
static int cnode_trees_equal(const char *fname, struct jvst_cnode *n1, struct jvst_cnode *n2)
{
  size_t n;
  int ret, failed;
  static char buf1[65536];
  static char buf2[65536];
  size_t i, linenum, beg, off;

  STATIC_ASSERT(sizeof buf1 == sizeof buf2, buffer_size_not_equal);

  memset(buf1, 0, sizeof buf1);
  memset(buf2, 0, sizeof buf2);

  // kind of dumb but mostly reliable way to do deep equals...  generate
  // text dumps and compare
  // 
  // XXX - replace with an actual comparison
  if (jvst_cnode_dump(n1, buf1, sizeof buf1) != 0) {
    fprintf(stderr, "buffer for node 1 not large enough (currently %zu bytes)\n",
        sizeof buf1);
  }

  if (jvst_cnode_dump(n2, buf2, sizeof buf2) != 0) {
    fprintf(stderr, "buffer for node 2 not large enough (currently %zu bytes)\n",
        sizeof buf2);
  }

  if (strncmp(buf1, buf2, sizeof buf1) == 0) {
    // fprintf(stderr, "TREE:\n%s\n", buf1);
    return 1;
  }

  /*
  fprintf(stderr,
      "test %s cnode trees are not equal:\n"
      "Expected tree:\n%s\n\n"
      "Actual tree:\n%s\n",
      fname, buf2,buf1);
      */

  fprintf(stderr, "test %s cnode trees are not equal:\n", fname);
  {
    size_t i,n,l;

    fprintf(stderr, "Expected tree:\n");
    l = 1;
    fprintf(stderr, "%3zu | ", l);
    for (i=0; (i < sizeof buf2) && buf2[i] != '\0'; i++) {
      fputc(buf2[i], stderr);
      if (buf2[i] == '\n') {
        l++;
        fprintf(stderr, "%3zu | ", l);
      }
    }
    fprintf(stderr, "\n\n");

    fprintf(stderr, "Actual tree:\n");
    l = 1;
    fprintf(stderr, "%3zu | ", l);
    for (i=0; (i < sizeof buf1) && buf1[i] != '\0'; i++) {
      fputc(buf1[i], stderr);
      if (buf1[i] == '\n') {
        l++;
        fprintf(stderr, "%3zu | ", l);
      }
    }
  }
  fprintf(stderr, "\n\n");

  // slightly tedious job of finding first difference and printing out
  // both up to that point...
  for (i=0, linenum=1, off=0; i < sizeof buf1; i++) {
    size_t j;
    char line1[256], line2[256];

    if (buf1[i] == buf2[i]) {
      if (buf1[i] == '\0') {
        fprintf(stderr, "INTERNAL ERROR: cannot find difference.\n");
        abort();
      }

      if (buf1[i] == '\n') {
        size_t n;
        n = i-off;
        if (n >= sizeof line1) {
          n = sizeof line1 - 1;
        }
        if (n > 0) {
          memcpy(line1,&buf1[off],n);
          memcpy(line2,&buf2[off],n);
        }
        line1[n] = '\0';
        line2[n] = '\0';

        fprintf(stderr, "%3zu | %-40.40s | %-40.40s\n",
            linenum, line1, line2);

        linenum++;
        off = i+1;
      }

      continue;
    }

    // difference
    fprintf(stderr, "difference at line %zu, column %zu:\n", linenum, i-off+1);
    fprintf(stderr, "EXPECTED: ");
    for(j=off; j < sizeof buf2 && buf2[j] != '\n'; j++) {
      fputc(buf2[j], stderr);
    }
    fprintf(stderr, "\n");

    fprintf(stderr, "ACTUAL  : ");
    for(j=off; j < sizeof buf1 && buf1[j] != '\n'; j++) {
      fputc(buf1[j], stderr);
    }
    fprintf(stderr, "\n");

    fprintf(stderr, "DIFF    : ");
    for(j=off; j < i; j++) {
      fputc(' ', stderr);
    }
    fprintf(stderr, "^\n");

    break;
  }

  return 0;
}

#define RUNTESTS(testlist) runtests(__func__, (testlist))
static void runtests(const char *testname, const struct cnode_test tests[])
{
  int i;

  for (i=0; tests[i].op != STOP; i++) {
    ntest++;

    if (!run_test(testname, &tests[i])) {
      printf("%s_%d: failed\n", testname, i+1);
      nfail++;
    }
  }
}

static void test_xlate_empty_schema(void)
{
  struct arena_info A = {0};

  const struct cnode_test tests[] = {
    { TRANSLATE, empty_schema(), NULL, newcnode_switch(&A, 1, SJP_NONE) },
    { STOP },
  };

  RUNTESTS(tests);
}

static void test_xlate_type_number(void)
{
  struct arena_info A = {0};
  struct ast_schema schema = {
    .types = JSON_VALUE_NUMBER,
  };

  const struct cnode_test tests[] = {
    { TRANSLATE, &schema, NULL, newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE) },
    { STOP },
  };

  RUNTESTS(tests);
}

static void test_xlate_type_object(void)
{
  struct arena_info A = {0};
  struct ast_schema schema = {
    .types = JSON_VALUE_OBJECT,
  };

  const struct cnode_test tests[] = {
    { TRANSLATE, &schema, NULL, newcnode_switch(&A, 0, SJP_OBJECT_BEG, newcnode_valid(), SJP_NONE) },
    { STOP },
  };

  RUNTESTS(tests);
}

static void test_xlate_type_several(void)
{
  struct arena_info A = {0};
  struct ast_schema schema = {
    .types = JSON_VALUE_OBJECT | JSON_VALUE_STRING,
  };

  const struct cnode_test tests[] = {
    { TRANSLATE, &schema, NULL, newcnode_switch(&A, 0,
        SJP_OBJECT_BEG, newcnode_valid(),
        SJP_STRING, newcnode_valid(),
        SJP_NONE) },
    { STOP },
  };

  RUNTESTS(tests);
}

static void test_xlate_type_integer(void)
{
  struct arena_info A = {0};
  struct ast_schema schema = {
    .types = JSON_VALUE_INTEGER,
  };

  const struct cnode_test tests[] = {
    {
      TRANSLATE, &schema, NULL, newcnode_switch(&A, 0,
        SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER),
        SJP_NONE)
    },
    { STOP },
  };

  RUNTESTS(tests);
}

void test_xlate_minimum(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "minimum", 1.1,
      NULL);

  const struct cnode_test tests[] = {
    {
      TRANSLATE, schema, NULL, newcnode_switch(&A, 1,
        SJP_NUMBER, newcnode_bool(&A, JVST_CNODE_AND,
                      newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
                      newcnode_valid(),
                      NULL),
        SJP_NONE),
    },
    { STOP },
  };

  RUNTESTS(tests);
}

void test_xlate_properties(void)
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

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct cnode_test tests[] = {
    {
      TRANSLATE, &schema, NULL,
        newcnode_switch(&A, 1,
          SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                            newcnode_propset(&A,
                              newcnode_prop_match(&A, RE_LITERAL, "foo",
                                newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),
                              newcnode_prop_match(&A, RE_LITERAL, "bar",
                                newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                              NULL),
                            newcnode_valid(),
                            NULL),
          SJP_NONE),
    },
    { STOP },
  };

  RUNTESTS(tests);
}

void test_xlate_minproperties_1(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "minProperties", 1,
      NULL);

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct cnode_test tests[] = {
    {
      TRANSLATE, schema, NULL,
        newcnode_switch(&A, 1,
          SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                            newcnode_counts(&A, 1, 0),
                            newcnode_valid(),
                            NULL),
          SJP_NONE),
    },
    { STOP },
  };

  RUNTESTS(tests);
}

void test_xlate_minproperties_2(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "minProperties", 1,
      "properties", newprops(&A,
        "foo", newschema(&A, JSON_VALUE_NUMBER), // XXX - JSON_VALUE_INTEGER
        "bar", newschema(&A, JSON_VALUE_STRING),
        NULL),
      NULL);

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct cnode_test tests[] = {
    {
      TRANSLATE, schema, NULL,
        newcnode_switch(&A, 1,
          SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                            newcnode_counts(&A, 1, 0),
                            newcnode_bool(&A,JVST_CNODE_AND,
                              newcnode_propset(&A,
                                newcnode_prop_match(&A, RE_LITERAL, "foo",
                                  newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),
                                newcnode_prop_match(&A, RE_LITERAL, "bar",
                                  newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                                NULL),
                              newcnode_valid(),
                              NULL),
                            NULL),
          SJP_NONE),
    },
    { STOP },
  };

  RUNTESTS(tests);
}

void test_xlate_minproperties_3(void)
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

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct cnode_test tests[] = {
    {
      TRANSLATE, schema, NULL,
        newcnode_switch(&A, 1,
          SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                            newcnode_counts(&A, 1, 0),
                            newcnode_bool(&A,JVST_CNODE_AND,
                              newcnode_propset(&A,
                                newcnode_prop_match(&A, RE_LITERAL, "foo",
                                  newcnode_switch(&A, 0,
                                    SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                                                      newcnode_counts(&A, 1, 0),
                                                      newcnode_valid(),
                                                      NULL),
                                    SJP_NONE)),
                                newcnode_prop_match(&A, RE_LITERAL, "bar",
                                  newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                                NULL),
                              newcnode_valid(),
                              NULL),
                            NULL),
          SJP_NONE),
    },
    { STOP },
  };

  RUNTESTS(tests);
}

void test_xlate_maxproperties_1(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "maxProperties", 2,
      NULL);

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct cnode_test tests[] = {
    {
      TRANSLATE, schema, NULL,
        newcnode_switch(&A, 1,
          SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                            newcnode_counts(&A, 0, 2),
                            newcnode_valid(),
                            NULL),
          SJP_NONE),
    },
    { STOP },
  };

  RUNTESTS(tests);
}

void test_xlate_maxproperties_2(void)
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

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct cnode_test tests[] = {
    {
      TRANSLATE, schema, NULL,
        newcnode_switch(&A, 1,
          SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                            newcnode_counts(&A, 0, 1),
                            newcnode_bool(&A,JVST_CNODE_AND,
                              newcnode_propset(&A,
                                newcnode_prop_match(&A, RE_LITERAL, "foo",
                                  newcnode_switch(&A, 0,
                                    SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                                                      newcnode_counts(&A, 0, 1),
                                                      newcnode_valid(),
                                                      NULL),
                                    SJP_NONE)),
                                newcnode_prop_match(&A, RE_LITERAL, "bar",
                                  newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                                NULL),
                              newcnode_valid(),
                              NULL),
                            NULL),
          SJP_NONE),
    },
    { STOP },
  };

  RUNTESTS(tests);
}

void test_xlate_minmaxproperties_1(void)
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

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct cnode_test tests[] = {
    {
      TRANSLATE, schema, NULL,
        newcnode_switch(&A, 1,
          SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                            newcnode_counts(&A, 1, 1),
                            newcnode_bool(&A,JVST_CNODE_AND,
                              newcnode_propset(&A,
                                newcnode_prop_match(&A, RE_LITERAL, "foo",
                                  newcnode_switch(&A, 0,
                                    SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                                                      newcnode_counts(&A, 1, 2),
                                                      newcnode_valid(),
                                                      NULL),
                                    SJP_NONE)),
                                newcnode_prop_match(&A, RE_LITERAL, "bar",
                                  newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                                NULL),
                              newcnode_valid(),
                              NULL),
                            NULL),
          SJP_NONE),
    },
    { STOP },
  };

  RUNTESTS(tests);
}

void test_xlate_required(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "properties", newprops(&A,
        "foo", empty_schema(),
        "bar", empty_schema(),
        NULL),
      "required", stringset(&A, "foo", NULL),
      NULL);

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct cnode_test tests[] = {
    {
      TRANSLATE, schema, NULL,
        newcnode_switch(&A, 1,
          SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                            newcnode_required(&A, stringset(&A, "foo", NULL)),
                            newcnode_bool(&A,JVST_CNODE_AND,
                              newcnode_propset(&A,
                                newcnode_prop_match(&A, RE_LITERAL, "foo", newcnode_switch(&A, 1, SJP_NONE)),
                                newcnode_prop_match(&A, RE_LITERAL, "bar", newcnode_switch(&A, 1, SJP_NONE)),
                                NULL),
                              newcnode_valid(),
                              NULL),
                            NULL),
          SJP_NONE),
    },
    { STOP },
  };

  RUNTESTS(tests);
}

void test_xlate_dependencies(void)
{
  struct arena_info A = {0};

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct cnode_test tests[] = {
    {
      TRANSLATE, 
      // schema: { "dependencies": {"bar": ["foo"]} }
      newschema_p(&A, 0,
          "dep_strings", newpropnames(&A, "bar", stringset(&A, "foo", NULL), NULL),
          NULL),

      NULL,

      newcnode_switch(&A, 1,
        SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_AND,
                          newcnode_bool(&A, JVST_CNODE_OR,
                            newcnode_required(&A, stringset(&A, "bar", "foo", NULL)),
                            newcnode_propset(&A,
                              newcnode_prop_match(&A, RE_LITERAL, "bar", newcnode_invalid()),
                              NULL),
                            NULL),
                          newcnode_valid(),
                          NULL),
        SJP_NONE),
    },

    {
      TRANSLATE, 
      // schema: { "dependencies": {"quux": ["foo", "bar"]} }
      newschema_p(&A, 0,
          "dep_strings", newpropnames(&A, "quux", stringset(&A, "foo", "bar", NULL), NULL),
          NULL),

      NULL,

      newcnode_switch(&A, 1,
        SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_AND,
                          newcnode_bool(&A, JVST_CNODE_OR,
                            newcnode_required(&A, stringset(&A, "quux", "foo", "bar", NULL)),
                            newcnode_propset(&A,
                              newcnode_prop_match(&A, RE_LITERAL, "quux", newcnode_invalid()),
                              NULL),
                            NULL),
                          newcnode_valid(),
                          NULL),
        SJP_NONE),
    },

    {
      TRANSLATE, 
      // schema: { "dependencies": {"quux": ["foo", "bar"], "this": ["that"]} }
      newschema_p(&A, 0,
          "dep_strings", newpropnames(&A,
                           "quux", stringset(&A, "foo", "bar", NULL),
                           "this", stringset(&A, "that", NULL),
                           NULL),
          NULL),

      NULL,

      newcnode_switch(&A, 1,
        SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_AND,
                          newcnode_bool(&A, JVST_CNODE_OR,
                            newcnode_required(&A, stringset(&A, "quux", "foo", "bar", NULL)),
                            newcnode_propset(&A,
                              newcnode_prop_match(&A, RE_LITERAL, "quux", newcnode_invalid()),
                              NULL),
                            NULL),
                          newcnode_bool(&A, JVST_CNODE_OR,
                            newcnode_required(&A, stringset(&A, "this", "that", NULL)),
                            newcnode_propset(&A,
                              newcnode_prop_match(&A, RE_LITERAL, "this", newcnode_invalid()),
                              NULL),
                            NULL),
                          newcnode_valid(),
                          NULL),
        SJP_NONE),
    },

    {
      TRANSLATE, 
      // schema: { "dependencies": {"quux": ["foo", "bar"]} }
      // schema: {
      //   "dependencies": {
      //     "bar": {
      //       "properties": {
      //         "foo": {"type": "integer"},
      //         "bar": {"type": "integer"}
      //       }
      //     }
      //   }
      // },
      newschema_p(&A, 0,
          "dep_schema",
          newprops(&A, "bar", newschema_p(&A, 0,
                                "properties", newprops(&A,
                                  "foo", newschema(&A, JSON_VALUE_INTEGER),
                                  "bar", newschema(&A, JSON_VALUE_INTEGER),
                                  NULL),
                                NULL),
            NULL),
          NULL),

      NULL,

      newcnode_bool(&A, JVST_CNODE_AND,
          newcnode_switch(&A, 1, SJP_NONE),
          newcnode_bool(&A, JVST_CNODE_OR,
            newcnode_bool(&A, JVST_CNODE_AND,
              newcnode_switch(&A, 0, 
                SJP_OBJECT_BEG, newcnode_required(&A, stringset(&A, "bar", NULL)),
                SJP_NONE),
              newcnode_switch(&A, 1, 
                SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_AND,
                                  newcnode_propset(&A,
                                    newcnode_prop_match(&A, RE_LITERAL, "foo", 
                                      newcnode_switch(&A, 0, 
                                        SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER),
                                        SJP_NONE)),
                                    newcnode_prop_match(&A, RE_LITERAL, "bar", 
                                      newcnode_switch(&A, 0, 
                                        SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER),
                                        SJP_NONE)),
                                    NULL),
                                  newcnode_valid(),
                                  NULL),
                SJP_NONE),
              NULL),
            newcnode_switch(&A, 1, 
              SJP_OBJECT_BEG, newcnode_propset(&A,
                                newcnode_prop_match(&A, RE_LITERAL, "bar", newcnode_invalid()),
                                NULL),
              SJP_NONE),
            NULL),
          NULL),
    },

    { STOP },
  };

  RUNTESTS(tests);
}

void test_xlate_anyof_allof_oneof_1(void)
{
  struct arena_info A = {0};

  const struct cnode_test tests[] = {
    {
      TRANSLATE,
      newschema_p(&A, 0,
          "anyOf", schema_set(&A, 
            newschema_p(&A, JSON_VALUE_INTEGER, NULL),
            newschema_p(&A, 0, "minimum", 2.0, NULL),
            NULL),
          NULL),

      NULL,

      newcnode_bool(&A, JVST_CNODE_AND,
        newcnode_bool(&A, JVST_CNODE_OR,
          newcnode_switch(&A, 0,
            SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER),
            SJP_NONE),
          newcnode_switch(&A, 1,
            SJP_NUMBER, newcnode_bool(&A, JVST_CNODE_AND,
                          newcnode_range(&A, JVST_CNODE_RANGE_MIN, 2.0, 0.0),
                          newcnode_valid(),
                          NULL),
            SJP_NONE),
          NULL),
        newcnode_switch(&A, 1, SJP_NONE),
        NULL),
    },

    {
      TRANSLATE,
      newschema_p(&A, 0,
          "allOf", schema_set(&A, 
            newschema_p(&A, JSON_VALUE_INTEGER, NULL),
            newschema_p(&A, 0, "minimum", 2.0, NULL),
            NULL),
          NULL),

      NULL,

      newcnode_bool(&A, JVST_CNODE_AND,
        newcnode_bool(&A, JVST_CNODE_AND,
          newcnode_switch(&A, 0,
            SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER),
            SJP_NONE),
          newcnode_switch(&A, 1,
            SJP_NUMBER, newcnode_bool(&A, JVST_CNODE_AND,
                          newcnode_range(&A, JVST_CNODE_RANGE_MIN, 2.0, 0.0),
                          newcnode_valid(),
                          NULL),
            SJP_NONE),
          NULL),
        newcnode_switch(&A, 1, SJP_NONE),
        NULL),
    },

    {
      TRANSLATE,
      newschema_p(&A, 0,
          "oneOf", schema_set(&A, 
            newschema_p(&A, JSON_VALUE_INTEGER, NULL),
            newschema_p(&A, 0, "minimum", 2.0, NULL),
            NULL),
          NULL),

      NULL,

      newcnode_bool(&A, JVST_CNODE_AND,
        newcnode_bool(&A, JVST_CNODE_XOR,
          newcnode_switch(&A, 0,
            SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER),
            SJP_NONE),
          newcnode_switch(&A, 1,
            SJP_NUMBER, newcnode_bool(&A, JVST_CNODE_AND,
                          newcnode_range(&A, JVST_CNODE_RANGE_MIN, 2.0, 0.0),
                          newcnode_valid(),
                          NULL),
            SJP_NONE),
          NULL),
        newcnode_switch(&A, 1, SJP_NONE),
        NULL),
    },

    { STOP },
  };

  RUNTESTS(tests);
}

void test_xlate_anyof_2(void)
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

  const struct cnode_test tests[] = {
    {
      TRANSLATE, schema, NULL, newcnode_bool(&A, JVST_CNODE_AND,
          newcnode_bool(&A, JVST_CNODE_OR,
            newcnode_switch(&A, 0,
              SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_AND,
                                newcnode_propset(&A, 
                                  newcnode_prop_match(&A, RE_LITERAL, "foo",
                                    newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),
                                  newcnode_prop_match(&A, RE_LITERAL, "bar",
                                    newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                                  NULL),
                                newcnode_valid(),
                                NULL),
              SJP_NONE),

            newcnode_switch(&A, 0,
              SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_AND,
                                newcnode_propset(&A,
                                  newcnode_prop_match(&A, RE_LITERAL, "foo",
                                    newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                                  newcnode_prop_match(&A, RE_LITERAL, "bar",
                                    newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),
                                  NULL),
                                newcnode_valid(),
                                NULL),
              SJP_NONE),
            NULL),
          newcnode_switch(&A, 1, SJP_NONE),
          NULL),
    },
    { STOP },
  };

  RUNTESTS(tests);
}

static void test_simplify_ands(void)
{
  struct arena_info A = {0};

  const struct cnode_test tests[] = {
    // handle AND with only one level...
    {
      OPTIMIZE,

      NULL,

      newcnode_switch(&A, 1,
          SJP_NUMBER, newcnode_bool(&A, JVST_CNODE_AND,
                        newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
                        newcnode_valid(),
                        NULL),
          SJP_NONE),

      newcnode_switch(&A, 1,
          SJP_NUMBER, newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
          SJP_NONE),
    },

    // handle nested ANDs
    {
      OPTIMIZE,

      NULL,

      newcnode_switch(&A, 1,
          SJP_NUMBER, newcnode_bool(&A, JVST_CNODE_AND,
                        newcnode_bool(&A, JVST_CNODE_AND,
                          newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
                          newcnode_valid(),
                          NULL),
                        newcnode(&A,JVST_CNODE_NUM_INTEGER),
                        NULL),
          SJP_NONE),

      newcnode_switch(&A, 1,
          SJP_NUMBER, newcnode_bool(&A, JVST_CNODE_AND,
                        newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
                        newcnode(&A,JVST_CNODE_NUM_INTEGER),
                        NULL),
          SJP_NONE),
    },

    // handle more complex nested ANDs
    {
      OPTIMIZE,
      
      NULL,

      newcnode_switch(&A, 1,
          SJP_NUMBER, newcnode_bool(&A, JVST_CNODE_AND,
                        newcnode_bool(&A, JVST_CNODE_AND,
                          newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
                          newcnode_bool(&A, JVST_CNODE_AND,
                            newcnode(&A,JVST_CNODE_NUM_INTEGER),
                            newcnode_valid(),
                            NULL),
                          NULL),
                        newcnode_range(&A, JVST_CNODE_RANGE_MAX, 0.0, 3.2),
                        NULL),
          SJP_NONE),

      newcnode_switch(&A, 1,
          SJP_NUMBER, newcnode_bool(&A, JVST_CNODE_AND,
                        newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
                        newcnode(&A,JVST_CNODE_NUM_INTEGER),
                        newcnode_range(&A, JVST_CNODE_RANGE_MAX, 0.0, 3.2),
                        NULL),
          SJP_NONE),
    },

    { STOP },
  };

  RUNTESTS(tests);
}

void test_simplify_ored_schema(void)
{
  struct arena_info A = {0};
  const struct cnode_test tests[] = {
    {
      OPTIMIZE, NULL, 

        // initial tree
        newcnode_bool(&A, JVST_CNODE_AND,
          newcnode_bool(&A, JVST_CNODE_OR,
            newcnode_switch(&A, 0,
              SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_AND,
                                newcnode_propset(&A, 
                                  newcnode_prop_match(&A, RE_LITERAL, "foo",
                                    newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),
                                  newcnode_prop_match(&A, RE_LITERAL, "bar",
                                    newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                                  NULL),
                                newcnode_valid(),
                                NULL),
              SJP_NONE),

            newcnode_switch(&A, 0,
              SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_AND,
                                newcnode_propset(&A,
                                  newcnode_prop_match(&A, RE_LITERAL, "foo",
                                    newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                                  newcnode_prop_match(&A, RE_LITERAL, "bar",
                                    newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),
                                  NULL),
                                newcnode_valid(),
                                NULL),
              SJP_NONE),
            NULL),
          newcnode_switch(&A, 1, SJP_NONE),
          NULL),

        // optimized
        newcnode_switch(&A, 0,
          SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_OR,
                            newcnode_propset(&A, 
                              newcnode_prop_match(&A, RE_LITERAL, "foo",
                                newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),
                              newcnode_prop_match(&A, RE_LITERAL, "bar",
                                newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                              NULL),
                            newcnode_propset(&A,
                              newcnode_prop_match(&A, RE_LITERAL, "foo",
                                newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                              newcnode_prop_match(&A, RE_LITERAL, "bar",
                                newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),
                              NULL),
                            NULL),
          SJP_NONE),
    },

    {
      OPTIMIZE, 
      // schema: {
      //   "dependencies": {
      //     "bar": {
      //       "properties": {
      //         "foo": {"type": "integer"},
      //         "bar": {"type": "integer"}
      //       }
      //     }
      //   }
      // },
      NULL,

      // original cnode tree...
      newcnode_bool(&A, JVST_CNODE_AND,
          newcnode_switch(&A, 1, SJP_NONE),
          newcnode_bool(&A, JVST_CNODE_OR,
            newcnode_bool(&A, JVST_CNODE_AND,
              newcnode_switch(&A, 0, 
                SJP_OBJECT_BEG, newcnode_required(&A, stringset(&A, "bar", NULL)),
                SJP_NONE),
              newcnode_switch(&A, 1, 
                SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_AND,
                                  newcnode_propset(&A,
                                    newcnode_prop_match(&A, RE_LITERAL, "foo", 
                                      newcnode_switch(&A, 0, 
                                        SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER),
                                        SJP_NONE)),
                                    newcnode_prop_match(&A, RE_LITERAL, "bar", 
                                      newcnode_switch(&A, 0, 
                                        SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER),
                                        SJP_NONE)),
                                    NULL),
                                  newcnode_valid(),
                                  NULL),
                SJP_NONE),
              NULL),
            newcnode_switch(&A, 1, 
              SJP_OBJECT_BEG, newcnode_propset(&A,
                                newcnode_prop_match(&A, RE_LITERAL, "bar", newcnode_invalid()),
                                NULL),
              SJP_NONE),
            NULL),
          NULL),

      // simplified cnode tree
      newcnode_switch(&A, 1, 
          SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_OR,
                            newcnode_bool(&A, JVST_CNODE_AND,
                              newcnode_required(&A, stringset(&A, "bar", NULL)),
                              newcnode_propset(&A,
                                newcnode_prop_match(&A, RE_LITERAL, "foo", 
                                  newcnode_switch(&A, 0, 
                                    SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER),
                                    SJP_NONE)),
                                newcnode_prop_match(&A, RE_LITERAL, "bar", 
                                  newcnode_switch(&A, 0, 
                                    SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER),
                                    SJP_NONE)),
                                NULL),
                              NULL),
                            newcnode_propset(&A,
                              newcnode_prop_match(&A, RE_LITERAL, "bar", newcnode_invalid()),
                              NULL),
                            NULL),
          SJP_NONE),
    },
    { STOP },
  };

  RUNTESTS(tests);
}

int main(void)
{
  test_xlate_empty_schema();

  test_xlate_type_number();
  test_xlate_type_object();
  test_xlate_type_several();
  test_xlate_type_integer();

  test_xlate_minimum();

  test_xlate_properties();

  test_xlate_minproperties_1();
  test_xlate_minproperties_2();
  test_xlate_minproperties_3();
  test_xlate_maxproperties_1();
  test_xlate_maxproperties_2();
  test_xlate_minmaxproperties_1();

  test_xlate_required();
  test_xlate_dependencies();

  test_xlate_anyof_allof_oneof_1();
  test_xlate_anyof_2();

  test_simplify_ands();
  test_simplify_ored_schema();

  return report_tests();
}
