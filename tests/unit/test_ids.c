#include "validate_testing.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "jvst_macros.h"

#include "sjp_lexer.h"
#include "sjp_testing.h"

#include "parser.h"
#include "validate_constraints.h"
#include "idtbl.h"

struct id_test {
  const char *schema;
  struct id_pair *pairs;
};

static int
run_test(const char *fname, const struct id_test *t)
{
  struct sjp_lexer l = { 0 };
  struct ast_schema ast = { 0 };
  struct jvst_cnode *tree;
  struct jvst_id_table *tbl;
  struct id_pair *pair;
  size_t i,len;
  int ret;
  char buf[65536] = { 0 };

  sjp_lexer_init(&l);
  len = strlen(t->schema);
  assert(len < sizeof buf);

  memcpy(buf, t->schema, len);
  sjp_lexer_more(&l, buf, len);
  parse(&l, &ast);

  tbl = jvst_id_table_new();
  tree = jvst_cnode_translate_ast_with_ids(&ast, tbl);

  jvst_id_table_dump_ids(tbl);

  assert(tree != NULL);

  ret = 1;
  for (pair = t->pairs; pair != NULL; pair = pair->next) {
    struct jvst_cnode *ctree;
    const char *id;

    id = pair->id;
    ctree = jvst_id_table_lookup_cstr(tbl, id);
    if (ctree == NULL) {
      fprintf(stderr, "id '%s' does not exit\n", id);
      ret = 0;
      continue;
    }

    ret = ret && cnode_trees_equal(fname, ctree, pair->cnode);
  }

  jvst_id_table_delete(tbl);

  return ret;
}

#define UNIMPLEMENTED(testlist) do{ nskipped++; (void)testlist; }while(0)
#define RUNTESTS(testlist) runtests(__func__, (testlist))
static void runtests(const char *testname, const struct id_test tests[])
{
  int i;

  (void)testname;

  for (i=0; tests[i].schema != NULL; i++) {
    ntest++;

    if (!run_test(testname, &tests[i])) {
      printf("%s[%d]: failed\n", testname, i+1);
      nfail++;
    }
  }
}

static void test_path_root(void)
{
  struct arena_info A = {0};

  const struct id_test tests[] = {
    {
      "{}",
      new_idpairs(
          new_idpair(&A, "#", newcnode_switch(&A, 1, SJP_NONE)),
          NULL
      ),
    },

    { NULL },
  };

  RUNTESTS(tests);
}

static void test_path_properties(void)
{
  struct arena_info A = {0};

  const struct id_test tests[] = {
    {
      "{ \"properties\" : { \"foo\" : { \"type\" : \"integer\" } } }",
      new_idpairs(
          new_idpair(&A, "#",
            newcnode_switch(&A, 1,
              SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                                newcnode_propset(&A,
                                  newcnode_prop_match(&A, RE_LITERAL, "foo",
                                    newcnode_switch(&A, 0, SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER), SJP_NONE)),
                                  NULL),
                                newcnode_valid(),
                                NULL),
              SJP_NONE)),

          new_idpair(&A, "#/properties/foo",
            newcnode_switch(&A, 0, SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER), SJP_NONE)),
          NULL
      ),
    },

    { NULL },
  };

  RUNTESTS(tests);
}

static void test_path_dependencies(void)
{
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
  struct arena_info A = {0};

  const struct id_test tests[] = {
    {
      "{ \"dependencies\" : { "
        "\"bar\" : "
          "{ \"properties\" : "
            "{ "
              "\"foo\" : { \"type\" : \"number\" }, "
              "\"bar\" : { \"type\" : \"string\" } "
            "} "
          "} "
        "} "
      "}",

      new_idpairs(
          new_idpair(&A, "#/dependencies/bar",
            newcnode_switch(&A, 1,
            SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                              newcnode_propset(&A,
                                newcnode_prop_match(&A, RE_LITERAL, "bar",
                                  newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                                newcnode_prop_match(&A, RE_LITERAL, "foo",
                                  newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),
                                NULL),
                              newcnode_valid(),
                              NULL),
              SJP_NONE)),

          new_idpair(&A, "#/dependencies/bar/properties/foo",
            newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),

          new_idpair(&A, "#/dependencies/bar/properties/bar",
            newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
          NULL
      ),
    },

    { NULL },
  };

  RUNTESTS(tests);
}

static void test_ids(void)
{
  struct arena_info A = {0};

  // FIXME - id requires handling URIs correctly, which we don't
  // currently do.  Thus, this test isn't quite right.
  const struct id_test tests[] = {
    {
      "{ \"properties\" : { \"foo\" : { \"id\" : \"foo-thing\", \"type\" : \"integer\" } } }",
      new_idpairs(
          new_idpair(&A, "#",
            newcnode_switch(&A, 1,
              SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                                newcnode_propset(&A,
                                  newcnode_prop_match(&A, RE_LITERAL, "foo",
                                    newcnode_switch(&A, 0, SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER), SJP_NONE)),
                                  NULL),
                                newcnode_valid(),
                                NULL),
              SJP_NONE)),

          new_idpair(&A, "#/properties/foo",
            newcnode_switch(&A, 0, SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER), SJP_NONE)),

          new_idpair(&A, "foo-thing",
            newcnode_switch(&A, 0, SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER), SJP_NONE)),

          NULL
      ),
    },

    { NULL },
  };

  RUNTESTS(tests);
}

int main(void)
{
  test_path_root();
  test_path_properties();
  test_path_dependencies();
  test_ids();

  return report_tests();
}
