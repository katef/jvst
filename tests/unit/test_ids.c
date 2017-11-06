#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "jvst_macros.h"

#include "sjp_lexer.h"
#include "sjp_testing.h"

#include "parser.h"
#include "idtbl.h"
#include "validate_constraints.h"
#include "validate_ir.h"

#include "validate_testing.h"

// provided in ir_testing.c
int ir_trees_equal(const char *fname, struct jvst_ir_stmt *n1, struct jvst_ir_stmt *n2);

#define URI_BASE "http://example.com"

enum id_test_type {
  IDS,
  ROOTS,
  IR_TRANSLATE,
  IR_LINEARIZE,
  STOP,
};

struct id_test {
  enum id_test_type type;
  const char *schema;
  struct id_pair *pairs;
  struct ir_pair *ir_pairs;
};

static int
run_test(const char *fname, const struct id_test *t)
{
  struct sjp_lexer l = { 0 };
  struct ast_schema ast = { 0 };
  struct jvst_cnode_forest *forest;
  size_t i,len;
  int ret;
  char buf[65536] = { 0 };

  sjp_lexer_init(&l);
  len = strlen(t->schema);
  assert(len < sizeof buf);

  memcpy(buf, t->schema, len);
  sjp_lexer_more(&l, buf, len);
  parse(&l, &ast);

  forest = jvst_cnode_translate_ast_with_ids(&ast);
  assert(forest != NULL);

  // jvst_cnode_id_table_dump_ids(forest->all_ids);

  ret = 1;

  switch (t->type) {
  case IDS:
    {
      struct id_pair *pair;
      for (pair = t->pairs; pair != NULL; pair = pair->next) {
        struct jvst_cnode *ctree;
        const char *id;

        id = pair->id;
        ctree = jvst_cnode_id_table_lookup_cstr(forest->all_ids, id);
        if (ctree == NULL) {
          fprintf(stderr, "id '%s' does not exit\n", id);
          ret = 0;
          continue;
        }

        if (!cnode_trees_equal(fname, ctree, pair->cnode)) {
          ret = 0;
        }
      }
    }
    break;

  case ROOTS:
    {
      struct id_pair *pair;
      size_t i;

      for (i=0, pair = t->pairs; pair != NULL; i++, pair = pair->next) {
        struct jvst_cnode *ctree;

        if (i >= forest->len) {
          fprintf(stderr, "expected too many roots (only %zu)\n",
              forest->len);
          ret = 0;
          break;
        }

        ctree = forest->trees[i];
        assert(ctree != NULL);
        if (!cnode_trees_equal(fname, ctree, pair->cnode)) {
          ret = 0;
        }
      }

      if (i < forest->len) {
        fprintf(stderr, "too few roots (expected %zu, forest has %zu)\n",
            i, forest->len);
        ret = 0;
      }
    }
    break;

  case IR_TRANSLATE:
    {
      struct jvst_ir_forest *ir_forest;
      struct ir_pair *pair;
      size_t i;

      jvst_cnode_simplify_forest(forest);
      jvst_cnode_canonify_forest(forest);

      ir_forest = jvst_ir_translate_forest(forest);
      assert(ir_forest != NULL);
      assert(ir_forest->len == forest->len);

      assert(ir_forest->refs != NULL);
      size_t nrefs = jvst_ir_id_table_nitems(ir_forest->refs);
      size_t nrefids = jvst_cnode_id_table_nitems(forest->ref_ids);
      assert(nrefs == nrefids);

      for (i=0, pair = t->ir_pairs; pair != NULL; i++, pair = pair->next) {
        struct jvst_ir_stmt *ir;

        if (i >= ir_forest->len) {
          fprintf(stderr, "expected too many roots (only %zu)\n",
              ir_forest->len);
          ret = 0;
          break;
        }

        ir = ir_forest->trees[i];
        assert(ir != NULL);
        if (!ir_trees_equal(fname, ir, pair->ir)) {
          ret = 0;
        }
      }

      if (i < ir_forest->len) {
        fprintf(stderr, "too few roots (expected %zu, IR forest has %zu)\n",
            i, ir_forest->len);
        ret = 0;
      }

      jvst_ir_forest_free(ir_forest);
    }
    break;

  case IR_LINEARIZE:
    {
      struct jvst_ir_forest *ir_forest;
      struct jvst_ir_stmt *linear;
      struct ir_pair *pair;
      size_t i;

      jvst_cnode_simplify_forest(forest);
      jvst_cnode_canonify_forest(forest);

      ir_forest = jvst_ir_translate_forest(forest);
      assert(ir_forest != NULL);
      assert(ir_forest->len == forest->len);

      linear = jvst_ir_linearize_forest(ir_forest);

      assert(t->ir_pairs != NULL);
      assert(t->ir_pairs->ir != NULL);

      ret = ir_trees_equal(fname, linear, t->ir_pairs->ir);

      jvst_ir_forest_free(ir_forest);
    }
    break;

  case STOP:
    break;
  }

  jvst_cnode_forest_delete(forest);

  return ret;
}

// ir_testing.h defines this and we need to redefine it
// XXX - can we remove this from ir_testing.h?
#undef RUNTESTS

#define UNIMPLEMENTED(testlist) do{ nskipped++; (void)testlist; }while(0)
#define RUNTESTS(testlist) runtests(__func__, (testlist))
static void runtests(const char *testname, const struct id_test tests[])
{
  int i;

  (void)testname;

  // printf("test %s\n", testname);
  for (i=0; tests[i].type != STOP; i++) {
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
      IDS,
      "{}",
      new_idpairs(
          new_idpair(&A, "#", newcnode_switch(&A, 1, SJP_NONE)),
          NULL
      ),
    },

    { STOP },
  };

  RUNTESTS(tests);
}

static void test_definitions(void)
{
  struct arena_info A = {0};

  const struct id_test tests[] = {
    {
      IDS,
      "{ \"definitions\" : { \"foo\" : { \"type\" : \"number\" } } }",
      new_idpairs(
          new_idpair(&A, "#", newcnode_switch(&A, 1, SJP_NONE)),
          new_idpair(&A, "#/definitions/foo", newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),
          NULL
      ),
    },

    { STOP },
  };

  RUNTESTS(tests);

}

static void test_path_properties(void)
{
  struct arena_info A = {0};

  const struct id_test tests[] = {
    {
      IDS,
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

    { STOP },
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
      IDS,
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

    { STOP },
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
      IDS,
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

    { STOP },
  };

  RUNTESTS(tests);
}

static void test_rerooted_refs(void)
{
  struct arena_info A = {0};

  // FIXME - id requires handling URIs correctly, which we don't
  // currently do.  Thus, this test isn't quite right.
  const struct id_test tests[] = {
    {
      ROOTS,
      "{ \"properties\" : { \"foo\" : { \"$ref\" : \"#\" } } }",
      new_idpairs(
          new_idpair(&A, "",
            newcnode_switch(&A, 1,
              SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_AND,
                                newcnode_propset(&A,
                                  newcnode_prop_match(&A, RE_LITERAL, "foo",
                                    newcnode_ref(&A, "#")),
                                  NULL),
                                newcnode_valid(),
                                NULL),
              SJP_NONE)),

          NULL),
    },

    {
      ROOTS,
      "{ \"properties\" : { \"foo\" : { \"type\" : \"integer\" }, "
        "\"bar\" : { \"$ref\" : \"#/properties/foo\" } } }",
      new_idpairs(
          new_idpair(&A, "",
            newcnode_switch(&A, 1,
              SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_AND,
                                newcnode_propset(&A,
                                  newcnode_prop_match(&A, RE_LITERAL, "bar",
                                    newcnode_ref(&A, "#/properties/foo")),
                                  newcnode_prop_match(&A, RE_LITERAL, "foo",
                                    newcnode_ref(&A, "#/properties/foo")),
                                  NULL),
                                newcnode_valid(),
                                NULL),
              SJP_NONE)),

          new_idpair(&A, "",
            newcnode_switch(&A, 0,
              SJP_NUMBER, newcnode(&A,JVST_CNODE_NUM_INTEGER),
              SJP_NONE)),

          NULL),
    },

    { STOP },
  };

  RUNTESTS(tests);
}

static void test_ir_translation(void)
{
  struct arena_info A = {0};

  // FIXME - id requires handling URIs correctly, which we don't
  // currently do.  Thus, this test isn't quite right.
  const struct id_test tests[] = {
    {
      IR_TRANSLATE,
      "{ \"properties\" : { \"foo\" : { \"$ref\" : \"#\" } } }",
      NULL,
      new_irpairs(&A,
          "#", newir_frame(&A,
                 newir_matcher(&A, 0, "dfa"),
                 newir_stmt(&A, JVST_IR_STMT_TOKEN),
                 newir_if(&A, newir_istok(&A, SJP_OBJECT_BEG),
                   newir_seq(&A,
                     newir_loop(&A, "L_OBJ", 0,
                       newir_stmt(&A, JVST_IR_STMT_TOKEN),
                       newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                         newir_break(&A, "L_OBJ", 0),
                         newir_seq(&A,                                 // unnecessary SEQ should be removed in the future
                           newir_match(&A, 0,
                             // no match
                             newir_case(&A, 0, 
                               NULL,
                               newir_stmt(&A, JVST_IR_STMT_CONSUME)
                             ),

                             // match "foo"
                             newir_case(&A, 1,
                               newmatchset(&A, RE_LITERAL,  "foo", -1),
                               newir_callid(&A, "#")
                             ),

                             NULL
                           ),
                           NULL
                         )
                       ),
                       NULL
                     ),
                     newir_stmt(&A, JVST_IR_STMT_VALID),
                     NULL
                   ),

                   newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                     newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                     newir_if(&A, newir_istok(&A, SJP_ARRAY_END),
                       newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                       newir_seq(&A,
                         newir_stmt(&A, JVST_IR_STMT_CONSUME),
                         newir_stmt(&A, JVST_IR_STMT_VALID),
                         NULL
                       )
                     )
                   )
                 ),
                 NULL
               ),
          NULL
        ),
    },

    {
      IR_TRANSLATE,
      "{ \"properties\" : { \"foo\" : { \"type\" : \"integer\" }, "
        "\"bar\" : { \"$ref\" : \"#/properties/foo\" } } }",
      NULL,
      new_irpairs(&A,
          "#",
          newir_frame(&A,
            newir_matcher(&A, 0, "dfa"),
            newir_stmt(&A, JVST_IR_STMT_TOKEN),
            newir_if(&A, newir_istok(&A, SJP_OBJECT_BEG),
              newir_seq(&A,
                newir_loop(&A, "L_OBJ", 0,
                  newir_stmt(&A, JVST_IR_STMT_TOKEN),
                  newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                    newir_break(&A, "L_OBJ", 0),
                    newir_seq(&A,                                 // unnecessary SEQ should be removed in the future
                      newir_match(&A, 0,
                        // no match
                        newir_case(&A, 0, 
                          NULL,
                          newir_stmt(&A, JVST_IR_STMT_CONSUME)
                        ),
                 
                        // match "foo"
                        newir_case(&A, 1,
                          newmatchset(&A, RE_LITERAL,  "bar", -1),
                          newir_callid(&A, "#/properties/foo")
                        ),
                 
                        // match "foo"
                        newir_case(&A, 2,
                          newmatchset(&A, RE_LITERAL,  "foo", -1),
                          newir_callid(&A, "#/properties/foo")
                        ),
                 
                        NULL
                      ),
                      NULL
                    )
                  ),
                  NULL
                ),
                newir_stmt(&A, JVST_IR_STMT_VALID),
                NULL
              ),

              newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                newir_if(&A, newir_istok(&A, SJP_ARRAY_END),
                  newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                  newir_seq(&A,
                    newir_stmt(&A, JVST_IR_STMT_CONSUME),
                    newir_stmt(&A, JVST_IR_STMT_VALID),
                    NULL
                  )
                )
              )
            ),

            NULL
          ),

          "#/properties/foo",
          newir_frame(&A,
            newir_stmt(&A, JVST_IR_STMT_TOKEN),
            newir_if(&A, newir_istok(&A, SJP_NUMBER),
              newir_if(&A, newir_isint(&A, newir_expr(&A, JVST_IR_EXPR_TOK_NUM)),
                newir_seq(&A,
                  newir_stmt(&A, JVST_IR_STMT_CONSUME),
                  newir_stmt(&A, JVST_IR_STMT_VALID),
                  NULL
                ),
                newir_invalid(&A, JVST_INVALID_NOT_INTEGER, "number is not an integer")),
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
            ),
            NULL
          ),

          NULL
        ),
    },

    { STOP },
  };

  RUNTESTS(tests);
}

static void test_ir_linearize(void)
{
  struct arena_info A = {0};

  // FIXME - id requires handling URIs correctly, which we don't
  // currently do.  Thus, this test isn't quite right.
  const struct id_test tests[] = {
    {
      IR_LINEARIZE,
      "{ \"properties\" : { \"foo\" : { \"$ref\" : \"#\" } } }",
      NULL,
      new_irpairs(&A, "",
        newir_program(&A,
          newir_frame(&A, frameindex, 1,
            newir_matcher(&A, 0, "dfa"),

            newir_block(&A, 0, "entry",
              newir_stmt(&A, JVST_IR_STMT_TOKEN),
              newir_cbranch(&A,
                newir_istok(&A, SJP_OBJECT_BEG),
                4, "loop",
                14, "false"),
              NULL
            ),

            newir_block(&A, 14, "false",
              newir_cbranch(&A,
                newir_istok(&A, SJP_OBJECT_END),
                17, "invalid_1",
                18, "false"),
              NULL
            ),

            newir_block(&A, 18, "false",
              newir_cbranch(&A,
                newir_istok(&A, SJP_ARRAY_END),
                17, "invalid_1",
                21, "false"),
              NULL
            ),

            newir_block(&A, 21, "false",
              newir_stmt(&A, JVST_IR_STMT_CONSUME),
              newir_branch(&A, 13, "valid"),
              NULL
            ),

            newir_block(&A, 13, "valid",
              newir_stmt(&A, JVST_IR_STMT_VALID),
              NULL
            ),

            newir_block(&A, 4, "loop",
              newir_stmt(&A, JVST_IR_STMT_TOKEN),
              newir_cbranch(&A, newir_istok(&A, SJP_OBJECT_END),
                13, "valid",
                7, "false"
              ),
              NULL
            ),

            newir_block(&A, 7, "false",
              newir_move(&A, newir_itemp(&A, 0), newir_ematch(&A, 0)),
              newir_cbranch(&A, 
                newir_op(&A, JVST_IR_EXPR_EQ, newir_itemp(&A, 0), newir_size(&A, 0)),
                9, "M",
                10, "M_next"
              ),
              NULL
            ),

            newir_block(&A, 10, "M_next",
                newir_cbranch(&A, 
                  newir_op(&A, JVST_IR_EXPR_EQ, newir_itemp(&A, 0), newir_size(&A, 1)),
                  11, "M",
                  12, "invalid_9"
                ),
              NULL
            ),

            newir_block(&A, 12, "invalid_9",
              newir_invalid(&A, JVST_INVALID_MATCH_CASE, "invalid match case (internal error)"),
              NULL
            ),

            newir_block(&A, 9, "M",
              newir_stmt(&A, JVST_IR_STMT_CONSUME),
              newir_branch(&A, 4, "loop"),
              NULL
            ),

            newir_block(&A, 11, "M",
              newir_call(&A, 1),
              newir_branch(&A, 4, "loop"),
              NULL
            ),

            newir_block(&A, 17, "invalid_1",
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
              NULL
            ),

            NULL
          ),

          NULL
        ),

        NULL
      ),
    },

    {
      IR_LINEARIZE,
      "{ \"properties\" : { \"foo\" : { \"type\" : \"integer\" }, "
        "\"bar\" : { \"$ref\" : \"#/properties/foo\" } } }",
      NULL,
      new_irpairs(&A, "",
        newir_program(&A,
          newir_frame(&A, frameindex, 1,
            newir_matcher(&A, 0, "dfa"),

            newir_block(&A, 0, "entry",
              newir_stmt(&A, JVST_IR_STMT_TOKEN),
              newir_cbranch(&A,
                newir_istok(&A, SJP_OBJECT_BEG),
                4, "loop",
                16, "false"),
              NULL
            ),

            newir_block(&A, 16, "false",
              newir_cbranch(&A,
                newir_istok(&A, SJP_OBJECT_END),
                19, "invalid_1",
                20, "false"),
              NULL
            ),

            newir_block(&A, 20, "false",
              newir_cbranch(&A,
                newir_istok(&A, SJP_ARRAY_END),
                19, "invalid_1",
                23, "false"),
              NULL
            ),

            newir_block(&A, 23, "false",
              newir_stmt(&A, JVST_IR_STMT_CONSUME),
              newir_branch(&A, 15, "valid"),
              NULL
            ),

            newir_block(&A, 15, "valid",
              newir_stmt(&A, JVST_IR_STMT_VALID),
              NULL
            ),

            newir_block(&A, 4, "loop",
              newir_stmt(&A, JVST_IR_STMT_TOKEN),
              newir_cbranch(&A, newir_istok(&A, SJP_OBJECT_END),
                15, "valid",
                7, "false"
              ),
              NULL
            ),

            newir_block(&A, 7, "false",
              newir_move(&A, newir_itemp(&A, 0), newir_ematch(&A, 0)),
              newir_cbranch(&A, 
                newir_op(&A, JVST_IR_EXPR_EQ, newir_itemp(&A, 0), newir_size(&A, 0)),
                9, "M",
                10, "M_next"
              ),
              NULL
            ),

            newir_block(&A, 10, "M_next",
                newir_cbranch(&A, 
                  newir_op(&A, JVST_IR_EXPR_EQ, newir_itemp(&A, 0), newir_size(&A, 1)),
                  11, "M",
                  12, "M_next"
                ),
              NULL
            ),

            newir_block(&A, 12, "M_next",
                newir_cbranch(&A, 
                  newir_op(&A, JVST_IR_EXPR_EQ, newir_itemp(&A, 0), newir_size(&A, 2)),
                  13, "M",
                  14, "invalid_9"
                ),
              NULL
            ),

            newir_block(&A, 14, "invalid_9",
              newir_invalid(&A, JVST_INVALID_MATCH_CASE, "invalid match case (internal error)"),
              NULL
            ),

            newir_block(&A, 9, "M",
              newir_stmt(&A, JVST_IR_STMT_CONSUME),
              newir_branch(&A, 4, "loop"),
              NULL
            ),

            newir_block(&A, 11, "M",
              newir_call(&A, 2),
              newir_branch(&A, 4, "loop"),
              NULL
            ),

            newir_block(&A, 13, "M",
              newir_call(&A, 2),
              newir_branch(&A, 4, "loop"),
              NULL
            ),

            newir_block(&A, 19, "invalid_1",
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
              NULL
            ),

            NULL
          ),

          newir_frame(&A, frameindex, 2,
              newir_block(&A, 0, "entry",
                newir_stmt(&A, JVST_IR_STMT_TOKEN),   // XXX - is this necessary?
                newir_cbranch(&A,
                  newir_istok(&A, SJP_NUMBER),
                  2, "true",
                  9, "invalid_1"),
                NULL
              ),

              newir_block(&A, 9, "invalid_1",
                newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                NULL
              ),

              newir_block(&A, 2, "true",
                newir_cbranch(&A, newir_isint(&A, newir_expr(&A, JVST_IR_EXPR_TOK_NUM)),
                  4, "true",
                  7, "invalid_2"),
                NULL
              ),

              newir_block(&A, 7, "invalid_2",
                newir_invalid(&A, JVST_INVALID_NOT_INTEGER, "number is not an integer"),
                NULL
              ),

              newir_block(&A, 4, "true",
                newir_stmt(&A, JVST_IR_STMT_CONSUME),
                newir_branch(&A, 5, "valid"),
                NULL
              ),

              newir_block(&A, 5, "valid",
                newir_stmt(&A, JVST_IR_STMT_VALID),
                NULL
              ),

              NULL
          ),

          NULL
        ),

        NULL
      ),
    },

    { STOP },
  };

  RUNTESTS(tests);
}

int main(void)
{
  test_path_root();
  test_path_properties();
  test_path_dependencies();
  test_ids();
  test_definitions();

  test_rerooted_refs();

  test_ir_translation();
  test_ir_linearize();

  return report_tests();
}
