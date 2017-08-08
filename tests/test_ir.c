#include "validate_testing.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "jvst_macros.h"

#include "validate_ir.h"

#ifndef PRINT_IR
#  define PRINT_IR 0
#endif /* PRINT_IR */

enum ir_test_type {
  STOP = 0,
  TRANSLATE,
  LINEARIZE,
};

struct ir_test {
  enum ir_test_type type;
  struct jvst_cnode *ctree;
  struct jvst_ir_stmt *translated;
  struct jvst_ir_stmt *linearized;
};

static int ir_trees_equal(const char *fname, struct jvst_ir_stmt *n1, struct jvst_ir_stmt *n2);

static int run_test(const char *fname, const struct ir_test *t)
{
  struct jvst_cnode *simplified, *canonified;
  struct jvst_ir_stmt *translated, *result, *expected;

  assert(t->ctree != NULL);

  switch (t->type) {
  default:
  case STOP:
    fprintf(stderr, "SHOULD NOT REACH!\n");
    abort();

  case TRANSLATE:
    assert(t->translated != NULL);

    expected = t->translated;
    simplified = jvst_cnode_simplify(t->ctree);
    canonified = jvst_cnode_canonify(simplified);
    result = jvst_ir_translate(canonified);
    break;

  case LINEARIZE:
    assert(t->linearized != NULL);

    expected = t->linearized;
    simplified = jvst_cnode_simplify(t->ctree);
    canonified = jvst_cnode_canonify(simplified);
    translated = jvst_ir_translate(canonified);
    result = jvst_ir_linearize(translated);
    break;
  }

  assert(expected != NULL);

#if PRINT_IR
  jvst_ir_print(result);
#endif /* PRINT_IR */

  return ir_trees_equal(fname, result, expected);
}

// n1 is actual, n2 is expected
static int ir_trees_equal(const char *fname, struct jvst_ir_stmt *n1, struct jvst_ir_stmt *n2)
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
  if (jvst_ir_dump(n1, buf1, sizeof buf1) != 0) {
    fprintf(stderr, "buffer for node 1 not large enough (currently %zu bytes)\n",
        sizeof buf1);
  }

  if (jvst_ir_dump(n2, buf2, sizeof buf2) != 0) {
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

  fprintf(stderr, "test %s ir trees are not equal:\n", fname);
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

#define UNIMPLEMENTED(testlist) do{ nskipped++; (void)testlist; }while(0)
#define RUNTESTS(testlist) runtests(__func__, (testlist))
static void runtests(const char *testname, const struct ir_test tests[])
{
  int i;

  for (i=0; tests[i].type != STOP; i++) {
    ntest++;

    if (!run_test(testname, &tests[i])) {
      printf("%s[%d]: failed\n", testname, i+1);
      nfail++;
    }
  }
}

static void test_ir_empty_schema(void)
{
  struct arena_info A = {0};

  const struct ir_test tests[] = {
    {
      TRANSLATE,
      newcnode_switch(&A, 1, SJP_NONE),

      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
            newir_if(&A, newir_istok(&A, SJP_ARRAY_END),
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
              newir_stmt(&A, JVST_IR_STMT_VALID)
            )
          ),
          NULL
      )
    },

    {
      LINEARIZE,
      newcnode_switch(&A, 1, SJP_NONE),

      NULL,

      newir_program(&A,
        newir_frame(&A,
            newir_block(&A, 0, "entry",
              newir_stmt(&A, JVST_IR_STMT_TOKEN),
              newir_cbranch(&A, newir_istok(&A, SJP_OBJECT_END),
                2, "true",
                3, "false"
              ),
              newir_block(&A, 2, "true",
                newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                newir_branch(&A, 1, "join"),
                NULL
              ),
              newir_block(&A, 3, "false",
                newir_cbranch(&A, newir_istok(&A, SJP_ARRAY_END),
                  5, "true",
                  6, "false"
                ),
                newir_block(&A, 5, "true",
                  newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                  newir_branch(&A, 4, "join"),
                  NULL
                ),
                newir_block(&A, 6, "false",
                  newir_stmt(&A, JVST_IR_STMT_VALID),
                  newir_branch(&A, 4, "join"),
                  NULL
                ),
                newir_block(&A, 4, "join",
                  newir_branch(&A, 1, "join"),
                  NULL
                ),
                NULL
              ),
              newir_block(&A, 1, "join",
                newir_stmt(&A, JVST_IR_STMT_NOP),
                NULL
              ),
              NULL
            ),
            NULL
        ),
        NULL
      )
    },

    { STOP },
  };

  RUNTESTS(tests);
}

static void test_ir_type_constraints(void)
{
  struct arena_info A = {0};
  struct ast_schema schema = {
    .types = JSON_VALUE_NUMBER,
  };

  const struct ir_test tests[] = {
    {
      TRANSLATE,
      newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE),

      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_NUMBER),
            newir_stmt(&A, JVST_IR_STMT_VALID),
            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
          ),
          NULL
      )
    },

    {
      LINEARIZE,
      newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE),

      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_NUMBER),
            newir_stmt(&A, JVST_IR_STMT_VALID),
            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
          ),
          NULL
      ),

      newir_program(&A,
        newir_frame(&A,
          newir_block(&A, 0, "entry",
            newir_stmt(&A, JVST_IR_STMT_TOKEN),
            newir_cbranch(&A, newir_istok(&A, SJP_NUMBER),
              2, "true",
              3, "false"
            ),
            newir_block(&A, 2, "true",
              newir_stmt(&A, JVST_IR_STMT_VALID),
              newir_branch(&A, 1, "join"),
              NULL
            ),
            newir_block(&A, 3, "false",
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
              newir_branch(&A, 1, "join"),
              NULL
            ),
            newir_block(&A, 1, "join",
              newir_stmt(&A, JVST_IR_STMT_NOP),
              NULL
            ),
            NULL
          ),
          NULL
        ),
        NULL
      )
    },

    {
      TRANSLATE,
      newcnode_switch(&A, 0, SJP_OBJECT_BEG, newcnode_valid(), SJP_NONE),
      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_OBJECT_BEG),
            newir_stmt(&A, JVST_IR_STMT_VALID),
            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
          ),
          NULL
      )
    },

    {
      LINEARIZE,
      newcnode_switch(&A, 0, SJP_OBJECT_BEG, newcnode_valid(), SJP_NONE),
      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_OBJECT_BEG),
            newir_stmt(&A, JVST_IR_STMT_VALID),
            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
          ),
          NULL
      ),

      newir_program(&A,
        newir_frame(&A,
          newir_block(&A, 0, "entry",
            newir_stmt(&A, JVST_IR_STMT_TOKEN),
            newir_cbranch(&A, newir_istok(&A, SJP_OBJECT_BEG),
              2, "true",
              3, "false"
            ),
            newir_block(&A, 2, "true",
              newir_stmt(&A, JVST_IR_STMT_VALID),
              newir_branch(&A, 1, "join"),
              NULL
            ),
            newir_block(&A, 3, "false",
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
              newir_branch(&A, 1, "join"),
              NULL
            ),
            newir_block(&A, 1, "join",
              newir_stmt(&A, JVST_IR_STMT_NOP),
              NULL
            ),
            NULL
          ),
          NULL
        ),
        NULL
      )
    },

    {
      TRANSLATE,
      newcnode_switch(&A, 0,
        SJP_OBJECT_BEG, newcnode_valid(),
        SJP_STRING, newcnode_valid(),
        SJP_NONE),

      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_STRING),
            newir_stmt(&A, JVST_IR_STMT_VALID),
            newir_if(&A, newir_istok(&A, SJP_OBJECT_BEG),
              newir_stmt(&A, JVST_IR_STMT_VALID),
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
            )
          ),
          NULL
      )
    },

    {
      LINEARIZE,
      newcnode_switch(&A, 0,
        SJP_OBJECT_BEG, newcnode_valid(),
        SJP_STRING, newcnode_valid(),
        SJP_NONE),

      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_STRING),
            newir_stmt(&A, JVST_IR_STMT_VALID),
            newir_if(&A, newir_istok(&A, SJP_OBJECT_BEG),
              newir_stmt(&A, JVST_IR_STMT_VALID),
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
            )
          ),
          NULL
      ),

      newir_program(&A,
        newir_frame(&A,
          newir_block(&A, 0, "entry",
            newir_stmt(&A, JVST_IR_STMT_TOKEN),
            newir_cbranch(&A, newir_istok(&A, SJP_STRING),
              2, "true",
              3, "false"
            ),
            newir_block(&A, 2, "true",
              newir_stmt(&A, JVST_IR_STMT_VALID),
              newir_branch(&A, 1, "join"),
              NULL
            ),
            newir_block(&A, 3, "false",
              newir_cbranch(&A, newir_istok(&A, SJP_OBJECT_BEG),
                5, "true",
                6, "false"
              ),
              newir_block(&A, 5, "true",
                newir_stmt(&A, JVST_IR_STMT_VALID),
                newir_branch(&A, 4, "join"),
                NULL
              ),
              newir_block(&A, 6, "false",
                newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                newir_branch(&A, 4, "join"),
                NULL
              ),
              newir_block(&A, 4, "join",
                newir_branch(&A, 1, "join"),
                NULL
              ),
              NULL
            ),
            newir_block(&A, 1, "join",
              newir_stmt(&A, JVST_IR_STMT_NOP),
              NULL
            ),
            NULL
          ),
          NULL
        ),
        NULL
      )
    },

    { STOP },
  };

  RUNTESTS(tests);
}

static void test_ir_type_integer(void)
{
  struct arena_info A = {0};
  struct ast_schema schema = {
    .types = JSON_VALUE_INTEGER,
  };

  const struct ir_test tests[] = {
    {
      TRANSLATE,
      newcnode_switch(&A, 0,
        SJP_NUMBER,
        newcnode(&A,JVST_CNODE_NUM_INTEGER),
        SJP_NONE),

      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_NUMBER),
            newir_if(&A, newir_isint(&A, newir_expr(&A, JVST_IR_EXPR_TOK_NUM)),
              newir_stmt(&A, JVST_IR_STMT_VALID),
              newir_invalid(&A, JVST_INVALID_NOT_INTEGER, "number is not an integer")),
            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
          ),
          NULL
      )
    },

    {
      LINEARIZE,
      newcnode_switch(&A, 0,
        SJP_NUMBER,
        newcnode(&A,JVST_CNODE_NUM_INTEGER),
        SJP_NONE),

      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_NUMBER),
            newir_if(&A, newir_isint(&A, newir_expr(&A, JVST_IR_EXPR_TOK_NUM)),
              newir_stmt(&A, JVST_IR_STMT_VALID),
              newir_invalid(&A, JVST_INVALID_NOT_INTEGER, "number is not an integer")),
            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
          ),
          NULL
      ),

      newir_program(&A,
        newir_frame(&A,
          newir_block(&A, 0, "entry",
            newir_stmt(&A, JVST_IR_STMT_TOKEN),
            newir_cbranch(&A, newir_istok(&A, SJP_NUMBER),
              2, "true",
              6, "false"
            ),

            newir_block(&A, 2, "true",
              newir_cbranch(&A, newir_isint(&A, newir_expr(&A, JVST_IR_EXPR_TOK_NUM)),
                4, "true",
                5, "false"
              ),

              newir_block(&A, 4, "true",
                newir_stmt(&A, JVST_IR_STMT_VALID),
                newir_branch(&A, 3, "join"),
                NULL
              ),

              newir_block(&A, 5, "false",
                newir_invalid(&A, JVST_INVALID_NOT_INTEGER, "number is not an integer"),
                newir_branch(&A, 3, "join"),
                NULL
              ),

              newir_block(&A, 3, "join",
                newir_branch(&A, 1, "join"),
                NULL
              ),

              NULL
            ),

            newir_block(&A, 6, "false",
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
              newir_branch(&A, 1, "join"),
              NULL
            ),

            newir_block(&A, 1, "join",
              newir_stmt(&A, JVST_IR_STMT_NOP),
              NULL
            ),

            NULL
          ),

          NULL
        ),

        NULL
      )

    },

    { STOP },
  };

  RUNTESTS(tests);
}

void test_ir_minimum(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "minimum", 1.1,
      NULL);

  const struct ir_test tests[] = {
    {
      TRANSLATE,
      newcnode_switch(&A, 0,
          SJP_NUMBER, newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
          SJP_NONE),

      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_NUMBER),
            newir_if(&A,
              newir_op(&A, JVST_IR_EXPR_GE, 
                newir_expr(&A, JVST_IR_EXPR_TOK_NUM),
                newir_num(&A, 1.1)),
              newir_stmt(&A, JVST_IR_STMT_VALID),
              newir_invalid(&A, JVST_INVALID_NUMBER, "number not valid")),
            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
          ),
          NULL
      )
    },

    {
      LINEARIZE,
      newcnode_switch(&A, 0,
          SJP_NUMBER, newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
          SJP_NONE),

      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_NUMBER),
            newir_if(&A,
              newir_op(&A, JVST_IR_EXPR_GE, 
                newir_expr(&A, JVST_IR_EXPR_TOK_NUM),
                newir_num(&A, 1.1)),
              newir_stmt(&A, JVST_IR_STMT_VALID),
              newir_invalid(&A, JVST_INVALID_NUMBER, "number not valid")),
            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
          ),
          NULL
      ),

      newir_program(&A,
        newir_frame(&A,
          newir_block(&A, 0, "entry",
            newir_stmt(&A, JVST_IR_STMT_TOKEN),
            newir_cbranch(&A, newir_istok(&A, SJP_NUMBER),
              2, "true",
              6, "false"
            ),

            newir_block(&A, 2, "true",
              newir_cbranch(&A,
                newir_op(&A, JVST_IR_EXPR_GE, 
                  newir_expr(&A, JVST_IR_EXPR_TOK_NUM),
                  newir_eseq(&A,
                    newir_move(&A, newir_ftemp(&A, 0), newir_num(&A, 1.1)),
                    newir_ftemp(&A, 0)
                  )
                ),
                4, "true",
                5, "false"
              ),

              newir_block(&A, 4, "true",
                newir_stmt(&A, JVST_IR_STMT_VALID),
                newir_branch(&A, 3, "join"),
                NULL
              ),

              newir_block(&A, 5, "false",
                newir_invalid(&A, JVST_INVALID_NUMBER, "number not valid"),
                newir_branch(&A, 3, "join"),
                NULL
              ),

              newir_block(&A, 3, "join",
                newir_branch(&A, 1, "join"),
                NULL
              ),

              NULL
            ),

            newir_block(&A, 6, "false",
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
              newir_branch(&A, 1, "join"),
              NULL
            ),

            newir_block(&A, 1, "join",
              newir_stmt(&A, JVST_IR_STMT_NOP),
              NULL
            ),

            NULL
          ),

          NULL
        ),

        NULL
      )

    },

    { STOP },
  };

  RUNTESTS(tests);
}

void test_ir_properties(void)
{
  struct arena_info A = {0};

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct ir_test tests[] = {
    {
      TRANSLATE,
      newcnode_switch(&A, 1,
        SJP_OBJECT_BEG, newcnode_propset(&A,
                          newcnode_prop_match(&A, RE_LITERAL, "foo",
                            newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),
                          newcnode_prop_match(&A, RE_LITERAL, "bar",
                            newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                          NULL),
        SJP_NONE),

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

                      // match "bar"
                      newir_case(&A, 1,
                        newmatchset(&A, RE_LITERAL,  "bar", -1),
                        newir_frame(&A,
                          newir_stmt(&A, JVST_IR_STMT_TOKEN),
                          newir_if(&A, newir_istok(&A, SJP_STRING),
                            newir_stmt(&A, JVST_IR_STMT_VALID),
                            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
                          ),
                          NULL
                        )
                      ),

                      // match "foo"
                      newir_case(&A, 2,
                        newmatchset(&A, RE_LITERAL,  "foo", -1),
                        newir_frame(&A,
                          newir_stmt(&A, JVST_IR_STMT_TOKEN),
                          newir_if(&A, newir_istok(&A, SJP_NUMBER),
                            newir_stmt(&A, JVST_IR_STMT_VALID),
                            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
                          ),
                          NULL
                        )
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
                newir_stmt(&A, JVST_IR_STMT_VALID)
              )
            )
          ),
          NULL
      )
    },

    {
      TRANSLATE,
      newcnode_switch(&A, 1,
        SJP_OBJECT_BEG, newcnode_propset(&A,
                          newcnode_prop_match(&A, RE_NATIVE, "ba.",
                            newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),
                          newcnode_prop_match(&A, RE_LITERAL, "bar",
                            newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                          NULL),
        SJP_NONE),

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

                      // match "bar" AND "ba."
                      newir_case(&A, 1,
                        newmatchset(&A, RE_LITERAL, "bar", RE_NATIVE,  "ba.", -1),
                        newir_frame(&A,
                          newir_stmt(&A, JVST_IR_STMT_TOKEN),   // XXX - is this necessary?
                          newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                          NULL
                        )
                      ),

                      // match /ba./
                      newir_case(&A, 2,
                        newmatchset(&A, RE_NATIVE,  "ba.", -1),
                        newir_frame(&A,
                          newir_stmt(&A, JVST_IR_STMT_TOKEN),
                          newir_if(&A, newir_istok(&A, SJP_NUMBER),
                            newir_stmt(&A, JVST_IR_STMT_VALID),
                            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
                          ),
                          NULL
                        )
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
                newir_stmt(&A, JVST_IR_STMT_VALID)
              )
            )
          ),
          NULL
      )
    },

    { STOP },
  };

  RUNTESTS(tests);
}

void test_ir_minmax_properties_1(void)
{
  struct arena_info A = {0};

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct ir_test tests[] = {
    {
      TRANSLATE,
      newcnode_switch(&A, 1,
        SJP_OBJECT_BEG, newcnode_counts(&A, 1, 0),
        SJP_NONE),

      // XXX
      // this IR is not as compact as it could be we should be able to
      // short-circuit the loop when we've encountered one property
      // instead of keeping a full count
      newir_frame(&A,
          newir_counter(&A, 0, "num_props"),
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_OBJECT_BEG),
            newir_seq(&A,
              newir_loop(&A, "L_OBJ", 0,
                newir_stmt(&A, JVST_IR_STMT_TOKEN),
                newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                  newir_break(&A, "L_OBJ", 0),
                  newir_seq(&A,                                 // unnecessary SEQ should be removed in the future
                    // XXX The match could be eliminated here.  We'd
                    //     have to consume the string and the value.
                    //     This would be a good reason to add a CONSUME
                    //     statement instead of creating a frame and
                    //     using VALID to consume the entire token.
                    newir_match(&A, 0,
                      // no match
                      newir_case(&A, 0, 
                        NULL,
                        newir_stmt(&A, JVST_IR_STMT_CONSUME)
                      ),

                      NULL
                    ),
                    newir_incr(&A, 0, "num_props"),
                    // XXX as mentioned above, we could short-circuit
                    //     the loop if num_props >= 1.  This would
                    //     require adding an EAT_OBJECT or similar
                    //     statement to finish the object.
                    //
                    //     The IR might look like:
                    //     IF(GE(COUNT(num_props), 1),
                    //        SEQ(EAT_OBJECT, BREAK("L_OBJ")),
                    //        NOP)
                    //
                    //     In this particular case (at least one prop),
                    //     you could even eliminate the counter and
                    //     matcher and just check if the first token in
                    //     the object is OBJECT_END or not.  Ideally
                    //     that would fall out of some more general
                    //     reasoning and wouldn't need to be
                    //     special-cased.  But if { "minProperties" : 1 }
                    //     is a common constraint, we could just
                    //     special-case it.
                    NULL
                  )
                ),
                NULL
              ),

              // Post-loop check of number of properties
              newir_if(&A,
                  newir_op(&A, JVST_IR_EXPR_GE, 
                    newir_count(&A, 0, "num_props"),
                    newir_size(&A, 1)
                  ),
                  newir_stmt(&A, JVST_IR_STMT_VALID),
                  newir_invalid(&A, JVST_INVALID_TOO_FEW_PROPS, "too few properties")
              ),
              NULL
            ),

            newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
              newir_if(&A, newir_istok(&A, SJP_ARRAY_END),
                newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                newir_stmt(&A, JVST_IR_STMT_VALID)
              )
            )
          ),
          NULL
      )

    },

    {
      TRANSLATE,
      newcnode_switch(&A, 1,
        SJP_OBJECT_BEG, newcnode_counts(&A, 0, 2),
        SJP_NONE),

      // XXX - comments here are largely the same as in the previous
      //       test case
      newir_frame(&A,
          newir_counter(&A, 0, "num_props"),
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_OBJECT_BEG),
            newir_seq(&A,
              newir_loop(&A, "L_OBJ", 0,
                newir_stmt(&A, JVST_IR_STMT_TOKEN),
                newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                  newir_break(&A, "L_OBJ", 0),
                  newir_seq(&A,                                 // unnecessary SEQ should be removed in the future
                    // XXX The match could be eliminated here.  We'd
                    //     have to consume the string and the value.
                    //     This would be a good reason to add a CONSUME
                    //     statement instead of creating a frame and
                    //     using VALID to consume the entire token.
                    newir_match(&A, 0,
                      // no match
                      newir_case(&A, 0, 
                        NULL,
                        newir_stmt(&A, JVST_IR_STMT_CONSUME)
                      ),

                      NULL
                    ),
                    newir_incr(&A, 0, "num_props"),
                    // XXX as mentioned above, we could short-circuit
                    //     the loop if num_props >= 2.
                    //
                    //     The IR might look like:
                    //     IF(GT(COUNT(num_props), 2),
                    //        INVALID,
                    //        NOP)
                    NULL
                  )
                ),
                NULL
              ),

              // Post-loop check of number of properties
              newir_if(&A,
                  newir_op(&A, JVST_IR_EXPR_LE, 
                    newir_count(&A, 0, "num_props"),
                    newir_size(&A, 2)
                  ),
                  newir_stmt(&A, JVST_IR_STMT_VALID),
                  newir_invalid(&A, JVST_INVALID_TOO_MANY_PROPS, "too many properties")
              ),
              NULL
            ),

            newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
              newir_if(&A, newir_istok(&A, SJP_ARRAY_END),
                newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                newir_stmt(&A, JVST_IR_STMT_VALID)
              )
            )
          ),
          NULL
      )
    },

    {
      TRANSLATE,
      newcnode_switch(&A, 1,
        SJP_OBJECT_BEG, newcnode_counts(&A, 2, 5),
        SJP_NONE),

      // XXX - comments here are largely the same as in the first
      //       test case
      newir_frame(&A,
          newir_counter(&A, 0, "num_props"),
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_OBJECT_BEG),
            newir_seq(&A,
              newir_loop(&A, "L_OBJ", 0,
                newir_stmt(&A, JVST_IR_STMT_TOKEN),
                newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                  newir_break(&A, "L_OBJ", 0),
                  newir_seq(&A,                                 // unnecessary SEQ should be removed in the future
                    // XXX The match could be eliminated here.  We'd
                    //     have to consume the string and the value.
                    //     This would be a good reason to add a CONSUME
                    //     statement instead of creating a frame and
                    //     using VALID to consume the entire token.
                    newir_match(&A, 0,
                      // no match
                      newir_case(&A, 0, 
                        NULL,
                        newir_stmt(&A, JVST_IR_STMT_CONSUME)
                      ),

                      NULL
                    ),
                    newir_incr(&A, 0, "num_props"),
                    NULL
                  )
                ),
                NULL
              ),

              // Post-loop check of number of properties
              newir_if(&A,
                  newir_op(&A, JVST_IR_EXPR_GE, 
                    newir_count(&A, 0, "num_props"),
                    newir_size(&A, 2)
                  ),
                  newir_if(&A,
                    newir_op(&A, JVST_IR_EXPR_LE, 
                      newir_count(&A, 0, "num_props"),
                      newir_size(&A, 5)
                    ),
                    newir_stmt(&A, JVST_IR_STMT_VALID),
                    newir_invalid(&A, JVST_INVALID_TOO_MANY_PROPS, "too many properties")
                  ),
                  newir_invalid(&A, JVST_INVALID_TOO_FEW_PROPS, "too few properties")
              ),
              NULL
            ),

            newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
              newir_if(&A, newir_istok(&A, SJP_ARRAY_END),
                newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                newir_stmt(&A, JVST_IR_STMT_VALID)
              )
            )
          ),
          NULL
      )
    },

    { STOP },
  };

  RUNTESTS(tests);
}

void test_ir_minproperties_2(void)
{
  struct arena_info A = {0};

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct ir_test tests[] = {
    {
      TRANSLATE,
      newcnode_switch(&A, 1,
          SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                          newcnode_counts(&A, 1, 0),
                          newcnode_propset(&A,
                            newcnode_prop_match(&A, RE_LITERAL, "foo",
                              newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE)),
                            newcnode_prop_match(&A, RE_LITERAL, "bar",
                              newcnode_switch(&A, 0, SJP_STRING, newcnode_valid(), SJP_NONE)),
                            NULL),
                          NULL),
          SJP_NONE),

      newir_frame(&A,
          newir_counter(&A, 0, "num_props"),
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

                      // match "bar"
                      newir_case(&A, 1,
                        newmatchset(&A, RE_LITERAL,  "bar", -1),
                        newir_frame(&A,
                          newir_stmt(&A, JVST_IR_STMT_TOKEN),
                          newir_if(&A, newir_istok(&A, SJP_STRING),
                            newir_stmt(&A, JVST_IR_STMT_VALID),
                            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
                          ),
                          NULL
                        )
                      ),

                      // match "foo"
                      newir_case(&A, 2,
                        newmatchset(&A, RE_LITERAL,  "foo", -1),
                        newir_frame(&A,
                          newir_stmt(&A, JVST_IR_STMT_TOKEN),
                          newir_if(&A, newir_istok(&A, SJP_NUMBER),
                            newir_stmt(&A, JVST_IR_STMT_VALID),
                            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
                          ),
                          NULL
                        )
                      ),

                      NULL
                    ),
                    newir_incr(&A, 0, "num_props"),
                    NULL
                  )
                ),
                NULL
              ),

              // Post-loop check of number of properties
              newir_if(&A,
                  newir_op(&A, JVST_IR_EXPR_GE, 
                    newir_count(&A, 0, "num_props"),
                    newir_size(&A, 1)
                  ),
                  newir_stmt(&A, JVST_IR_STMT_VALID),
                  newir_invalid(&A, JVST_INVALID_TOO_FEW_PROPS, "too few properties")
              ),
              NULL
            ),

            newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
              newir_if(&A, newir_istok(&A, SJP_ARRAY_END),
                newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                newir_stmt(&A, JVST_IR_STMT_VALID)
              )
            )
          ),
          NULL
      )
    },

    { STOP },
  };

  RUNTESTS(tests);
}

void test_ir_required(void)
{
  struct arena_info A = {0};

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct ir_test tests[] = {
    {
      TRANSLATE,
      // schema:
      // {
      //   "properties" : {
      //     "foo" : { "type" : "number" },
      //     "foo" : { "type" : "string" }
      //   },
      //   "required" : [ "foo" ]
      // }
      newcnode_switch(&A, 1,
        SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                          newcnode_required(&A, stringset(&A, "foo", NULL)),
                          newcnode_propset(&A,
                            newcnode_prop_match(&A, RE_LITERAL, "foo",
                              newcnode_switch(&A, 0,
                                SJP_NUMBER, newcnode_valid(),
                                SJP_NONE)),
                            newcnode_prop_match(&A, RE_LITERAL, "bar",
                              newcnode_switch(&A, 0,
                                SJP_STRING, newcnode_valid(),
                                SJP_NONE)),
                            NULL),
                          NULL),
        SJP_NONE),

      newir_frame(&A,
          newir_bitvec(&A, 1, "reqmask", 1),
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

                      // match "bar"
                      newir_case(&A, 1,
                        newmatchset(&A, RE_LITERAL,  "bar", -1),
                        newir_frame(&A,
                          newir_stmt(&A, JVST_IR_STMT_TOKEN),
                          newir_if(&A, newir_istok(&A, SJP_STRING),
                            newir_stmt(&A, JVST_IR_STMT_VALID),
                            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
                          ),
                          NULL
                        )
                      ),

                      // match "foo"
                      newir_case(&A, 2,
                        newmatchset(&A, RE_LITERAL,  "foo", RE_LITERAL, "foo", -1),
                        newir_seq(&A,
                          newir_frame(&A,
                            newir_stmt(&A, JVST_IR_STMT_TOKEN),
                            newir_if(&A, newir_istok(&A, SJP_NUMBER),
                              newir_stmt(&A, JVST_IR_STMT_VALID),
                              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
                            ),
                            NULL
                          ),
                          newir_bitop(&A, JVST_IR_STMT_BSET, 1, "reqmask", 0),
                          NULL
                        )
                      ),

                      NULL
                    ),
                    NULL
                  )
                ),
                NULL
              ),
              newir_if(&A,
                  newir_btestall(&A, 1, "reqmask", 0,-1),
                  newir_stmt(&A, JVST_IR_STMT_VALID),
                  newir_invalid(&A, JVST_INVALID_MISSING_REQUIRED_PROPERTIES,
                    "missing required properties")
              ),
              NULL
            ),

            newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
              newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
              newir_if(&A, newir_istok(&A, SJP_ARRAY_END),
                newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                newir_stmt(&A, JVST_IR_STMT_VALID)
              )
            )
          ),
          NULL
      )
    },

    { STOP },
  };

  RUNTESTS(tests);
}

void test_ir_dependencies(void)
{
  struct arena_info A = {0};

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct ir_test tests[] = {
    {
      TRANSLATE,
      // schema: { "dependencies": {"bar": ["foo"]} }
      newcnode_switch(&A, 1,
        SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_OR,
                          newcnode_required(&A, stringset(&A, "bar", "foo", NULL)),
                          newcnode_propset(&A,
                            newcnode_prop_match(&A, RE_LITERAL, "bar", newcnode_invalid()),
                            NULL),
                          NULL),
        SJP_NONE),

      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_OBJECT_BEG),
              newir_if(&A,
                newir_op(&A, JVST_IR_EXPR_GE, 
                  newir_split(&A,
                    newir_frame(&A,
                      newir_matcher(&A, 0, "dfa"),
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

                                // match "bar"
                                newir_case(&A, 1,
                                  newmatchset(&A, RE_LITERAL,  "bar", -1),
                                  newir_invalid(&A, JVST_INVALID_BAD_PROPERTY_NAME, "bad property name")
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
                      NULL
                    ),

                    newir_frame(&A,
                      newir_bitvec(&A, 0, "reqmask", 2),
                      newir_matcher(&A, 0, "dfa"),
                      newir_seq(&A,
                        newir_loop(&A, "L_OBJ", 0,
                          newir_stmt(&A, JVST_IR_STMT_TOKEN),
                          newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                            newir_break(&A, "L_OBJ", 0),
                            newir_seq(&A,
                              newir_match(&A, 0,
                                // no match
                                newir_case(&A, 0, 
                                  NULL,
                                  newir_stmt(&A, JVST_IR_STMT_CONSUME)
                                ),

                                // match "bar"
                                newir_case(&A, 1,
                                  newmatchset(&A, RE_LITERAL,  "bar", -1),
                                  newir_seq(&A,
                                    newir_bitop(&A, JVST_IR_STMT_BSET, 0, "reqmask", 0),
                                    newir_stmt(&A, JVST_IR_STMT_CONSUME),
                                    NULL
                                  )
                                ),

                                // match "foo"
                                newir_case(&A, 2,
                                  newmatchset(&A, RE_LITERAL,  "foo", -1),
                                  newir_seq(&A,
                                    newir_bitop(&A, JVST_IR_STMT_BSET, 0, "reqmask", 1),
                                    newir_stmt(&A, JVST_IR_STMT_CONSUME),
                                    NULL
                                  )
                                ),

                                NULL
                              ),
                              NULL
                            )
                          ),
                          NULL
                        ),
                        newir_if(&A,
                            newir_btestall(&A, 0, "reqmask", 0, -1),
                            newir_stmt(&A, JVST_IR_STMT_VALID),
                            newir_invalid(&A, JVST_INVALID_MISSING_REQUIRED_PROPERTIES,
                              "missing required properties")
                        ),
                        NULL
                      ),
                      NULL
                    ),

                    NULL
                  ),
                  newir_size(&A, 1)
                ),
                newir_stmt(&A, JVST_IR_STMT_VALID),
                newir_invalid(&A, JVST_INVALID_SPLIT_CONDITION, "invalid split condition")
              ),
              newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                newir_if(&A, newir_istok(&A, SJP_ARRAY_END),
                  newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                  newir_stmt(&A, JVST_IR_STMT_VALID)
                )
              )
          ),
          NULL
      )
    },

    {
      TRANSLATE,
      // schema: { "dependencies": {"quux": ["foo", "bar"]} }
      newcnode_switch(&A, 1,
        SJP_OBJECT_BEG, newcnode_bool(&A, JVST_CNODE_OR,
                          newcnode_required(&A, stringset(&A, "quux", "foo", "bar", NULL)),
                          newcnode_propset(&A,
                            newcnode_prop_match(&A, RE_LITERAL, "quux", newcnode_invalid()),
                            NULL),
                          NULL),
        SJP_NONE),

      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_OBJECT_BEG),
              newir_if(&A,
                newir_op(&A, JVST_IR_EXPR_GE, 
                  newir_split(&A,
                    newir_frame(&A,
                      newir_matcher(&A, 0, "dfa"),
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

                                // match "bar"
                                newir_case(&A, 1,
                                  newmatchset(&A, RE_LITERAL,  "quux", -1),
                                  newir_invalid(&A, JVST_INVALID_BAD_PROPERTY_NAME, "bad property name")
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
                      NULL
                    ),

                    newir_frame(&A,
                      newir_bitvec(&A, 0, "reqmask", 3),
                      newir_matcher(&A, 0, "dfa"),
                      newir_seq(&A,
                        newir_loop(&A, "L_OBJ", 0,
                          newir_stmt(&A, JVST_IR_STMT_TOKEN),
                          newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                            newir_break(&A, "L_OBJ", 0),
                            newir_seq(&A,
                              newir_match(&A, 0,
                                // no match
                                newir_case(&A, 0, 
                                  NULL,
                                  newir_stmt(&A, JVST_IR_STMT_CONSUME)
                                ),

                                // match "bar"
                                newir_case(&A, 1,
                                  newmatchset(&A, RE_LITERAL,  "bar", -1),
                                  newir_seq(&A,
                                    newir_bitop(&A, JVST_IR_STMT_BSET, 0, "reqmask", 2),
                                    newir_stmt(&A, JVST_IR_STMT_CONSUME),
                                    NULL
                                  )
                                ),

                                // match "foo"
                                newir_case(&A, 2,
                                  newmatchset(&A, RE_LITERAL,  "foo", -1),
                                  newir_seq(&A,
                                    newir_bitop(&A, JVST_IR_STMT_BSET, 0, "reqmask", 1),
                                    newir_stmt(&A, JVST_IR_STMT_CONSUME),
                                    NULL
                                  )
                                ),

                                // match "quux"
                                newir_case(&A, 3,
                                  newmatchset(&A, RE_LITERAL,  "quux", -1),
                                  newir_seq(&A,
                                    newir_bitop(&A, JVST_IR_STMT_BSET, 0, "reqmask", 0),
                                    newir_stmt(&A, JVST_IR_STMT_CONSUME),
                                    NULL
                                  )
                                ),

                                NULL
                              ),
                              NULL
                            )
                          ),
                          NULL
                        ),
                        newir_if(&A,
                            newir_btestall(&A, 0, "reqmask", 0, -1),
                            newir_stmt(&A, JVST_IR_STMT_VALID),
                            newir_invalid(&A, JVST_INVALID_MISSING_REQUIRED_PROPERTIES,
                              "missing required properties")
                        ),
                        NULL
                      ),
                      NULL
                    ),

                    NULL
                  ),
                  newir_size(&A, 1)
                ),
                newir_stmt(&A, JVST_IR_STMT_VALID),
                newir_invalid(&A, JVST_INVALID_SPLIT_CONDITION, "invalid split condition")
              ),
              newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                newir_if(&A, newir_istok(&A, SJP_ARRAY_END),
                  newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                  newir_stmt(&A, JVST_IR_STMT_VALID)
                )
              )
          ),
          NULL
      )
    },

    {
      TRANSLATE,
      // schema: { "dependencies": {"quux": ["foo", "bar"], "this": ["that"]} }
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
                          NULL),
        SJP_NONE),

      newir_frame(&A,
          newir_bitvec(&A, 0, "splitvec", 4),
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_OBJECT_BEG),
              newir_seq(&A,
                newir_splitvec(&A, 0, "splitvec",
                  newir_frame(&A,
                    newir_matcher(&A, 0, "dfa"),
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

                              // match "bar"
                              newir_case(&A, 1,
                                newmatchset(&A, RE_LITERAL,  "quux", -1),
                                newir_invalid(&A, JVST_INVALID_BAD_PROPERTY_NAME, "bad property name")
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
                    NULL
                  ),

                  newir_frame(&A,
                    newir_bitvec(&A, 0, "reqmask", 3),
                    newir_matcher(&A, 0, "dfa"),
                    newir_seq(&A,
                      newir_loop(&A, "L_OBJ", 0,
                        newir_stmt(&A, JVST_IR_STMT_TOKEN),
                        newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                          newir_break(&A, "L_OBJ", 0),
                          newir_seq(&A,
                            newir_match(&A, 0,
                              // no match
                              newir_case(&A, 0, 
                                NULL,
                                newir_stmt(&A, JVST_IR_STMT_CONSUME)
                              ),

                              // match "bar"
                              newir_case(&A, 1,
                                newmatchset(&A, RE_LITERAL,  "bar", -1),
                                newir_seq(&A,
                                  newir_bitop(&A, JVST_IR_STMT_BSET, 0, "reqmask", 2),
                                  newir_stmt(&A, JVST_IR_STMT_CONSUME),
                                  NULL
                                )
                              ),

                              // match "foo"
                              newir_case(&A, 2,
                                newmatchset(&A, RE_LITERAL,  "foo", -1),
                                newir_seq(&A,
                                  newir_bitop(&A, JVST_IR_STMT_BSET, 0, "reqmask", 1),
                                  newir_stmt(&A, JVST_IR_STMT_CONSUME),
                                  NULL
                                )
                              ),

                              // match "quux"
                              newir_case(&A, 3,
                                newmatchset(&A, RE_LITERAL,  "quux", -1),
                                newir_seq(&A,
                                  newir_bitop(&A, JVST_IR_STMT_BSET, 0, "reqmask", 0),
                                  newir_stmt(&A, JVST_IR_STMT_CONSUME),
                                  NULL
                                )
                              ),

                              NULL
                            ),
                            NULL
                          )
                        ),
                        NULL
                      ),
                      newir_if(&A,
                          newir_btestall(&A, 0, "reqmask", 0, -1),
                          newir_stmt(&A, JVST_IR_STMT_VALID),
                          newir_invalid(&A, JVST_INVALID_MISSING_REQUIRED_PROPERTIES,
                            "missing required properties")
                      ),
                      NULL
                    ),
                    NULL
                  ),

                  newir_frame(&A,
                    newir_matcher(&A, 0, "dfa"),
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

                              // match "bar"
                              newir_case(&A, 1,
                                newmatchset(&A, RE_LITERAL,  "this", -1),
                                newir_invalid(&A, JVST_INVALID_BAD_PROPERTY_NAME, "bad property name")
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
                    NULL
                  ),

                  newir_frame(&A,
                    newir_bitvec(&A, 0, "reqmask", 2),
                    newir_matcher(&A, 0, "dfa"),
                    newir_seq(&A,
                      newir_loop(&A, "L_OBJ", 0,
                        newir_stmt(&A, JVST_IR_STMT_TOKEN),
                        newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                          newir_break(&A, "L_OBJ", 0),
                          newir_seq(&A,
                            newir_match(&A, 0,
                              // no match
                              newir_case(&A, 0, 
                                NULL,
                                newir_stmt(&A, JVST_IR_STMT_CONSUME)
                              ),

                              // match "quux"
                              newir_case(&A, 1,
                                newmatchset(&A, RE_LITERAL,  "that", -1),
                                newir_seq(&A, 
                                  newir_bitop(&A, JVST_IR_STMT_BSET, 0, "reqmask", 1),
                                  newir_stmt(&A, JVST_IR_STMT_CONSUME),
                                  NULL
                                )
                              ),

                              // match "bar"
                              newir_case(&A, 2,
                                newmatchset(&A, RE_LITERAL,  "this", -1),
                                newir_seq(&A, 
                                  newir_bitop(&A, JVST_IR_STMT_BSET, 0, "reqmask", 0),
                                  newir_stmt(&A, JVST_IR_STMT_CONSUME),
                                  NULL
                                )
                              ),

                              NULL
                            ),
                            NULL
                          )
                        ),
                        NULL
                      ),
                      newir_if(&A,
                          newir_btestall(&A, 0, "reqmask", 0, -1),
                          newir_stmt(&A, JVST_IR_STMT_VALID),
                          newir_invalid(&A, JVST_INVALID_MISSING_REQUIRED_PROPERTIES,
                            "missing required properties")
                      ),
                      NULL
                    ),
                    NULL
                  ),

                  NULL
                ),
                newir_if(&A,
                  newir_op(&A, JVST_IR_EXPR_AND, 
                    newir_op(&A, JVST_IR_EXPR_OR, 
                      newir_btestany(&A, 0, "splitvec", 0, 0),  // XXX - can combine the OR'd stuff...
                      newir_btest(&A, 0, "splitvec", 1)
                    ),
                    newir_op(&A, JVST_IR_EXPR_OR,               // XXX - can combine the OR'd stuff...
                      newir_btestany(&A, 0, "splitvec", 2, 2),
                      newir_btest(&A, 0, "splitvec", 3)
                    )
                  ),
                  newir_stmt(&A, JVST_IR_STMT_VALID),
                  newir_invalid(&A, JVST_INVALID_SPLIT_CONDITION, "invalid split condition")
                ),

                NULL
              ),
              newir_if(&A, newir_istok(&A, SJP_OBJECT_END),
                newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                newir_if(&A, newir_istok(&A, SJP_ARRAY_END),
                  newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token"),
                  newir_stmt(&A, JVST_IR_STMT_VALID)
                )
              )
          ),
          NULL
      )
    },

    { STOP },
  };

  const struct ir_test unfinished_tests[] = {
    {
      TRANSLATE,
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

      NULL
    },

    { STOP },
  };

  RUNTESTS(tests);
}

/* incomplete tests... placeholders for conversion from cnode tests */
static void test_ir_minproperties_3(void);
static void test_ir_maxproperties_1(void);
static void test_ir_maxproperties_2(void);
static void test_ir_minmax_properties_2(void);

static void test_ir_anyof_allof_oneof_1(void);
static void test_ir_anyof_2(void);

static void test_ir_simplify_ands(void);
static void test_ir_simplify_ored_schema(void);

int main(void)
{
  test_ir_empty_schema();
  test_ir_type_constraints();

  test_ir_type_integer();
  test_ir_minimum();

  test_ir_properties();

  test_ir_minmax_properties_1();
  test_ir_minproperties_2();

  test_ir_required();

  test_ir_dependencies();

  /* incomplete tests... placeholders for conversion from cnode tests */
  test_ir_minproperties_3();
  test_ir_maxproperties_1();
  test_ir_maxproperties_2();
  test_ir_minmax_properties_2();

  test_ir_anyof_allof_oneof_1();
  test_ir_anyof_2();

  test_ir_simplify_ands();
  test_ir_simplify_ored_schema();

  return report_tests();
}

/* incomplete tests... placeholders for conversion from cnode tests */
void test_ir_minproperties_3(void)
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
  const struct ir_test tests[] = {
    {
      TRANSLATE,
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

      NULL
    },

    { STOP },
  };

  UNIMPLEMENTED(tests);
}

void test_ir_maxproperties_1(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "maxProperties", 2,
      NULL);

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct ir_test tests[] = {
    {
      TRANSLATE,
      newcnode_switch(&A, 1,
        SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                          newcnode_counts(&A, 0, 2),
                          newcnode_valid(),
                          NULL),
        SJP_NONE),

      NULL
    },

    { STOP },
  };

  UNIMPLEMENTED(tests);
}

void test_ir_maxproperties_2(void)
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
  const struct ir_test tests[] = {
    {
      TRANSLATE,
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

      NULL
    },

    { STOP },
  };

  UNIMPLEMENTED(tests);
}

void test_ir_minmax_properties_2(void)
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
  const struct ir_test tests[] = {
    {
      TRANSLATE,
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

      NULL
    },

    { STOP },
  };

  UNIMPLEMENTED(tests);
}

void test_ir_anyof_allof_oneof_1(void)
{
  struct arena_info A = {0};

  const struct ir_test tests[] = {
    {
      TRANSLATE,
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

      NULL
    },

    {
      TRANSLATE,
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

      NULL
    },

    {
      TRANSLATE,
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

      NULL
    },

    { STOP },
  };

  UNIMPLEMENTED(tests);
}

void test_ir_anyof_2(void)
{
  struct arena_info A = {0};

  const struct ir_test tests[] = {
    {
      TRANSLATE,
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
      NULL
    },

    { STOP },
  };

  UNIMPLEMENTED(tests);
}

static void test_ir_simplify_ands(void)
{
  struct arena_info A = {0};

  const struct ir_test tests[] = {
    // handle AND with only one level...
    {
      TRANSLATE,
      newcnode_switch(&A, 1,
          SJP_NUMBER, newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
          SJP_NONE),

      NULL
    },

    // handle nested ANDs
    {
      TRANSLATE,
      newcnode_switch(&A, 1,
          SJP_NUMBER, newcnode_bool(&A, JVST_CNODE_AND,
                        newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
                        newcnode(&A,JVST_CNODE_NUM_INTEGER),
                        NULL),
          SJP_NONE),

      NULL
    },

    // handle more complex nested ANDs
    {
      TRANSLATE,
      newcnode_switch(&A, 1,
          SJP_NUMBER, newcnode_bool(&A, JVST_CNODE_AND,
                        newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
                        newcnode(&A,JVST_CNODE_NUM_INTEGER),
                        newcnode_range(&A, JVST_CNODE_RANGE_MAX, 0.0, 3.2),
                        NULL),
          SJP_NONE),

      NULL
    },

    { STOP },
  };

  UNIMPLEMENTED(tests);
}

void test_ir_simplify_ored_schema(void)
{
  struct arena_info A = {0};
  const struct ir_test tests[] = {
    {
      TRANSLATE,
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

      NULL
    },

    {
      TRANSLATE,
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

      NULL
    },

    { STOP },
  };

  UNIMPLEMENTED(tests);
}

