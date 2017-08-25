#include "validate_testing.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "jvst_macros.h"

#include "validate_op.h"
#include "validate_ir.h"

struct op_test {
  struct jvst_cnode *ctree;
  struct jvst_ir_stmt *ir;
  struct jvst_op_program *prog;
};

static int
op_progs_equal(const char *fname, struct jvst_op_program *p1, struct jvst_op_program *p2);

static int
run_test(const char *fname, const struct op_test *t)
{
  struct jvst_cnode *simplified, *canonified;
  struct jvst_ir_stmt *ir;
  struct jvst_op_program *result;
  int ret;

  assert(t->ctree != NULL);
  assert(t->ir != NULL);
  assert(t->prog != NULL);

  assert(t->ir != NULL);

  simplified = jvst_cnode_simplify(t->ctree);
  canonified = jvst_cnode_canonify(simplified);
  ir = jvst_ir_translate(canonified);

  // jvst_ir_print(ir);
  result = jvst_op_assemble(ir);

  // fprintf(stderr, "\n");
  // jvst_op_print(result);

  ret = op_progs_equal(fname, result, t->prog);
  if (!ret) {
    // jvst_ir_print(ir);
  }

  return ret;
}

// n1 is actual, n2 is expected
static int
op_progs_equal(const char *fname, struct jvst_op_program *p1, struct jvst_op_program *p2)
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
  if (jvst_op_dump(p1, buf1, sizeof buf1) != 0) {
    fprintf(stderr, "buffer for program 1 not large enough (currently %zu bytes)\n",
        sizeof buf1);
  }

  if (jvst_op_dump(p2, buf2, sizeof buf2) != 0) {
    fprintf(stderr, "buffer for program 2 not large enough (currently %zu bytes)\n",
        sizeof buf2);
  }

  if (strncmp(buf1, buf2, sizeof buf1) == 0) {
    // fprintf(stderr, "TREE:\n%s\n", buf1);
    return 1;
  }

  fprintf(stderr, "test %s op programs are not equal:\n", fname);
  {
    size_t i,n,l;

    fprintf(stderr, "Expected program:\n");
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

    fprintf(stderr, "Actual program:\n");
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

  buffer_diff(stderr, buf1, buf2, sizeof buf1);

  return 0;
}

#define UNIMPLEMENTED(testlist) do{ nskipped++; (void)testlist; }while(0)
#define RUNTESTS(testlist) runtests(__func__, (testlist))
static void runtests(const char *testname, const struct op_test tests[])
{
  int i;

  (void)testname;

  for (i=0; tests[i].ir != NULL; i++) {
    ntest++;

    if (!run_test(testname, &tests[i])) {
      printf("%s[%d]: failed\n", testname, i+1);
      nfail++;
    }
  }
}

static void
test_op_empty_schema(void)
{
  struct arena_info A = {0};

  const struct op_test tests[] = {
    {
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
      ),

      newop_program(&A,
          newop_proc(&A,
            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "L_2",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_ARRAY_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            NULL
          ),

          NULL
      ),
    },

    { NULL },
  };

  RUNTESTS(tests);
}

static void test_op_type_constraints(void)
{
  struct arena_info A = {0};

  const struct op_test tests[] = {
    {
      newcnode_switch(&A, 0, SJP_NUMBER, newcnode_valid(), SJP_NONE),

      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_NUMBER),
            newir_stmt(&A, JVST_IR_STMT_VALID),
            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
          ),
          NULL
      ),

      newop_program(&A,
          newop_proc(&A,
            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_NUMBER)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          NULL
      ),

    },

    {
      newcnode_switch(&A, 0, SJP_OBJECT_BEG, newcnode_valid(), SJP_NONE),

      newir_frame(&A,
          newir_stmt(&A, JVST_IR_STMT_TOKEN),
          newir_if(&A, newir_istok(&A, SJP_OBJECT_BEG),
            newir_stmt(&A, JVST_IR_STMT_VALID),
            newir_invalid(&A, JVST_INVALID_UNEXPECTED_TOKEN, "unexpected token")
          ),
          NULL
      ),

      newop_program(&A,
          newop_proc(&A,
            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_BEG)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          NULL
      ),

    },

    {
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

      newop_program(&A,
          newop_proc(&A,
            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_STRING)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "L_2",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_BEG)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          NULL
      ),

    },

    { NULL },
  };

  RUNTESTS(tests);
}

static void test_op_type_integer(void)
{
  struct arena_info A = {0};
  struct ast_schema schema = {
    .types = JSON_VALUE_INTEGER,
  };

  const struct op_test tests[] = {
    {
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

      newop_program(&A,
          newop_proc(&A,
            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_NUMBER)),
            newop_br(&A, JVST_OP_CBT, "L_1"),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "L_1",
            newop_cmp(&A, JVST_OP_FINT, oparg_tnum(), oparg_none()),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_2",
            newop_invalid(&A, 2),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          NULL
      ),

    },

    { NULL },
  };

  RUNTESTS(tests);
}

void test_op_minimum(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "minimum", 1.1,
      NULL);

  const struct op_test tests[] = {
    {
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

      newop_program(&A,
          newop_proc(&A,
            opfloat, 1.1,

            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_NUMBER)),
            newop_br(&A, JVST_OP_CBT, "L_1"),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "L_1",
            newop_load(&A, JVST_OP_FLOAD, oparg_ftmp(0), oparg_lit(0)),
            newop_cmp(&A, JVST_OP_FGE, oparg_tnum(), oparg_ftmp(0)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_3",
            newop_invalid(&A, 3),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          NULL
      ),

    },

    { NULL },
  };

  RUNTESTS(tests);
}

void test_op_properties(void)
{
  struct arena_info A = {0};

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct op_test tests[] = {
    {
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
      ),

      newop_program(&A,
          newop_proc(&A,
            opdfa, 1,

            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_BEG)),
            newop_br(&A, JVST_OP_CBT, "loop_2"),

            oplabel, "L_11",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "L_14",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_ARRAY_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "loop_2",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "L_6",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "M_8"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(1)),
            newop_br(&A, JVST_OP_CBT, "M_9"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(2)),

            oplabel, "M_10",
            newop_call(&A, 2),
            newop_br(&A, JVST_OP_BR, "loop_2"),

            oplabel, "M_9",
            newop_call(&A, 1),
            newop_br(&A, JVST_OP_BR, "loop_2"),

            oplabel, "M_8",
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_2"),

            NULL
          ),

          newop_proc(&A,
            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_STRING)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          newop_proc(&A,
            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_NUMBER)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          NULL
      ),

    },

    {
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
      ),

      newop_program(&A,
          newop_proc(&A,
            opdfa, 1,

            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_BEG)),
            newop_br(&A, JVST_OP_CBT, "loop_2"),

            oplabel, "L_11",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "L_14",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_ARRAY_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "loop_2",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "L_6",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "M_8"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(1)),
            newop_br(&A, JVST_OP_CBT, "M_9"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(2)),

            oplabel, "M_10",
            newop_call(&A, 2),
            newop_br(&A, JVST_OP_BR, "loop_2"),

            oplabel, "M_9",
            newop_call(&A, 1),
            newop_br(&A, JVST_OP_BR, "loop_2"),

            oplabel, "M_8",
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_2"),

            NULL
          ),

          newop_proc(&A,
            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            NULL
          ),

          newop_proc(&A,
            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_NUMBER)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          NULL
      ),

    },

    { NULL },
  };

  RUNTESTS(tests);
}

void test_op_minmax_properties_1(void)
{
  struct arena_info A = {0};

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct op_test tests[] = {
    {
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
      ),

      newop_program(&A,
          newop_proc(&A,
            opslots, 1,
            opdfa, 1,

            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_BEG)),
            newop_br(&A, JVST_OP_CBT, "loop_2"),

            oplabel, "L_12",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "L_15",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_ARRAY_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "loop_2",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "loop_end_2"),

            oplabel, "L_6",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),

            oplabel, "M_8",
            newop_instr(&A, JVST_OP_CONSUME),

            oplabel, "match_join_7",
            newop_incr(&A, 0),
            newop_br(&A, JVST_OP_BR, "loop_2"),

            oplabel, "loop_end_2",
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(0), oparg_slot(0)),
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(1), oparg_lit(1)),
            newop_cmp(&A, JVST_OP_IGE, oparg_itmp(0), oparg_itmp(1)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_4",
            newop_invalid(&A, 4),

            NULL
          ),

          NULL
      ),
    },

    {
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
      ),

      newop_program(&A,
          newop_proc(&A,
            opslots, 1,
            opdfa, 1,

            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_BEG)),
            newop_br(&A, JVST_OP_CBT, "loop_2"),

            oplabel, "L_12",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "L_15",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_ARRAY_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "loop_2",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "loop_end_2"),

            oplabel, "L_6",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),

            oplabel, "M_8",
            newop_instr(&A, JVST_OP_CONSUME),

            oplabel, "match_join_7",
            newop_incr(&A, 0),
            newop_br(&A, JVST_OP_BR, "loop_2"),

            oplabel, "loop_end_2",
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(0), oparg_slot(0)),
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(1), oparg_lit(2)),
            newop_cmp(&A, JVST_OP_ILE, oparg_itmp(0), oparg_itmp(1)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_5",
            newop_invalid(&A, 5),

            NULL
          ),

          NULL
      ),
    },

    {
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
      ),

      newop_program(&A,
          newop_proc(&A,
            opslots, 1,
            opdfa, 1,

            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_BEG)),
            newop_br(&A, JVST_OP_CBT, "loop_2"),

            oplabel, "L_15",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "L_18",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_ARRAY_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "loop_2",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "loop_end_2"),

            oplabel, "L_6",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),

            oplabel, "M_8",
            newop_instr(&A, JVST_OP_CONSUME),

            oplabel, "match_join_7",
            newop_incr(&A, 0),
            newop_br(&A, JVST_OP_BR, "loop_2"),

            oplabel, "loop_end_2",
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(2), oparg_slot(0)),
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(3), oparg_lit(2)),
            newop_cmp(&A, JVST_OP_IGE, oparg_itmp(2), oparg_itmp(3)),
            newop_br(&A, JVST_OP_CBT, "L_10"),

            oplabel, "invalid_4",
            newop_invalid(&A, 4),

            oplabel, "L_10",
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(0), oparg_slot(0)),
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(1), oparg_lit(5)),
            newop_cmp(&A, JVST_OP_ILE, oparg_itmp(0), oparg_itmp(1)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_5",
            newop_invalid(&A, 5),

            NULL
          ),

          NULL
      ),
    },

    { NULL },
  };

  RUNTESTS(tests);
}

void test_op_minproperties_2(void)
{
  struct arena_info A = {0};

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct op_test tests[] = {
    {
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

                      // match "foo"
                      newir_case(&A, 1,
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

                      // match "bar"
                      newir_case(&A, 2,
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
      ),

      newop_program(&A,
          newop_proc(&A,
            opslots, 1,
            opdfa, 1,

            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_BEG)),
            newop_br(&A, JVST_OP_CBT, "loop_2"),

            oplabel, "L_14",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "L_17",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_ARRAY_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "loop_2",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "loop_end_2"),

            oplabel, "L_6",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "M_8"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(1)),
            newop_br(&A, JVST_OP_CBT, "M_9"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(2)),

            oplabel, "M_10",
            newop_call(&A, 2),

            oplabel, "match_join_7",
            newop_incr(&A, 0),
            newop_br(&A, JVST_OP_BR, "loop_2"),

            oplabel, "M_9",
            newop_call(&A, 1),
            newop_br(&A, JVST_OP_BR, "match_join_7"),

            oplabel, "M_8",
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "match_join_7"),

            oplabel, "loop_end_2",
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(0), oparg_slot(0)),
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(1), oparg_lit(1)),
            newop_cmp(&A, JVST_OP_IGE, oparg_itmp(0), oparg_itmp(1)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_4",
            newop_invalid(&A, 4),

            NULL
          ),

          newop_proc(&A,
            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_STRING)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          newop_proc(&A,
            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_NUMBER)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          NULL
      ),

    },

    { NULL },
  };

  RUNTESTS(tests);
}

void test_op_required(void)
{
  struct arena_info A = {0};

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct op_test tests[] = {
    {
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
      ),

      newop_program(&A,
          newop_proc(&A,
            opslots, 1,
            opdfa, 1,

            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_BEG)),
            newop_br(&A, JVST_OP_CBT, "loop_2"),

            oplabel, "L_14",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "L_17",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_ARRAY_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "loop_2",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "loop_end_2"),

            oplabel, "L_6",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "M_8"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(1)),
            newop_br(&A, JVST_OP_CBT, "M_9"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(2)),

            oplabel, "M_10",
            newop_call(&A, 2),
            newop_bitop(&A, JVST_OP_BSET, 0, 0),
            newop_br(&A, JVST_OP_BR, "loop_2"),

            oplabel, "M_9",
            newop_call(&A, 1),
            newop_br(&A, JVST_OP_BR, "loop_2"),

            oplabel, "M_8",
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_2"),

            oplabel, "loop_end_2",
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(0), oparg_slot(0)),
            newop_instr2(&A, JVST_OP_BAND, oparg_itmp(0), oparg_lit(1)),
            newop_cmp(&A, JVST_OP_IEQ, oparg_itmp(0), oparg_lit(1)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_6",
            newop_invalid(&A, 6),

            NULL
          ),

          newop_proc(&A,
            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_STRING)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          newop_proc(&A,
            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_NUMBER)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          NULL
      ),

    },

    { NULL },
  };

  RUNTESTS(tests);
}

void test_op_dependencies(void)
{
  struct arena_info A = {0};

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct op_test tests[] = {
    {
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

                                // match "foo"
                                newir_case(&A, 1,
                                  newmatchset(&A, RE_LITERAL,  "foo", -1),
                                  newir_seq(&A,
                                    newir_bitop(&A, JVST_IR_STMT_BSET, 0, "reqmask", 1),
                                    newir_stmt(&A, JVST_IR_STMT_CONSUME),
                                    NULL
                                  )
                                ),

                                // match "bar"
                                newir_case(&A, 2,
                                  newmatchset(&A, RE_LITERAL,  "bar", -1),
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
      ),

      newop_program(&A,
          newop_proc(&A,
            opsplit, 2, 1, 2,

            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_BEG)),
            newop_br(&A, JVST_OP_CBT, "L_1"),

            oplabel, "L_5",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "L_8",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_ARRAY_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "L_1",
            newop_instr2(&A, JVST_OP_SPLIT, oparg_lit(0), oparg_itmp(0)),
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(1), oparg_lit(1)),
            newop_cmp(&A, JVST_OP_IGE, oparg_itmp(0), oparg_itmp(1)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_7",
            newop_invalid(&A, 7),
            NULL
          ),

          newop_proc(&A,
            opdfa, 1,

            oplabel, "loop_0",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "L_4",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "M_6"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(1)),

            oplabel, "invalid_8",
            newop_invalid(&A, 8),

            oplabel, "M_6",
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          newop_proc(&A,
            opslots, 1,
            opdfa, 1,

            oplabel, "loop_0",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "loop_end_0"),

            oplabel, "L_4",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "M_6"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(1)),
            newop_br(&A, JVST_OP_CBT, "M_7"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(2)),

            oplabel, "M_8",
            newop_bitop(&A, JVST_OP_BSET, 0, 1),
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "M_7",
            newop_bitop(&A, JVST_OP_BSET, 0, 0),
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "M_6",
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "loop_end_0",
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(0), oparg_slot(0)),
            newop_instr2(&A, JVST_OP_BAND, oparg_itmp(0), oparg_lit(3)),
            newop_cmp(&A, JVST_OP_IEQ, oparg_itmp(0), oparg_lit(3)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_6",
            newop_invalid(&A, 6),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),
              
          NULL
      ),

    },

    {
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
      ),

      newop_program(&A,
          newop_proc(&A,
            opsplit, 2, 1, 2,

            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_BEG)),
            newop_br(&A, JVST_OP_CBT, "L_1"),

            oplabel, "L_5",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "L_8",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_ARRAY_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "L_1",
            newop_instr2(&A, JVST_OP_SPLIT, oparg_lit(0), oparg_itmp(0)),
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(1), oparg_lit(1)),
            newop_cmp(&A, JVST_OP_IGE, oparg_itmp(0), oparg_itmp(1)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_7",
            newop_invalid(&A, 7),
            NULL
          ),

          newop_proc(&A,
            opdfa, 1,

            oplabel, "loop_0",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "L_4",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "M_6"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(1)),

            oplabel, "invalid_8",
            newop_invalid(&A, 8),

            oplabel, "M_6",
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          newop_proc(&A,
            opslots, 1,
            opdfa, 1,

            oplabel, "loop_0",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "loop_end_0"),

            oplabel, "L_4",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "M_6"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(1)),
            newop_br(&A, JVST_OP_CBT, "M_7"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(2)),
            newop_br(&A, JVST_OP_CBT, "M_8"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(3)),

            oplabel, "M_9",
            newop_bitop(&A, JVST_OP_BSET, 0, 0),
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "M_8",
            newop_bitop(&A, JVST_OP_BSET, 0, 1),
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "M_7",
            newop_bitop(&A, JVST_OP_BSET, 0, 2),
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "M_6",
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "loop_end_0",
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(0), oparg_slot(0)),
            newop_instr2(&A, JVST_OP_BAND, oparg_itmp(0), oparg_lit(7)),
            newop_cmp(&A, JVST_OP_IEQ, oparg_itmp(0), oparg_lit(7)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_6",
            newop_invalid(&A, 6),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),
              
          NULL
      ),

    },

    {
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
      ),

      newop_program(&A,
          newop_proc(&A,
            opsplit, 4, 1, 2, 3, 4,
            opslots, 1,

            oplabel, "entry",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_BEG)),
            newop_br(&A, JVST_OP_CBT, "L_1"),

            oplabel, "L_8",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "L_11",
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_ARRAY_END)),
            newop_br(&A, JVST_OP_CBT, "invalid_1"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            oplabel, "invalid_1",
            newop_invalid(&A, 1),

            oplabel, "L_1",
            newop_instr2(&A, JVST_OP_SPLITV, oparg_lit(0), oparg_slot(0)),
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(0), oparg_slot(0)),
            newop_instr2(&A, JVST_OP_BAND, oparg_itmp(0), oparg_lit(1)),
            newop_cmp(&A, JVST_OP_INEQ, oparg_itmp(0), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "and_true_5"),

            oplabel, "or_false_6",
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(1), oparg_slot(0)),
            newop_instr2(&A, JVST_OP_BAND, oparg_itmp(1), oparg_lit(2)),
            newop_cmp(&A, JVST_OP_IEQ, oparg_itmp(1), oparg_lit(2)),
            newop_br(&A, JVST_OP_CBT, "and_true_5"),

            oplabel, "invalid_7",
            newop_invalid(&A, 7),

            oplabel, "and_true_5",
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(2), oparg_slot(0)),
            newop_instr2(&A, JVST_OP_BAND, oparg_itmp(2), oparg_lit(4)),
            newop_cmp(&A, JVST_OP_INEQ, oparg_itmp(2), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "or_false_7",
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(3), oparg_slot(0)),
            newop_instr2(&A, JVST_OP_BAND, oparg_itmp(3), oparg_lit(8)),
            newop_cmp(&A, JVST_OP_IEQ, oparg_itmp(3), oparg_lit(8)),
            newop_br(&A, JVST_OP_CBT, "valid"),
            newop_br(&A, JVST_OP_BR, "invalid_7"),

            NULL
          ),

          newop_proc(&A,
            opdfa, 1,

            oplabel, "loop_0",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "L_4",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "M_6"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(1)),

            oplabel, "invalid_8",
            newop_invalid(&A, 8),

            oplabel, "M_6",
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          newop_proc(&A,
            opslots, 1,
            opdfa, 1,

            oplabel, "loop_0",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "loop_end_0"),

            oplabel, "L_4",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "M_6"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(1)),
            newop_br(&A, JVST_OP_CBT, "M_7"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(2)),
            newop_br(&A, JVST_OP_CBT, "M_8"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(3)),

            oplabel, "M_9",
            newop_bitop(&A, JVST_OP_BSET, 0, 0),
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "M_8",
            newop_bitop(&A, JVST_OP_BSET, 0, 1),
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "M_7",
            newop_bitop(&A, JVST_OP_BSET, 0, 2),
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "M_6",
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "loop_end_0",
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(0), oparg_slot(0)),
            newop_instr2(&A, JVST_OP_BAND, oparg_itmp(0), oparg_lit(7)),
            newop_cmp(&A, JVST_OP_IEQ, oparg_itmp(0), oparg_lit(7)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_6",
            newop_invalid(&A, 6),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),
              
          newop_proc(&A,
            opdfa, 1,

            oplabel, "loop_0",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "L_4",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "M_6"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(1)),

            oplabel, "invalid_8",
            newop_invalid(&A, 8),

            oplabel, "M_6",
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),

          newop_proc(&A,
            opslots, 1,
            opdfa, 1,

            oplabel, "loop_0",
            newop_instr(&A, JVST_OP_TOKEN),
            newop_cmp(&A, JVST_OP_IEQ, oparg_tt(), oparg_tok(SJP_OBJECT_END)),
            newop_br(&A, JVST_OP_CBT, "loop_end_0"),

            oplabel, "L_4",
            newop_match(&A, 0),
            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(0)),
            newop_br(&A, JVST_OP_CBT, "M_6"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(1)),
            newop_br(&A, JVST_OP_CBT, "M_7"),

            newop_cmp(&A, JVST_OP_IEQ, oparg_m(), oparg_lit(2)),

            oplabel, "M_8",
            newop_bitop(&A, JVST_OP_BSET, 0, 0),
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "M_7",
            newop_bitop(&A, JVST_OP_BSET, 0, 1),
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "M_6",
            newop_instr(&A, JVST_OP_CONSUME),
            newop_br(&A, JVST_OP_BR, "loop_0"),

            oplabel, "loop_end_0",
            newop_load(&A, JVST_OP_ILOAD, oparg_itmp(0), oparg_slot(0)),
            newop_instr2(&A, JVST_OP_BAND, oparg_itmp(0), oparg_lit(3)),
            newop_cmp(&A, JVST_OP_IEQ, oparg_itmp(0), oparg_lit(3)),
            newop_br(&A, JVST_OP_CBT, "valid"),

            oplabel, "invalid_6",
            newop_invalid(&A, 6),

            oplabel, "valid",
            newop_instr(&A, JVST_OP_VALID),

            NULL
          ),
              
          NULL
      ),

    },
#if 0
#endif /* 0 */

    { NULL },
  };

  const struct op_test unfinished_tests[] = {
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

    { NULL },
  };

  (void)unfinished_tests;
  RUNTESTS(tests);
}

/* incomplete tests... placeholders for conversion from cnode tests */
static void test_op_minproperties_3(void);
static void test_op_maxproperties_1(void);
static void test_op_maxproperties_2(void);
static void test_op_minmax_properties_2(void);

static void test_op_anyof_allof_oneof_1(void);
static void test_op_anyof_2(void);

static void test_op_simplify_ands(void);
static void test_op_simplify_ored_schema(void);

int main(void)
{
  test_op_empty_schema();
  test_op_type_constraints();

  test_op_type_integer();
  test_op_minimum();

  test_op_properties();

  test_op_minmax_properties_1();
  test_op_minproperties_2();

  test_op_required();

  test_op_dependencies();

  /* incomplete tests... placeholders for conversion from cnode tests */
  test_op_minproperties_3();
  test_op_maxproperties_1();
  test_op_maxproperties_2();
  test_op_minmax_properties_2();

  test_op_anyof_allof_oneof_1();
  test_op_anyof_2();

  test_op_simplify_ands();
  test_op_simplify_ored_schema();

  return report_tests();
}

/* incomplete tests... placeholders for conversion from cnode tests */
void test_op_minproperties_3(void)
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
  const struct op_test tests[] = {
    {
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

    { NULL },
  };

  UNIMPLEMENTED(tests);
}

void test_op_maxproperties_1(void)
{
  struct arena_info A = {0};
  struct ast_schema *schema = newschema_p(&A, 0,
      "maxProperties", 2,
      NULL);

  // initial schema is not reduced (additional constraints are ANDed
  // together).  Reduction will occur on a later pass.
  const struct op_test tests[] = {
    {
      newcnode_switch(&A, 1,
        SJP_OBJECT_BEG, newcnode_bool(&A,JVST_CNODE_AND,
                          newcnode_counts(&A, 0, 2),
                          newcnode_valid(),
                          NULL),
        SJP_NONE),

      NULL
    },

    { NULL },
  };

  UNIMPLEMENTED(tests);
}

void test_op_maxproperties_2(void)
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
  const struct op_test tests[] = {
    {
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

    { NULL },
  };

  UNIMPLEMENTED(tests);
}

void test_op_minmax_properties_2(void)
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
  const struct op_test tests[] = {
    {
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

    { NULL },
  };

  UNIMPLEMENTED(tests);
}

void test_op_anyof_allof_oneof_1(void)
{
  struct arena_info A = {0};

  const struct op_test tests[] = {
    {
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

    { NULL },
  };

  UNIMPLEMENTED(tests);
}

void test_op_anyof_2(void)
{
  struct arena_info A = {0};

  const struct op_test tests[] = {
    {
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

    { NULL },
  };

  UNIMPLEMENTED(tests);
}

static void test_op_simplify_ands(void)
{
  struct arena_info A = {0};

  const struct op_test tests[] = {
    // handle AND with only one level...
    {
      newcnode_switch(&A, 1,
          SJP_NUMBER, newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
          SJP_NONE),

      NULL
    },

    // handle nested ANDs
    {
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
      newcnode_switch(&A, 1,
          SJP_NUMBER, newcnode_bool(&A, JVST_CNODE_AND,
                        newcnode_range(&A, JVST_CNODE_RANGE_MIN, 1.1, 0.0),
                        newcnode(&A,JVST_CNODE_NUM_INTEGER),
                        newcnode_range(&A, JVST_CNODE_RANGE_MAX, 0.0, 3.2),
                        NULL),
          SJP_NONE),

      NULL
    },

    { NULL },
  };

  UNIMPLEMENTED(tests);
}

void test_op_simplify_ored_schema(void)
{
  struct arena_info A = {0};
  const struct op_test tests[] = {
    {
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

    { NULL },
  };

  UNIMPLEMENTED(tests);
}

