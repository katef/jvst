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

static int cnode_trees_equal(struct jvst_cnode *n1, struct jvst_cnode *n2);

static int run_test(const struct cnode_test *t)
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
      fprintf(stderr, "OPTIMIZE pass not implemented\n");
      abort();
      break;

    case OPTIMIZE:
      assert(t->cnode != NULL);
      fprintf(stderr, "OPTIMIZE pass not implemented\n");
      abort();
  }

  // compare result with expected output
  return cnode_trees_equal(result, t->expected);
}

// n1 is actual, n2 is expected
static int cnode_trees_equal(struct jvst_cnode *n1, struct jvst_cnode *n2)
{
  size_t n;
  int ret, failed;
  static char buf1[65536];
  static char buf2[65536];
  size_t i, linenum, off;

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
    return 1;
  }

  fprintf(stderr,
      "cnode trees are not equal:\n"
      "Expected tree:\n%s\n\n"
      "Actual tree:\n%s\n",
      buf2,buf1);

  // slightly tedious job of finding first difference and printing out
  // both up to that point...
  for (i=0, linenum=1, off=0; i < sizeof buf1; i++) {
    size_t j;

    if (buf1[i] == buf2[i]) {
      if (buf1[i] == '\0') {
        fprintf(stderr, "INTERNAL ERROR: cannot find difference.\n");
        abort();
      }

      if (buf1[i] == '\n') {
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

    if (!run_test(&tests[i])) {
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

int main(void)
{
  test_xlate_empty_schema();

  /*
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
  */

  return report_tests();
}
