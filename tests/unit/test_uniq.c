#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "jvst_macros.h"

#include "sjp_lexer.h"
#include "sjp_parser.h"
#include "sjp_testing.h"

#include "validate_uniq.h"

#include "validate_testing.h"

const char END[4] = "END";

struct uniq_step {
  const char *buf;
  int not_uniq;
};

struct uniq_test {
  const char *input;
  struct uniq_step *steps;
};

static int
run_test(const char *fname, const struct uniq_test *t)
{
  struct sjp_lexer l = { 0 };
  struct sjp_parser p = { 0 };

  char stack[SJP_PARSER_MIN_STACK];
  char lbuf[4096] = { 0 };
  char buf[65536] = { 0 };

  sjp_lexer_init(&l);
  sjp_parser_init(&p, &stack[0], sizeof stack, &lbuf[0], sizeof lbuf);

  size_t len = strlen(t->input);
  assert(len < sizeof buf);
  memcpy(&buf[0], &t->input[0], len);

  sjp_parser_more(&p, &buf[0], len);

  enum SJP_RESULT ret;
  struct sjp_event evt = { 0 };

  // first event should be an SJP_ARRAY_BEG event
  ret = sjp_parser_next(&p, &evt);
  assert(ret == SJP_OK);
  assert(evt.type == SJP_ARRAY_BEG);

  struct jvst_vm_unique *uniq = jvst_vm_uniq_initialize();

  int nerrs = 0;

  int narr = 1; // keeps track of array beg/end, so we know when we've hit the pair to the opening token
  size_t i;
  for (i=0; narr > 0 && nerrs == 0; i++) {
    ret = sjp_parser_next(&p, &evt);
    assert( !SJP_ERROR(ret) );

    fprintf(stderr, "%-25s %p [%3zu] %s\n", fname, (void *)t, i, evt2name(evt.type));

    if (evt.type == SJP_ARRAY_BEG) {
      narr++;
    }

    if (evt.type == SJP_ARRAY_END && --narr == 0) {
      break;
    }

    assert(t->steps[i].buf != &END[0]);

    int uniq_ret = jvst_vm_uniq_evaluate(uniq, ret, &evt);
    int is_uniq = (uniq_ret != JVST_INVALID);

    int expect_uniq = !t->steps[i].not_uniq;
    if (expect_uniq != is_uniq) {
      fprintf(stderr, "%s ERROR: step %zu: expected unique=%d, but found %d\n",
          fname, i, expect_uniq, is_uniq);
      nerrs++;
    }

    if (t->steps[i].buf != NULL) {
      size_t blen = strlen(t->steps[i].buf);
      struct jvst_vm_unique_stack *stack = &uniq->stack[uniq->top];
      if (blen != stack->buf.len || memcmp(t->steps[i].buf, stack->buf.ptr, blen) != 0) {
        fprintf(stderr, "%s ERROR: step %zu: buffers don't match\n", fname, i);
        fprintf(stderr, "  expected: '%s'\n", t->steps[i].buf);
        fprintf(stderr, "  actual  : '%.*s'\n\n", (int)stack->buf.len, stack->buf.ptr);
        nerrs++;
      }
    }
  }

  if (uniq->top != 0) {
    fprintf(stderr, "%s ERROR: at end, unique stack top is %zu, not 0\n", fname, uniq->top);
    nerrs++;
  }

  jvst_vm_uniq_finalize(uniq);

  sjp_lexer_close(&l);
  sjp_parser_close(&p);

  return (nerrs == 0);
}

#define UNIMPLEMENTED(testlist) do{ nskipped++; (void)testlist; }while(0)
#define RUNTESTS(testlist) runtests(__func__, (testlist))
static void runtests(const char *testname, const struct uniq_test tests[])
{
  int i;

  for (i=0; tests[i].input != NULL; i++) {
    ntest++;

    if (!run_test(testname, &tests[i])) {
      printf("%s[%d]: failed\n", testname, i+1);
      nfail++;
    }
  }
}

static struct uniq_step step_pool[1024];
struct uniq_arena {
  size_t ind;
};

static struct uniq_step *usteps(struct uniq_arena *U, ...)
{
  struct uniq_step *st;
  va_list args;
  size_t ind;

  va_start(args, U);
  st = &step_pool[U->ind];

  ind=0;
  for(;;) {
    int not_uniq;

    st[ind].buf = va_arg(args, const char *);
    if (st[ind].buf == &END[0]) {
      ind++;
      break;
    }

    st[ind++].not_uniq = va_arg(args, int);
  }

  U->ind += ind;
  va_end(args);
  return st;
}

static void test_number_uniqueness(void)
{
  struct uniq_arena U = { 0 };

  struct uniq_test tests[] = {
    {
      "[ 1, 2, 3, 4, 5 ]",
      usteps(&U,
          "", 0,        // 1
          "", 0,        // 2
          "", 0,        // 3
          "", 0,        // 4
          "", 0,        // 5
          END),
    },

    {
      "[ 1, 2, 3, 4, 1 ]",
      usteps(&U,
          "", 0,        // 1
          "", 0,        // 2
          "", 0,        // 3
          "", 0,        // 4
          "", 1,        // 1
          END),
    },
    { NULL },
  };

  RUNTESTS(tests);
}

static void test_string_uniqueness(void)
{
  struct uniq_arena U = { 0 };

  struct uniq_test tests[] = {
    {
      "[ \"this\", \"that\", \"this that\" ]",
      usteps(&U,
          "", 0,        // "this"
          "", 0,        // "that"
          "", 0,        // "this that"
          END),
    },

    {
      "[ \"this\", \"that\", \"this that\", \"that\" ]",
      usteps(&U,
          "", 0,        // "this"
          "", 0,        // "that"
          "", 0,        // "this that"
          "", 1,        // "that"
          END),
    },
    { NULL },
  };

  RUNTESTS(tests);
}

static void test_literal_uniqueness(void)
{
  struct uniq_arena U = { 0 };

  struct uniq_test tests[] = {
    {
      "[ true, false, null ]",
      usteps(&U,
          "", 0,        // true
          "", 0,        // false
          "", 0,        // null
          END),
    },

    {
      "[ true, false, null, false ]",
      usteps(&U,
          "", 0,        // true
          "", 0,        // false
          "", 0,        // null
          "", 1,        // false
          END),
    },
    { NULL },
  };

  RUNTESTS(tests);
}

static void test_array_uniqueness(void)
{
  struct uniq_arena U = { 0 };

  struct uniq_test tests[] = {
    {
      "[ [] ]",
      usteps(&U,
          "", 0, "", 0, // []
          END),
    },

    {
      "[ [], [1] ]",
      usteps(&U,
          "", 0, "", 0, // []
          "", 0,        // [
                "", 0,  //      1
          "", 0,        // ]
          END),
    },

    {
      "[ [], [1], [1,2], [2,1] ]",
      usteps(&U,
          "", 0, "", 0, // []

          "", 0,        // [
                "", 0,  //      1
          "", 0,        // ]

          "", 0,        // [
                "", 0,  //      1
                "", 0,  //      2
          "", 0,        // ]

          "", 0,        // [
                "", 0,  //      2
                "", 0,  //      1
          "", 0,        // ]
          END),
    },

    {
      "[ [], [1], [1,2], [2,1], [1] ]",
      usteps(&U,
          "", 0, "", 0, // []

          "", 0,        // [
                "", 0,  //      1
          "", 0,        // ]

          "", 0,        // [
                "", 0,  //      1
                "", 0,  //      2
          "", 0,        // ]

          "", 0,        // [
                "", 0,  //      2
                "", 0,  //      1
          "", 0,        // ]

          "", 0,        // [
                "", 0,  //      1
          "", 1,        // ]
          END),
    },

    { NULL },
  };

  RUNTESTS(tests);
}

static void test_object_uniqueness(void)
{
  struct uniq_arena U = { 0 };

  struct uniq_test tests[] = {
    {
      "[ {} ]",
      usteps(&U,
          "", 0, "", 0, // {}
          END),
    },

    {
      "[ { \"a\" : 3 } ]",
      usteps(&U,
          "", 0,        // {
                "", 0,  //   "a"
                "", 0,  //   3
          "", 0,        // }
          END),
    },

    {
      "[ { \"a\" : 3 }, { \"b\" : 2, \"a\" : 3 } ]",
      usteps(&U,
          "", 0,        // {
                "", 0,  //   "a"
                "", 0,  //   3
          "", 0,        // }
          "", 0,        // {
                "", 0,  //   "b"
                "", 0,  //   2

                "", 0,  //   "a"
                "", 0,  //   3
          "", 0,        // }
          END),
    },

    // property order does not matter...
    {
      "[ { \"b\" : 2, \"a\" : 3 }, { \"a\" : 3, \"b\" : 2 } ]",
      usteps(&U,
          "", 0,        // {
                "", 0,  //   "b"
                "", 0,  //   2

                "", 0,  //   "a"
                "", 0,  //   3
          "", 0,        // }
          "", 0,        // {
                "", 0,  //  "a"
                "", 0,  //  3

                "", 0,  //  "b"
                "", 0,  //  2
          "", 1,        // }
          END),
    },

    { NULL },
  };

  RUNTESTS(tests);
}



int main(void)
{
  test_number_uniqueness();
  test_string_uniqueness();
  test_literal_uniqueness();
  test_array_uniqueness();
  test_object_uniqueness();

  return report_tests();
}
