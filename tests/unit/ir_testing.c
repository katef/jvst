#include "ir_testing.h"

#include <string.h>
#include <stdio.h>

#ifndef PRINT_IR
#  define PRINT_IR 0
#endif /* PRINT_IR */

int
run_ir_test(const char *fname, const struct ir_test *t)
{
	struct jvst_cnode *simplified, *canonified;
	struct jvst_ir_stmt *translated, *result, *expected;

	assert(t->ctree != NULL);

	switch (t->type) {
	default:
	case STOP:
		fprintf(stderr, "%s:%d (%s) SHOULD NOT REACH!\n",
			__FILE__, __LINE__, __func__);
		abort();

	case TRANSLATE:
		assert(t->translated != NULL);

		expected = t->translated;
		simplified = jvst_cnode_simplify(t->ctree);
		canonified = jvst_cnode_canonify(simplified);
		result = jvst_ir_translate(canonified);
		break;

	case LINEARIZE:
		assert(t->xformed != NULL);

		expected = t->xformed;
		simplified = jvst_cnode_simplify(t->ctree);
		canonified = jvst_cnode_canonify(simplified);
		translated = jvst_ir_translate(canonified);
		result = jvst_ir_linearize(translated);
		break;

	case FLATTEN:
		{
			struct jvst_ir_stmt *linearized;
			assert(t->xformed != NULL);

			expected = t->xformed;
			simplified = jvst_cnode_simplify(t->ctree);
			canonified = jvst_cnode_canonify(simplified);
			translated = jvst_ir_translate(canonified);
			linearized = jvst_ir_linearize(translated);
			result = jvst_ir_flatten(linearized);
		}
		break;
	}

	assert(expected != NULL);

#if PRINT_IR
	jvst_ir_print(result);
#endif /* PRINT_IR */

	return ir_trees_equal(fname, result, expected);
}

// n1 is actual, n2 is expected
int
ir_trees_equal(const char *fname, struct jvst_ir_stmt *n1, struct jvst_ir_stmt *n2)
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
		fprintf(stderr, "Expected tree:\n");
		print_buffer_with_lines(stderr, buf2, sizeof buf2);
		fprintf(stderr, "\n");

		fprintf(stderr, "Actual tree:\n");
		print_buffer_with_lines(stderr, buf1, sizeof buf1);
		fprintf(stderr, "\n");
	}
	fprintf(stderr, "\n\n");

	buffer_diff(stderr, buf1, buf2, sizeof buf1);
	return 0;
}

void
run_ir_tests(const char *testname, const struct ir_test tests[])
{
	int i;

	for (i=0; tests[i].type != STOP; i++) {
		ntest++;

		if (!run_ir_test(testname, &tests[i])) {
			printf("%s[%d]: failed\n", testname, i+1);
			nfail++;
		}
	}
}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
