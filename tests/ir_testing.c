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
