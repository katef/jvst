#ifndef IR_TESTING_H
#define IR_TESTING_H

#include "validate_testing.h"

enum ir_test_type {
	STOP = 0,
	TRANSLATE,
	LINEARIZE,
};

struct ir_test {
	enum ir_test_type type;
	struct jvst_cnode *ctree;
	struct jvst_ir_stmt *translated;
	struct jvst_ir_stmt *xformed;
};

#define UNIMPLEMENTED(testlist) do{ nskipped++; (void)testlist; }while(0)
#define RUNTESTS(testlist) run_ir_tests(__func__, (testlist))
int ir_trees_equal(const char *fname, struct jvst_ir_stmt *n1, struct jvst_ir_stmt *n2);
int run_ir_test(const char *fname, const struct ir_test *t);
void run_ir_tests(const char *testname, const struct ir_test tests[]);

#endif /* IR_TESTING_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
