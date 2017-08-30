.include "../../share/mk/top.mk"

TEST_PROG += test_validation
TEST_PROG += test_constraints
TEST_PROG += test_ir
TEST_PROG += test_op

# currently each test_*.c is a separate program
TEST_SRC += tests/unit/test_validation.c
TEST_SRC += tests/unit/test_constraints.c
TEST_SRC += tests/unit/test_ir.c
TEST_SRC += tests/unit/test_op.c

TEST_SRC += tests/unit/validate_testing.c
TEST_SRC += tests/unit/ir_testing.c

SRC += ${TEST_SRC}

.for src in ${TEST_SRC}
CFLAGS.${src} += -I share/git/sjp -I src
DFLAGS.${src} += -I share/git/sjp -I src

CFLAGS.${src} += -std=c99 -Wno-missing-field-initializers -Wno-unused
DFLAGS.${src} += -std=c99

CFLAGS.${src} += ${CFLAGS.libre} ${CFLAGS.libfsm}
DFLAGS.${src} += ${CFLAGS.libre} ${CFLAGS.libfsm}
.endfor

# All the .o files that the tests depend on
TEST_DEP_OBJS = 
.for src in ${SRC:Msrc/*.c:Nsrc/main.c:Nsrc/parser.c} ${TEST_SRC:Ntests/unit/test_*.c}
TEST_DEP_OBJS += ${BUILD}/${src:R}.o
.endfor

.for prog in ${TEST_PROG}
LFLAGS.${prog} += ${LIBS.libre} ${LIBS.libfsm}
LFLAGS.${prog} += -lm
.endfor

.for prog in ${TEST_PROG}

test::	${BUILD}/tests/unit/${prog}
CLEAN += ${BUILD}/tests/unit/${prog}

${BUILD}/tests/unit/${prog}: ${BUILD}/tests/unit/${prog:R}.o ${TEST_DEP_OBJS}
	${CC} -o $@ ${LFLAGS} ${.ALLSRC:M*.o} ${.ALLSRC:M*.a} ${LFLAGS.${prog}}

MODE.test/${prog} = 755

.endfor
