.include "../share/mk/top.mk"

SRC += src/ast.c
SRC += src/jdom.c
SRC += src/kw.c
SRC += src/main.c
SRC += src/parser.c
SRC += src/xalloc.c

SRC += src/sjp_lexer.c

PARSER += src/parser.sid

.for src in ${SRC:Msrc/ast.c} ${SRC:Msrc/sjp_lexer.c} ${SRC:Msrc/parser.c} ${SRC:Msrc/main.c}
CFLAGS.${src} += -I share/git/sjp
DFLAGS.${src} += -I share/git/sjp
.endfor

.for src in ${SRC:Msrc/ast.c} ${SRC:Msrc/sjp_lexer.c} ${SRC:Msrc/parser.c} ${SRC:Msrc/main.c}
CFLAGS.${src} += -std=c99 -Wno-missing-field-initializers
DFLAGS.${src} += -std=c99
.endfor

PROG += jvst
PROG += test_validation
PROG += test_constraints
PROG += test_ir

.for src in ${SRC:Msrc/*.c}
${BUILD}/bin/jvst: ${BUILD}/${src:R}.o
.endfor

VALID_SRC += src/validate_sbuf.c
VALID_SRC += src/validate.c
VALID_SRC += src/validate_constraints.c
VALID_SRC += src/validate_testing.c
VALID_SRC += src/validate_ir.c
VALID_SRC += src/sjp_parser.c
VALID_SRC += src/sjp_testing.c

# currently each test_*.c is a separate program
VALID_TESTS_SRC += src/test_validation.c
VALID_TESTS_SRC += src/test_constraints.c
VALID_TESTS_SRC += src/test_ir.c

.for src in ${VALID_SRC} ${VALID_TESTS_SRC}
CFLAGS.${src} += -std=c99 -fsanitize=address -Wno-missing-field-initializers -Wno-unused
DFLAGS.${src} += -std=c99
.endfor

.for src in ${VALID_SRC:Msrc/*.c} ${VALID_SRC:Msrc/test_validation.c}
CFLAGS.${src} += -I share/git/sjp
DFLAGS.${src} += -I share/git/sjp
.endfor

.for prog in ${PROG:Mtest_*}
LFLAGS.${prog} += -fsanitize=address
.endfor

.for test in ${VALID_TESTS_SRC:Msrc/*.c}
_p = ${BUILD}/bin/${test:T:R}
${_p}: ${BUILD}/${test:R}.o

.for src in ${VALID_SRC:Msrc/*.c} ${SRC:Msrc/*.c:Nsrc/main.c:Nsrc/parser.c}
${_p}: ${BUILD}/${src:R}.o
.endfor

# THE_TESTS += ${BUILD}/bin/${t0:R}
.endfor

SRC += ${VALID_SRC} ${VALID_TESTS_SRC}

.for src in ${SRC:Msrc/*.c}
CFLAGS.${src} += ${CFLAGS.libre} ${CFLAGS.libfsm}
DFLAGS.${src} += ${CFLAGS.libre} ${CFLAGS.libfsm}
.endfor

.for prog in ${PROG}
LFLAGS.${prog} += ${LIBS.libre} ${LIBS.libfsm}
.endfor

