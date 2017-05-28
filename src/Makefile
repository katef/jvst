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
CFLAGS.${src} += -std=c99
DFLAGS.${src} += -std=c99
.endfor

PROG += jvst
PROG += test_validation

.for src in ${SRC:Msrc/*.c}
${BUILD}/bin/jvst: ${BUILD}/${src:R}.o
.endfor

VALID_SRC += src/validate.c
VALID_SRC += src/sjp_parser.c
VALID_SRC += src/sjp_testing.c

VALID_SRC += src/test_validation.c

.for src in ${VALID_SRC}
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

.for src in ${VALID_SRC:Msrc/*.c} ${SRC:Msrc/sjp_lexer.c}
${BUILD}/bin/test_validation: ${BUILD}/${src:R}.o
.endfor

SRC += ${VALID_SRC}

.for src in ${SRC:Msrc/*.c}
CFLAGS.${src} += ${CFLAGS.libre}
DFLAGS.${src} += ${CFLAGS.libre}
.endfor

