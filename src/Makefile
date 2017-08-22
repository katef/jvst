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

.for src in ${SRC:Msrc/*.c}
${BUILD}/bin/jvst: ${BUILD}/${src:R}.o
.endfor

VALID_SRC += src/validate_sbuf.c
VALID_SRC += src/validate.c
VALID_SRC += src/validate_constraints.c
# VALID_SRC += src/validate_testing.c
VALID_SRC += src/validate_ir.c
VALID_SRC += src/validate_op.c
VALID_SRC += src/validate_vm.c
VALID_SRC += src/sjp_parser.c
VALID_SRC += src/sjp_testing.c

.for src in ${VALID_SRC:Msrc/*.c}
CFLAGS.${src} += -std=c99 -fsanitize=address -Wno-missing-field-initializers -Wno-unused
DFLAGS.${src} += -std=c99

CFLAGS.${src} += -I share/git/sjp
DFLAGS.${src} += -I share/git/sjp
.endfor

SRC += ${VALID_SRC}

.for src in ${SRC:Msrc/*.c}
CFLAGS.${src} += ${CFLAGS.libre} ${CFLAGS.libfsm}
DFLAGS.${src} += ${CFLAGS.libre} ${CFLAGS.libfsm}
.endfor

.for prog in ${PROG}
LFLAGS.${prog} += ${LIBS.libre} ${LIBS.libfsm}
.endfor

