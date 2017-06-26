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

.for src in ${SRC:Msrc/*.c}
${BUILD}/bin/jvst: ${BUILD}/${src:R}.o
.endfor

.for src in ${SRC:Msrc/*.c}
CFLAGS.${src} += ${CFLAGS.libre}
DFLAGS.${src} += ${CFLAGS.libre}
.endfor
