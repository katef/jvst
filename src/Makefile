.include "../share/mk/top.mk"

SRC += src/json.c
SRC += src/parser.c
SRC += src/main.c
SRC += src/kw.c

LEXER  += src/kw.lx
PARSER += src/parser.sid

LX_CFLAGS.src/kw.lx += -g agetc -e lxkw_ -t LXKW_
LX_CFLAGS.src/kw.lx += -x name -x example -x pos

# TODO: find LX_FIXED_SIZE from kw list?
.for src in ${SRC:Msrc/kw.c} ${SRC:Msrc/parser.c}
CFLAGS.${src} += -D LX_FIXED_SIZE=128
DFLAGS.${src} += -D LX_FIXED_SIZE=128
.endfor

.for src in ${SRC:Msrc/kw.c}
CFLAGS.${src} += -D LX_HEADER='"kw.h"'
DFLAGS.${src} += -D LX_HEADER='"kw.h"'
.endfor

.for src in ${SRC:Msrc/json.c} ${SRC:Msrc/main.c} ${SRC:Msrc/parser.c}
CFLAGS.${src} += -I share/git/pdjson # for json_private.h
DFLAGS.${src} += -I share/git/pdjson # for json_private.h
.endfor

.for src in ${SRC:Msrc/json.c} ${SRC:Msrc/main.c}
CFLAGS.${src} += -std=c99
DFLAGS.${src} += -std=c99
.endfor

PROG += jvst

.for src in ${SRC:Msrc/*.c}
${BUILD}/bin/jvst: ${BUILD}/${src:R}.o
.endfor

src/parser.c: src/kw.h

