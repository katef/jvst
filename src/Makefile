.include "../share/mk/top.mk"

SRC += src/json.c
SRC += src/parser.c
SRC += src/main.c

PARSER += src/parser.sid

.for src in ${SRC:Msrc/json.c} ${SRC:Msrc/main.c} ${SRC:Msrc/parser.c}
CFLAGS.${src} += -I share/git/pdjson # for json_private.h
DFLAGS.${src} += -I share/git/pdjson # for json_private.h
.endfor

.for src in ${SRC:Msrc/json.c} ${SRC:Msrc/main.c}
CFLAGS.${src} += -std=c99
DFLAGS.${src} += -std=c99
.endfor

PROG += jsvt

.for src in ${SRC:Msrc/*.c}
${BUILD}/bin/jsvt: ${BUILD}/${src:R}.o
.endfor

