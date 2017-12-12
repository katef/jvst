.include "../../share/mk/top.mk"

SRC += src/uriparser/UriCommon.c
SRC += src/uriparser/UriCompare.c
SRC += src/uriparser/UriEscape.c
SRC += src/uriparser/UriFile.c
SRC += src/uriparser/UriIp4.c
SRC += src/uriparser/UriIp4Base.c
SRC += src/uriparser/UriNormalize.c
SRC += src/uriparser/UriNormalizeBase.c
SRC += src/uriparser/UriParse.c
SRC += src/uriparser/UriParseBase.c
SRC += src/uriparser/UriQuery.c
SRC += src/uriparser/UriRecompose.c
SRC += src/uriparser/UriResolve.c
SRC += src/uriparser/UriShorten.c

.for src in ${SRC:Msrc/uriparser/*.c}
CFLAGS.${src} += -I include
DFLAGS.${src} += -I include
.endfor

