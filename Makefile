.MAKEFLAGS: -r -m share/mk

# targets
all::  mkdir .WAIT dep .WAIT prog
dep::
gen::
test:: all
install:: all
uninstall::
clean::

# things to override
CC     ?= gcc
BUILD  ?= build
PREFIX ?= /usr/local

# ${unix} is an arbitrary variable set by sys.mk
.if defined(unix)
.BEGIN::
	@echo "We don't use sys.mk; run ${MAKE} with -r" >&2
	@false
.endif

PKG += libre
PKG += libfsm

# layout
SUBDIR += src/uriparser
SUBDIR += src
SUBDIR += tests/unit
SUBDIR += tests/jvst
SUBDIR += tests

.include <subdir.mk>
.include <sid.mk>
.include <pkgconf.mk>
.include <obj.mk>
.include <dep.mk>
.include <part.mk>
.include <prog.mk>
.include <mkdir.mk>
.include <install.mk>
.include <clean.mk>

