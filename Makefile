.MAKEFLAGS: -r -m share/mk

# targets
all::  mkdir .WAIT dep .WAIT prog
dep::
gen::
test:: all
install:: all
clean::

# things to override
CC     ?= gcc
BUILD  ?= build
PREFIX ?= /usr/local

PKG += libre

# layout
SUBDIR += src

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

