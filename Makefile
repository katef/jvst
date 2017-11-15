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

PKG += libre
PKG += libfsm

# layout
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

