/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#ifndef DEBUG_H
#define DEBUG_H

enum {
	DEBUG_SJP   = 1 << 0,
	DEBUG_LEX   = 1 << 1,
	DEBUG_ACT   = 1 << 2
};

extern unsigned debug;

#endif

