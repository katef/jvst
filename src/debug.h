/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#ifndef DEBUG_H
#define DEBUG_H

enum {
	DEBUG_SJP              = 1 <<  0,
	DEBUG_LEX              = 1 <<  1,
	DEBUG_ACT              = 1 <<  2,
	DEBUG_PARSED_SCHEMA    = 1 <<  3,
	DEBUG_INITIAL_CNODE    = 1 <<  4,
	DEBUG_SIMPLIFIED_CNODE = 1 <<  5,
	DEBUG_CANONIFIED_CNODE = 1 <<  6,
	DEBUG_IR               = 1 <<  7,
	DEBUG_LINEAR_IR        = 1 <<  8,
	DEBUG_FLATTENED_IR     = 1 <<  9,
	DEBUG_OPCODES          = 1 << 10,
	DEBUG_VMPROG           = 1 << 11,
        DEBUG_VMOP             = 1 << 12,
        DEBUG_VMTOK            = 1 << 13,
};

extern unsigned debug;

#endif

