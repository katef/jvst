#ifndef JVST_VALIDATE_H
#define JVST_VALIDATE_H

#include "sjp_parser.h"

enum jvst_result {
	JVST_INVALID = -1,
	JVST_VALID   = 0,
	JVST_MORE    = 1,

	// Internal states... should never be returned by
	// the public API...
	JVST_NEXT = 2,
};

// For use internally.  This indicates that a variable of enum
// jvst_result has not yet been set to a valid state.
//
// FIXME: This isn't ideal, but internally we need some way to indicate
// that we don't yet have a result, ideally without an additional
// boolean variable.
#define JVST_INDETERMINATE SCHAR_MIN

#define JVST_IS_INVALID(x) ((x) < 0)

struct ast_schema;

enum { JVST_DEFAULT_STACK_SIZE = 1024,
};

struct jvst_state;

/* validation state */
struct jvst_validator {
	const struct ast_schema *schema;

	struct jvst_state *sstack;
	size_t stop;
	size_t smax;

	struct sjp_parser p;
	char pstack[4096];
	char pbuf[4096];

	char kbuf[128]; // object key buffer

	// XXX - revisit this
	struct {
		char msg[64];
		const char *file;
		int line;
	} errstack[16];
	int etop;
};

void
jvst_validate_init_defaults(struct jvst_validator *v, const struct ast_schema *schema);

enum jvst_result
jvst_validate_more(struct jvst_validator *v, char *data, size_t n);

enum jvst_result
jvst_validate_close(struct jvst_validator *v);

struct jvst_vm_program;

struct jvst_vm_program *
jvst_compile_schema(const struct ast_schema *schema);

#endif /* JVST_VALIDATE_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
