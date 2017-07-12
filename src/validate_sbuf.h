#ifndef VALIDATE_SBUF_H
#define VALIDATE_SBUF_H

#include <stdlib.h>

struct sbuf {
	char *buf;
	size_t cap;
	size_t len;
	size_t np;
};

int
sbuf_indent(struct sbuf *buf, int indent);

void
sbuf_snprintf(struct sbuf *b, const char *fmt, ...);

#endif /* VALIDATE_SBUF_H */

