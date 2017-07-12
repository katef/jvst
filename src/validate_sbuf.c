#include "validate_sbuf.h"

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>

int
sbuf_indent(struct sbuf *buf, int indent)
{
	int i;

	for (i = 0; i < indent; i++) {
		if (buf->len >= buf->cap) {
			break;
		}
		buf->buf[buf->len++] = ' ';
	}

	buf->np += indent;

	return indent;
}

void
sbuf_snprintf(struct sbuf *b, const char *fmt, ...)
{
	int ret;
	va_list args;
	char *p;
	size_t nb;

	assert(b->len <= b->cap);

	p  = b->buf + b->len;
	nb = b->cap - b->len;

	va_start(args, fmt);
	ret = vsnprintf(p, nb, fmt, args);
	va_end(args);
	if (ret < 0) {
		// FIXME: handle this more gracefully!
		perror("ERROR dumping cnode to a buffer");
		abort();
	}

	if ((size_t)ret <= nb) {
		b->len += ret;
	} else {
		b->len = b->cap;
	}

	b->np += ret;
}

