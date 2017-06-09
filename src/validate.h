#ifndef JVST_VALIDATE_H
#define JVST_VALIDATE_H

#include "sjp_parser.h"

enum JVST_RESULT {
  JVST_INVALID = -1,
  JVST_VALID = 0,
  JVST_MORE = 1,
};

#define JVST_IS_INVALID(x) ((x) < 0)

struct ast_schema;

enum {
  JVST_DEFAULT_STACK_SIZE = 1024,
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
};

void jvst_validate_init_defaults(struct jvst_validator *v, const struct ast_schema *schema);
enum JVST_RESULT jvst_validate_more(struct jvst_validator *v, char *data, size_t n);
enum JVST_RESULT jvst_validate_close(struct jvst_validator *v);

#endif /* JVST_VALIDATE_H */

