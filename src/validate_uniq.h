#ifndef VALIDATE_UNIQ_H
#define VALIDATE_UNIQ_H

#include "sjp_testing.h"
#include "jdom.h"

#define MODULE_NAME VALIDATE_UNIQ

#define DEFAULT_UNIQ_BUCKETS 16
#define DEFAULT_UNIQ_LOAD   0.6f
#define UNIQ_BUFSIZE  4096
#define UNIQ_STACK    4096

// XXX - naming

enum unique_entry_type {
	UNIQ_TRUE = 0,
	UNIQ_FALSE,
	UNIQ_NULL,
	UNIQ_NUM,
	UNIQ_STR,
	UNIQ_OBJ,
	UNIQ_ARR,
};

enum jvst_vm_uniq_state {
  JVST_VM_UNIQ_BARE = 0,
  JVST_VM_UNIQ_ARRAY,
  JVST_VM_UNIQ_OBJKEY,
  JVST_VM_UNIQ_OBJVAL,
};

struct hmap;
struct jvst_vm;

struct jvst_vm_uniq_entry {
	enum SJP_EVENT type;
	union {
		struct {
			char *data;
			size_t len;
		} b;

		double d;
	} u;
};

struct jvst_vm_unique_stack {
	enum jvst_vm_uniq_state state;
	char buf0[UNIQ_BUFSIZE];
	struct {
		char *ptr;
		size_t len;
		size_t cap;
	} buf;

	struct {
		struct jvst_vm_uniq_entry *items;
		size_t len;
		size_t cap;
	} entries;
};

struct jvst_vm_unique
{
	struct hmap *entries;

	struct jvst_vm_unique_stack stack[UNIQ_STACK];
	size_t top;
	// need stack to store state of objects so we can sort them...
};

struct jvst_vm_unique *
jvst_vm_uniq_initialize(void);

void
jvst_vm_uniq_finalize(struct jvst_vm_unique *uniq);

int
jvst_vm_uniq_evaluate(struct jvst_vm_unique *uniq, enum SJP_RESULT pret, struct sjp_event *evt);

#undef MODULE_NAME

#endif /* VALIDATE_UNIQ_H */

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
