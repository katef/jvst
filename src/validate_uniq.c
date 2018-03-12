#include "validate_uniq.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "xalloc.h"
#include "hmap.h"
#include "xxhash.h"

#define WHEREFMT "%s:%d (%s) "
#define WHEREARGS __FILE__, __LINE__, __func__

#define NOT_YET_IMPLEMENTED(what) do { \
	fprintf(stderr, WHEREFMT "%s is not yet implemented\n", \
		WHEREARGS, (what));				\
	abort(); } while(0)

#define SHOULD_NOT_REACH() do {				\
	fprintf(stderr, WHEREFMT "SHOULD NOT REACH\n",	\
		WHEREARGS);				\
	abort(); } while (0)

static uint64_t
hash_entry(void *hopaque, const void *key)
{
	const struct jvst_vm_uniq_entry *entry = key;

	(void)hopaque;

	switch (entry->type) {
	default:
	case SJP_NONE:
	case SJP_OBJECT_END:
	case SJP_ARRAY_END:
		SHOULD_NOT_REACH();

	case SJP_NULL:
	case SJP_TRUE:
	case SJP_FALSE:
	case SJP_NUMBER:
		return XXH64(entry, sizeof *entry, 0 /* XXX - SEED */);

	case SJP_STRING:
	case SJP_OBJECT_BEG:
	case SJP_ARRAY_BEG:
		// first byte of the data should indicate the type...
		return XXH64(entry->u.b.data, entry->u.b.len, 0 /* XXX - SEED */);
	}
}

static int
compare_entries(void *hopaque, const void *k1, const void *k2)
{
	const struct jvst_vm_uniq_entry *e1 = k1;
	const struct jvst_vm_uniq_entry *e2 = k2;

	(void)hopaque;

	if (e1->type != e2->type) {
		return 0;
	}

	switch (e1->type) {
	default:
	case SJP_NONE:
	case SJP_OBJECT_END:
	case SJP_ARRAY_END:
		SHOULD_NOT_REACH();

	case SJP_NULL:
	case SJP_TRUE:
	case SJP_FALSE:
		return 1;

	case SJP_NUMBER:
		return e1->u.d == e2->u.d;

	case SJP_STRING:
	case SJP_OBJECT_BEG:
	case SJP_ARRAY_BEG:
		if (e1->u.b.len != e2->u.b.len) {
			return 0;
		}

		return (memcmp(e1->u.b.data, e2->u.b.data, e1->u.b.len) == 0);
	}
}

static void
uniq_stack_init(struct jvst_vm_unique_stack *frame, enum jvst_vm_uniq_state state)
{
	frame->state = state;

	frame->buf.ptr = NULL;
	frame->buf.len = 0;
	frame->buf.cap = 0;

	frame->entries.items = NULL;
	frame->entries.len = 0;
	frame->entries.cap = 0;
}

static void
finalize_entry(struct jvst_vm_uniq_entry *entry);

static void
uniq_stack_final(struct jvst_vm_unique_stack *frame)
{
	size_t i,n;

	frame->state = JVST_VM_UNIQ_BARE;

	free(frame->buf.ptr);
	frame->buf.ptr = NULL;
	frame->buf.len = 0;
	frame->buf.cap = 0;

	n = frame->entries.len;
	for (i=0; i < n; i++) {
		finalize_entry(&frame->entries.items[i]);
	}

	free(frame->entries.items);
	frame->entries.items = NULL;
	frame->entries.len = 0;
	frame->entries.cap = 0;
}

struct jvst_vm_unique *
jvst_vm_uniq_initialize(void)
{
	struct jvst_vm_unique *uniq;
	uniq = malloc(sizeof *uniq);
	// hmap_create_string(DEFAULT_UNIQ_BUCKETS, DEFAULT_UNIQ_LOAD);
	uniq->entries = hmap_create(
		DEFAULT_UNIQ_BUCKETS,
		DEFAULT_UNIQ_LOAD,
		NULL, 
		hash_entry, 
		compare_entries);

	uniq->top = 0;
	uniq_stack_init(&uniq->stack[uniq->top], JVST_VM_UNIQ_BARE);

	return uniq;
}

void
jvst_vm_uniq_finalize(struct jvst_vm_unique *uniq)
{
	hmap_free(uniq->entries);
	free(uniq);
}

static struct jvst_vm_uniq_entry *
number_entry(struct jvst_vm_unique *uniq, double d)
{
	struct jvst_vm_uniq_entry *entry;
	(void)uniq;

	entry = malloc(sizeof *entry);  // XXX - replace with pool allocator?
	entry->type = SJP_NUMBER;
	entry->u.d = d;

	return entry;
}

static struct jvst_vm_uniq_entry *
string_entry(struct jvst_vm_unique *uniq, const char *buf, size_t n)
{
	struct jvst_vm_uniq_entry *entry;
	struct jvst_vm_unique_stack *stack;
	char *s, *sp;
	size_t len;

	stack = &uniq->stack[uniq->top];

	entry = malloc(sizeof *entry);  // XXX - replace with pool allocator?
	entry->type = SJP_STRING;

	len = 1 + stack->buf.len + n;
	s = xmalloc(len);

	sp = s;
	*sp++ = (char)SJP_STRING;
	if (stack->buf.len > 0) {
		memcpy(sp, stack->buf.ptr, stack->buf.len);
		sp += stack->buf.len;

		stack->buf.len = 0;
	}

	memcpy(sp, buf, n);

	entry->u.b.data = s;
	entry->u.b.len = len;

	return entry;
}

static struct jvst_vm_uniq_entry *
literal_entry(struct jvst_vm_unique *uniq, enum SJP_EVENT type)
{
	struct jvst_vm_uniq_entry *entry;

	(void)uniq;

	entry = malloc(sizeof *entry);  // XXX - replace with pool allocator?
	entry->type = type;
	entry->u.b.data = NULL;
	entry->u.b.len = 0;

	return entry;
}

static struct jvst_vm_uniq_entry *
composite_entry(struct jvst_vm_unique *uniq, enum SJP_EVENT composite_state)
{
	struct jvst_vm_uniq_entry *entry;
	struct jvst_vm_unique_stack *stack;
	char *buf, *p;
	size_t i,n, len;

	assert(uniq->top > 0);
	stack = &uniq->stack[uniq->top];

	len = 1;
	n = stack->entries.len;
	for (i=0; i < n; i++) {
		len += 1;
		switch (stack->entries.items[i].type) {
		case SJP_TRUE:
		case SJP_FALSE:
		case SJP_NULL:
			break;

		case SJP_NUMBER:
			len += sizeof stack->entries.items[i].u.d;
			break;

		case SJP_STRING:
		case SJP_ARRAY_BEG:
		case SJP_OBJECT_BEG:
			len += stack->entries.items[i].u.b.len;
			break;

		default:
		case SJP_ARRAY_END:
		case SJP_OBJECT_END:
			SHOULD_NOT_REACH();
		}
	}

	buf = xmalloc(len);
	p = buf;

	*p++ = SJP_ARRAY_BEG;
	for (i=0; i < n; i++) {
		assert(p < buf+len);
		*p++ = stack->entries.items[i].type;

		switch (stack->entries.items[i].type) {
		case SJP_TRUE:
		case SJP_FALSE:
		case SJP_NULL:
			break;

		case SJP_NUMBER:
			{
				size_t nb = sizeof stack->entries.items[i].u.d;
				memcpy(p, &stack->entries.items[i].u.d, nb);
				p += nb;
			}
			break;

		case SJP_STRING:
		case SJP_ARRAY_BEG:
		case SJP_OBJECT_BEG:
			{
				size_t nb = stack->entries.items[i].u.b.len;
				memcpy(p, stack->entries.items[i].u.b.data, nb);
				p += nb;
			}
			break;

		default:
		case SJP_ARRAY_END:
		case SJP_OBJECT_END:
			SHOULD_NOT_REACH();
		}
	}

	entry = malloc(sizeof *entry);  // XXX - replace with pool allocator?
	entry->type = composite_state;

	entry->u.b.data = buf;
	entry->u.b.len = len;

	return entry;
}

static struct jvst_vm_uniq_entry *
array_entry(struct jvst_vm_unique *uniq)
{
	assert(uniq->stack[uniq->top].state == JVST_VM_UNIQ_ARRAY);
	return composite_entry(uniq, SJP_ARRAY_BEG);
}

static int obj_pair_compare(const void *a, const void *b)
{
	const struct jvst_vm_uniq_entry *ea = a;
	const struct jvst_vm_uniq_entry *eb = b;

	assert(ea->type == SJP_STRING);
	assert(eb->type == SJP_STRING);

	size_t na = ea->u.b.len;
	size_t nb = eb->u.b.len;

	size_t nmin = na < nb ? na : nb;
	int cmp = memcmp(ea->u.b.data, eb->u.b.data, nmin);
	if (cmp != 0) {
		return cmp;
	}

	return (na > nb) - (na < nb);
}

static void
sort_pairs(struct jvst_vm_unique *uniq)
{
	struct jvst_vm_unique_stack *stack;

	stack = &uniq->stack[uniq->top];
	assert(stack->entries.len % 2 == 0); // even number

	if (stack->entries.len < 4) {
		return; // no need to sort...
	}

	qsort(&stack->entries.items[0],
		stack->entries.len/2,
		2 * sizeof stack->entries.items[0],
		obj_pair_compare);
}

static struct jvst_vm_uniq_entry *
object_entry(struct jvst_vm_unique *uniq)
{
	assert(uniq->stack[uniq->top].state == JVST_VM_UNIQ_OBJKEY);
	sort_pairs(uniq);
	return composite_entry(uniq, SJP_OBJECT_BEG);
}

static void
finalize_entry(struct jvst_vm_uniq_entry *entry)
{
	if (!entry) {
		return;
	}

	switch (entry->type) {
	default:
	case SJP_NONE:
	case SJP_OBJECT_END:
	case SJP_ARRAY_END:
		SHOULD_NOT_REACH();

	case SJP_NULL:
	case SJP_TRUE:
	case SJP_FALSE:
	case SJP_NUMBER:
		return;

	case SJP_STRING:
	case SJP_OBJECT_BEG:
	case SJP_ARRAY_BEG:
		free(entry->u.b.data);
		return;
	}
}

static void
free_entry(struct jvst_vm_uniq_entry *entry)
{
	if (!entry) {
		return;
	}

	finalize_entry(entry);
	free(entry);
}


static void uniq_add_entry(struct jvst_vm_unique *uniq, struct jvst_vm_uniq_entry *entry)
{
	struct jvst_vm_unique_stack *stack;

	stack = &uniq->stack[uniq->top];
	assert(stack->state == JVST_VM_UNIQ_ARRAY   ||
		stack->state == JVST_VM_UNIQ_OBJKEY ||
		stack->state == JVST_VM_UNIQ_OBJVAL);

	if (stack->entries.len >= stack->entries.cap) {
		stack->entries.items = xenlargevec(stack->entries.items, &stack->entries.cap, 1, sizeof stack->entries.items[0]);
	}

	assert(stack->entries.len < stack->entries.cap);

	stack->entries.items[stack->entries.len++] = *entry;
}

/* Unique evaluation machine (UEM)
 *
 * The UEM is a pushdown automaton.  There's a stack used for processing
 * nested structures.  Each level of the stack has an attached state,
 * and a pointer into a storage buffer.
 *
 * The stack state is:
 * 1) ARRAY                     array expecting item or ']'
 * 2) OBJECT_KEY                expecting property key or '}'
 * 3) OBJECT_VALUE              expecting property value 
 * 4) PARTIAL                   expecting more of a string token
 *
 * On receiving a token:
 *
 * 1) If a unique violation previously occurred, return ERR_NOT_UNIQUE
 *
 * 2) If the token is '[', push ARRAY and return OK.
 * 3) If the token is '{', push OBJECT_KEY and return OK.
 *
 * 4) If the token is ']', pop state, assert ARRAY, go to step ###
 *    (finish array)
 * 5) If the token is '}', pop state, assert OBJECT_KEY, go to step ###
 *    (finish object)
 * 6) If the token is STR and PARTIAL, copy state to a buffer,  if the
 *    top of the stack is not PARTIAL, push PARTIAL.
 *
 * 7) If the token is STR and not PARTIAL:
 *    if the top of the stack is PARTIAL, pop it.
 *    go to step ### (finish scalar)
 *
 * 8) If the token is NUM/BOOL/NULL, go to step ### (finish scalar)
 *
 * Finish scalar:
 * 9) If the stack is empty, 
 *
 *
 * Basic outer states are:
 *   1. no current item                 NO_CURRENT_ITEM
 *
 *   2. processing current item         CURRENT_ITEM
 *   3. invalid (items not unique)      UNIQ_INVALID
 *
 * transitions:
 * 
 * From                         TO                      EVENT
 * NO_CURRENT_ITEM              NO_CURRENT_ITEM         unique string/number/true/false/null
 * NO_CURRENT_ITEM              CURRENT_ITEM            '[' or '{' (ARRAY_BEG or OBJECT_BEG)
 *
 *
 * States while processing an item:
 *
 *
 */


enum jvst_result
jvst_vm_uniq_evaluate(struct jvst_vm_unique *uniq, enum SJP_RESULT pret, struct sjp_event *evt)
{
	struct jvst_vm_uniq_entry *entry;

	if (SJP_ERROR(pret)) {
		return JVST_INVALID;
	}

	if (pret == SJP_PARTIAL || pret == SJP_MORE) {
		// FIXME: need to handle partial!
		return JVST_MORE;
	}

	if (uniq->top == 0 && uniq->stack[uniq->top].state == JVST_VM_UNIQ_DONE) {
		return JVST_VALID;
	}

	assert(pret == SJP_OK);

	switch (evt->type) {
	case SJP_NULL:
	case SJP_TRUE:
	case SJP_FALSE:
		entry = literal_entry(uniq,evt->type);
		break;

	case SJP_STRING:
		entry = string_entry(uniq,evt->text, evt->n);
		break;

	case SJP_NUMBER:
		entry = number_entry(uniq,evt->extra.d);
		break;

	case SJP_ARRAY_BEG:
		uniq_stack_init(&uniq->stack[++uniq->top], JVST_VM_UNIQ_ARRAY);
		return JVST_NEXT;

	case SJP_ARRAY_END:
		if (uniq->top == 0) {
			uniq->stack[uniq->top].state = JVST_VM_UNIQ_DONE;
			return JVST_VALID;
		}

		assert(uniq->stack[uniq->top].state == JVST_VM_UNIQ_ARRAY);
		entry = array_entry(uniq);
		uniq_stack_final(&uniq->stack[uniq->top--]);
		break;

	case SJP_OBJECT_BEG:
		uniq_stack_init(&uniq->stack[++uniq->top], JVST_VM_UNIQ_OBJKEY);
		return JVST_NEXT;

	case SJP_OBJECT_END:
		assert(uniq->stack[uniq->top].state == JVST_VM_UNIQ_OBJKEY);
		entry = object_entry(uniq);
		uniq_stack_final(&uniq->stack[uniq->top--]);
		break;

	default:
	case SJP_NONE: SHOULD_NOT_REACH();
	}

	switch (uniq->stack[uniq->top].state) {
	case JVST_VM_UNIQ_BARE:
		if (hmap_get(uniq->entries, entry) != NULL) {
			free_entry(entry);
			// XXX - set state to
			// unique violation
			return JVST_INVALID;
		}

		hmap_setptr(uniq->entries, entry, NULL);
		return JVST_VALID;

	case JVST_VM_UNIQ_ARRAY:
		uniq_add_entry(uniq, entry);
		return JVST_NEXT;

	case JVST_VM_UNIQ_OBJKEY:
		uniq_add_entry(uniq, entry);
		uniq->stack[uniq->top].state = JVST_VM_UNIQ_OBJVAL;
		return JVST_NEXT;

	case JVST_VM_UNIQ_OBJVAL:
		uniq_add_entry(uniq, entry);
		uniq->stack[uniq->top].state = JVST_VM_UNIQ_OBJKEY;
		return JVST_NEXT;

	default:
		SHOULD_NOT_REACH();
	}

}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
