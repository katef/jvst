#include "idtbl.h"

#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#include "jvst_macros.h"
#include "hmap.h"
#include "xxhash.h"

/*** cnode ID table */

/* have to do this a few times, so might as well do some macro
 * templating */
#define IDTBL_NAME jvst_cnode_id_table
#define IDTBL_VTYPE struct jvst_cnode
// cnodes freed through the cnode garbage collection machinery
#define IDTBL_VFREE(x) 
#include "idtbl_generic.c.in"
#undef IDTBL_NAME
#undef IDTBL_VTYPE
#undef IDTBL_VFREE

#define IDTBL_NO_SUPPORTING /* only define supporting things once */

/* cnode ID table extras */
void
jvst_cnode_debug(struct jvst_cnode *node);

void
jvst_cnode_id_table_dump_ids(struct jvst_cnode_id_table *tbl)
{
	void *k;
	struct hmap_iter it;

	// iterate over keys, freeing keys.  the ID table makes a
	// duplicate copy of each key.
	for (k = hmap_iter_first(tbl->map, &it); k != NULL; k = hmap_iter_next(&it)) {
		struct json_string *str = k;
		struct jvst_cnode *ctree = it.v.p;
		fprintf(stderr, "ID: %.*s\n", (int)str->len, str->s);
		jvst_cnode_debug(ctree);
	}
}


/*** IR ID table */

#define IDTBL_NAME jvst_ir_id_table
#define IDTBL_VTYPE struct jvst_ir_stmt
// IR nodes freed through the cnode garbage collection machinery
#define IDTBL_VFREE(x) 
#include "idtbl_generic.c.in"
#undef IDTBL_NAME
#undef IDTBL_VTYPE
#undef IDTBL_VFREE

#undef IDTBL_NO_SUPPORTING

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
