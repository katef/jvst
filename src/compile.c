#include "validate.h"
#include "validate_constraints.h"
#include "validate_ir.h"
#include "validate_op.h"
#include "validate_vm.h"

struct jvst_vm_program *
jvst_compile_schema(const struct ast_schema *schema)
{
	struct jvst_cnode *cnodes;
	struct jvst_ir_stmt *ir;
	struct jvst_op_program *opasm;
	struct jvst_vm_program *prog;

	cnodes = jvst_cnode_from_ast(schema);
	ir = jvst_ir_from_cnode(cnodes);
	opasm = jvst_op_assemble(ir);
	prog = jvst_op_encode(opasm);

	return prog;
}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
