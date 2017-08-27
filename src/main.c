/*
 * Copyright 2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#define _POSIX_C_SOURCE 2

#include <unistd.h>

#include <assert.h>
#include <errno.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "sjp_lexer.h"
#include "sjp_testing.h"

#include "debug.h"
#include "parser.h"
#include "jdom.h"
#include "ast.h"
#include "xalloc.h"
#include "validate.h"
#include "validate_constraints.h"
#include "validate_ir.h"
#include "validate_op.h"
#include "validate_vm.h"

enum {
	PRINT_SCHEMA           = 1 << 0,
	PRINT_INITIAL_CNODE    = 1 << 1,
	PRINT_SIMPLIFIED_CNODE = 1 << 2,
	PRINT_CANONIFIED_CNODE = 1 << 3,
	PRINT_IR               = 1 << 4,
	PRINT_LINEAR_IR        = 1 << 5,
	PRINT_FLATTENED_IR     = 1 << 6,
	PRINT_OPCODES          = 1 << 7,
	PRINT_VMPROG           = 1 << 8
};

unsigned debug;
unsigned print;

static char *
readfile(FILE *f, size_t *np)
{
	size_t sz, n;
	char *p;

	assert(f != NULL);

	p  = NULL;
	sz = 0;
	n  = 0;

	for (;;) {
		size_t r;

		assert(n <= sz);
		if (n + BUFSIZ >= sz) {
			sz += BUFSIZ;
			p = xrealloc(p, sz);
		}

		r = fread(p + n, 1, sz - n, f);
		if (r == 0) {
			break;
		}

		n += r;
	}

	if (ferror(f)) {
		free(p);
		return NULL;
	}

	assert(n < sz);
	p[n] = '\0';

	if (np != NULL) {
		*np = n;
	}

	return p;
}

static int
debug_flags(const char *s)
{
	int v;

	assert(s != NULL);

	v = 1;

	for ( ; *s != '\0'; s++) {
		int e;

		switch (*s) {
		case '+': v = 1; continue;
		case '-': v = 0; continue;

		case 'a': e = ~0U;         break;
		case 's': e = DEBUG_SJP;   break;
		case 'l': e = DEBUG_LEX;   break;
		case 'c': e = DEBUG_ACT;   break;

		default:
			fprintf(stderr, "-d: unrecognised flag '%c'\n", *s);
			return -1;
		}

		if (v) {
			debug |=  e;
		} else {
			debug &= ~e;
		}
	}

	return 0;
}

static int
print_flags(const char *s)
{
	int v;

	assert(s != NULL);

	v = 1;

	for ( ; *s != '\0'; s++) {
		int e;

		switch (*s) {
		case '+': v = 1; continue;
		case '-': v = 0; continue;

		case 'a': e = ~0U;                    break;
		case 's': e = PRINT_SCHEMA;           break;
		case 'c': e = PRINT_INITIAL_CNODE;    break;
		case 'S': e = PRINT_SIMPLIFIED_CNODE; break;
		case 'n': e = PRINT_CANONIFIED_CNODE; break;
		case 'i': e = PRINT_IR;               break;
		case 'l': e = PRINT_LINEAR_IR;        break;
		case 'F': e = PRINT_FLATTENED_IR;     break;
		case 'o': e = PRINT_OPCODES;          break;
		case 'p': e = PRINT_VMPROG;           break;

		case ',': continue;

		default:
			fprintf(stderr, "-p: unrecognised flag '%c'\n", *s);
			return -1;
		}

		if (v) {
			print |=  e;
		} else {
			print &= ~e;
		}
	}

	return 0;
}


int
main(int argc, char *argv[])
{
	static const struct ast_schema ast_default;
	int r;
	int compile=0, runvm=0, genc=0;
	struct jvst_vm_program *prog = NULL;
	struct jvst_ir_stmt *ir;

	{
		int c;

		while (c = getopt(argc, argv, "p:rcCd:"), c != -1) {
			switch (c) {
			case 'c':
				compile = 1;
				break;

			case 'C':
				genc = 1;
				// fprintf(stderr, "generating C is not yet supported\n");
				// exit(EXIT_FAILURE);
				break;

			case 'd':
				if (-1 == debug_flags(optarg)) {
					goto usage;
				}
				break;

			case 'p':
				if (-1 == print_flags(optarg)) {
					goto usage;
				}
				break;

			case 'r':
				runvm = 1;
				break;

			default:
				goto usage;
			}
		}

		argc -= optind;
		argv += optind;
	}

	if (compile || genc) {
		FILE *f_schema;
		char *p;
		size_t n;

		if (argc < 1) {
			// TODO: genc does not... when we add that,
			// allow jvst to be used as a filter
			fprintf(stderr, "compiling requires a schema file\n");
			goto usage;
		}

		f_schema = fopen(argv[0], "r");
		if (f_schema == NULL) {
			fprintf(stderr, "error opening schema '%s': %s\n",
					argv[0], strerror(errno));
			exit(EXIT_FAILURE);
		}
		argc--;
		argv++;

		struct sjp_lexer l;
		struct ast_schema ast = ast_default;
		struct jvst_cnode *ctree, *simplified, *canonified;

		sjp_lexer_init(&l);

		/* TODO: until sjp gets various streamed IO interfaces */
		p = readfile(f_schema, &n);
		if (f_schema != stdin) {
			fclose(f_schema);
		}
		if (p == NULL) {
			perror("readfile");
			exit(EXIT_FAILURE);
		}

		sjp_lexer_more(&l, p, n);

		parse(&l, &ast);

		if (print & PRINT_SCHEMA) {
			ast_dump(stdout, &ast);
		}

		r = sjp_lexer_close(&l);
		if (SJP_ERROR(r)) {
			/* TODO: make this better */
			fprintf(stderr, "sjp error B (%d): encountered %s\n", r, ret2name(r));
			exit(EXIT_FAILURE);
		}

		free(p);
		n = 0;

		ctree = jvst_cnode_translate_ast(&ast);
		if (print & PRINT_INITIAL_CNODE) {
			printf("Initial cnode tree\n");
			jvst_cnode_print(stdout, ctree);
			printf("\n");
		}

		simplified = jvst_cnode_simplify(ctree);
		if (print & PRINT_SIMPLIFIED_CNODE) {
			printf("Simplified cnode tree\n");
			jvst_cnode_print(stdout, simplified);
			printf("\n");
		}

		canonified = jvst_cnode_canonify(simplified);
		if (print & PRINT_CANONIFIED_CNODE) {
			printf("Canonified cnode tree\n");
			jvst_cnode_print(stdout, canonified);
			printf("\n");
		}

		ir = jvst_ir_translate(canonified);
		if (print & PRINT_IR) {
			printf("Initial IR\n");
			jvst_ir_print(stdout, ir);
			printf("\n");
		}
	}

	if (compile) {
		struct jvst_ir_stmt *linearized, *flattened;
		struct jvst_op_program *op_prog;

		linearized = jvst_ir_linearize(ir);
		if (print & PRINT_LINEAR_IR) {
			printf("Linearized IR\n");
			jvst_ir_print(stdout, linearized);
			printf("\n");
		}

		flattened = jvst_ir_flatten(linearized);
		if (print & PRINT_FLATTENED_IR) {
			printf("Flattened IR\n");
			jvst_ir_print(stdout, flattened);
			printf("\n");
		}

		op_prog = jvst_op_assemble(flattened);
		if (print & PRINT_OPCODES) {
			printf("Assembled OP codes\n");
			jvst_op_print(stdout, op_prog);
			printf("\n");
		}

		prog = jvst_op_encode(op_prog);
		if (print & PRINT_VMPROG) {
			printf("Final VM program:\n");
			jvst_vm_program_print(stdout, prog);
			printf("\n");
		}

		// TODO: add bit where the vm program is saved, possibly
		// if runvm is false
	}

	if (runvm) {
		char *p;
		size_t n;
		FILE *f_data;
		struct jvst_vm vm = { 0 };
		enum jvst_result ret;

		jvst_vm_init_defaults(&vm, prog);

		if (prog == NULL) {
			// TODO: add bit where we load the vm program
			fprintf(stderr, "runvm currently requires compiling\n");
			exit(EXIT_FAILURE);
		}

		if (argc < 1) {
			f_data = stdin;
		} else {
			f_data = fopen(argv[0], "r");
			if (f_data == NULL) {
				fprintf(stderr, "error opening json '%s': %s\n",
					argv[0], strerror(errno));
				exit(EXIT_FAILURE);
			}
		}

		// FIXME: should stream this!
		p = readfile(f_data, &n);
		if (f_data != stdin) {
			fclose(f_data);
		}
		if (p == NULL) {
			perror("readfile");
			exit(EXIT_FAILURE);
		}

		// XXX - can't do this if we're streaming
		(void) jvst_vm_more(&vm, p, n);
		ret = jvst_vm_close(&vm);

		// TODO - better diagnostics!
		if (ret == JVST_INVALID) {
			exit(EXIT_FAILURE);
		} else {
			return 0;
		}
	}

	return 0;

usage:

	fprintf(stderr, "usage: jvst [-d +-aslc] -c <schema> [<compiled>]\n"
			"       jvst [-d +-aslc] -c -r <schema> [<json>]\n"
			// "       jvst [-d +-aslc] -r <compiled> [<json>]\n"
			"\n"
			"  -c       compile schema to jvst VM code\n"
			"\n"
			"  -r       run jvst VM code on json\n"
			"\n"
			"  -d       debug flags\n"
			"       +/- enables/disables\n"
			"           a   all\n"
			"           s   sjp parser\n"
			"           l   schema lexer\n"
			"           c   schema actions\n"
			"\n"
			"  -p       print intermediates\n"
			"       +/- enables/disables\n"
			"           a   all\n"
			"           s   schema\n"
			"           c   initial cnode tree\n"
			"           S   simplified cnode tree\n"
			"           n   canonical cnode tree\n"
			"           i   IR tree\n"
			"           l   linearized IR tree\n"
			"           F   flattened IR tree\n"
			"           o   assembled opcodes\n"
			"           p   final VM program\n");

	return 1;
}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */
