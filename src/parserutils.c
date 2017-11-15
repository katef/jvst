#include "parserutils.h"

#include <assert.h>
#include <limits.h>

#include "xalloc.h"


static void print_uri_error(int err);

struct path_element *
push_element(struct path *p)
{
	static const struct path_element zero;
	struct path_element *elt;

	if (p->len >= p->cap) {
		size_t newcap;
		newcap = p->cap;
		if (newcap < 8) {
			newcap = 8;
		}
		newcap *= 2;

		p->items = xrealloc(p->items, newcap * sizeof p->items[0]);
		p->cap = newcap;
	}

	assert(p->len < p->cap);
	elt = &p->items[p->len++];
	*elt = zero;
	return elt;
}

struct path_element *
peek_element(struct path *p)
{
	if (p->len == 0) {
		return NULL;
	}

	assert(p->len <= p->cap);
	return &p->items[p->len-1];
}


void
path_push_empty(struct path *p)
{
	static const struct json_string zero;
	struct path_element *elt;
	elt = push_element(p);

	elt->isnum = 0;
	elt->u.str = zero;
}

static struct json_string
escape_json_pointer(struct json_string s)
{
	struct json_string ret;
	char *b, *p;
	size_t i,n;

	n=0;
	for (i=0; i < s.len; i++) {
		n++;
		if (s.s[i] == '/' || s.s[i] == '~') {
			n++;
		}
	}

	if (n == s.len) {
		return json_strdup(s);
	}

	b = xmalloc(n);
	p = b;
	for (i=0; i < s.len; i++) {
		switch (s.s[i]) {
		case '/':
			*p++ = '~';
			*p++ = '1';
			break;

		case '~':
			*p++ = '~';
			*p++ = '0';
			break;

		default:
			*p++ = s.s[i];
		}
	}

	ret.s = b;
	ret.len = n;

	return ret;
}

void
path_push_str(struct path *p, struct json_string s)
{
	struct path_element *elt;
	elt = push_element(p);

	elt->isnum = 0;
	elt->u.str = escape_json_pointer(s);
}

void
path_push_num_zero(struct path *p)
{
	struct path_element *elt;
	elt = push_element(p);

	elt->isnum = 1;
	elt->u.num = 0;
}

void
path_push_num_next(struct path *p)
{
	struct path_element *elt;
	elt = peek_element(p);

	assert(elt != NULL);
	assert(elt->isnum != 0);

	elt->u.num++;
}

void
path_pop(struct path *p)
{
	assert(p->len > 0);
	p->len--;
}

char *
build_fragment(size_t *lenp, struct path_element *pbeg, struct path_element *pend)
{
	struct path_element *p;
	size_t plen, plen0;
	char *frag, *frag_end;

	char *escbuf;
	size_t eblen;

	// build out path
	plen0 = 0;
	frag = frag_end = NULL;

	if (!pbeg->isnum && pbeg->u.str.len == 0) {
		pbeg++;
	}

	escbuf = NULL;
	eblen = 0;

build_path:
	if (frag != NULL) {
		*frag = '#';
	}
	plen = 1;

	for (p = pbeg; p != pend; p++) {
		size_t l;
		char *s;

		s = (frag != NULL) ? frag + plen : NULL;
		l = (frag != NULL) ? frag_end - s : 0;

		if (p->isnum) {
			plen += snprintf(s, l, "/%zu", p->u.num);
		} else {
			const char *str;
			size_t len, esclen;

			/* XXX - escape JSON pointer things! */
			len = p->u.str.len;
			str = p->u.str.s;

			if (eblen < 6*(len+1)) {
				eblen = 6*(len+1);
				escbuf = xrealloc(escbuf, eblen);
			}

			uriEscapeExA(str, str+len, escbuf, URI_TRUE, URI_TRUE);
			esclen = strlen(escbuf);

			if (esclen > INT_MAX) {
				// XXX - handle error more gracefully?
				fprintf(stderr, "escaped path element is too long:");
				fwrite(escbuf, 1, esclen, stderr);
				fprintf(stderr, "\n");
				abort();
			}

			plen += snprintf(s, l, "/%.*s", (int)esclen, escbuf);
		}

		assert(frag == NULL || frag + plen < frag_end);
	}

	if (frag != NULL) {
		assert(plen0 == plen);

		free(escbuf);

		*lenp = plen;
		return frag;
	}

	// assemble fragment path
	frag = xmalloc(plen + 1);
	frag_end = frag + plen + 1;
	plen0 = plen;
	goto build_path;
}

static struct json_string
uri_as_json_string(const UriUriA *uri);

static struct ast_string_set **
add_id_from_uri(struct ast_string_set **idpp, const UriUriA *uri);

static struct ast_string_set **
add_id_from_uri_with_fragment(
	struct ast_string_set **idpp, const UriUriA *uri, const char *frag, size_t len);

static UriUriA *find_base_uri(struct path_element *pbeg, struct path_element *pend)
{
	UriUriA *base_uri;
	size_t i,n;

	assert(pend-pbeg >= 0);

	base_uri = NULL;
	n = pend-pbeg + 1;
	for (i=n; i > 0; i--) {
		base_uri = pbeg[i-1].base_id;
		if (base_uri != NULL) {
			break;
		}
	}

	return base_uri;
}

struct json_string path_ref(struct path *path, struct json_string rel_ref)
{
	struct json_string abs_ref;
	UriUriA *base_uri, frag_uri, ref_uri;
	UriParserStateA state;
	const char *beg, *end;
	char *buf;
	int ret, uri_len;

	beg = rel_ref.s;
	end = beg + rel_ref.len;

	assert(path->len > 0);
	base_uri = find_base_uri(&path->items[0], &path->items[path->len-1]);

	state.uri = &frag_uri;
	if (ret = uriParseUriExA(&state, beg,end), ret != URI_SUCCESS) {
		print_uri_error(ret);
	}

	if (ret = uriAddBaseUriA(&ref_uri, &frag_uri, base_uri), ret != URI_SUCCESS) {
		print_uri_error(ret);
	}

	uriFreeUriMembersA(&frag_uri);

	uri_len = -1;
	if (uriToStringCharsRequiredA(&ref_uri, &uri_len) != URI_SUCCESS) {
		print_uri_error(ret);
	}
	uri_len++; /* NUL character */

	buf = xmalloc(uri_len);
        if (uriToStringA(buf, &ref_uri, uri_len, NULL) != URI_SUCCESS) {
		print_uri_error(ret);
        }
	uriFreeUriMembersA(&ref_uri);

	abs_ref.s = buf;
	abs_ref.len = strlen(buf);

	return abs_ref;
}

void path_set_baseid(struct path_element *ptop, struct path_element *pnode, struct json_string baseid)
{
	UriUriA *base_uri, *prev_uri;
	UriParserStateA state;
	const char *beg,*end;
	int ret;

	if (baseid.len == 0) {
		return;
	}

	beg = baseid.s;
	end = beg + baseid.len;

	prev_uri = find_base_uri(ptop, pnode);
	base_uri = xmalloc(sizeof *base_uri);
	state.uri = base_uri;

	if (ret = uriParseUriExA(&state, beg,end), ret != URI_SUCCESS) {
		print_uri_error(ret);
	}

	if (prev_uri != NULL) {
		UriUriA *rel_uri;

		rel_uri = base_uri;
		base_uri = xmalloc(sizeof *base_uri);
		if (ret = uriAddBaseUriA(base_uri, rel_uri, prev_uri), ret != URI_SUCCESS) {
			print_uri_error(ret);
		}

		uriFreeUriMembersA(rel_uri);
	}

	if (ret = uriNormalizeSyntaxA(base_uri), ret != URI_SUCCESS) {
		print_uri_error(ret);
	}

	pnode->base_id = base_uri;
}

void
path_add_all_ids(struct path *path, struct ast_schema *ast)
{
	struct ast_string_set **idspp;
	struct path_element *ptop;
	size_t i;

	assert(ast != NULL);
	assert(path != NULL);

	/* when this function is called, the path should *never* be empty */
	assert(path->len > 0);

	/* Adds all possible id to the ast's ids list.  The path
	 * stack represents the path from the current AST node back
	 * to the root.  Each item in the stack has a fragment name
	 * and an optional base id.  This function expects the base
	 * id to be a correct URI base.
	 *
	 * To assemble all possible ids, start at the top of the stack
	 * and walk down.  Keep track of the current fragment length 
	 * curing the walk to make building ids easier.
	 *
	 * When a path element with a base_id or the bottom of the stack
	 * is encountered:
	 *      0) if this is the bottom of the stack and it has no base_id,
	 *         assume the base_id is the empty string
	 *
	 *         XXX - is the correct or should we assume some default base URI?
	 *
	 *      1) if this is the top node, add:
	 *              - base_id                         if it's not the empty string
	 *              - base_id + '#' (empty fragment)  even if it is the empty string
	 *
	 *      2) if this isn't the top node, add:
	 *              - base_id + current fragment
	 *
	 * Once the IDs have been added, proceed down the stack until the bottom is
	 * encountered.
	 */

	assert(ast->all_ids == NULL && "add_all_ids called on AST node that has non-NULL ids");

	ast->all_ids = NULL;
	idspp = &ast->all_ids;

	// keep track of the top of th stack, it's used a lot below */
	ptop = &path->items[path->len];

	for (i=path->len; i > 0; i--) {
		struct path_element *elt;
		UriUriA *base_id;

		elt = &path->items[i-1];
		base_id = elt->base_id;

		if (i > 1 && base_id == NULL) {
			/* only add ids when we encounter an explicit ID
			   or reach the root of the schema */
			continue;
		}

		/* add IDs */
		if (i == path->len) {
			/* path element is the top element */
			if (base_id != NULL) {
				idspp = add_id_from_uri(idspp, base_id);
			}

			idspp = add_id_from_uri_with_fragment(idspp, base_id, "#", 1);
		} else {
			/* path element is not the top */

			char *frag;
			size_t fraglen;

			/* assemble fragment */
			frag = NULL;
			fraglen = 0;

			/* XXX - should probably keep track of fragment length as we go to
			   avoid recalculating it.  Not sure that this is worthwhile, though. */
			frag = build_fragment(&fraglen, elt+1, ptop);

			/* build the URI from base_id and the fragment */
			idspp = add_id_from_uri_with_fragment(idspp, base_id, frag, fraglen);

			free(frag);
		}
	}

	// should have at least one ID to add
	assert(ast->all_ids != NULL);
}

static struct json_string
uri_as_json_string(const UriUriA *uri)
{
	static const struct json_string zero;
	struct json_string s;
	char *data;
	int len,err, written;

	assert(uri != NULL);

	// XXX - wtf: use of int for a length.
	len = -1;
	err = uriToStringCharsRequiredA(uri, &len);
	if (err != 0) {
		// TODO: handle panicky errors in a better way
		perror("calculating string length of URI");
		abort();
	}

	if (len < 0) {
		// TODO: handle panicky errors in a better way
		fprintf(stderr, "internal error: negative URI length\n");
		abort();
	}

	data = xmalloc(len+1); /* uriparser adds a trailing NUL character */

	written = 0;
	err = uriToStringA(data, uri, len+1, &written);
	if (err != 0) {
		perror("converting URI to string");
		abort();
	}

	s = zero;
	s.len = len;
	s.s   = data;
	return s;
}

static struct ast_string_set **
add_id_from_uri(struct ast_string_set **idpp, const UriUriA *uri)
{
	static const struct ast_string_set zero;
	struct ast_string_set *id;

	id = xmalloc(sizeof *id);
	*id = zero;

	id->str = uri_as_json_string(uri);

	*idpp = id;
	idpp = &id->next;
	return idpp;
}

static struct ast_string_set **
add_id_from_uri_with_fragment(
	struct ast_string_set **idpp, const UriUriA *uri, const char *frag, size_t len)
{
	UriUriA uriFrag;
	UriUriA uriWhole;
	UriParserStateA state;
	int ret;

	if (uri == NULL) {
		/* just use the fragment
		 * XXX - should parse the fragment to ensure that it's
		 * a proper fragment
		 */
		struct ast_string_set *id;
		static const struct ast_string_set zero;
		struct json_string stmp = { .s = frag, .len = len };
		id = xmalloc(sizeof *id);
		*id = zero;

		id->str = json_strdup(stmp);

		*idpp = id;
		idpp = &id->next;
		return idpp;
	}

	state.uri = &uriFrag;
	if (ret = uriParseUriExA(&state, frag, frag+len), ret != URI_SUCCESS) {
		print_uri_error(ret);
	}

	if (ret = uriAddBaseUriA(&uriWhole, &uriFrag, uri), ret != URI_SUCCESS) {
		print_uri_error(ret);
	}

	idpp = add_id_from_uri(idpp, &uriWhole);

	uriFreeUriMembersA(&uriFrag);
	uriFreeUriMembersA(&uriWhole);

	return idpp;
}

static void print_uri_error(int err)
{

	switch (err) {
	case URI_SUCCESS: 
		return;

	case URI_ERROR_SYNTAX: /* Parsed text violates expected format */
		fprintf(stderr, "URI error %d: syntax error while parsing URI\n", err);
		break;

	case URI_ERROR_NULL: /* One of the params passed was NULL although it mustn't be */
		fprintf(stderr, "URI error %d: NULL parameter\n", err);
		break;

	case URI_ERROR_MALLOC: /* Requested memory could not be allocated */
		fprintf(stderr, "URI error %d: memory could not be allocated\n", err);
		break;

	case URI_ERROR_OUTPUT_TOO_LARGE: /* Some output is to large for the receiving buffer */
	/* case URI_ERROR_TOSTRING_TOO_LONG: */   /* Deprecated, test for URI_ERROR_OUTPUT_TOO_LARGE instead */
		fprintf(stderr, "URI error %d: output is too large for buffer\n", err);
		break;

	case URI_ERROR_NOT_IMPLEMENTED: /* The called function is not implemented yet */
		fprintf(stderr, "URI error %d: not implemented\n", err);
		break;

	case URI_ERROR_RANGE_INVALID: /* The parameters passed contained invalid ranges */
		fprintf(stderr, "URI error %d: invalid range\n", err);
		break;

	/* Errors specific to AddBaseUri */
	case URI_ERROR_ADDBASE_REL_BASE:        /* Given base is not absolute */
		fprintf(stderr, "URI error %d: adding base, but base URI is not absolute\n", err);
		break;

	/* Errors specific to RemoveBaseUri */
	case URI_ERROR_REMOVEBASE_REL_BASE:     /* Given base is not absolute */
		fprintf(stderr, "URI error %d: removing base, but base URI is not absolute\n", err);
		break;

	case URI_ERROR_REMOVEBASE_REL_SOURCE:   /* Given base is not absolute */
		fprintf(stderr, "URI error %d: removing base, but source URI is not absolute\n", err);
		break;

	default:
		fprintf(stderr, "unknown URI error %d\n", err);
	}

	abort();
}

void
ast_add_definitions(struct ast_schema *ast, struct ast_schema *def)
{
	struct ast_schema_set *sset;

	sset = xmalloc(sizeof *sset);
	sset->schema = def;
	sset->next = ast->definitions;

	ast->definitions = sset;
}

/* vim: set tabstop=8 shiftwidth=8 noexpandtab: */

