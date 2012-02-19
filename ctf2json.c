/*
 * CDDL HEADER START
 *
 * The contents of this file are subject to the terms of the
 * Common Development and Distribution License (the "License").
 * You may not use this file except in compliance with the License.
 *
 * You can obtain a copy of the license at usr/src/OPENSOLARIS.LICENSE
 * or http://www.opensolaris.org/os/licensing.
 * See the License for the specific language governing permissions
 * and limitations under the License.
 *
 * When distributing Covered Code, include this CDDL HEADER in each
 * file and include the License file at usr/src/OPENSOLARIS.LICENSE.
 * If applicable, add the following below this CDDL HEADER, with the
 * fields enclosed by brackets "[]" replaced with your own identifying
 * information: Portions Copyright [yyyy] [name of copyright owner]
 *
 * CDDL HEADER END
 */
/*
 * Copyright (c) 2011, Joyent, Inc. All rights reserved.
 * Copyright (c) 2011, Robert Mustacchi, Inc. All rights reserved.
 */

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <strings.h>
#include <libctf.h>
#include <stdio.h>
#include <assert.h>
#include <time.h>
#include <libgen.h>
#include <libelf.h>
#include <gelf.h>

/*
 * <sys/avl.h> is a private header. It's a little naughty to go in and expose
 * it. However, in all honesty better this than using some other avl
 * implementation.
 */
#include <sys/avl.h>

/*
 * <sys/list.h> is historically only for kernel drivers. We might as well use it
 * for the userland as well. We've graciously used the CDDL list.c from
 * usr/src/uts/common/list/list.c
 */
#include <sys/list.h>

#define	CTF_TYPE_NAMELEN	256		/* 2xDT_TYPE_NAMELEN */

#define	JSON_FORMAT_VERSION	"1.0"
#define	LIBCTF_VERSION		CTF_VERSION_2

typedef struct visit {
	avl_node_t	v_link;			/* list link */
	ctf_id_t	v_id;			/* id of this node */
} visit_t;

typedef struct psm_cb {
	ctf_file_t	*psm_fp;
	FILE		*psm_out;
	size_t		psm_size;
	unsigned int    psm_count;
} psm_cb_t;

typedef struct arg {
	list_node_t	a_link;
	const char	*a_arg;
} arg_t;

static avl_tree_t g_visited;
static avl_tree_t g_visiting;
static list_t g_types;
static const char *g_file;
static const char *g_prog;

static void walk_type(ctf_file_t *, ctf_id_t);

static int
visited_compare(const void *arg0, const void *arg1)
{
	const visit_t *l = arg0;
	const visit_t *r = arg1;

	if (l->v_id > r->v_id)
		return (1);

	if (l->v_id < r->v_id)
		return (-1);

	return (0);
}

static void
vwarn(const char *format, va_list alist)
{
	(void) fprintf(stderr, "%s: ", g_prog);
	(void) vfprintf(stderr, format, alist);
}

/*PRINTFLIKE2*/
static void
ctfdie(ctf_file_t *fp, const char *format, ...)
{
	va_list ap;

	va_start(ap, format);
	vwarn(format, ap);

	(void) fputs(": ", stderr);
	(void) fprintf(stderr, "%s\n", ctf_errmsg(ctf_errno(fp)));
	va_end(ap);
	exit(1);
}

/*PRINTFLIKE1*/
static void
die(const char *format, ...)
{
	va_list alist;

	va_start(alist, format);
	vwarn(format, alist);
	va_end(alist);
	exit(1);
}

/*
 * Make sure that we understand the type the array contains
 */
static void
walk_array(ctf_file_t *fp, ctf_id_t id)
{
	ctf_arinfo_t arp;
	if (ctf_array_info(fp, id, &arp) != 0)
		ctfdie(fp, "failed to read array information");
	walk_type(fp, arp.ctr_contents);
}

/*ARGSUSED*/
static int
walk_struct_member(const char *name, ctf_id_t id, ulong_t offset, void *arg)
{
	ctf_file_t *fp = arg;
	walk_type(fp, id);
	return (0);
}

static void
walk_struct(ctf_file_t *fp, ctf_id_t id)
{
	(void) ctf_member_iter(fp, id, walk_struct_member, fp);
}


/*
 * Always attempt to resolve the type.
 */
static void
walk_type(ctf_file_t *fp, ctf_id_t id)
{
	int kind;
	visit_t search, *found;

	search.v_id = id;
	found = avl_find(&g_visited, &search, NULL);
	if (found != NULL)
		return;

	found = avl_find(&g_visiting, &search, NULL);
	if (found != NULL)
		return;

	/*
	 * Mark node as being visited
	 * We need this to prevent infinite recursion through pointers.
	 */
	found = malloc(sizeof (visit_t));
	if (found == NULL)
		die("Failed to malloc\n");
	found->v_id = id;
	avl_add(&g_visiting, found);

	if ((kind = ctf_type_kind(fp, id)) == CTF_ERR)
		ctfdie(fp, "could not determine kind of type %ld", id);

	/*
	 * There are three different classes of types that we need to concern
	 * ourselves with here.
	 *
	 *  - Basic types with no aditional resolution. (ints, floats)
	 *  - Types that we never should deal with (const, volatile)
	 *  - Types that we need to look further at (arrays, structs, unions)
	 */
	switch (kind) {
	case CTF_K_ARRAY:
		walk_array(fp, id);
		break;
	case CTF_K_UNION:
	case CTF_K_STRUCT:
		walk_struct(fp, id);
		break;
	case CTF_K_TYPEDEF:
	case CTF_K_POINTER:
		walk_type(fp, ctf_type_reference(fp, id));
		break;
	case CTF_K_FUNCTION:
	case CTF_K_INTEGER:
	case CTF_K_FLOAT:
	case CTF_K_ENUM:
		break;
	case CTF_K_FORWARD:
	case CTF_K_UNKNOWN:
	case CTF_K_VOLATILE:
	case CTF_K_CONST:
	case CTF_K_RESTRICT:
		goto out;
	default:
		die("unknown or unresolved CTF kind for id %ld: %d\n", id,
		    kind);
	}

	/* Mark node as visited and don't forget where we came from */
	found = malloc(sizeof (visit_t));
	if (found == NULL)
		die("Failed to malloc\n");
	found->v_id = id;
	avl_add(&g_visited, found);
out:
	search.v_id = id;
	if ((found = avl_find(&g_visiting, &search, NULL)) != NULL)
		avl_remove(&g_visiting, found);
}

static void
print_int(FILE *out, ctf_file_t *fp, ctf_id_t id)
{
	char name[CTF_TYPE_NAMELEN];
	ctf_encoding_t ep;

	if (ctf_type_encoding(fp, id, &ep) != 0)
		ctfdie(fp, "failed to read integer type encoding for %ld",
		    id);
	if (ctf_type_name(fp, id, name, sizeof (name)) == NULL)
		ctfdie(fp, "failed to get name of type %ld", id);

	(void) fprintf(out, "\t\t{ \"name\": \"%s\", \"integer\": { "
	    "\"length\": %d, \"signed\": %s } }", name, ep.cte_bits / 8,
	    ep.cte_format & CTF_INT_SIGNED ? "true" : "false");
}

static void
print_pointer(FILE *out, ctf_file_t *fp, ctf_id_t id)
{
	char name[CTF_TYPE_NAMELEN];
	char tname[CTF_TYPE_NAMELEN];
	ctf_id_t subtype;

	if (ctf_type_name(fp, id, name, sizeof (name)) == NULL)
		die("failed to get name of type %ld\n", id);

	subtype = ctf_type_reference(fp, id);
	if (ctf_type_name(fp, subtype, tname, sizeof (tname)) == NULL)
		die("failed to get name of pointee type %ld\n",
		    subtype);

	(void) fprintf(out, "\t\t{ \"name\": \"%s\", \"pointer\": \"%s\" }",
	    name, tname);
}

static void
print_float(FILE *out, ctf_file_t *fp, ctf_id_t id)
{
	char name[CTF_TYPE_NAMELEN];
	ctf_encoding_t ep;

	if (ctf_type_encoding(fp, id, &ep) != 0)
		ctfdie(fp, "failed to read float type encoding for %ld",
		    id);
	if (ctf_type_name(fp, id, name, sizeof (name)) == NULL)
		ctfdie(fp, "failed to get name of type %ld", id);

	(void) fprintf(out, "\t\t{ \"name\": \"%s\", \"float\": { "
	    "\"length\": %d } }", name, ep.cte_bits / 8);
}

/*ARGSUSED*/
static int
count_struct_members(const char *name, ctf_id_t id, ulong_t off, void *arg)
{
	(*(int *)arg)++;
	return (0);
}

/*ARGSUSED*/
static int
print_struct_member(const char *name, ctf_id_t id, ulong_t off, void *arg)
{
	psm_cb_t *cb = arg;
	char type[CTF_TYPE_NAMELEN];

	cb->psm_count++;

	if (ctf_type_name(cb->psm_fp, id, type, sizeof (type)) == NULL)
		ctfdie(cb->psm_fp, "failed to get name of type %ld", id);

	(void) fprintf(cb->psm_out, "\t\t\t{ \"name\": \"%s\", \"type\": "
	    "\"%s\" }%s\n",
	    name, type, (cb->psm_count < cb->psm_size) ? "," : "");

	return (0);
}

static void
print_struct(FILE *out, ctf_file_t *fp, ctf_id_t id)
{
	char name[CTF_TYPE_NAMELEN];
	psm_cb_t cb;
	int n = 0;

	if (ctf_type_name(fp, id, name, sizeof (name)) == NULL)
		ctfdie(fp, "failed to get name of type %ld", id);

	(void) ctf_member_iter(fp, id, count_struct_members, &n);

	cb.psm_fp = fp;
	cb.psm_out = out;
	cb.psm_count = 0;
	cb.psm_size = n;

	(void) fprintf(out, "\t\t{ \"name\": \"%s\", \"struct\": [\n", name);
	(void) ctf_member_iter(fp, id, print_struct_member, &cb);
	(void) fprintf(out, "\t\t] }");
}

static void
print_union(FILE *out, ctf_file_t *fp, ctf_id_t id)
{
	char name[CTF_TYPE_NAMELEN];
	psm_cb_t cb;
	int n = 0;

	if (ctf_type_name(fp, id, name, sizeof (name)) == NULL)
		die("failed to get name of type %ld\n", id);

	(void) ctf_member_iter(fp, id, count_struct_members, &n);

	cb.psm_fp = fp;
	cb.psm_out = out;
	cb.psm_count = 0;
	cb.psm_size = n;

	(void) fprintf(out, "\t\t{ \"name\": \"%s\", \"union\": [\n", name);
	(void) ctf_member_iter(fp, id, print_struct_member, &cb);
	(void) fprintf(out, "\t\t] }");
}

/*ARGSUSED*/
static int
count_enum_members(const char *name, int value, void *arg)
{
	(*(int *)arg)++;
	return (0);
}

static int
print_enum_member(const char *name, int value, void *arg)
{
	psm_cb_t *cb = (psm_cb_t *)arg;

	cb->psm_count++;

	(void) fprintf(cb->psm_out, "\t\t\t{ \"name\": \"%s\", "
	    "\"value\": %d }%s\n", name, value,
	    (cb->psm_count < cb->psm_size) ? "," : "");

	return (0);
}

static void
print_enum(FILE *out, ctf_file_t *fp, ctf_id_t id)
{
	char name[CTF_TYPE_NAMELEN];
	psm_cb_t cb;
	int n = 0;

	if (ctf_type_name(fp, id, name, sizeof (name)) == NULL)
		ctfdie(fp, "failed to get name of type %ld", id);

	(void) ctf_enum_iter(fp, id, count_enum_members, &n);

	cb.psm_fp = fp;
	cb.psm_out = out;
	cb.psm_size = n;
	cb.psm_count = 0;

	(void) fprintf(out, "\t\t{ \"name\": \"%s\", \"enum\": [\n", name);
	(void) ctf_enum_iter(fp, id, print_enum_member, &cb);
	(void) fprintf(out, "\t\t] }");
}

static void
print_typedef(FILE *out, ctf_file_t *fp, ctf_id_t id)
{
	char from[CTF_TYPE_NAMELEN], to[CTF_TYPE_NAMELEN];
	ctf_id_t sub = 0;

	sub = ctf_type_reference(fp, id);

	if (ctf_type_name(fp, id, from, sizeof (from)) == NULL)
		ctfdie(fp, "failed to get name of type %ld", id);
	if (ctf_type_name(fp, sub, to, sizeof (to)) == NULL)
		ctfdie(fp, "failed to get name of type %ld", sub);

	(void) fprintf(out, "\t\t{ \"name\": \"%s\", \"typedef\": \"%s\" }",
	    from, to);
}

static void
print_function(FILE *out, ctf_file_t *fp, ctf_id_t id)
{
	char name[CTF_TYPE_NAMELEN];

	if (ctf_type_name(fp, id, name, sizeof (name)) == NULL)
		ctfdie(fp, "failed to get name of type %ld", id);

	(void) fprintf(out, "\t\t{ \"name\": \"%s\", \"function\": true }",
	    name);
}

static void
print_tree(ctf_file_t *fp, avl_tree_t *avl)
{
	FILE *out = stdout;
	visit_t *cur;
	int kind;
	int needcomma = 0;

	cur = avl_first(avl);

	(void) fprintf(out, "\t[\n");
	for (; cur != NULL; cur = AVL_NEXT(avl, cur)) {
		kind = ctf_type_kind(fp, cur->v_id);
		assert(kind != CTF_ERR);

		if (kind == CTF_K_ARRAY)
			continue;

		if (needcomma++)
			(void) fprintf(out, ",\n");

		switch (kind) {
		case CTF_K_INTEGER:
			print_int(out, fp, cur->v_id);
			break;
		case CTF_K_FLOAT:
			print_float(out, fp, cur->v_id);
			break;
		case CTF_K_POINTER:
			print_pointer(out, fp, cur->v_id);
			break;
		case CTF_K_STRUCT:
			print_struct(out, fp, cur->v_id);
			break;
		case CTF_K_UNION:
			print_union(out, fp, cur->v_id);
			break;
		case CTF_K_ENUM:
			print_enum(out, fp, cur->v_id);
			break;
		case CTF_K_FUNCTION:
			print_function(out, fp, cur->v_id);
			break;
		case CTF_K_TYPEDEF:
			print_typedef(out, fp, cur->v_id);
			break;
		default:
			die("Unimplemented kind. kind/id:  %d %ld\n",
			    kind, cur->v_id);
			break;
		}
	}

	(void) fprintf(out, "\n\t]");
}

static void
print_metadata(FILE *out)
{
	time_t now;
	arg_t *arg, *last;

	now = time(NULL);
	(void) fprintf(out, "\t{\n\t\t\"ctf2json_version\": \"%s\",\n\t\t\""
	    "created_at\": "
	    "%ld,\n\t\t\"derived_from\": \"%s\",\n\t\t\"ctf_version\": %d",
	    JSON_FORMAT_VERSION, now, g_file, LIBCTF_VERSION);

	if (!list_is_empty(&g_types)) {
		(void) fprintf(out, ",\n\t\t\"requested_types\": [ ");
		last = list_tail(&g_types);
		for (arg = list_head(&g_types); arg != NULL;
		    arg = list_next(&g_types, arg)) {
			(void) fprintf(out, "\"%s\" ", arg->a_arg);
			if (arg != last)
				(void) fprintf(out, ", ");
		}

		(void) fprintf(out, "]");
	}

	(void) fprintf(out, "\n\t}");
}

static void
add_list_arg(list_t *list, const char *arg)
{
	arg_t *a;

	a = malloc(sizeof (arg_t));
	if (a == NULL)
		die("failed to allocate memory\n");

	list_link_init(&a->a_link);
	a->a_arg = arg;
	list_insert_tail(list, a);
}

static int
each_type(ctf_id_t id, void *arg)
{
	ctf_file_t *fp = (ctf_file_t *)arg;

	walk_type(fp, id);
	return (0);
}

static void
build_tree(ctf_file_t *fp)
{
	ctf_id_t id;
	arg_t *arg;

	if (list_is_empty(&g_types)) {
		(void) ctf_type_iter(fp, each_type, fp);
	} else {
		for (arg = list_head(&g_types); arg != NULL;
		    arg = list_next(&g_types, arg)) {
			id = ctf_lookup_by_name(fp, arg->a_arg);
			if (id < 0)
				ctfdie(fp, "type not present in binary: %s",
				    arg->a_arg);

			walk_type(fp, id);
		}
	}
}

static void
usage(void)
{
	(void) fprintf(stderr, "Usage: %s [-F] -f file [ -f file ...] "
	    "[-t type ...]\n\n", g_prog);
	(void) fprintf(stderr, "\t-f  use file for CTF data\n");
	(void) fprintf(stderr, "\t-F  display information about functions\n");
	(void) fprintf(stderr, "\t-t  dump CTF data for type\n");
	exit(1);
}

typedef struct symtab_sym {
	int ss_indx;
	GElf_Sym ss_sym;
	char *ss_name;
} symtab_sym_t;


static int
print_funcsym(ctf_file_t *fp, symtab_sym_t *ss, int firstp)
{
	ctf_funcinfo_t finfo;
	ctf_id_t *args = NULL;
	char retname[CTF_TYPE_NAMELEN];

	/* We only care about global functions */
	if ((GELF_ST_TYPE(ss->ss_sym.st_info) != STT_FUNC) ||
	    GELF_ST_BIND(ss->ss_sym.st_info) != STB_GLOBAL)
		return (0);

	if (ctf_func_info(fp, ss->ss_indx, &finfo) == CTF_ERR) {
		/*
		 * I'd like to check for ECTF_NOFUNCDAT and error
		 * otherwise but the error codes are hidden in
		 * ctf_impl.h, in an enum so you can't even safely
		 * crib the value
		 */
		return (0);
	}

	if ((args = malloc(sizeof (ctf_id_t) * finfo.ctc_argc)) == NULL)
		die("could not allocate memory\n");

	if (ctf_func_args(fp, ss->ss_indx, finfo.ctc_argc, args) == CTF_ERR)
		ctfdie(fp, "could not lookup arguments for %s", ss->ss_name);

	if (ctf_type_name(fp, finfo.ctc_return, retname,
	    sizeof (retname)) == NULL)
		ctfdie(fp, "failed to get name of type %ld",
		    finfo.ctc_return);

	if (firstp == 0)
		(void) fprintf(stdout, ",\n");

	(void) fprintf(stdout, "\t\t{ \"name\": \"%s\", \"function\": "
	    "{ \"return\": \"%s\", \"arguments\": [\n", ss->ss_name, retname);

	for (unsigned i = 0; i < finfo.ctc_argc; i++) {
		char argtype[CTF_TYPE_NAMELEN];

		if (ctf_type_name(fp, args[i], argtype,
		    sizeof (argtype)) == NULL)
			ctfdie(fp, "failed to get name of type %ld",
			    args[i]);

		(void) fprintf(stdout, "\t\t\t\"%s\"%s\n", argtype,
		    (i == (finfo.ctc_argc - 1)) ? "" : ",");
	}

	(void) fprintf(stdout, "\t\t] } }");

	free(args);
	return (1);
}

static int
print_objtsym(ctf_file_t *fp, symtab_sym_t *ss, int firstp)
{
	ctf_id_t id;
	char tname[CTF_TYPE_NAMELEN];

	/* We only care about global functions */
	if ((GELF_ST_TYPE(ss->ss_sym.st_info) != STT_OBJECT) ||
	    (GELF_ST_BIND(ss->ss_sym.st_info) != STB_GLOBAL &&
	    GELF_ST_BIND(ss->ss_sym.st_info) != STB_LOCAL))
		return (0);

	/* Some symbols legitimately won't have types, sadly */
	if ((id = ctf_lookup_by_symbol(fp, ss->ss_indx)) == CTF_ERR)
		return (0);

	if (ctf_type_name(fp, id, tname, sizeof (tname)) == NULL)
		ctfdie(fp, "failed to get name of type %ld", id);

	if (firstp == 0)
		(void) fprintf(stdout, ",\n");

	(void) fprintf(stdout, "\t\t{ \"name\": \"%s\", \"type\": \"%s\" }",
	    ss->ss_name, tname);

	return (1);
}

static void
walk_symtab(ctf_file_t *fp, int (*callback)(ctf_file_t *, symtab_sym_t *, int))
{
	Elf *elf;
	Elf_Scn *scn = NULL;
	Elf_Data *data = NULL;
	GElf_Shdr shdr;
	int fd, found = 0;
	int firstp = 1;
	symtab_sym_t ss;

	if (elf_version(EV_CURRENT) == EV_NONE)
		die("mismatched libelf versions\n");

	if ((fd = open(g_file, O_RDONLY)) == -1)
		die("could not open %s\n", g_file);

	if ((elf = elf_begin(fd, ELF_C_READ, NULL)) == NULL)
		die("could not interpret ELF from %s\n",
		    g_file);

	while ((scn = elf_nextscn(elf, scn)) != NULL) {
		(void) gelf_getshdr(scn, &shdr);

		if (shdr.sh_type == SHT_SYMTAB) {
			found = 1;
			break;
		}
	}

	if (!found) {
		(void) fprintf(stdout, "[]");
		goto out;
	}

	(void) fprintf(stdout, "\t[\n");

	data = elf_getdata(scn, NULL);

	for (unsigned symdx = 0; symdx < (shdr.sh_size / shdr.sh_entsize);
	    symdx++) {
		(void) gelf_getsym(data, symdx, &ss.ss_sym);

		ss.ss_indx = symdx;
		ss.ss_name = elf_strptr(elf, shdr.sh_link, ss.ss_sym.st_name);

		if (callback(fp, &ss, firstp) == 1)
			firstp = 0;
	}
	(void) fprintf(stdout, "\n\t]");

out:
	(void) elf_end(elf);
	(void) close(fd);
}

int
main(int argc, char **argv)
{
	int errp, c;
	ctf_file_t *ctfp, *pctfp;
	list_t files;
	int showfuncs = 0, showvars = 0;

	g_prog = basename(argv[0]);
	avl_create(&g_visited, visited_compare, sizeof (visit_t), 0);
	avl_create(&g_visiting, visited_compare, sizeof (visit_t), 0);
	list_create(&g_types, sizeof (arg_t), 0);
	list_create(&files, sizeof (arg_t), 0);

	if (argc == 1)
		usage();

	while ((c = getopt(argc, argv, "VFt:f:")) != EOF) {
		switch (c) {
		case 'f':
			/*
			 * The first file is _the_ file, subsequent are
			 * antescedents
			 */
			if (g_file == NULL)
				g_file = optarg;
			else
				add_list_arg(&files, optarg);
			break;
		case 'F':
			showfuncs = 1;
			break;
		case 'V':
			showvars = 1;
			break;
		case 't':
			add_list_arg(&g_types, optarg);
			break;
		case ':':
		case '?':
		default:
			usage();
			break;
		}
	}

	if (g_file == NULL)
		die("missing required -f option\n");

	(void) ctf_version(LIBCTF_VERSION);
	ctfp = ctf_open(g_file, &errp);
	if (ctfp == NULL)
		die("failed to ctf_open file: %s: %s\n", g_file,
		    ctf_errmsg(errp));

	if (!list_is_empty(&files)) {
		if (ctf_parent_name(ctfp) == NULL) {
			(void) fprintf(stderr, "%s: warning: %s has no "
			    "parent module, but parents are specified\n",
			    g_prog, g_file);
		} else {
			for (arg_t *arg = list_head(&files); arg != NULL;
			    arg = list_next(&files, arg)) {
				pctfp = ctf_open(arg->a_arg, &errp);
				if (pctfp == NULL)
					die("failed to ctf_open file: %s: %s\n",
					    arg->a_arg,
					    ctf_errmsg(errp));

				if (ctf_import(ctfp, pctfp) == CTF_ERR)
					die("failed to import parent CTF: %s\n",
					    ctf_errmsg(ctf_errno(ctfp)));

				ctf_close(pctfp);
			}
		}
	}

	build_tree(ctfp);

	(void) fprintf(stdout, "{ \"metadata\":\n");
	print_metadata(stdout);
	(void) fprintf(stdout, ",\n\"data\":\n");
	print_tree(ctfp, &g_visited);
	if (showfuncs) {
		(void) fprintf(stdout, ",\n\"functions\":\n");
		walk_symtab(ctfp, print_funcsym);
	}
	if (showvars) {
		(void) fprintf(stdout, ",\n\"variables\":\n");
		walk_symtab(ctfp, print_objtsym);
	}
	(void) fprintf(stdout, "\n}\n");

	exit(0);
}
