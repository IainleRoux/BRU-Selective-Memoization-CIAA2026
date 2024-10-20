#include <stdlib.h>

#include "../fa/constructions/glushkov.h"
#include "../fa/constructions/thompson.h"
#include "../fa/transformers/flatten.h"
#include "../fa/transformers/memoisation.h"
#include "../re/sre.h"
#include "../utils.h"
#include "compiler.h"

#define COMPILER_OPTS_DEFAULT \
    ((BruCompilerOpts){ BRU_THOMPSON, FALSE, BRU_CS_PCRE, BRU_MS_NONE, FALSE })

#define SET_OFFSET(p, pc) (*(p) = pc - (byte *) ((p) + 1))

#define PTASETS_DEFAULT                            \
    ((PTASets){ stc_linkedlist_new_with_cmp(NULL), \
                stc_linkedlist_new_with_cmp(NULL), \
                stc_linkedlist_new_with_cmp(NULL), FALSE })

static void compile_state_markers(void *meta, BruProgram *prog)
{
    BRU_UNUSED(meta);
    BRU_BCPUSH(prog->insts, BRU_STATE);
}

BruCompiler *bru_compiler_new(const BruParser      *parser,
                              const BruCompilerOpts opts)
{
    BruCompiler *compiler = malloc(sizeof(*compiler));

    compiler->parser = parser;
    compiler->opts   = opts;

    return compiler;
}

BruCompiler *bru_compiler_default(const BruParser *parser)
{
    return bru_compiler_new(parser, COMPILER_OPTS_DEFAULT);
}

void bru_compiler_free(BruCompiler *self)
{
    bru_parser_free((BruParser *) self->parser);
    free(self);
}

void join_left(StcLinkedList *left, StcLinkedList *right)
{
    while (!stc_linkedlist_is_empty(right))
        stc_linkedlist_enqueue(left, stc_linkedlist_dequeue(right));
}

PTASets pta_memo_ancestors(BruRegexNode *re)
{
    PTASets ptasets = PTASETS_DEFAULT;
    PTASets ptasets_left, ptasets_right;

    switch (re->type) {
        case BRU_CC:
        case BRU_LITERAL: stc_linkedlist_enqueue(ptasets.optional, re); break;
        case BRU_ALT:
            ptasets      = pta_memo_ancestors(re->left);
            ptasets_left = pta_memo_ancestors(re->right);
            join_left(ptasets.optional, ptasets_left.optional);
            join_left(ptasets.required, ptasets_left.required);
            join_left(ptasets.memo_ancestors, ptasets_left.memo_ancestors);
            ptasets.nullable |= ptasets_left.nullable;
            break;
        case BRU_CONCAT:
            ptasets_left  = pta_memo_ancestors(re->left);
            ptasets_right = pta_memo_ancestors(re->right);

            if (ptasets_left.nullable && ptasets_right.nullable) {
                ptasets = ptasets_left;
                join_left(ptasets.optional, ptasets_right.optional);
                join_left(ptasets.required, ptasets_right.required);
                join_left(ptasets.memo_ancestors, ptasets_right.memo_ancestors);
            } else if (ptasets_right.nullable) {
                ptasets = ptasets_left;
                join_left(ptasets.required, ptasets_right.required);
                join_left(ptasets.memo_ancestors, ptasets_right.memo_ancestors);
            } else if (ptasets_left.nullable) {
                ptasets = ptasets_right;
                join_left(ptasets.required, ptasets_left.required);
                join_left(ptasets.memo_ancestors, ptasets_left.memo_ancestors);
            } else if (stc_linkedlist_len(ptasets_left.optional) <=
                       stc_linkedlist_len(ptasets_right.optional)) {
                ptasets = ptasets_left;
                join_left(ptasets.required, ptasets_right.required);
                join_left(ptasets.memo_ancestors, ptasets_right.memo_ancestors);
            } else {
                ptasets = ptasets_right;
                join_left(ptasets.required, ptasets_left.required);
                join_left(ptasets.memo_ancestors, ptasets_left.memo_ancestors);
            }
            break;
        case BRU_STAR:
            ptasets = pta_memo_ancestors(re->left);

            if (stc_linkedlist_len(ptasets.optional) != 0)
                stc_linkedlist_enqueue(ptasets.memo_ancestors, re);

            join_left(ptasets.required, ptasets.optional);
            ptasets.nullable = TRUE;
            break;
        case BRU_PLUS:
            ptasets = pta_memo_ancestors(re->left);

            if (stc_linkedlist_len(ptasets.optional) != 0)
                stc_linkedlist_enqueue(ptasets.memo_ancestors, re);

            join_left(ptasets.required, ptasets.optional);
            break;
        case BRU_QUES:
            ptasets          = pta_memo_ancestors(re->left);
            ptasets.nullable = TRUE;
            break;
        case BRU_CAPTURE: ptasets = pta_memo_ancestors(re->left); break;
        case BRU_EPSILON:
        case BRU_CARET:
        case BRU_DOLLAR: ptasets.nullable = TRUE; break;
        case BRU_COUNTER:
        case BRU_LOOKAHEAD:
        case BRU_BACKREFERENCE:
        case BRU_NREGEXTYPES:
        default: fprintf(stderr, "ERROR: type=%d\n", re->type);
    }

    return ptasets;
}

void add_mfn_nodes(BruRegex re, BruConstruction con, FILE *logfile)
{
    PTASets ptasets;
    int     k = 0;

    if (con != BRU_FLAT && con != BRU_THOMPSON) {
        fprintf(stderr, "ERROR: MFN is only supported for FLAT and THOMPSON\n");
        return;
    }

    ptasets = pta_memo_ancestors(re.root);

    if (con == BRU_FLAT)
        while (!stc_linkedlist_is_empty(ptasets.required)) {
            ((BruRegexNode *) stc_linkedlist_dequeue(ptasets.required))->mfn =
                1;
            k++;
        }

    if (con == BRU_THOMPSON)
        while (!stc_linkedlist_is_empty(ptasets.memo_ancestors)) {
            ((BruRegexNode *) stc_linkedlist_dequeue(ptasets.memo_ancestors))
                ->mfn = 1;
            k++;
        }

#ifdef BRU_BENCHMARK
    if (logfile)
        fprintf(logfile, "NUMBER OF STATES MEMOISED: %d\n", k);
#else
    
#endif /* BRU_BENCHMARK */
}

const BruProgram *bru_compiler_compile(const BruCompiler *self)
{
    BruRegex          re;
    BruParseResult    res;
    const BruProgram *prog;
    BruStateMachine  *sm = NULL, *tmp = NULL;
    bru_byte_t        parse_tree_memoised = FALSE;

    res = bru_parser_parse(self->parser, &re);
    if (res.code != BRU_PARSE_SUCCESS) return NULL;

    if (self->opts.memo_scheme == BRU_MS_MFN &&
        (self->opts.construction == BRU_FLAT ||
         self->opts.construction == BRU_THOMPSON)) {
        add_mfn_nodes(re, self->opts.construction, self->parser->opts.logfile);
        parse_tree_memoised = TRUE;
    }

    switch (self->opts.construction) {
        case BRU_THOMPSON: sm = bru_thompson_construct(re, &self->opts); break;
        case BRU_GLUSHKOV: sm = bru_glushkov_construct(re, &self->opts); break;
        case BRU_FLAT:
            tmp = bru_thompson_construct(re, &self->opts);
            sm  = bru_transform_flatten(tmp, self->parser->opts.logfile);
            bru_smir_free(tmp);
            break;
    }
    bru_regex_node_free(re.root);

    if (self->opts.memo_scheme != BRU_MS_NONE && !parse_tree_memoised)
        sm = bru_transform_memoise(sm, self->opts.memo_scheme,
                                   self->parser->opts.logfile);
    
    bru_smir_print(sm, stderr);

#ifdef BRU_DEBUG
    bru_smir_print(sm, stderr);
#endif /* BRU_DEBUG */

    prog = bru_smir_compile_with_meta(
        sm, self->opts.mark_states ? compile_state_markers : NULL, NULL);
    bru_smir_free(sm);

    return prog;
}
