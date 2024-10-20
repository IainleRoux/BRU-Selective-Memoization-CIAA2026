#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "../../utils.h"
#include "memoisation.h"

#define top   ((bru_state_id *) stc_linkedlist_first(stack))
#define DEBUG FALSE

/* --- Helper functions ----------------------------------------------------- */

static bru_byte_t *memoise_in(BruStateMachine *sm)
{
    size_t        i, n, nstates = bru_smir_get_num_states(sm);
    size_t       *in_degrees = calloc(nstates, sizeof(size_t));
    bru_byte_t   *memo_sids  = calloc(nstates, sizeof(bru_byte_t));
    bru_state_id  sid, dst;
    bru_trans_id *out_transitions;

    for (sid = 0; sid <= nstates; sid++) {
        out_transitions = bru_smir_get_out_transitions(sm, sid, &n);
        for (i = 0; i < n; i++) {
            dst = bru_smir_get_dst(sm, out_transitions[i]);
            if (!BRU_IS_FINAL_STATE(dst)) in_degrees[dst - 1]++;
        }
        if (out_transitions) free(out_transitions);
    }

    for (sid = 1; sid <= nstates; sid++)
        memo_sids[sid - 1] = in_degrees[sid - 1] > 1;

    if (in_degrees) free(in_degrees);

    return memo_sids;
}

static void cn_dfs(BruStateMachine *sm,
                   bru_state_id     sid,
                   bru_byte_t      *has_backedge,
                   bru_byte_t      *on_path)
{
    bru_trans_id *out_transitions;
    size_t        i, n;
    bru_state_id  dst;

    if (sid) on_path[sid - 1] = TRUE;
    out_transitions = bru_smir_get_out_transitions(sm, sid, &n);
    for (i = 0; i < n; i++) {
        dst = bru_smir_get_dst(sm, out_transitions[i]);

        if (BRU_IS_FINAL_STATE(dst)) continue;

        if (on_path[dst - 1]) {
            has_backedge[dst - 1] = TRUE;
            continue;
        }

        cn_dfs(sm, dst, has_backedge, on_path);
    }

    if (out_transitions) free(out_transitions);
    if (sid) on_path[sid - 1] = FALSE;
}

static bru_byte_t *memoise_cn(BruStateMachine *sm)
{
    size_t      nstates   = bru_smir_get_num_states(sm);
    bru_byte_t *memo_sids = calloc(nstates, sizeof(bru_byte_t));
    bru_byte_t *on_path;

    if (nstates > 0) {
        on_path = calloc(nstates, sizeof(bru_byte_t));
        cn_dfs(sm, BRU_INITIAL_STATE_ID, memo_sids, on_path);
        free(on_path);
    }

    return memo_sids;
}

void debug_fprintf(FILE *stream, const char *format, ...)
{
    if (DEBUG) {
        va_list args;
        va_start(args, format);
        vfprintf(stream, format, args);
        va_end(args);
    }
}

static int state_cmp(void *key1, void *key2)
{
    debug_fprintf(stderr, "comparing (%d, %d)\n", *((bru_state_id *) key1),
                  *((bru_state_id *) key2));
    debug_fprintf(stderr, "*%d != %d: %d \n", *((bru_state_id *) key1),
                  *((bru_state_id *) key2),
                  *((bru_state_id *) key1) != *((bru_state_id *) key2));
    return *((bru_state_id *) key1) != *((bru_state_id *) key2);
}

static StcLinkedList *MFVS(BruStateMachine *sm, bru_state_id sid)
{
    size_t         n, nstates = bru_smir_get_num_states(sm);
    StcLinkedList *S            = stc_linkedlist_new_with_cmp(state_cmp);
    StcLinkedList *stack        = stc_linkedlist_new_with_cmp(state_cmp);
    bru_byte_t    *number       = calloc(nstates + 1, sizeof(bru_byte_t));
    bru_byte_t    *l            = calloc(nstates + 1, sizeof(bru_byte_t));
    bru_byte_t     c            = 1;
    bru_byte_t     halt         = 0;
    bru_byte_t   **marked_edges = calloc(nstates + 1, sizeof(bru_byte_t *));
    bru_byte_t    *visited      = calloc(nstates + 1, sizeof(bru_byte_t));
    bru_trans_id  *out_transitions;
    bru_state_id  *v, dst, *v_prime;

    for (unsigned int i = 0; i < nstates + 1; i++)
        marked_edges[i] = calloc(nstates + 1, sizeof(bru_byte_t));

    debug_fprintf(stderr, "Step 1:\n");
    stc_linkedlist_push(stack, &sid);

    while (TRUE) {
        debug_fprintf(stderr, "Step 2:\n");
        number[*top] = c++;
        l[*top]      = 0;

        while (TRUE) {
            debug_fprintf(stderr, "Step 3:\n");
            out_transitions = bru_smir_get_out_transitions(sm, *top, &n);
            v               = (bru_state_id *) malloc(sizeof(bru_state_id));
            *v              = 0;
            for (unsigned int i = 0; i < n; i++) {
                dst = bru_smir_get_dst(sm, out_transitions[i]);
                if (BRU_IS_FINAL_STATE(dst)) continue;

                if (!marked_edges[*top][dst]) {
                    debug_fprintf(stderr, "\tunmarked edge = (%d, %d)\n", *top,
                                  dst);
                    marked_edges[*top][dst] = 1;
                    *v                      = dst;
                    break;
                }
            }
            debug_fprintf(stderr, "v=%d\n", *v);
            if (*v) {
                debug_fprintf(stderr, "Step 4:\n");
                if (!visited[*v]) {
                    debug_fprintf(stderr, "\tPushing %d\n", *v);
                    debug_fprintf(stderr, "\tStack top = %d\n", *top);
                    stc_linkedlist_push(stack, v);
                    debug_fprintf(stderr, "\tPushed %d\n", *v);
                    debug_fprintf(stderr, "\tStack top = %d\n", *top);
                    visited[*v] = 1; // TODO check this
                    break;
                }

                debug_fprintf(stderr, "Step 5:\n");
                if (stc_linkedlist_contains(stack, v)) {
                    debug_fprintf(stderr, "\tBackwards edge = (%d, %d)\n", *top,
                                  *v);
                    if (l[*top] < number[*v]) l[*top] = number[*v];
                    continue;
                }

                debug_fprintf(stderr, "Step 6:\n");
                if (l[*top] < l[*v]) l[*top] = l[*v];
                continue;
            }
            debug_fprintf(stderr, "Step 7:\n");
            if (l[*top] == number[*top]) {
                debug_fprintf(stderr, "\tAdded %d to MFVS\n", *top);
                stc_linkedlist_enqueue(S, &(*top));
                l[*top] = 0;
            }
            debug_fprintf(stderr, "Step 8:\n");
            v_prime = stc_linkedlist_pop(stack);
            if (stc_linkedlist_is_empty(stack)) {
                halt = 1;
                break;
            } else {
                if (l[*top] < l[*v_prime]) l[*top] = l[*v_prime];
            }
        }

        if (halt) break;
    }

    return S;
}

static bru_byte_t *memoise_shamir(BruStateMachine *sm)
{
    size_t        nstates   = bru_smir_get_num_states(sm);
    bru_byte_t   *memo_sids = calloc(nstates, sizeof(bru_byte_t));
    bru_state_id *v;

    StcLinkedList *S = MFVS(sm, 0);
    fprintf(stderr, "[");
    while (!stc_linkedlist_is_empty(S)) {
        v             = ((bru_state_id *) stc_linkedlist_pop(S));
        memo_sids[*v-1] = 1;
        fprintf(stderr, "%u", *v + 1);
        if (!stc_linkedlist_is_empty(S)) fprintf(stderr, ",");
    }
    fprintf(stderr, "]\n");

    return memo_sids;
}

/**
 * Memoise the states of a state machine in the given set of state identifiers.
 *
 * The set of state identifiers, `sids`, is interpretted as a boolean array
 * indexed by state identifier. A non-zero value in the array for a given state
 * identifier `i` indicates that state should be memoised, while a value of zero
 * indicates it should not be.
 *
 * @param[in] sm      the state machine
 * @param[in] sids    a boolean array indicating if a state is in the set to be
 *                    memoised
 * @param[in] logfile the file for logging output
 */
static void memoise_states(BruStateMachine *sm, bru_byte_t *sids, FILE *logfile)
{
    bru_state_id sid;
    size_t       nstates, k = SIZE_MAX;
    // NOTE: `k` can be any value -- it must only be unique amongst MEMO
    // actions. Of course, if there is already memoisation then there could be
    // overlap. It is expected that starting at the maximum possible value for k
    // and decrementing should give the least overlap.

    for (sid = 1, nstates = bru_smir_get_num_states(sm); sid <= nstates; sid++)
        if (sids[sid - 1])
            bru_smir_state_prepend_action(
                sm, sid, bru_smir_action_num(BRU_ACT_MEMO, k--));

#ifdef BRU_BENCHMARK
    if (logfile)
        fprintf(logfile, "NUMBER OF STATES MEMOISED: %zu\n", SIZE_MAX - k);
#else
    BRU_UNUSED(logfile);
#endif /* BRU_BENCHMARK */
}

/* --- API function definitions --------------------------------------------- */

BruStateMachine *
bru_transform_memoise(BruStateMachine *sm, BruMemoScheme memo, FILE *logfile)
{
    bru_byte_t *memo_sids;

    if (!sm) return sm;

    switch (memo) {
        case BRU_MS_NONE: return sm;
        case BRU_MS_IN: memo_sids = memoise_in(sm); break;
        case BRU_MS_CN: memo_sids = memoise_cn(sm); break;
        case BRU_MS_IAR: return sm;
        case BRU_MS_MFN: return sm;
        // NOTE: SHAMIR only works for Thompson graphs
        case BRU_MS_SHAMIR: memo_sids = memoise_shamir(sm); break;
    }

    memoise_states(sm, memo_sids, logfile);
    if (memo_sids) free(memo_sids);

    return sm;
}
