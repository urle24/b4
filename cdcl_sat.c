/*
 * cdcl_sat.c - small embeddable CDCL SAT solver (C11)
 *
 * Literals are signed integers:
 *   variable v (0-based) positive literal:  v + 1
 *   variable v (0-based) negative literal: -(v + 1)
 *
 * Public API:
 *   Sat *sat_create(void);
 *   void sat_destroy(Sat *s);
 *   int  sat_new_var(Sat *s);                         // returns 0-based id
 *   int  sat_add_clause(Sat *s, const int *lits, int n);
 *   SatResult sat_solve(Sat *s);
 *   int  sat_value(const Sat *s, int var);             // -1 false, 0 undef, +1 true
 *
 * The implementation uses:
 *   - two-watched literals
 *   - first-UIP conflict analysis
 *   - non-chronological backtracking
 *   - learned clauses
 *   - VSIDS-like variable activity
 *   - phase saving
 *   - geometric restarts
 *
 * It intentionally omits learned-clause deletion and a branching heap to keep
 * the implementation compact and readable. It is suitable for small/medium
 * embedded uses and as a base for further development.
 */

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef enum SatResult {
    SAT_RESULT_UNSAT = 0,
    SAT_RESULT_SAT   = 1,
    SAT_RESULT_ERROR = -1
} SatResult;

typedef struct Sat Sat;

Sat *sat_create(void);
Sat *sat_clone(const Sat *src);
Sat *sat_clone_formula(const Sat *src);
void sat_destroy(Sat *s);
int sat_new_var(Sat *s);
int sat_add_clause(Sat *s, const int *lits, int n);
SatResult sat_solve(Sat *s);
int sat_value(const Sat *s, int var);

#define SAT_POS(var) ((var) + 1)
#define SAT_NEG(var) (-(var) - 1)

/* ---------------------------- implementation ---------------------------- */

typedef struct Clause {
    int size;
    unsigned learnt : 1;
    double activity;
    int lits[];
} Clause;

typedef struct ClauseVec {
    Clause **data;
    int size;
    int cap;
} ClauseVec;

typedef struct IntVec {
    int *data;
    int size;
    int cap;
} IntVec;

struct Sat {
    int nvars;
    int vars_cap;

    int8_t *assigns;       /* -1 false, 0 undefined, +1 true */
    int8_t *phase;         /* saved preferred assignment */
    int *level;
    Clause **reason;
    double *activity;
    uint8_t *seen;

    ClauseVec clauses;
    ClauseVec learnts;
    ClauseVec *watches;    /* two entries per variable */
    int watches_cap;       /* number of ClauseVec entries */

    IntVec trail;
    IntVec trail_lim;
    int qhead;

    double var_inc;
    double var_decay;

    int ok;
    int solving;
    int oom;

    int conflicts;
    int restart_limit;
    double restart_growth;
};

static void *sat_realloc(Sat *s, void *p, size_t n)
{
    void *q = realloc(p, n);
    if (!q && n != 0) s->oom = 1;
    return q;
}

static int intvec_reserve(Sat *s, IntVec *v, int need)
{
    if (need <= v->cap) return 1;
    int cap = v->cap ? v->cap : 8;
    while (cap < need) {
        if (cap > INT32_MAX / 2) { s->oom = 1; return 0; }
        cap *= 2;
    }
    int *p = (int *)sat_realloc(s, v->data, (size_t)cap * sizeof(int));
    if (!p) return 0;
    v->data = p;
    v->cap = cap;
    return 1;
}

static int intvec_push(Sat *s, IntVec *v, int x)
{
    if (!intvec_reserve(s, v, v->size + 1)) return 0;
    v->data[v->size++] = x;
    return 1;
}

static int clausevec_reserve(Sat *s, ClauseVec *v, int need)
{
    if (need <= v->cap) return 1;
    int cap = v->cap ? v->cap : 4;
    while (cap < need) {
        if (cap > INT32_MAX / 2) { s->oom = 1; return 0; }
        cap *= 2;
    }
    Clause **p = (Clause **)sat_realloc(s, v->data,
                                        (size_t)cap * sizeof(Clause *));
    if (!p) return 0;
    v->data = p;
    v->cap = cap;
    return 1;
}

static int clausevec_push(Sat *s, ClauseVec *v, Clause *c)
{
    if (!clausevec_reserve(s, v, v->size + 1)) return 0;
    v->data[v->size++] = c;
    return 1;
}

static int lit_var(int lit)
{
    return (lit > 0 ? lit : -lit) - 1;
}

static int lit_index(int lit)
{
    int v = lit_var(lit);
    return 2 * v + (lit < 0);
}

static int decision_level(const Sat *s)
{
    return s->trail_lim.size;
}

static int lit_value(const Sat *s, int lit)
{
    int a = s->assigns[lit_var(lit)];
    if (a == 0) return 0;
    return lit > 0 ? a : -a;
}

static Clause *clause_new(Sat *s, const int *lits, int n, int learnt)
{
    size_t bytes = sizeof(Clause) + (size_t)n * sizeof(int);
    Clause *c = (Clause *)malloc(bytes);
    if (!c) {
        s->oom = 1;
        return NULL;
    }
    c->size = n;
    c->learnt = learnt ? 1u : 0u;
    c->activity = 0.0;
    if (n > 0) memcpy(c->lits, lits, (size_t)n * sizeof(int));
    return c;
}

static int attach_clause(Sat *s, Clause *c)
{
    assert(c->size >= 2);
    return clausevec_push(s, &s->watches[lit_index(-c->lits[0])], c) &&
           clausevec_push(s, &s->watches[lit_index(-c->lits[1])], c);
}

static int enqueue(Sat *s, int lit, Clause *reason)
{
    int v = lit_var(lit);
    int val = lit_value(s, lit);
    if (val > 0) return 1;
    if (val < 0) return 0;

    s->assigns[v] = (int8_t)(lit > 0 ? 1 : -1);
    s->phase[v] = s->assigns[v];
    s->level[v] = decision_level(s);
    s->reason[v] = reason;
    return intvec_push(s, &s->trail, lit);
}

/* Returns a conflicting clause, or NULL if propagation succeeds. */
static Clause *propagate(Sat *s)
{
    while (s->qhead < s->trail.size) {
        int p = s->trail.data[s->qhead++];
        ClauseVec *ws = &s->watches[lit_index(p)];
        int out = 0;

        for (int i = 0; i < ws->size; ++i) {
            Clause *c = ws->data[i];
            int false_lit = -p;

            if (c->lits[0] == false_lit) {
                int t = c->lits[0];
                c->lits[0] = c->lits[1];
                c->lits[1] = t;
            }
            assert(c->lits[1] == false_lit);

            int other = c->lits[0];
            if (lit_value(s, other) > 0) {
                ws->data[out++] = c;
                continue;
            }

            int k;
            for (k = 2; k < c->size; ++k) {
                if (lit_value(s, c->lits[k]) >= 0) {
                    int new_watch = c->lits[k];
                    c->lits[k] = c->lits[1];
                    c->lits[1] = new_watch;
                    if (!clausevec_push(s,
                            &s->watches[lit_index(-new_watch)], c)) {
                        ws->data[out++] = c;
                        ws->size = out;
                        return c; /* caller will convert OOM to ERROR */
                    }
                    break;
                }
            }

            if (k < c->size) continue;

            ws->data[out++] = c;
            if (lit_value(s, other) < 0) {
                while (++i < ws->size) ws->data[out++] = ws->data[i];
                ws->size = out;
                return c;
            }
            if (!enqueue(s, other, c)) {
                while (++i < ws->size) ws->data[out++] = ws->data[i];
                ws->size = out;
                return c;
            }
        }
        ws->size = out;
    }
    return NULL;
}

static void var_bump_activity(Sat *s, int v)
{
    s->activity[v] += s->var_inc;
    if (s->activity[v] > 1e100) {
        for (int i = 0; i < s->nvars; ++i) s->activity[i] *= 1e-100;
        s->var_inc *= 1e-100;
    }
}

static void var_decay_activity(Sat *s)
{
    s->var_inc *= (1.0 / s->var_decay);
}

static void cancel_until(Sat *s, int level)
{
    int cur = decision_level(s);
    if (cur <= level) return;

    int target = s->trail_lim.data[level];
    for (int i = s->trail.size - 1; i >= target; --i) {
        int v = lit_var(s->trail.data[i]);
        s->assigns[v] = 0;
        s->level[v] = 0;
        s->reason[v] = NULL;
    }
    s->trail.size = target;
    s->trail_lim.size = level;
    if (s->qhead > target) s->qhead = target;
}

/* First-UIP analysis. learnt[0] is the asserting literal. */
static int analyze(Sat *s, Clause *conflict, IntVec *learnt,
                   int *backtrack_level)
{
    learnt->size = 0;
    if (!intvec_push(s, learnt, 0)) return 0;

    int path_count = 0;
    int p = 0;
    int trail_i = s->trail.size - 1;
    Clause *c = conflict;

    do {
        assert(c != NULL);
        for (int j = 0; j < c->size; ++j) {
            int q = c->lits[j];
            int v = lit_var(q);
            if (p != 0 && v == lit_var(p)) continue;
            if (s->seen[v] || s->level[v] == 0) continue;

            s->seen[v] = 1;
            var_bump_activity(s, v);
            if (s->level[v] == decision_level(s)) {
                ++path_count;
            } else {
                if (!intvec_push(s, learnt, q)) return 0;
            }
        }

        while (trail_i >= 0 && !s->seen[lit_var(s->trail.data[trail_i])])
            --trail_i;
        assert(trail_i >= 0);

        p = s->trail.data[trail_i--];
        c = s->reason[lit_var(p)];
        s->seen[lit_var(p)] = 0;
        --path_count;
    } while (path_count > 0);

    learnt->data[0] = -p;

    int bt = 0;
    int max_i = 1;
    for (int i = 1; i < learnt->size; ++i) {
        int lv = s->level[lit_var(learnt->data[i])];
        if (lv > bt) {
            bt = lv;
            max_i = i;
        }
    }

    /* Put the highest-level non-asserting literal in watch position 1. */
    if (learnt->size > 1 && max_i != 1) {
        int t = learnt->data[1];
        learnt->data[1] = learnt->data[max_i];
        learnt->data[max_i] = t;
    }

    for (int i = 1; i < learnt->size; ++i)
        s->seen[lit_var(learnt->data[i])] = 0;

    *backtrack_level = bt;
    return 1;
}

static int pick_branch_lit(const Sat *s)
{
    int best = -1;
    double best_activity = -1.0;
    for (int v = 0; v < s->nvars; ++v) {
        if (s->assigns[v] == 0 && s->activity[v] > best_activity) {
            best_activity = s->activity[v];
            best = v;
        }
    }
    if (best < 0) return 0;
    return s->phase[best] >= 0 ? SAT_POS(best) : SAT_NEG(best);
}

static int ensure_var_capacity(Sat *s, int need)
{
    if (need <= s->vars_cap) return 1;
    int cap = s->vars_cap ? s->vars_cap : 8;
    while (cap < need) {
        if (cap > INT32_MAX / 2) { s->oom = 1; return 0; }
        cap *= 2;
    }

#define GROW_ARRAY(field, type) do { \
        type *p__ = (type *)sat_realloc(s, s->field, (size_t)cap * sizeof(type)); \
        if (!p__) return 0; \
        s->field = p__; \
    } while (0)

    int old = s->vars_cap;
    GROW_ARRAY(assigns, int8_t);
    GROW_ARRAY(phase, int8_t);
    GROW_ARRAY(level, int);
    GROW_ARRAY(reason, Clause *);
    GROW_ARRAY(activity, double);
    GROW_ARRAY(seen, uint8_t);

#undef GROW_ARRAY

    memset(s->assigns + old, 0, (size_t)(cap - old) * sizeof(int8_t));
    memset(s->level + old, 0, (size_t)(cap - old) * sizeof(int));
    memset(s->reason + old, 0, (size_t)(cap - old) * sizeof(Clause *));
    memset(s->activity + old, 0, (size_t)(cap - old) * sizeof(double));
    memset(s->seen + old, 0, (size_t)(cap - old) * sizeof(uint8_t));
    for (int i = old; i < cap; ++i) s->phase[i] = 1;

    int watch_need = 2 * cap;
    ClauseVec *w = (ClauseVec *)sat_realloc(
        s, s->watches, (size_t)watch_need * sizeof(ClauseVec));
    if (!w) return 0;
    s->watches = w;
    for (int i = s->watches_cap; i < watch_need; ++i) {
        s->watches[i].data = NULL;
        s->watches[i].size = 0;
        s->watches[i].cap = 0;
    }
    s->watches_cap = watch_need;
    s->vars_cap = cap;
    return 1;
}

Sat *sat_create(void)
{
    Sat *s = (Sat *)calloc(1, sizeof(Sat));
    if (!s) return NULL;
    s->var_inc = 1.0;
    s->var_decay = 0.95;
    s->ok = 1;
    s->restart_limit = 100;
    s->restart_growth = 1.5;
    return s;
}


/*
 * Return the clause in dst corresponding to p in src.
 * This is linear in the number of clauses. Cloning is normally infrequent,
 * so this keeps the implementation simple and avoids a temporary hash table.
 */
static Clause *mapped_clause(const Sat *src, const Sat *dst, const Clause *p)
{
    if (!p) return NULL;

    for (int i = 0; i < src->clauses.size; ++i) {
        if (src->clauses.data[i] == p) return dst->clauses.data[i];
    }
    for (int i = 0; i < src->learnts.size; ++i) {
        if (src->learnts.data[i] == p) return dst->learnts.data[i];
    }
    return NULL;
}

static Clause *clone_clause(Sat *dst, const Clause *src)
{
    Clause *c = clause_new(dst, src->lits, src->size, src->learnt);
    if (c) c->activity = src->activity;
    return c;
}

/*
 * Deep-copy the complete solver state.
 *
 * This copies assignments, trail, learned clauses, activities, restart state,
 * and rebuilds every internal pointer so that the clone owns all of its data.
 * The source must not currently be inside sat_solve().
 */
Sat *sat_clone(const Sat *src)
{
    if (!src || src->solving || src->oom) return NULL;

    Sat *dst = sat_create();
    if (!dst) return NULL;

    if (!ensure_var_capacity(dst, src->nvars)) goto fail;
    dst->nvars = src->nvars;

    if (src->nvars > 0) {
        size_t n = (size_t)src->nvars;
        memcpy(dst->assigns, src->assigns, n * sizeof(int8_t));
        memcpy(dst->phase, src->phase, n * sizeof(int8_t));
        memcpy(dst->level, src->level, n * sizeof(int));
        memcpy(dst->activity, src->activity, n * sizeof(double));
        memcpy(dst->seen, src->seen, n * sizeof(uint8_t));
        memset(dst->reason, 0, n * sizeof(Clause *));
    }

    if (!intvec_reserve(dst, &dst->trail, src->trail.size)) goto fail;
    if (src->trail.size > 0) {
        memcpy(dst->trail.data, src->trail.data,
               (size_t)src->trail.size * sizeof(int));
    }
    dst->trail.size = src->trail.size;

    if (!intvec_reserve(dst, &dst->trail_lim, src->trail_lim.size)) goto fail;
    if (src->trail_lim.size > 0) {
        memcpy(dst->trail_lim.data, src->trail_lim.data,
               (size_t)src->trail_lim.size * sizeof(int));
    }
    dst->trail_lim.size = src->trail_lim.size;

    for (int i = 0; i < src->clauses.size; ++i) {
        Clause *c = clone_clause(dst, src->clauses.data[i]);
        if (!c || !clausevec_push(dst, &dst->clauses, c)) {
            if (c) free(c);
            goto fail;
        }
    }

    for (int i = 0; i < src->learnts.size; ++i) {
        Clause *c = clone_clause(dst, src->learnts.data[i]);
        if (!c || !clausevec_push(dst, &dst->learnts, c)) {
            if (c) free(c);
            goto fail;
        }
    }

    /* Rebuild watch lists from the cloned clauses' current watch positions. */
    for (int i = 0; i < dst->clauses.size; ++i) {
        Clause *c = dst->clauses.data[i];
        if (c->size >= 2 && !attach_clause(dst, c)) goto fail;
    }
    for (int i = 0; i < dst->learnts.size; ++i) {
        Clause *c = dst->learnts.data[i];
        if (c->size >= 2 && !attach_clause(dst, c)) goto fail;
    }

    /* Translate reason pointers from source clauses to cloned clauses. */
    for (int v = 0; v < src->nvars; ++v) {
        if (src->reason[v]) {
            dst->reason[v] = mapped_clause(src, dst, src->reason[v]);
            if (!dst->reason[v]) goto fail;
        }
    }

    dst->qhead = src->qhead;
    dst->var_inc = src->var_inc;
    dst->var_decay = src->var_decay;
    dst->ok = src->ok;
    dst->solving = 0;
    dst->oom = 0;
    dst->conflicts = src->conflicts;
    dst->restart_limit = src->restart_limit;
    dst->restart_growth = src->restart_growth;
    return dst;

fail:
    sat_destroy(dst);
    return NULL;
}

/*
 * Copy only the original CNF into a fresh, independent solver.
 * Learned clauses, decisions, activities, and the current model are omitted.
 * This is the safer operation when the clone will receive additional clauses.
 */
Sat *sat_clone_formula(const Sat *src)
{
    if (!src || src->solving || src->oom) return NULL;

    Sat *dst = sat_create();
    if (!dst) return NULL;

    for (int v = 0; v < src->nvars; ++v) {
        if (sat_new_var(dst) < 0) goto fail;
    }

    for (int i = 0; i < src->clauses.size; ++i) {
        const Clause *c = src->clauses.data[i];
        if (!sat_add_clause(dst, c->lits, c->size)) {
            /* A false return may simply mean that the copied CNF is UNSAT. */
            if (dst->oom) goto fail;
            break;
        }
    }

    if (!src->ok) dst->ok = 0;
    return dst;

fail:
    sat_destroy(dst);
    return NULL;
}

void sat_destroy(Sat *s)
{
    if (!s) return;

    for (int i = 0; i < s->clauses.size; ++i) free(s->clauses.data[i]);
    for (int i = 0; i < s->learnts.size; ++i) free(s->learnts.data[i]);
    for (int i = 0; i < s->watches_cap; ++i) free(s->watches[i].data);

    free(s->clauses.data);
    free(s->learnts.data);
    free(s->watches);
    free(s->trail.data);
    free(s->trail_lim.data);

    free(s->assigns);
    free(s->phase);
    free(s->level);
    free(s->reason);
    free(s->activity);
    free(s->seen);
    free(s);
}

int sat_new_var(Sat *s)
{
    if (!s || s->solving || s->oom) return -1;
    if (!ensure_var_capacity(s, s->nvars + 1)) return -1;
    return s->nvars++;
}

int sat_add_clause(Sat *s, const int *lits, int n)
{
    if (!s || s->solving || s->oom || n < 0 || (n > 0 && !lits)) return 0;
    if (!s->ok) return 0;

    cancel_until(s, 0);

    IntVec tmp = {0};
    if (!intvec_reserve(s, &tmp, n)) {
        free(tmp.data);
        return 0;
    }

    for (int i = 0; i < n; ++i) {
        int lit = lits[i];
        if (lit == 0) { free(tmp.data); return 0; }
        int v = lit_var(lit);
        if (v < 0 || v >= s->nvars) { free(tmp.data); return 0; }

        int val = lit_value(s, lit);
        if (val > 0) { free(tmp.data); return 1; }
        if (val < 0) continue;

        int duplicate = 0;
        for (int j = 0; j < tmp.size; ++j) {
            if (tmp.data[j] == lit) { duplicate = 1; break; }
            if (tmp.data[j] == -lit) { free(tmp.data); return 1; }
        }
        if (!duplicate && !intvec_push(s, &tmp, lit)) {
            free(tmp.data);
            return 0;
        }
    }

    if (tmp.size == 0) {
        s->ok = 0;
        free(tmp.data);
        return 0;
    }

    Clause *c = clause_new(s, tmp.data, tmp.size, 0);
    free(tmp.data);
    if (!c) return 0;

    if (!clausevec_push(s, &s->clauses, c)) {
        free(c);
        return 0;
    }

    if (c->size == 1) {
        if (!enqueue(s, c->lits[0], c)) {
            s->ok = 0;
            return 0;
        }
        Clause *conflict = propagate(s);
        if (s->oom || conflict) {
            s->ok = 0;
            return 0;
        }
    } else if (!attach_clause(s, c)) {
        return 0;
    }

    return 1;
}

SatResult sat_solve(Sat *s)
{
    if (!s || s->oom) return SAT_RESULT_ERROR;
    if (!s->ok) return SAT_RESULT_UNSAT;
    if (s->solving) return SAT_RESULT_ERROR;
    s->solving = 1;

    Clause *root_conflict = propagate(s);
    if (s->oom) { s->solving = 0; return SAT_RESULT_ERROR; }
    if (root_conflict) { s->ok = 0; s->solving = 0; return SAT_RESULT_UNSAT; }

    IntVec learnt = {0};
    int conflicts_since_restart = 0;

    for (;;) {
        Clause *conflict = propagate(s);
        if (s->oom) {
            free(learnt.data);
            s->solving = 0;
            return SAT_RESULT_ERROR;
        }

        if (conflict) {
            ++s->conflicts;
            ++conflicts_since_restart;

            if (decision_level(s) == 0) {
                s->ok = 0;
                free(learnt.data);
                s->solving = 0;
                return SAT_RESULT_UNSAT;
            }

            int backtrack_level = 0;
            if (!analyze(s, conflict, &learnt, &backtrack_level)) {
                free(learnt.data);
                s->solving = 0;
                return SAT_RESULT_ERROR;
            }

            cancel_until(s, backtrack_level);

            Clause *c = clause_new(s, learnt.data, learnt.size, 1);
            if (!c || !clausevec_push(s, &s->learnts, c)) {
                if (c) free(c);
                free(learnt.data);
                s->solving = 0;
                return SAT_RESULT_ERROR;
            }
            if (c->size >= 2 && !attach_clause(s, c)) {
                free(learnt.data);
                s->solving = 0;
                return SAT_RESULT_ERROR;
            }
            if (!enqueue(s, c->lits[0], c)) {
                free(learnt.data);
                s->ok = 0;
                s->solving = 0;
                return SAT_RESULT_UNSAT;
            }

            var_decay_activity(s);

            if (conflicts_since_restart >= s->restart_limit) {
                cancel_until(s, 0);
                conflicts_since_restart = 0;
                int next = (int)(s->restart_limit * s->restart_growth);
                s->restart_limit = next > s->restart_limit ? next : s->restart_limit + 1;
            }
        } else {
            int decision = pick_branch_lit(s);
            if (decision == 0) {
                free(learnt.data);
                s->solving = 0;
                return SAT_RESULT_SAT;
            }

            if (!intvec_push(s, &s->trail_lim, s->trail.size) ||
                !enqueue(s, decision, NULL)) {
                free(learnt.data);
                s->solving = 0;
                return SAT_RESULT_ERROR;
            }
        }
    }
}

int sat_value(const Sat *s, int var)
{
    if (!s || var < 0 || var >= s->nvars) return 0;
    return s->assigns[var];
}

#ifdef __cplusplus
}
#endif

/*
Example:

#include <stdio.h>
#include "cdcl_sat.c"

int main(void)
{
    Sat *s = sat_create();
    int x = sat_new_var(s);
    int y = sat_new_var(s);

    int c1[] = { SAT_POS(x), SAT_POS(y) };
    int c2[] = { SAT_NEG(x), SAT_POS(y) };
    int c3[] = { SAT_POS(x), SAT_NEG(y) };

    sat_add_clause(s, c1, 2);
    sat_add_clause(s, c2, 2);
    sat_add_clause(s, c3, 2);

    if (sat_solve(s) == SAT_RESULT_SAT) {
        printf("x=%d y=%d\n", sat_value(s, x), sat_value(s, y));
    }

    sat_destroy(s);
    return 0;
}
*/
