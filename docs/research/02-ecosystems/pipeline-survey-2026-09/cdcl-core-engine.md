# The CDCL engine: heuristics and clause-database policy

Read-only survey lane `research-cdcl-core`, 2026-09-08. Subject: the search
*quality* half of `crates/axeyum-cnf/src/proof_sat.rs` — decision heuristics,
clause-database management, restarts, LBD, phases, and the propagation loop —
measured against Kissat 4.0.4 and CaDiCaL (master `c6073042`, 2026-07-19), both
in `references/` (gitignored; `scripts/fetch-references.sh`).

**Claim tags.** `[C]` read from source, cited `file:line`. `[P]` from a paper.
`[I]` my inference. Constants are quoted from source; where I did not verify
something I say so.

**Framing note for the reader.** The premise of this lane is that our raw
propagation throughput is within ~40% of Kissat's but we need ~2.5x more
conflicts for the same progress. I did not re-measure that; I take it as the
question. Everything below is about what decides *which* conflicts happen.

---

## Part 0 — The one-paragraph answer

Our engine is a well-built **2010-era MiniSat/Glucose hybrid**: one EVSIDS heap
for the whole search, Luby restarts at a 100-conflict base unit, and a clause
database reduced by **clause activity** with a permanent `LBD <= 2` exemption.
Kissat and CaDiCaL are a different machine: they run **two alternating search
modes** with **two different decision heuristics**, restart **~100x more often**
in the focused mode, and manage clauses by a **three-tier LBD scheme with a
per-clause `used` counter and dynamically recomputed tier boundaries** — where
the boundaries are read off the *observed glue distribution of clauses that
actually got resolved*, not hard-coded. Each of those three is a separable
policy object. The clause-DB tiering is the single largest gap and also the one
that needs the least new machinery.

---

## Part 1 — What the references actually do

### 1.1 Decision heuristics: two of them, chosen by mode

Kissat carries **both** a VMTF queue and an EVSIDS heap for the entire search
and picks by mode at every decision:

```c
// references/kissat/src/decide.c:126-153
unsigned kissat_next_decision_variable (kissat *solver) {
  unsigned res = next_random_decision (solver);
  if (res == INVALID_IDX) {
    if (solver->stable) {
      res = largest_score_unassigned_variable (solver);   // EVSIDS heap
      INC (score_decisions);
    } else {
      res = last_enqueued_unassigned_variable (solver);   // VMTF queue
      INC (queue_decisions);
    }
  }
  ...
}
```

`[C]` Bumping is likewise mode-split — one call site, two entirely different
data structures:

```c
// references/kissat/src/bump.c:103-112
void kissat_bump_analyzed (kissat *solver) {
  const size_t bumped = SIZE_STACK (solver->analyzed);
  if (!solver->stable)
    move_analyzed_variables_to_front_of_queue (solver);  // VMTF
  else
    bump_analyzed_variable_scores (solver);              // EVSIDS
  ...
}
```

`[C]` The VMTF bump sorts the analyzed set **by existing queue stamp** before
moving to front (`bump.c:81-101`), using quicksort below 32 elements and radix
sort above (`bump.c:15-25`). That ordering is load-bearing: the POS'20 paper
says VSIDS at decay 0.5 "is a poor man's version of VMTF: it is as agile as VMTF
but does not keep the order of literals when bumping several literals at once,
which is important for the performance of VMTF" `[P]`.

`[C]` EVSIDS constants, Kissat:

| Thing | Value | Source |
| --- | --- | --- |
| `decay` | 50 per mille | `options.h:34` |
| increment update | `scinc *= 1/(1 - 0.05)` = 1.0526 per conflict | `bump.c:43-53` |
| rescale trigger | `MAX_SCORE` = `1e150` | `bump.h:14` |
| rescale factor | `1/max(max_score_on_heap, scinc)` | `bump.c:28-41` |

`[C]` CaDiCaL is numerically identical by a different spelling: `scorefactor`
= 950 per mille, `f = 1e3/950` = 1.0526 (`analyze.cpp:135-137`,
`options.hpp:203`), EVSIDS limit `1e150` (`analyze.cpp:77`). CaDiCaL's
`use_scores()` is the same stable/focused switch (`decide.cpp:113-116`).

**Reason-side bumping.** Both bump not only the literals resolved in analysis
but the literals in the *reasons* of the learned clause's literals:

```c
// references/kissat/src/analyze.c:169-212  (analyze_reason_side_literals)
  const double decision_rate = AVERAGE (decision_rate);
  const int decision_rate_limit = GET_OPTION (bumpreasonsrate);   // 10
  if (decision_rate >= decision_rate_limit) return;               // too agile: skip
  const size_t saved = SIZE_STACK (solver->analyzed);
  const size_t limit = GET_OPTION (bumpreasonslimit) * saved;     // 10 * saved
```

`[C]` Options: `bumpreasons` 1, `bumpreasonslimit` 10, `bumpreasonsrate` 10
(`options.h:17-19`). If the extra literals overrun `limit`, the whole extension
is rolled back and a *delay* counter is bumped so it is skipped for a while
(`analyze.c:200-211`). CaDiCaL: `bumpreason` 1, `bumpreasondepth` 1,
`bumpreasonlimit` 10, `bumpreasonrate` 100 (`options.hpp:39-42`).

`[P]` The POS'20 paper is unusually direct about why this matters: *"implementing
the alternation of stable and focused mode was easy, but performance
significantly dropped to the point that our implementation became much worse
than the original implementation of Glucose. We resolved that issue by bumping
not only the resolved literals and the literals in the learned clause but also
the literals in the reasons of the literals in the learned clause, following the
idea pioneered by MapleSAT. Experiments with CaDiCaL confirmed the importance of
this heuristic."* So reason-side bumping is a **prerequisite** for mode
alternation paying off, not an independent tweak `[P]`.

**Random decision sequences.** Kissat interleaves short bursts of purely random
decisions: length `randeclength * log10(count+9)` conflicts, scheduled at
`randecint` = 500 base interval scaled by `LOGN` (`decide.c:57-124`,
`options.h:103-108`). Default **on in focused mode, off in stable**
(`randecfocused` 1, `randecstable` 0). `[C]`

**Tie-breaking.** Kissat's heap comparison is on the `double` score with the
heap's own internal position as the implicit tiebreak (`inlineheap.h`, not read
in detail — did not verify the exact tiebreak). VMTF's tiebreak is the enqueue
stamp, i.e. recency. `[C]/[I]`

**LRB / CHB.** Neither Kissat 4.0.4 nor this CaDiCaL implements LRB or CHB; the
POS'20 paper cites LRB (MapleSAT) only as related work and Biere's line has
stayed on VMTF+EVSIDS `[C]/[P]`. I did not survey MapleSAT/Cadical-LRB sources —
**did not verify** LRB's exact update rule from primary source, so I am not
quoting one.

### 1.2 Mode switching (stable vs focused)

This is the spine everything else hangs off.

```c
// references/kissat/src/mode.c:186-199
bool kissat_switching_search_mode (kissat *solver) {
  if (GET_OPTION (stable) != 1) return false;
  if (limits->mode.count & 1)
    return statistics->search_ticks >= limits->mode.ticks;
  else
    return statistics->conflicts >= limits->mode.conflicts;
}
```

`[C]` The two modes are measured in **different units**, deliberately:

- **Focused phases are measured in conflicts.** `mode.conflicts = conflicts +
  modeint * nlogpown(count, 4)` where `count = (switched+1)/2` and
  `nlogpown(c,4) = c * log10(c+9)^4` (`mode.c:87-100`, `kimits.c:27-37`).
  `modeinit` = `modeint` = 1e3 (`options.h:84-85`). So the first focused phase
  is 1000 conflicts; the n-th is `1000 * n * log10(n+9)^4`.
- **Stable phases are measured in ticks** (estimated cache lines touched during
  propagation), and get exactly as many ticks as the *preceding focused phase
  spent*: `mode.ticks = search_ticks + delta_ticks` where `delta_ticks` is the
  ticks consumed by the phase just ending (`mode.c:77-86`, `mode.c:112-116`).

`[P]` The paper explains the tick unit: *"Kissat determines the time spent in
focused and stable mode by estimating the number of memory accesses (instead of
measuring the time directly in order to be deterministic across runs)."* This
matters for us — **it is a determinism-preserving way to budget in a wall-clock-
like unit**, which our determinism promise otherwise forbids `[P]/[I]`.

`[C]` Ticks are counted in the propagation loop itself:

```c
// references/kissat/src/proplit.h:63-64
  const size_t size_watches = SIZE_WATCHES (*watches);
  uint64_t ticks = 1 + kissat_cache_lines (size_watches, sizeof (watch));
```
and incremented once per large-clause deref, per assignment, and per watch
relocation (`proplit.h:92, 98, 148, 174`).

`[C]` Mode transitions also reset state: switching to focused resets the VMTF
queue search pointer and recomputes the focused restart limit
(`mode.c:164-165`); switching to stable re-inits the reluctant-doubling counter
and pushes every active variable back onto the score heap (`mode.c:182-183`,
`bump.c:114-120`). Averages are re-initialized per mode — `AVERAGES` is
`solver->averages[solver->stable]`, i.e. **two independent sets of EMAs**
(`averages.h:24`).

`[C]` CaDiCaL's equivalent (`restart.cpp:18-85`) starts on conflicts
(`stabilizeinit` = 1e3) then switches to ticks, with `next_delta_ticks =
inc.stabilize * stabphases^2` (`restart.cpp:59-61`, `options.hpp:212`). Note the
different growth law: CaDiCaL `n^2`, Kissat `n log^4 n`. Neither is derived;
both are tuned `[I]`.

### 1.3 Clause database — the three tiers

**The tier boundaries are not constants.** Kissat 4.0.4 and current CaDiCaL both
compute them from the observed glue distribution of *used* clauses:

```c
// references/kissat/src/tiers.c:6-49
static void compute_tier_limits (kissat *solver, bool stable,
                                 unsigned *tier1_ptr, unsigned *tier2_ptr) {
  uint64_t *used_stats = statistics->used[stable].glue;
  uint64_t total_used = 0;
  for (unsigned glue = 0; glue <= MAX_GLUE_USED; glue++)
    total_used += used_stats[glue];
  ...
  uint64_t accumulated_tier1_limit = total_used * TIER1RELATIVE;   // 0.50
  uint64_t accumulated_tier2_limit = total_used * TIER2RELATIVE;   // 0.90
  // tier1 := smallest glue whose cumulative used-count reaches 50%
  // tier2 := smallest glue whose cumulative used-count reaches 90%
```

`[C]` `TIER1RELATIVE` = `tier1relative`/1000 = 0.5, `TIER2RELATIVE` = 0.9
(`options.h:152, 154, 221-222`). Fallback when nothing has been used yet:
`tier1` = 2, `tier2` = 6 (`options.h:151, 153`; `tiers.c:38-40`;
`search.c:27-43`). Limits are kept **per mode**: `solver->tier1[stable]`
(`tiers.c:51-61`).

`[P]` The SAT Competition 2024 solver description states the rationale
verbatim: *"we realized that the average glue (LBD) varies dramatically between
different formulas and actually also on the same formula between running in an
interleaved fashion in stable and focused mode... Our dynamic glue limit for
tier 1 is computed as the glue of 50% of the used clauses, i.e., a clause with
glue up to that limit has a 50% chance of being used. The limit for tier 2 is
the glue where 90% of the used clauses is reached, i.e., clauses with glue above
that limit have a chance of less than 10% of being used. Typical hard coded
limits are glue 2 and 6 for tier 1 and tier 2 respectively, which we also use
initially."* It also records a caveat worth copying: *"we actually only use
those limits computed during focused mode, even in stable mode"* — see
`focusedtiers` = 1 (`options.h:69`) and `vivifyfocusedtiers` = 1
(`options.h:162`) `[P]/[C]`.

**Recomputation schedule.** Kissat: a doubling conflict interval starting at 2,
capped at 2^16:

```c
// references/kissat/src/analyze.c:519-525
static void update_tier_limits (kissat *solver) {
  INC (retiered);
  kissat_compute_and_set_tier_limits (solver);
  if (solver->limits.glue.interval < (1u << 16))
    solver->limits.glue.interval *= 2;
  solver->limits.glue.conflicts = CONFLICTS + solver->limits.glue.interval;
}
```
`[C]` (also recomputed at every reduce: `reduce.c:159`). CaDiCaL uses the same
shape: `delta = tierecomputed >= 16 ? 1<<16 : (1 << tierecomputed)`
(`tier.cpp:12-14`), first at conflict 5000 (`internal.cpp:446`), with floors
`tier1minglue`/`tier2minglue` and the invariant `tier2 > tier1`
(`tier.cpp:63-75`), and percentile options `tier1limit` = 50, `tier2limit` = 90
(`options.hpp:246-249`).

**The `used` counter — the "second chance" mechanism.** Every clause carries a
5-bit `used` field, `max_used` = 31 in both solvers (`kissat/src/clause.h:14,17`;
`cadical/src/internal.hpp:317-318`).

- Set to `max_used` when the clause is **learned** (`kissat/src/learn.c:110`)
  and when it is **resolved during conflict analysis**
  (`kissat/src/deduce.c:18`; `cadical/src/analyze.cpp:227`).
- **Decremented once per reduce round** (`kissat/src/reduce.c:70-72`;
  `cadical/src/reduce.cpp:109-111`).

The keep rules, which are the actual tier semantics:

```c
// references/kissat/src/reduce.c:65-87   (identical logic in cadical/src/reduce.cpp:102-123)
  for (clause *c = start; c != end; c = kissat_next_clause (c)) {
    if (!c->redundant) continue;         // irredundant: never a candidate
    if (c->garbage)    continue;
    const unsigned used = c->used;
    if (used) c->used = used - 1;
    if (c->reason)     continue;         // locked
    const unsigned glue = c->glue;
    if (glue <= tier1 && used)                  continue;  // tier1: kept if used at all
    if (glue <= tier2 && used >= MAX_USED - 1)  continue;  // tier2: one round's grace
    ... push as reduction candidate ...
  }
```

`[C]` Read carefully, this is a **three-tier lifetime policy**:

- **tier1** (`glue <= tier1`): survives as long as it is touched at least once
  per reduce round. Effectively permanent while useful, deleted the round after
  it goes cold.
- **tier2** (`tier1 < glue <= tier2`): survives only if `used >= 30`, i.e. only
  if it was resolved **since the last reduce round** (`max_used` was just
  written and one decrement has happened). One round of grace, then a candidate.
- **tier3** (`glue > tier2`): always a candidate.

Note there is no separate list per tier — the tier is a *predicate on glue*
evaluated at reduce time against the current dynamic boundary. That is why
promotion is cheap `[I]`.

**Promotion / demotion.** Glue is recomputed whenever a clause is resolved and
the clause is *promoted* if the new glue is smaller. There is no demotion:

```c
// references/kissat/src/deduce.c:6-12
static inline void recompute_and_promote (kissat *solver, clause *c) {
  const unsigned old_glue = c->glue;
  const unsigned new_glue = kissat_recompute_glue (solver, c, old_glue);
  if (new_glue < old_glue)
    kissat_promote_clause (solver, c, new_glue);
}
```
`[C]` `kissat_promote_clause` only sets `c->glue = new_glue` and counts which
tier transition happened (`promote.c:5-42`) — the tier is derived, never stored.

**How much is deleted per round.** Kissat ramps the fraction up over the run:

```c
// references/kissat/src/reduce.c:102-114
  const double high = GET_OPTION (reducehigh) * 0.1;   // 90.0
  const double low  = GET_OPTION (reducelow)  * 0.1;   // 50.0
  percent = high - (high - low) / log10 (statistics->reductions + 9);
  const double fraction = percent / 100.0;
  size_t target = size * fraction;
```
`[C]` `reducelow` = 500, `reducehigh` = 900 per mille (`options.h:110, 113`).
Evaluated: reduction 1 -> 50%, reduction 91 -> 70%, reduction 991 -> ~76.7%,
asymptotically 90%. Kissat's NEWS calls this *"dynamically increased
reduced-clauses fraction (60% - 90%)"* for 4.0.0 — the shipped constants are
50/90 `[C]`. CaDiCaL uses a flat `reducetarget` = 75% (`reduce.cpp:126`,
`options.hpp:183`).

**Deletion ranking.** Kissat packs a 64-bit key and radix-sorts:

```c
// references/kissat/src/reduce.c:82-85
    const uint64_t negative_size = ~c->size;
    const uint64_t negative_glue = ~c->glue;
    red.rank = negative_size | (negative_glue << 32);
```
`[C]` Ascending rank = descending glue, then descending size. Worst-first.
CaDiCaL sorts the same order with a `stable_sort`, and comments that stability
means *"more recently learned clauses are kept if they otherwise have the same
glue and size"* (`reduce.cpp:74-82, 88-94, 125`). **Neither solver ranks by
clause activity.** `[C]`

**Reduce interval.** Kissat: `UPDATE_CONFLICT_LIMIT(reduce, reductions, SQRT,
false)` (`reduce.c:193`) expands to `limits->reduce.conflicts = conflicts +
reduceint * sqrt(reductions)` (`kimits.h:112-124`), with `reduceinit` =
`reduceint` = 1e3 (`options.h:111-112`). CaDiCaL: `delta = reduceint *
sqrt(conflicts)` with `reduceint` = 25, `reduceinit` = 300, plus a
`log10(irredundant/1e4)` widening for formulas over 1e5 irredundant clauses
(`reduce.cpp:234-254`, `options.hpp:180-183`).

**Sweep start.** Kissat remembers `first_reducible`, the arena offset of the
first redundant clause, and only sweeps from there (`reduce.c:37-61, 161`). The
reduce round is followed by an arena compaction (`kissat_sparse_collect`,
`reduce.c:183`). `[C]`

### 1.4 Restarts

**Focused mode — Glucose EMA rule, with a tiny base interval.**

```c
// references/kissat/src/restart.c:14-37
bool kissat_restarting (kissat *solver) {
  if (!solver->level) return false;
  if (CONFLICTS < solver->limits.restart.conflicts) return false;
  if (solver->stable) return kissat_reluctant_triggered (&solver->reluctant);
  const double fast = AVERAGE (fast_glue);
  const double slow = AVERAGE (slow_glue);
  const double margin = (100.0 + GET_OPTION (restartmargin)) / 100.0;   // 1.10
  return (margin * slow <= fast);
}
```

```c
// references/kissat/src/restart.c:39-51
void kissat_update_focused_restart_limit (kissat *solver) {
  uint64_t delta = GET_OPTION (restartint);            // 1
  if (restarts) delta += kissat_logn (restarts) - 1;   // log10(restarts + 9)
  limits->restart.conflicts = CONFLICTS + delta;
}
```

`[C]` `restartint` default is **1** (`options.h:180`; `RESTARTINT_SAT` = 50 in
the `--sat` build). `restartmargin` = 10% (`options.h:126`). CaDiCaL:
`restartint` = 2, `restartmarginfocused` = 10, `restartmarginstable` = 25
(`options.hpp:195-197`).

**Stable mode — reluctant doubling (Luby), ticked per learned clause.**

```c
// references/kissat/src/learn.c:118-131
void kissat_update_learned (kissat *solver, unsigned glue, unsigned size) {
  if (solver->stable)
    kissat_tick_reluctant (&solver->reluctant);
  UPDATE_AVERAGE (fast_glue, glue);
  UPDATE_AVERAGE (slow_glue, glue);
}
```
`[C]` `reluctantint` = 1024, `reluctantlim` = 2^20 (`options.h:115-116`); the
u/v doubling is `reluctant.c:20-55`. `[P]` The paper: *"Since 2019, Luby
restarts are used with a relatively large base interval (1 024 compared to
MiniSAT's default value of 100)"*.

**EMA formula.** Bias-corrected, with `alpha = 1/window`:

```c
// references/kissat/src/smooth.c:5-14 and 25-65
  const double alpha = 1.0 / window;
  smooth->beta = 1.0 - alpha;  smooth->exp = 1.0;
  ...
  new_biased = old_biased + alpha * (y - old_biased);
  new_exp = old_exp * beta;
  new_value = new_biased / (1 - new_exp);       // bias correction, until exp underflows to 0
```
`[C]` Windows: `emafast` = 33 (alpha ~= 0.0303), `emaslow` = 1e5 (alpha = 1e-5)
(`options.h:49-50`; `averages.c:13-14`). CaDiCaL identical: `emagluefast` = 33,
`emaglueslow` = 1e5 (`options.hpp:109-110`).

**Restart blocking on high trail: neither solver does it any more.** Kissat's
`kissat_restarting` has no trail term at all. The Glucose blocking idea was
*replaced* by target phasing plus mode alternation — the POS'20 paper says so
explicitly: blocking *"is only required for satisfiable problems... We extend
that idea with a heuristic called target phasing"* `[P]/[C]`. Kissat tracks a
`trail` EMA only under `#ifndef QUIET`, i.e. for reporting (`averages.h:13-15`).

**Reuse trail.** Both restart to the highest level whose decision variable still
outranks the next decision, rather than to 0:

```c
// references/kissat/src/restart.c:53-110
static unsigned reuse_stable_trail (kissat *solver) {     // by heap score
static unsigned reuse_focused_trail (kissat *solver) {    // by VMTF stamp
```
`[C]` `restartreusetrail` = 1 (`options.h:127`); CaDiCaL `restart.cpp:125-160`.

### 1.5 LBD (glue)

**Computed incrementally during analysis — no sort, no dedup, no allocation.**
The per-level `frame` struct carries a `used` counter; the first literal pulled
in at a level pushes that level onto a `levels` stack, and the glue is that
stack's size:

```c
// references/kissat/src/deduce.c:62-67
    frame *f = frames + level;
    if (f->used++) return false;     // level already counted
    PUSH_STACK (solver->levels, level);
```
```c
// references/kissat/src/learn.c:193
  const size_t glue = SIZE_STACK (solver->levels);
```
`[C]` The `frames` array is indexed by decision level and reset by walking the
`levels` stack (`analyze.c:311-324`) — O(glue), not O(levels).

**Recomputation uses a per-frame flag with an early exit at the old glue:**

```c
// references/kissat/src/promote.h:50-73
static inline unsigned kissat_recompute_glue (kissat *solver, clause *c, unsigned limit) {
  unsigned res = 0;
  for (all_literals_in_clause (lit, c)) {
    frame *frame = &FRAME (LEVEL (lit));
    if (frame->promote) continue;
    if (++res == limit) break;          // cannot beat the old glue; stop
    frame->promote = true;
    PUSH_STACK (solver->promote, level);
  }
  ... unmark ...
}
```
`[C]` CaDiCaL uses a monotone stamp table instead, so there is no unmark pass at
all:
```cpp
// references/cadical/src/analyze.cpp:194-206
int Internal::recompute_glue (Clause *c) {
  const int64_t stamp = ++stats.recomputed;
  for (const auto &lit : *c) {
    int level = var (lit).level;
    if (gtab[level] == stamp) continue;
    gtab[level] = stamp;
    res++;
  }
}
```
`[C]` `gtab` is a `vector<int64_t>` indexed by level; one global counter, no
clearing. This is the cheapest correct LBD I have seen `[I]`.

**Glue is capped** at `MAX_GLUE` = 2^19 - 1 on storage (`clause.h:13-16`,
`clause.c:34`) and at `MAX_GLUE_USED` = 127 for the tier histogram
(`statistics.h:310`, `deduce.c:21`).

### 1.6 Phase saving, target phases, rephasing

Three parallel arrays of `signed char` per variable: `saved`, `target`, `best`
(`kissat/src/phases.c:20-27`).

**Update rule — trail high-water marks, stable mode only:**

```c
// references/kissat/src/backtrack.c:37-68
static void kissat_update_target_and_best_phases (kissat *solver) {
  if (solver->probing) return;
  if (!solver->stable) return;
  const unsigned assigned = kissat_assigned (solver);
  if (solver->target_assigned < assigned) {
    solver->target_assigned = assigned;
    kissat_save_target_phases (solver);
  }
  if (solver->best_assigned < assigned) {
    solver->best_assigned = assigned;
    kissat_save_best_phases (solver);
  }
}
```
`[C]` Called on backtrack. `[P]` The paper notes Kissat measures *"the number of
assigned variables plus the number of fixed, substituted, or eliminated
variables"*, not raw trail length — because inprocessing removes variables and
raw trail length is then not comparable across time.

**Decision phase priority:** target (if stable, or `target > 1`) -> saved ->
`INITIAL_PHASE` (`decide.c:155-207`). Plus a curious focused-mode override that
forces the initial phase on the 2nd and 4th mode-switch octant:
```c
// references/kissat/src/decide.c:178-187
  if (!solver->stable) {
    switch ((solver->statistics.switched >> 1) & 7) {
    case 1: res =  INITIAL_PHASE; break;
    case 3: res = -INITIAL_PHASE; break;
    }
  }
```
`[C]` CaDiCaL ports this under `stubbornIOfocused` and notes *"kissat has 3 but
5 looks better"* (`decide.cpp:146-157`).

**Rephasing schedule — a literal table:**

```c
// references/kissat/src/rephase.c:86-89
static char (*rephase_schedule[]) (kissat *) = {
    rephase_best, rephase_walking, rephase_inverted,
    rephase_best, rephase_walking, rephase_original,
};
```
`[C]` i.e. `(B W I B W O)^ω`, selected by `(rephased - 1) % 6`
(`rephase.c:112`). Kissat rephases **only in stable mode**
(`rephase.c:32-38`). Interval: `UPDATE_CONFLICT_LIMIT(rephase, rephased,
NLOG3N, false)` = `conflicts + rephaseint * rephased * log10(rephased+9)^3`,
with `rephaseinit` = `rephaseint` = 1e3 (`rephase.c:119`, `options.h:122-123`).

**Critical detail — the target is reset after every rephase:**
```c
// references/kissat/src/rephase.c:117-123
  memcpy (solver->phases.target, solver->phases.saved, VARS);
  UPDATE_CONFLICT_LIMIT (rephase, rephased, NLOG3N, false);
  kissat_reset_target_assigned (solver);     // target_assigned := 0
  if (type == 'B') kissat_reset_best_assigned (solver);
```
`[P]` The paper's reason: *"the target assignment is reset after each rephasing
to the initial all-unassigned state. This encourages the solver to find larger
and larger target assignments until the next rephasing. The largest one will be
recorded as best assignment and reused in the next best rephasing."* This is a
ratchet-with-release, and the release is the point — a monotone high-water mark
that is never reset saturates and stops distinguishing `[P]/[I]`.

`[P]` CaDiCaL's schedules per the paper: focused `OI(BWOBWI)^ω`, stable
`(IBWFBW#BWOBW)^ω`, where `F` = flip and `#` = randomize. `W` = a bounded
ProbSAT local-search walk that minimizes falsified clauses over the saved
phases.

`[P]` Measured effect: the paper reports CDFs over SAT Competition 2018 + SAT
Race 2019 for seven configurations (`default`, `always-target`, `no-rephase`,
`always-target-no-rephase`, `no-target`, `no-target-no-rephase`,
`no-phase-saving`) and concludes the heuristics *"improve the performance on
satisfiable instances"*. I could not extract the per-configuration solved counts
— the numbers are in the plotted CDF, not in the text I recovered. **Did not
verify** a specific instance-count delta.

### 1.7 The propagation loop

```c
// references/kissat/src/proplit.h:71-100 (abridged)
  while (p != end_watches) {
    const watch head = *q++ = *p++;
    const unsigned blocking = head.blocking.lit;
    const value blocking_value = values[blocking];
    const bool binary = head.type.binary;
    watch tail;
    if (!binary) tail = *q++ = *p++;
    if (blocking_value > 0) continue;          // satisfied: no deref at all
    if (binary) {
      if (blocking_value < 0) { res = kissat_binary_conflict (...); break; }
      else { kissat_fast_binary_assign (...); ticks++; }
    } else { ... deref clause ... }
```

Four things worth naming `[C]`:

1. **Binary clauses are not clauses.** A binary watch is *one* 32-bit word
   holding the other literal plus a tag bit; a large watch is *two* words
   (blocking literal + arena reference). One watch array holds both, variably
   sized, discriminated by the tag bit (`watch.h:18-42`). A binary propagation
   never touches an arena.
2. **The blocking literal is checked before anything else**, so a satisfied
   clause costs one array read.
3. **The circular search cursor.** Each clause stores `searched`, the position
   where the last replacement search stopped, and the next search resumes there
   and wraps (`proplit.h:114-138`, `clause.h:33`). Kissat searches
   `[searched, end)` then `[2, searched)`, and writes the new position back.
4. **New watches are delayed.** A relocated watch is pushed onto a `delayed`
   stack and installed after the loop finishes (`proplit.h:1-32, 146, 184`), so
   the loop never mutates a watch array it might be iterating.

`[C]` Ticks (the mode-switching budget unit) are charged in this loop:
`1 + cache_lines(size_watches)` up front, then `+1` per binary assign, per large
clause deref, per relocation, and per reference assign.

---

## Part 2 — What we already have

Inventory of `crates/axeyum-cnf/src/proof_sat.rs` (6690 lines). Line numbers are
this file.

| Mechanism | Us | Verdict |
| --- | --- | --- |
| EVSIDS activity + increment decay | `bump_var` 2026, `decay` 2078, `VSIDS_DECAY` 0.95 (line 74) | **Have**, numerically same as Kissat/CaDiCaL |
| EVSIDS rescale | 1e100 trigger, 1e-100 factor, **plus a full heap rebuild** (2028-2052) | **Have, differently.** Kissat rescales at 1e150 and does not rebuild; we rebuild because our secondary key is the variable index and rescale can create ties (a correct and well-reasoned difference) |
| Order heap, lazy deletion | `heap` / `heap_pos` / `HEAP_ABSENT`, `pick_branch` 3755 | **Have** |
| VMTF queue | — | **Absent** |
| Stable/focused mode switching | — | **Absent** (`grep -ci stable` = 4, all in prose about `IncrementalSat`) |
| Reason-side bumping | — | **Absent**. `analyze` (2965) bumps only variables it resolves through (2995) |
| Random decision bursts | — | **Absent** |
| Phase saving | `phase[]`, written in `enqueue` (2179); decision at 2444-2449 | **Have** |
| Target phases | `best_phase` + `best_trail_len`, `snapshot_target_phase` 2137 | **Have, differently** — see below |
| Best phases (separate from target) | — | **Absent** (one array serves both roles) |
| Rephasing schedule (B/W/I/O/F/#) | — | **Absent**. Our only "rephase" is `phase := best_phase` at every restart (2402-2404) |
| Local search / walk | — | **Absent** |
| LBD computed | `compute_lbd` 3388 — `map -> Vec -> sort_unstable -> dedup -> len` | **Have, differently** (allocates + sorts per conflict) |
| LBD recomputation / promotion | — | **Absent**. `self.lbd[cid]` is written once at learning (2593) and never updated |
| Clause `used` counter | — | **Absent** |
| Tier1/tier2/tier3 | — | **Absent**. One boundary: `GLUE_LBD` = 2 (line 96), permanent exemption |
| Dynamic tier boundaries from used-glue histogram | — | **Absent** |
| Clause activity (EVSIDS-for-clauses) | `cla_activity`, `bump_clause` 3399, `decay_clause` 3416, decay 0.999 | **Have** — and it is our *only* ranking key |
| Reduce ranking | activity ascending, tiebreak clause id (3475-3481) | **Different.** References rank by (glue desc, size desc) and do not use activity at all |
| Reduce fraction | fixed `candidates.len() / 2` (3483) | **Different.** Kissat ramps 50% -> 90%; CaDiCaL is flat 75% |
| Reduce trigger | `learned_live > REDUCE_FIRST + REDUCE_INC * reductions` = `2000 + 300n` (3422-3428, 2603) | **Different** (clause-count budget vs. conflict-interval `sqrt` schedule) |
| Locked-clause protection | `is_locked` 3429 | **Have** |
| Irredundant/theory-lemma protection | `learned[cid]` flag, deliberately false for theory lemmas | **Have**, and better documented than the references' `redundant` bit |
| Arena compaction after reduce | — | **Absent.** We tombstone (`deleted[]`) and `rebuild_watches` (3500) rebuilds *every* watch list over *every* clause |
| Luby restarts | `luby` 131, `LUBY_UNIT` = 100 (line 85), `restart_limit` 2083 | **Have** — but this is the *default*, and the unit is 100 |
| Glucose EMA restarts | `update_restart_emas` 2095, `should_restart` 2116 | **Have but OFF** (`use_ema_restart: false`, line 1630) |
| EMA alphas | fast 2^-5 = 0.03125, slow 2^-14 = 6.1e-5 (lines 111-112) | **Different.** Kissat: 1/33 = 0.0303 fast (close), **1e-5 slow (6x slower than ours)** |
| EMA bias correction | — | **Absent.** We seed at 0.0 and never correct, so both averages start biased low and the *slow* one stays biased for ~10^4 conflicts `[I]` |
| Per-mode EMAs | — | **Absent** (single set) |
| Restart margin | `RESTART_MARGIN` = 1.25 (line 114) | **Different.** Kissat 1.10 focused; CaDiCaL 1.10 focused / 1.25 stable |
| Blocking restart on trail | `TRAIL_EMA_ALPHA`, `BLOCKING_MARGIN` = 1.40, in `should_restart` | **Have** — a mechanism current Kissat has *dropped* |
| Reuse trail on restart | — | **Absent.** We always `backtrack_to(0)` (2401) |
| Reluctant doubling | via `luby()`, equivalent | **Have** |
| Blocking literals in watches | `Watch { clause, blocker }` (1108), checked first (2879) | **Have** |
| Binary clause special-casing | — | **Absent.** A binary goes through `headers[cid]`, an arena read, and the (empty) `2..len` replacement loop |
| Circular search cursor (`searched`) | — | **Absent.** Replacement search always restarts at index 2 (2911) |
| Delayed watch installation | — | **Different.** We `push` to `self.watches[new_code]` mid-loop, which is safe only because the current list was `mem::take`n (2865) |
| Chronological backtracking | — | **Absent** |
| Recursive clause minimization | `minimize` 3284 + `lit_redundant` 3337 | **Have** |
| All-UIP shrinking | — | **Absent** (Kissat `shrink` = 3 by default) |
| On-the-fly strengthening / subsumption | — | **Absent** (Kissat `otfs` = 1, `eagersubsume` = 4) |
| Per-conflict `seen` allocation | `vec![false; nvars]` **every conflict** (2966) | **Different, and costly.** References use persistent flags cleared by walking the analyzed stack |
| Ticks / deterministic effort metric | `watch_visits`, `clause_visits` counters exist but are opt-in and unused by policy | **Half-have.** The counter exists; nothing budgets on it |

### Notes on the three "have, differently" entries that matter most

**Our target phasing is a monotone ratchet that never releases.**
`best_trail_len` (2137-2147) only ever increases; nothing resets it. Kissat
resets `target_assigned` at every rephase (`rephase.c:120`). `[I]` Consequence:
after our first deep dive, `snapshot_target_phase` stops firing for the rest of
the run, and `phase := best_phase` at every restart pins the search to one
region — a *stronger* commitment than plain phase saving, applied at every
restart, with no diversification path out. This is plausibly counterproductive
on UNSAT instances and I would rank re-checking it above building anything new.

**Our clause DB has no middle.** Glue 2 is immortal; glue 3 and glue 40 are
ranked by the same activity number and half of the union is deleted. The
references treat glue 3-6 as a distinct population with a one-round grace period
keyed on actual recent use. `[I]`

**Our restart default is ~100x slower than a focused-mode restart.** Our Luby
base unit is 100 conflicts (line 85), so the sequence is 100, 100, 200, 100,
100, 200, 400, ... Kissat's focused base is 1 conflict plus `log10(restarts+9)`,
gated by the EMA rule; its *stable* base is 1024. We run something close to
"stable mode only, forever, with an aggressive best-phase pin." `[C]/[I]`

---

## Part 3 — Ranked findings

Ranking is by expected reduction in conflicts-to-solution, my judgment `[I]`.
Costs are rough.

### R1. Clause-database tiering with a `used` counter — highest expected gain

Replace activity-ranked "delete worst half" with the tier scheme. Concretely:

- Add `used: u8` per clause. Set to 31 on learn and on every resolution in
  `analyze` (our `bump_clause` call site at 2984 is already exactly the right
  hook — it fires once per antecedent).
- At reduce: decrement `used` for every redundant clause; keep if
  `glue <= tier1 && used_before > 0`, keep if
  `glue <= tier2 && used_before >= 30`, else candidate.
- Rank candidates by `(glue desc, size desc)`; delete a ramped fraction.
- Recompute glue on resolution and promote when it drops.

Why this and not activity: `[P]` the tier scheme is what every top solver since
~2013 uses, and `[C]` neither reference consults clause activity anywhere in
`reduce`. `[I]` Our current policy has two specific failure modes it removes: a
clause that was resolved five times ten thousand conflicts ago outranks one
resolved twice last round (activity decays but never expires), and a glue-3
clause carrying real structure competes on equal terms with a glue-40 clause.

Retaining our correctness properties: deletion must still emit a DRAT `d` step
and must still skip `!learned[cid]` (theory lemmas and inputs). The ranking key
change is invisible to the proof.

**Cost:** medium. The `used` field, the keep predicate, and the ranking are each
a few lines; the histogram (R2) can land separately.

### R2. Dynamic tier boundaries from the used-glue histogram

`used[stable].glue[0..=127]`, incremented at every clause resolution;
`tier1` = smallest glue reaching 50% of cumulative used, `tier2` = 90%;
recomputed on a doubling conflict interval capped at 2^16, with fallback 2/6.

`[P]` The justification is measured and stated in the SC2024 description (quoted
in §1.3): average glue *"varies dramatically between different formulas"*, so
fixed 2/6 is wrong on most of them. `[I]` This is the finding I would most
expect to move our number on the QF_BV corpora specifically, because bit-blasted
formulas have a very different glue profile from combinatorial benchmarks and
nobody has ever tuned 2/6 for them.

**Cost:** small once R1 exists — a 128-entry array and ~40 lines.

**Note for whoever builds it:** the histogram is per mode in the references. If
we have no modes (yet), keep one histogram and note in the code that it is the
degenerate case, so R4 does not have to rediscover the indexing.

### R3. Restart policy: turn the EMA rule on, fix its constants, add reuse-trail

Three separate defects in what we already have:

1. **Default is Luby at unit 100.** `[I]` For a search that has no stable/focused
   distinction, a Glucose EMA rule with a small base interval is the standard
   choice and the one both references use in focused mode.
2. **Our slow alpha is 6.1e-5 vs. Kissat's 1e-5**, and we have **no bias
   correction**. `[C]` Kissat's `smooth` divides by `1 - beta^n` until the
   exponent underflows (`smooth.c:41-64`). `[I]` Without it, an EMA seeded at
   0.0 with alpha 1e-5 needs ~10^5 conflicts to be meaningful — which is why our
   `EMA_RESTART_WARMUP` = 100 is far too short to make the rule trustworthy, and
   plausibly part of why the measured result was "neutral-to-slightly-negative"
   on the `p4dfa` slice. **This is a real candidate explanation for that
   measurement and it is cheap to re-test.**
3. **Margin 1.25 vs. 1.10.** `[C]` CaDiCaL uses 1.25 only in *stable* mode.

Also add **reuse-trail** (`restart.c:53-110`): on restart, walk down from level 0
and keep every level whose decision variable still outranks the next decision.
`[I]` This is pure saved work — it does not change which decisions are made, only
how many times they are re-made — so it should show up as conflicts-per-second
rather than conflicts-to-solution. Cheap, low risk, and it makes frequent
restarts affordable, which is the precondition for (1).

**Cost:** small. Constants + bias correction + ~30 lines of reuse-trail.

### R4. Stable/focused mode alternation with two decision heuristics

The structural change. `[P]` It is also the one the POS'20 paper warns will make
things *worse* if landed without reason-side bumping (R5).

Components:
- A `SearchMode { Stable, Focused }` on the solver, with **per-mode EMAs**,
  per-mode tier limits, and per-mode restart policy.
- A VMTF queue (doubly-linked list over variables + `stamp` per variable +
  a `search` cursor), used for decisions and bumping in focused mode.
- A deterministic effort unit ("ticks") to budget stable phases. We already
  count `watch_visits` and `clause_visits` in `propagate` (2870, 2886) behind
  `count_search` — that is the same quantity. `[I]` Making it unconditional and
  budgeting on it is exactly Kissat's design and preserves determinism.

**Cost:** large. This is the "slice it, do not defer it" case: VMTF alone, behind
a flag, decided by a mode that starts permanently Focused, is a landable
increment that changes nothing until switched on.

### R5. Reason-side bumping

Bump the literals in the *reasons* of the learned clause's literals, capped at
`10 * |analyzed|`, skipped when the decision-rate EMA is above 10, with a
roll-back and an exponential delay when the cap is hit
(`kissat/src/analyze.c:169-212`).

`[P]` Direct quote from the paper (§1.1): omitting it made mode alternation
*"much worse than the original implementation of Glucose"*. `[I]` I rank it
below R4 only because its measured effect is reported *in the presence of* mode
alternation; standalone it is unquantified. If R4 is scheduled, R5 is a
prerequisite, not a follow-up.

**Cost:** small-medium (~60 lines, plus a decision-rate EMA).

### R6. Rephasing schedule, and un-pinning our target phase

Two parts, and the first is a possible *regression fix*, not a feature:

- **Reset `best_trail_len` periodically.** `[C]` Kissat resets
  `target_assigned` at every rephase and `best_assigned` on every `B` rephase.
  `[I]` Ours never resets, so after the first deep dive the target stops
  updating and `phase := best_phase` at every restart pins the search. This
  costs nothing to test: reset `best_trail_len` on a schedule and re-measure.
- **A rephase schedule.** `(B W I B W O)^ω` on interval
  `1000 * n * log10(n+9)^3`. Without a local-search walker, `(B I B O)^ω` is the
  reachable subset; `W` needs a bounded ProbSAT pass (a separable component,
  and one we could reuse elsewhere).

Also separate `target` from `best`: target drives decisions and is reset often;
best is the long-run archive that `B` rephasing restores from.

**Cost:** small for the reset and the B/I/O schedule; medium for `W`.

### R7. LBD without allocation, and glue promotion

`compute_lbd` (3388) allocates a `Vec`, sorts, and dedups on **every conflict**.
Replace with CaDiCaL's stamp table: a `Vec<u64>` indexed by decision level plus a
monotone counter, O(clause length), no allocation, no clearing
(`cadical/src/analyze.cpp:194-206`). Kissat's variant additionally early-exits
once the count reaches the old glue, which is what makes recomputation on every
resolution affordable (`kissat/src/promote.h:50-73`).

`[I]` The allocation-and-sort is a throughput item; the thing that affects
conflicts-to-solution is that having a cheap recompute makes **promotion**
possible (R1), which is how a clause that was learned wide but became narrow
gets protected.

**Cost:** small, and it is a strict prerequisite for R1's promotion rule.

### R8. Per-conflict `seen` allocation

`analyze` allocates `vec![false; self.assign.len()]` per conflict (2966). We even
count the bytes (`analyze_mark_bytes`), so somebody already noticed. `[C]` Both
references keep a persistent per-variable flag and clear only the analyzed set
(`kissat/src/analyze.c:326-338`). `[I]` Throughput only — no effect on which
conflicts happen — but it is O(variables) per conflict on a path that runs
millions of times, and the fix is mechanical.

### R9. Binary-clause special-casing in the watch lists

`[C]` A Kissat binary watch is one word carrying the other literal; propagating
it never touches an arena. Ours derefs `headers[cid]`, reads `arena[off]`,
possibly swaps, and runs an empty replacement loop. `[I]` Throughput only, but
binaries dominate watch traffic on bit-blasted formulas, and R3's more frequent
restarts increase propagation volume. Our `Watch` is `{ CRef, CnfLit }`; a tag
bit in the `CRef` plus a variable-stride scan is the reference layout.

Related and cheaper: add Kissat's `searched` cursor per clause
(`proplit.h:114-138`) so the replacement scan resumes where it stopped instead
of restarting at index 2.

### R10. Reduce-round cost: sweep start and arena compaction

`[C]` Kissat sweeps only from `first_reducible` and compacts the arena
(`reduce.c:37-61, 161, 183`). We scan **all** headers (3459) and
`rebuild_watches` (3500) rebuilds every watch list over every live clause,
including originals, on every reduction. `[I]` Throughput only, but it is
O(total clauses + total literals) per reduce round and it will get worse if R1
makes reductions more frequent.

---

## Part 4 — Component boundaries for the implementer

The brief asks for configurable, reusable pieces rather than constants inlined
into the loop. What the reference structure suggests `[I]`:

**`DecisionHeuristic`** — `pick(&mut self, assigned) -> Option<Var>`,
`bump(&mut self, analyzed: &[Var])`, `on_unassign(&mut self, v)`,
`on_mode_change(&mut self)`. Two implementations (`EvsidsHeap`, `VmtfQueue`) and
a `ModeSwitching<A, B>` combinator. Note both references keep *both* structures
live for the whole search and never migrate state between them — switching modes
only changes which one is consulted, plus a cheap re-sync
(`kissat/src/mode.c:164, 183`).

**`ClauseDbPolicy`** — the separable decisions are: (a) the keep predicate
`fn keep(&self, glue, used, size, locked, reason) -> bool`; (b) the ranking key
`fn rank(&self, c) -> u64`; (c) the fraction `fn fraction(&self, round) -> f64`;
(d) the schedule `fn next_limit(&self, conflicts, round) -> u64`; (e) the tier
boundaries, which are *state*, not config — a `TierEstimator` fed by
`on_clause_used(glue)` and queried at reduce time. Keeping (e) separate is what
lets 2/6-fixed and percentile-dynamic coexist behind one policy object.

**`RestartPolicy`** — `should_restart(&self, ctx) -> bool`,
`on_conflict(&mut self, glue)`, `on_restart(&mut self)`, plus a
`reuse_level(&self, ctx) -> usize` that is orthogonal to *when* to restart.
`Luby`, `GlucoseEma`, and `Reluctant` are three implementations;
`ModeSwitching` picks.

**`PhasePolicy`** — owns `saved`, `target`, `best`, the high-water marks, and the
rephase schedule table. The schedule really is a `[fn(&mut Phases); 6]` in the
reference (`rephase.c:86-89`); there is no reason for ours to be less literal.

**`Effort`** — the deterministic tick counter. One counter, incremented in
`propagate`, read by mode switching and (in the references) by every
inprocessing budget. Making it unconditional rather than gated on
`count_search` is what turns it from an observability field into a policy input.

Shared state that all four read: `conflicts`, `decision_level`, `trail`,
`mode`. The references pass the whole solver; we would want a small
`SearchCtx<'_>` borrow so the policies stay unit-testable.

---

## Sources

Code, in-tree (`references/`, gitignored):
Kissat 4.0.4 `8af8e56f` — `src/{decide,restart,reduce,tiers,bump,mode,learn,deduce,analyze,promote,rephase,phases,backtrack,proplit,propsearch,smooth,averages,reluctant,kimits,options,clause,watch,search}.{c,h}`;
CaDiCaL `c6073042` — `src/{decide,restart,reduce,tier,analyze,internal,options,clause}.{cpp,hpp}`.

Papers:
- [Armin Biere and Mathias Fleury, *Chasing Target Phases*, POS 2020](https://fmv.jku.at/papers/BiereFleury-POS20.pdf)
- [Biere, Faller, Fazekas, Fleury, Froleyks, Pollitt, *CaDiCaL, Gimsatul, IsaSAT and Kissat Entering the SAT Competition 2024*](https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-SAT-Competition-2024-solvers.pdf)
- [Biere, Fleury, Pollitt, *SAT Competition 2023 solvers*](https://cca.informatik.uni-freiburg.de/papers/BiereFleuryPollitt-SAT-Competition-2023-solvers.pdf) (skimmed; not cited above)

## What I did not verify

- LRB and CHB update rules from primary source. Neither reference implements
  them; I did not read MapleSAT.
- The per-configuration solved-instance counts in the POS'20 experiments (they
  are in a plotted CDF; the recovered text gives the setup and the qualitative
  conclusion only).
- Kissat's exact heap tie-break in `inlineheap.h`.
- The claim that our propagation throughput is within ~40% of Kissat's and that
  we need ~2.5x the conflicts — taken from the brief, not re-measured here.
- Any of this against our actual corpora. Every ranking in Part 3 is a
  judgment about mechanism, not a measurement.
