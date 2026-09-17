# ADR-2142: the warm session slowed with age because the target-phase snapshot re-walked the trail per decision

Status: proposed
Index-summary: Glaurung's 2026-09-17 six-cell rerun found the retained `IncrementalBvSolver`'s per-check latency growing with session age (DptfDevGen p90 0.1 ms in a session's first 50 checks, 178 ms past 500). A verbatim replay of that session (`examples/warm_session_age.rs`, 1,206 checks, 0 verdict disagreements, every `sat` replayed) reproduced it at 0.24 → 269 ms p90 (1,101×); `git bisect` over 5,804 commits converged in 13 steps on **`f019d503f`** (2026-09-05, ADR-1703: the native CDCL core becomes the SAT engine), whose parent measures 4.7 ms. The hot frame was `proof_sat.rs::snapshot_target_phase`: it walked the WHOLE trail on every fresh high-water mark, and a conflict-free descent sets one at every decision, so a warm check with ~60k retained level-zero assignments cost O(decisions × trail). CaDiCaL and Kissat take the same snapshot once per backtrack. The fix keeps a stable-prefix mark per phase vector and copies only `trail[stable..]`: same vectors, same trajectory — the verdict+model digest is identical on both streams, the session's conflict count is 19 either way — and the replayed session's last band falls from 306 ms to 7.5 ms p90 back to back (total 34.9 s → 1.66 s; the July BatSat engine measures 3.7 ms / 0.87 s on the same stream). A counter test pins the linear bound (320,800 entries copied under the old walk vs a bound of 3,200; reverting kills exactly that test). What remains is linear in the retained database (0.2 → 7.5 ms over 1,200 checks against July's 0.2 → 3.7 ms) because the incremental core re-propagates from an empty assignment every solve by design, where z3's `sat::solver::pop` keeps the surviving scopes' assignments; that is the follow-up, not this repair. No default moves.
Index-status: proposed
Date: 2026-09-17

## Context

Glaurung re-ran ADR-0272's six-cell timing campaign on 2026-09-17 at Axeyum
pin `8df853252` (Glaurung `solver-033`). Cold one-shot Axeyum was at parity
or faster than cold z3 on three of four Windows drivers, but the retained
`IncrementalBvSolver` session was not: its per-check latency grew with the
session's age. On DptfDevGen the p90 per check was 0.1 ms in a session's
first 50 checks and 178 ms past 500, on queries that solve cold in about
2 ms; July's campaign at pin `c38a9515e` had warm Axeyum at 0.84–2.28× z3,
now 0.09–1.22×. Between the pins are 11,607 commits, including the
retirement of BatSat (ADR-1703).

Reading the campaign trace confirmed the shape before anything was built:
owner 1 of `01-dptf-r1` served 1,206 checks; its warm p90 by band of 50 rose
0.57 → 2.7 → 7.2 → … → 235 ms while the cold p90 of the same queries stayed
at 0.7–3.8 ms, and the growth was on the `sat` checks (max 4.6 ms in the
first hundred, 243 ms in the eleventh) with the unsat checks rising 20×
alongside.

## The reproducer

`crates/axeyum-solver/examples/warm_session_age.rs` drives one retained
`IncrementalBvSolver` through a long push/assert/check/pop stream and prints
p50/p90/max per band of 50 checks, plus a FNV digest of every verdict and
every `sat` model value in order.

- `--replay <stream>` replays a real session **verbatim**. The lane's
  `extract_owner.py` reads the Glaurung ordered trace (`events-v1.ndjson`
  and the per-check `queries/*.smt2`, whose assertion lists were verified to
  equal the per-path stacks reconstructed from the push/assert/pop events on
  all 1,365 checks), keeps owner 1's 1,206 checks, and writes one script
  with every distinct assertion (599, over 3 symbols) plus an ops file
  naming each check's persistent stack and temporary assumptions. The
  driver synchronises each check exactly as Glaurung's serial warm owner
  does (`warm_paths.rs::transition_and_check`): pop to the longest common
  prefix, push+assert the suffix one scope per assertion, then `check` or
  `check_assuming`. The stream is derived from restricted driver analysis
  and stays on `/data0`; it is not committed.
- `--synthetic [n]` is an explorer-shaped walk with no external data: a
  path grows one branch constraint per feasible check, probes an overflow
  assumption every third step, abandons an infeasible branch for its
  sibling, and forks a sibling a few levels up at depth 40. The 64-bit
  adders are shared between constraints as the drivers' prefixes are, so
  1,200 checks retain 54k clauses (the trace: 148k for 1,206).

Every `sat` is replayed against the original assertions; a replay failure
or a verdict that disagrees with the trace's recorded outcome fails the run,
and `--assert-flat <ratio>` makes the exit status depend on the growth.

**At `8df853252` / the lane's base, replaying DptfDevGen r1 owner 1**
(1,206 checks; sat 725, unsat 481, unknown 0; disagreements 0; replay
failures 0; retained 147,661 clauses / 63,154 variables):

| band | p50 ms | p90 ms | max ms |
|-----:|-------:|-------:|-------:|
| 0 | 0.051 | 0.244 | 1.55 |
| 250 | 0.504 | 23.5 | 26.0 |
| 500 | 1.568 | 58.3 | 62.7 |
| 750 | 1.604 | 120.8 | 127.0 |
| 1000 | 3.185 | 206.6 | 220.6 |
| 1150 | 2.381 | 268.7 | 277.2 |

`first_band_p90_ms=0.244 last_band_p90_ms=268.686 ratio=1101`, 31.1 s total.

## The bisect

Oracle: the replay with `--assert-flat 40` (the July engine measures 16–31×
on this stream — see below — so the brief's 10× would have called the good
side bad; the bad side measures 636–1,160×). Each candidate was extracted
with `scripts/lane-snapshot.sh`, built `--release --features full` into
`/data0/axeyum-lane-targets/ax-warm-bisect` through
`scripts/cargo-serialized.sh`, and run pinned to cores 0–7. 5,804 commits,
13 steps, one transition:

| commit | date | last-band p90 | ratio | verdict |
|---|---|---:|---:|---|
| `c38a9515e` (July pin) | 07-20 | 3.26 ms | 16.0 | good |
| `fe01a04da` | 08-27 | 4.78 ms | 23.0 | good |
| `0ba67b82e` | 09-04 | 6.75 ms | 31.1 | good |
| `9abb438d4` (parent of first bad) | 09-05 | 4.69 ms | 22.5 | good |
| **`f019d503f`** | 09-05 | **158.1 ms** | **636.6** | **bad** |
| `a305df5ce` | 09-05 | 168.0 ms | 703.5 | bad |
| `f2d792a9e` | 09-08 | 266.4 ms | 1160.5 | bad |

`f019d503f` — "feat(sat): the native CDCL core is the SAT engine; batsat
becomes a feature-gated oracle" (ADR-1703 slice 1 steps 2–4; 28 files,
`axeyum-cnf/src/lib.rs` +699/−…, `IncrementalSat` re-implemented over
`NativeIncrementalCdcl`). The growth arrived in one step: the commit that
made the native core the warm engine. The full `git bisect log` is in the
lane's scratch record.

## The diagnosis

`perf record` of the replay at head: 94.9 % of samples in
`Cdcl<IncrementalSink>::run` self time. With line tables
(`CARGO_PROFILE_RELEASE_DEBUG=line-tables-only`) the hot instructions were
the loop at `crates/axeyum-cnf/src/proof_sat.rs:3126-3132`, the body of
`snapshot_target_phase` (T1.3.1 target-phase rephasing, `950fcfcd2`,
2026-07-07 — present in July but the native core was not the warm engine
then):

```rust
for idx in 0..depth {
    let var = self.trail[idx];
    let polarity = self.assign[var] == Some(true);
    if fresh_target { self.target_phase[var] = polarity; }
    if fresh_best   { self.best_phase[var]   = polarity; }
}
```

Its doc said "only walks the trail on a fresh high-water mark, so the
amortized cost is negligible". A fresh high-water mark is not rare: the
search loop calls it at every conflict-free fixpoint, and a conflict-free
descent — which is what a warm `sat` check is (19 conflicts in the whole
1,206-check session) — grows the trail at every decision, so every decision
set a new mark and re-walked the whole trail. A retained session's trail
carries every variable ever encoded (63k here), so a check cost
O(decisions × retained variables): quadratic in session size. The one-shot
core pays this too but its trail is one formula's, and nobody had measured a
retained one.

CaDiCaL (`references/cadical/src/backtrack.cpp:46-84`,
`update_target_and_best` called from `backtrack`) and Kissat
(`references/kissat/src/backtrack.c:51-66`) take the target/best snapshot
**once per backtrack**, copying the saved phases, so their cost is O(vars)
per conflict; ours was O(trail) per decision.

## The fix

Two marks per `Cdcl` — `target_stable` and `best_stable`, the length of the
trail prefix the corresponding vector already reflects — and the walks start
there:

- `snapshot_target_phase` copies `trail[target_stable..depth]` into
  `target_phase` (and likewise for `best`), then sets the mark to `depth`;
- `backtrack_to(level)` lowers both marks to the surviving trail length;
- `apply_rephase` zeroes `target_stable` (the vector is overwritten
  wholesale; `best_phase` is only read there, so its mark stands);
- `reset_search_state` zeroes both (the trail is cleared).

A prefix that has not been unassigned has the polarities it had when it was
copied, so the vectors are byte-identical to the full walk's and no
decision, verdict or model changes. Measured, not asserted: the reproducer's
verdict+model digest is `9fe6d1e14afe9c19` on the replayed session and
`0d31b2edfe790805` on the synthetic stream under BOTH the old walk and the
fix, with 19 and 0 conflicts respectively either way.

The snapshot placement (per fixpoint) is deliberately unchanged: moving it
to backtrack time as CaDiCaL does would snapshot a different assignment and
change trajectories, which is a heuristic change with its own A/B, not a
regression repair.

**Control.** `SearchCounters::phase_snapshot_entries` counts entries copied,
incremented inside the loop so it measures the walk that ran. The test
`phase_snapshot_cost_is_linear_in_the_trail_on_a_conflict_free_descent`
(400 independent binary clauses, 400 decisions, 0 conflicts) requires the
count to be at most `2 × assignments + 2 × vars` = 3,200; the old walk
copies 320,800. Reverting the two loop starts to `0` killed exactly that
test of the 636 in `axeyum-cnf --lib`.

## The measurement after

Same stream, same cores (`taskset -c 0-7`), back to back at load 4–5, the
old walk (the fix's two loop starts reverted to `0`, i.e. the shipped
behaviour, in the same binary shape) against the fix:

| band | old p50 | old p90 | old max | fixed p50 | fixed p90 | fixed max |
|-----:|--------:|--------:|--------:|----------:|----------:|----------:|
| 0 | 0.056 | 0.228 | 2.04 | 0.048 | 0.202 | 0.35 |
| 250 | 0.394 | 29.0 | 30.1 | 0.261 | 1.34 | 1.43 |
| 500 | 0.877 | 68.1 | 72.2 | 0.555 | 2.49 | 3.05 |
| 750 | 1.370 | 140.2 | 142.2 | 0.948 | 3.83 | 4.03 |
| 1000 | 2.209 | 219.2 | 242.6 | 1.778 | 6.49 | 8.25 |
| 1150 | 3.229 | 305.8 | 314.1 | 2.128 | 7.54 | 8.10 |

Old: `ratio=1340`, 34.9 s total. Fixed: `ratio=37`, 1.66 s total. Same
digest, same 19 conflicts. The synthetic stream (1,200 checks, 54k retained
clauses): last-band p90 71 ms → 2.6 ms, total 41 s → 2.1 s (taken under
bisect load, so the absolute numbers there are pessimistic).

The July pin's engine (BatSat, `c38a9515e`, rebuilt with the same
reproducer) interleaved with the fix on the same stream, two rounds each:
July 0.20 → 3.6 / 3.7 ms p90 (0.86 / 0.88 s total), fixed 0.20 → 6.4 / 6.1 ms
(1.43 / 1.34 s). So the fix returns the warm path to within about 1.7× of
the July engine at 1,200 checks of age, from 80× before it.

## What remains, and why it is not this repair

The last band is still 30–37× the first, and the July engine on the same
stream is 16–18×. Profiled after the fix: `propagate` 63 %,
`heap_percolate_down` 13 %, `IncrementalSat::solve_inner` 9 % (its
`assignment_is_model` pass over all 148k clauses), `reset_search_state` 2 %.
Counters at check ~600: 0 decisions, 24k propagations, 57k watch visits per
`sat` check, 0 conflicts. That is the cost of re-deriving the whole retained
assignment every solve, which `proof_sat/incremental.rs` chooses on purpose
("Between solves the solver holds no assignment at all, including at level
zero … That costs one level-zero propagation per solve and buys the property
that makes `add_clause` simple"). z3's `sat::solver::pop`
(`references/z3/src/sat/sat_solver.cpp:3650`) unassigns only the trail
above the popped scope's limit and keeps the surviving scopes' assignments,
so a retained check there costs the delta. Making the warm core keep the
surviving prefix (and register new clauses against a live assignment) is
the lever for the linear term; it changes propagation order and therefore
trajectories, so it needs the pinned-list A/B this repair did not.

## Consequences

- Warm sessions no longer degrade quadratically; a Glaurung re-pin and
  rerun of the six-cell campaign is the follow-up that measures the
  production effect (the campaign's `IOCTLANCE_SOLVE_SECS=60` cut was hit
  because of this growth).
- `IncrementalBvSolver::retained_learned_clause_count` /
  `retained_sat_conflicts` and `IncrementalCnf::learned_clause_count` /
  `total_conflicts` are new read-only gauges; the reproducer prints them per
  band so a future "warm gets slower" report can tell a learned-clause leak
  (it was not one: 19 learned clauses over 1,206 checks) from a per-check
  cost that scales with the retained database.
- No `SolverConfig` default, schedule or bound moved, so there is nothing to
  register in `config_registry.rs` and no pinned-list A/B was owed.
