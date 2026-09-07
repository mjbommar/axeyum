# Lane: s2-followup-lia-probe — recover the QF_LIA −2 without reopening S2's dispatch-overrun fix

<!-- plan-section: lane-status -->

**IN PROGRESS.** Baseline measured and committed; the fix is designed and
empirically checked against a real overrun candidate, not yet implemented in
`dpll_lia.rs`.

## The task

Slice S2 (`b4d042ae4`) added `arith_dpll_admission_preflight` so an oversized
`QF_LIA`/`QF_LRA`/`QF_LIRA` skeleton declines on a size constant before
spending the online CDCL(T) probe's share of the caller's reserve. That fixed
a real dispatch overrun (QF_IDL timeouts summing `dl-online`'s reserve plus
`lia-dpll`'s ~8 s past the caller's 24 s nominal budget, killing the process
before any output). It also cost two QF_LIA files lane S1b diagnosed and
handed back (`docs/plan/status/s1b-cdclt-heap-minimize.md`):

- `QF_LIA/bofill-scheduling/SMT_real_LIA/ex3000_2400_100.smt2` (declared `unsat`)
- `QF_LIA/bofill-scheduling/SMT_real_LIA/ex4320_2400_100.smt2` (declared `unsat`)

Both used to be refuted by the online probe itself, inside its root
propagation fixpoint (zero decisions), before S2 made the admission decline
run first and skip the probe entirely.

## Baseline, measured before any code change

Binary `smtcomp_cli`, commit `cc75cd023` (this lane's branch point, local
`main` fast-forwarded onto `f3ce8ef58` afterward — see Commits). Idle s6,
`taskset -c 8-15` (cores 0-7 were held by a concurrent lane's `uf_unknown_probe`
process; 8-15 confirmed idle via `mpstat -P ALL` immediately before every run
below), `AXEYUM_TRACE=1 --trace`, `--timeout-ms 24000`, three repeats:

| file | verdict | wall | note |
|---|---|---|---|
| `ex3000_2400_100.smt2` | `unknown` | 0.047-0.054 s | no `; theory-layer` trace line at all — the admission preflight declines before the probe ever runs (S2's intended behaviour) |
| `ex4320_2400_100.smt2` | `unknown` | 0.047-0.054 s | same |
| `QF_IDL/sal/lpsat/lpsat-goal-18.smt2` | `unsat` | 7.22-7.25 s | **does not hit admission decline at all** — `decisions=53011, restarts=61`, decided by genuine CDCL(T) search inside the online probe's own share. `exceeds_pre_sat_skeleton_boundary` is false for this file; it is protected by `dl_probe_budget`'s reservation (a different mechanism), not by the admission constant. Confirms criterion 4 is a no-op check against this fix (see below) rather than a live interaction. |

Raw log: `bench-results/s2-followup-lia-probe-20260906/before-arm-three-files.txt`.

## Root-cause measurement: why the old dispatch order recovered these two files

Direct calls to `axeyum_solver::theories::arithmetic::check_qf_lia_online_cdclt`
(bypassing dispatch), `taskset -c 8-15`, idle cores confirmed via `mpstat`,
`TheoryLayerStatsGuard` enabled:

| explicit budget | ex3000 | ex4320 |
|---|---|---|
| 6000 ms | `Unknown(Timeout)` at 6.04 s | `Unknown(Timeout)` at 6.06 s |
| 7000 ms | `Unsat` at 7.01 s | `Unsat` at 7.06 s |
| 8000 ms | `Unsat` at 8.03 s | `Unsat` at 8.06 s |
| 30000 ms | `Unsat` at 26.4 s | `Unsat` at 30.0 s |

`decisions=0, restarts=0, theory_conflicts=1` at every budget ≥ 7000 ms: the
refutation is always a pure root-propagation fixpoint, never a real search.
But the wall time to reach it tracks the budget handed to the call rather
than converging to one intrinsic completion time once above ~7 s — giving it
more time makes it do more (evidently redundant) work before landing on the
identical answer. This is consistent with (and reproduces almost exactly) the
S1b lane's independent prior measurement: the old dispatch order handed this
probe `timeout/3` of a 24 s caller budget = 8 s, and it decided both files in
"8.1 s" with `decisions=0`. **~7-8 s is therefore both necessary and
apparently what the implementation will consume once available** — see
`bench-results/s2-followup-lia-probe-20260906/probe_bound_sweep_idle_s6_cores8-15.txt`.

This matters for the fix: a *proportional* share (like the old `timeout/3`)
or any budget picked without an upper bound is not "cheap" in the sense of
being fast when unneeded — it is exactly as expensive as whatever cap is set,
for files that time out on it too. The fix must not spend this cost
unconditionally.

## Why an unconditional bounded probe would reopen S2's fix — measured, not assumed

Ran `dispatch_probe` (a scratch driver over the full `solve_smtlib`
dispatcher; not committed) against a real oversized `QF_IDL` file that
currently declines the same admission constant
(`QF_IDL/bcnscheduling/bcnscheduling105.smt2`, `atoms=1560, cnf_vars=9652`,
same `exceeds_pre_sat_skeleton_boundary` gate as the two target files):

```
verdict=unknown elapsed_ms=18070 kind=ResourceLimit
detail=... declining before the online CDCL(T) probe ...
```

`explain_corpus --json --timed-trace` on the same three files shows the
mechanism precisely (`bench-results/s2-followup-lia-probe-20260906/explain_corpus_route_attempts.jsonl`):

| file | `dl-online` outcome | `dl-online` elapsed |
|---|---|---|
| `ex3000_2400_100.smt2` | `declined: not-applicable` | **20 ms** |
| `ex4320_2400_100.smt2` | `declined: not-applicable` | **18 ms** |
| `bcnscheduling105.smt2` | `declined: budget` (budget exhausted in the online DL driver) | **18.011 s** |

For the two target files, `dl-online` recognizes near-instantly that the
query is not difference-logic shaped and declines for free — `lia-dpll` then
runs with the *entire* nominal budget still available. For a genuine `QF_IDL`
file, `dl-online` is difference-logic shaped by construction, so it spends
its **entire reserved share** (`dl_probe_budget`: `timeout - min(timeout/4,
6s)` = 18 s of a 24 s caller budget) searching before giving up — leaving
only ~6 s of nominal budget for everything downstream (`bv2nat-range`,
`lia-diophantine`, `lia-simplex`, `lia-dpll`) **combined**. Because
`check_with_arith_dpll` measures its own deadline from its own entry
(`Instant::now() + config.timeout`, unaware of what `dl-online` already
spent — the same "not drawn against one shared, shrinking deadline"
structural property S2's own docs name), it cannot see that only ~6 s of the
nominal 24 s genuinely remains. An unconditional ~7-8 s bounded-probe
attempt added to the admission-decline path would therefore add ~7-8 s
*on top of* `dl-online`'s already-spent 18 s for files like
`bcnscheduling105.smt2`, reproducing the same class of overrun S2 fixed
(measured total ≈ 26 s against a 24 s nominal budget) — even though the
probe itself is "bounded."

## The fix (designed, not yet landed)

Gate the new bounded probe attempt on a cheap, purely structural, local
signal that is available before spending any time: **the query is not
difference-logic shaped** — i.e., the same test `dl_online::scan_dl` already
applies (its `None` is exactly `dl-online`'s "not-applicable" outcome above).
When it is not DL-shaped, `dl-online` (if it ran at all) declined for free
and the nominal budget is intact, so it is safe to spend an explicit, capped
budget (≥ 8 s, based on the measured floor with margin) trying
`check_qf_lia_online_cdclt` before declining. When it *is* DL-shaped, skip
the probe and decline immediately exactly as today — that is precisely the
population (real `QF_IDL`/`QF_RDL` oversized files) whose reserve `dl-online`
already spent.

This needs a small crate-visibility change in `dl_online.rs` (exposing the
shape test, e.g. `pub(crate) fn is_difference_logic_shape` wrapping the
existing private `scan_dl`) so `dpll_lia.rs` can call it without duplicating
or re-deriving `dl-online`'s own acceptance criteria — duplicating that logic
independently would risk silently diverging from what `dl-online` actually
accepts.

Not yet implemented: the `dpll_lia.rs` gate + bounded probe call, the
`dl_online.rs` visibility change, before/after re-measurement of both target
files plus the QF_LIA reference-only population
(`bench-results/parity-losses-20260905/QF_LIA.txt` + the two target files),
and confirmation that `bcnscheduling105.smt2` (and `lpsat-goal-18.smt2`,
which per the baseline above does not even reach this code path) are
unaffected.

## Notes for the resumer / self

- `lpsat-goal-18.smt2` does **not** exercise `arith_dpll_admission_preflight`
  at all (see baseline table). Non-negotiable outcome 4 in the brief is
  satisfied by construction once the gate above is scoped to the
  `exceeds_pre_sat_skeleton_boundary` branch only — there is no interaction
  to protect, but it should still be re-run after the fix lands as a direct
  check (identical verdict/timing expected).
- `bcnscheduling105.smt2` is the concrete regression control for "the
  dispatch overrun does not come back": before = 18.07 s decline, after must
  stay close to that (not jump toward 18 + 8 = 26 s).
- Two scratch, uncommitted example binaries were used for diagnosis only and
  must not be committed: `probe_bound_experiment.rs` and `dispatch_probe.rs`
  (both temporarily added under a scratch copy of the tree on s6/s7, never
  this worktree).
- `bench-results/parity-losses-20260905/QF_LIA.census.tsv`'s `class` column
  is flagged unverified as of `b57800c06`/`f3ce8ef58` (S3 loss census
  correction, not yet confirmed for `QF_LIA`) — the `.txt` file list itself
  (used for the before/after population count) is unaffected.

<!-- plan-section: landed-changes -->

| 2026-09-06 | *(this commit)* | Baseline measured before any code change: current (post-S2) dispatch declines both `ex3000_2400_100.smt2` and `ex4320_2400_100.smt2` in ~0.05 s (no probe ever runs); `QF_IDL/sal/lpsat/lpsat-goal-18.smt2` does not exercise the admission preflight at all (decided by genuine search, 7.25 s). Direct calls to `check_qf_lia_online_cdclt` show both target files need ≥7 s of the probe's own budget to refute via a decisions=0 root-propagation fixpoint, and consume however much larger a budget they are given rather than converging to one intrinsic time. `explain_corpus` route-attempt tracing shows why an unconditional bounded-probe-before-decline would be unsafe: `dl-online` declines in ~20 ms (`not-applicable`) for the two target files but spends its full ~18 s reserve (`budget` exhausted) for a real oversized `QF_IDL` file (`bcnscheduling105.smt2`) that hits the same admission constant — so the fix gates the new probe attempt on "not difference-logic shaped," reusing `dl_online::scan_dl`'s own acceptance test rather than an unconditional or purely time-proportional budget. |
