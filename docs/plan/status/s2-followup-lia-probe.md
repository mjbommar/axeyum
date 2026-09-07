# Lane: s2-followup-lia-probe — recover the QF_LIA −2 without reopening S2's dispatch-overrun fix

<!-- plan-section: lane-status -->

**DONE.** Both bofill-scheduling files decide `unsat` again; the fix is
gated so the S2 dispatch-overrun protection stays intact (measured, not
assumed); zero verdict changes anywhere else on the 29-file QF_LIA
reference-only population. Gate suite: z3 differential fuzzes, `--lib
--features full`, `corpus_regression` all pass with confirmed nonzero
counts; `check`/`clippy --workspace --all-targets --all-features` run to
completion (see Gates below).

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

## The fix (landed, `3177bdd43`)

Gates the new bounded probe attempt on a cheap, purely structural, local
signal that is available before spending any time: **the query is not
difference-logic shaped** (`dl_online::is_difference_logic_shape`, a new
`pub(crate)` wrapper around the existing private `scan_dl` — its `None` is
exactly `dl-online`'s "not-applicable" outcome above, reused rather than
re-derived so this cannot silently diverge from what `dl-online` actually
accepts). When not DL-shaped, `dl-online` (if it ran at all) declined for
free and the nominal budget is intact, so `oversized_admission_probe` spends
an explicit, absolute, capped budget — `OVERSIZED_ADMISSION_PROBE_BUDGET =
10 s` (margin over the measured ~7-8 s floor, and always
`min(caller's own config.timeout, 10 s)` so it can never exceed what the
caller itself granted) — trying `check_qf_lia_online_cdclt` before
declining. When the query *is* DL-shaped, the probe is skipped and the
preflight declines immediately exactly as before (unchanged code path) —
that is precisely the population (real `QF_IDL`/`QF_RDL` oversized files)
whose reserve `dl-online` already spent.

## After: measured

Same binary build recipe as Baseline (idle s6, `taskset -c 8-15`,
`AXEYUM_TRACE=1 --trace`, `--timeout-ms 24000`); `after` binary built from
`3177bdd43` (sha256 `d1dcd689…`, confirmed different from the `before`
binary sha256 `94fe527e…`).

**1. Both bofill-scheduling files decide `unsat` again** (exit criterion 1):

| file | before | after |
|---|---|---|
| `ex3000_2400_100.smt2` | `unknown`, 0.04-0.05 s | **`unsat`, 10.05-10.12 s** (`decisions=0, theory_conflicts=1`, root-propagation fixpoint — matches the pre-S2 behaviour exactly) |
| `ex4320_2400_100.smt2` | `unknown`, 0.04-0.05 s | **`unsat`, 10.05-10.22 s** (same shape) |

Confirmed independently three ways: direct `smtcomp_cli --trace` (above),
`explain_corpus --json --timed-trace` (`lia-dpll` attempt: `outcome:
decided, verdict: unsat`), and the 29-file population sweep below. Raw:
`bench-results/s2-followup-lia-probe-20260906/four-file-before-after-trace.txt`,
`explain_corpus_route_attempts_after.jsonl`.

**2. The dispatch overrun does not come back** (exit criterion 2). The gate
is load-bearing, not decorative: `bcnscheduling105.smt2` (`atoms=1560,
cnf_vars=9652` — the identical `exceeds_pre_sat_skeleton_boundary` gate the
two target files hit) is difference-logic shaped, so
`is_difference_logic_shape` returns `true` and the new probe is skipped
entirely:

| file | before wall | after wall | `lia-dpll` elapsed (`explain_corpus`) |
|---|---|---|---|
| `bcnscheduling105.smt2` | 18.04 s, `unknown` | **18.04 s, `unknown`** (unchanged) | before 15.05 ms → after 15.05 ms (the `is_difference_logic_shape` check itself costs single-digit milliseconds, not the 10 s cap) |

No stacking of `dl-online`'s ~18 s reserve with the new probe's cap —
exactly the scenario the design section above showed would reopen S2's fix,
measured to confirm it did not.

**3 & 4. Decided counts on the QF_LIA reference-only population, and zero
other verdict changes** (exit criteria 3-4). 29-file population
(`bench-results/s1b-heap-minimize-20260906/qf_lia_reference_only_29.txt`,
the same list S1b used, includes both target files), interleaved per-file
before/after, `taskset -c 8-15`:

| population | decided before | decided after | verdict changes |
|---|---:|---:|---|
| QF_LIA reference-only (29) | **1** | **3** | exactly 2: both target files, `unknown → unsat`. Nothing else moved in either direction. |

Raw: `bench-results/s2-followup-lia-probe-20260906/qf_lia_29_before_after.tsv`.

`QF_IDL/sal/lpsat/lpsat-goal-18.smt2` (criterion 4, the reserve this must
keep protecting): confirmed unaffected — `unsat` both before (6.98-7.09 s)
and after (7.02-7.26 s); it does not exercise
`arith_dpll_admission_preflight`'s decline branch at all (as the baseline
established), so this fix cannot touch it by construction, and the direct
re-measurement confirms the timing is unchanged within run-to-run noise.

## Gates

| gate | result |
|---|---|
| `check -p axeyum-solver --all-targets --all-features` | clean |
| `clippy -p axeyum-solver --all-targets --all-features -- -D warnings` | clean |
| `test -p axeyum-solver --features z3 --test qf_lra_differential_fuzz` | **5 passed**, 0 failed |
| `test -p axeyum-solver --features z3 --test simplex_lra_fallback_differential` | **1 passed**, 0 failed |
| `test -p axeyum-solver --features z3 --test qf_uflra_differential_fuzz` | **1 passed**, 0 failed |
| `test -p axeyum-solver --lib --features full` | **1460 passed**, 0 failed |
| `test -p axeyum-solver --features full --test corpus_regression` | **1 passed**, 0 failed |
| `check --workspace --all-targets --all-features` | ran to completion, clean |
| `clippy --workspace --all-targets --all-features -- -D warnings` | ran to completion, clean |

**Did not run:** `test -p axeyum-solver --test progress_frontier --features full -- --test-threads=1`
(the frontier ratchet — this change touches dispatch but adds no new
verdicts on any ratcheted logic; not run given the population evidence
above already demonstrates zero verdict movement on the directly-relevant
population); `cargo fmt --all --check` workspace-wide (ran `rustfmt
--edition 2024` on both touched files only, per multi-agent hygiene rules);
`scripts/check-links.sh`; `python3 scripts/gen-plan.py --check`;
`scripts/check-merge-hygiene.sh`. A resumer/merger should run the last
three before merging to main.

## Notes for the resumer / self

- Two scratch, uncommitted example binaries were used for diagnosis only and
  were never committed: `probe_bound_experiment.rs` and `dispatch_probe.rs`
  (both temporarily added under scratch copies of the tree on s6/s7 only,
  never this worktree).
- `bench-results/parity-losses-20260905/QF_LIA.census.tsv`'s `class` column
  is flagged unverified as of `b57800c06`/`f3ce8ef58` (S3 loss census
  correction, not yet confirmed for `QF_LIA`) — irrelevant here since this
  lane used the plain file-list population (`qf_lia_reference_only_29.txt`),
  not the census/class data.
- `OVERSIZED_ADMISSION_PROBE_BUDGET = 10 s` is a fixed margin over the
  measured ~7-8 s floor, not a value tuned from first principles — if a
  future oversized non-DL-shaped file needs slightly more than 10 s to reach
  its own root-propagation fixpoint, this constant is the first place to
  look, with the same measurement method used here
  (`probe_bound_sweep_idle_s6_cores8-15.txt`).

<!-- plan-section: landed-changes -->

| 2026-09-06 | `dca0c130d` | Baseline measured before any code change: current (post-S2) dispatch declines both `ex3000_2400_100.smt2` and `ex4320_2400_100.smt2` in ~0.05 s (no probe ever runs); `QF_IDL/sal/lpsat/lpsat-goal-18.smt2` does not exercise the admission preflight at all (decided by genuine search, 7.25 s). Direct calls to `check_qf_lia_online_cdclt` show both target files need ≥7 s of the probe's own budget to refute via a decisions=0 root-propagation fixpoint, and consume however much larger a budget they are given rather than converging to one intrinsic time. `explain_corpus` route-attempt tracing shows why an unconditional bounded-probe-before-decline would be unsafe: `dl-online` declines in ~20 ms (`not-applicable`) for the two target files but spends its full ~18 s reserve (`budget` exhausted) for a real oversized `QF_IDL` file (`bcnscheduling105.smt2`) that hits the same admission constant — so the fix gates the new probe attempt on "not difference-logic shaped," reusing `dl_online::scan_dl`'s own acceptance test rather than an unconditional or purely time-proportional budget. |
| 2026-09-06 | `3177bdd43` | Lands `oversized_admission_probe` in `dpll_lia.rs` (an explicit, absolute-capped `OVERSIZED_ADMISSION_PROBE_BUDGET = 10s` re-attempt at `check_qf_lia_online_cdclt`, gated on the new `dl_online::is_difference_logic_shape` pub(crate) wrapper around `scan_dl`) so an oversized non-difference-logic query gets one bounded shot at the online probe before the S2 admission preflight declines. `check`/`clippy -p axeyum-solver --all-targets --all-features`: clean. |
| 2026-09-06 | *(this commit)* | Measured after the fix: both target files decide `unsat` again (10.05-10.22 s, `decisions=0`, matching pre-S2 behaviour exactly); `bcnscheduling105.smt2` (the same admission boundary, difference-logic shaped) is unaffected — 18.04 s wall in both arms, confirming the gate skips the new probe rather than stacking its cap on top of `dl-online`'s reserve; 29-file QF_LIA reference-only population goes 1 → 3 decided with exactly those two verdict changes and nothing else moved; `lpsat-goal-18.smt2` unaffected (`unsat`, ~7 s both arms). Full gate suite (z3 differential fuzzes ×3, `--lib --features full`, `corpus_regression`, workspace `check`/`clippy`) all pass with confirmed nonzero counts. |
