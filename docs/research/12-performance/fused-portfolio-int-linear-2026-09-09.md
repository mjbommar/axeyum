# The fused portfolio, built small — and what the seven "middle-band" files
# turned out to be

Lane `portfolio-build`, 2026-09-09. Implementation note plus the measurement
that decides whether to turn it on.

Read [the portfolio answer](the-portfolio-answer-is-not-yet.md) first. This lane
was dispatched on its REVERSED conclusion — eight middle-band files, seven
reproducing, "build it, small". What follows both builds the thing and reports
that the file list underneath the brief had moved again.

## The headline

- The fused-group primitive is in (`crates/axeyum-solver/src/portfolio.rs`),
  with a cooperative stop (`axeyum_ir::stop`) that is the part with no prior art
  in this tree.
- One group is wired: `{lia-dpll, int-blast-ladder}` at the rung where
  `dispatch_int_linear_refuters` today returns `lia-dpll`'s `Unknown` as
  terminal.
- **Default is one worker, and at one worker no group is constructed at all.**
  The shipped path is the pre-portfolio path, not an equivalent of it.
- Measured yield at two workers, on the seven files the brief named: **one
  converted 3 of 3, one converted 2 of 3, two blocked by a reserve ABOVE the
  group, and three already decided by the current tree with no portfolio at
  all.**
- Measured yield on the **divisions**, which is the number that decides it, over
  **complete** sweeps of both (300 paired files): **+6 files, -0, zero verdict
  disagreements, zero aborts, one decided file more than half a second slower.**
  Five of the six gains are files the brief never named, the whole wall-clock
  cost sits on files lost at both worker counts, and on files we DECIDE two
  workers are net faster.

## What the seven files actually are, re-measured on an idle host

Every row is the shipped front door at the 24 s competition budget, **three runs
per arm**, on `s5` (`taskset -c 0-7`, load 1.8-2.1 at both ends, nothing else on
those cores). "w1" is the shipped default; "w2" is
`AXEYUM_PORTFOLIO_WORKERS=2`. Both arms are the SAME binary, so a difference
cannot be a build difference.

| file | division | w1 (x3) | w2 (x3) | verdict on the file |
|---|---|---|---|---|
| `182-incremental_scheduling-17280-0` | QF_LIA | unknown 24.13 / 24.13 / 24.13 s | **sat 8.12 / 8.11 / 7.91 s** | **converted, 3 of 3** |
| `queen42-1` | QF_IDL | unknown 25.03 / 25.03 / 25.03 s | **sat 21.73 / 21.73 s**, unknown 25.03 s | **converted, 2 of 3** |
| `super_queen61-1` | QF_IDL | unknown 21.23 / 21.23 / 21.23 s | unknown 24.13 / 24.23 / 24.23 s | not collected |
| `super_queen83-1` | QF_IDL | unknown 21.43 / 21.43 / 21.42 s | unknown 24.23 / 24.43 / 24.43 s | not collected |
| `hash_sat_08_05` | QF_UFLIA | **sat 18.32 s x3** | sat 18.32 s x3 | **already decided** |
| `fischer6-mutex-17` | QF_RDL | **unsat 15.52 / 15.92 / 15.42 s** | unsat 15.72 / 15.62 / 15.82 s | **already decided** |
| `orb06_900` | QF_RDL | **unsat 14.52 / 14.52 / 14.42 s** | unsat 14.42 / 14.72 / 14.62 s | **already decided** |

Three of the seven are not lost by the current tree. The measurement that
produced the brief was taken on contended hosts -- the oracle's own README says
every timing in it is advisory -- and `hash_sat_08_05`, which the earlier note
called "the confirmed middle-band case", is `sat` in 18.3 s on an idle box with
no portfolio at all, reproducibly, in all six runs here.

**Re-measure a loss list on the host you will report from, before building for
it.** Not because the earlier measurement was careless (it says so itself) but
because a list of losses has a short half-life in a tree this active. The parent
note recorded the same hazard at larger scale four days earlier -- "141 of the
403 loss files are already decided" -- and it reappeared on a seven-file list.

## The whole-division effect — the number that decides whether to turn it on

Seven files is not the question; *what the group does to the divisions it sits
in* is. Same A/B (one binary, `AXEYUM_PORTFOLIO_WORKERS` the only difference),
one run per arm, over the committed 200-file `bench-results/parity-lists/`
samples. Hosts held steady throughout (`s7` load 2.1-2.3, `s6` load 1.9-2.0),
so these frames are clean.

Both sweeps are **complete**.

| division | paired files | decided w1 | decided w2 | gained | **lost** | verdict disagreements | aborts | decided files >500 ms slower | total wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| QF_LIA | 200 of 200 | 119 | **123** | **+4** | **0** | 0 | 0 | **0** | -1.2 % |
| QF_IDL | 100 of 100 | 54 | **56** | **+2** | **0** | 0 | 0 | **1** | +2.6 % |
| **total** | **300** | **173** | **179** | **+6** | **0** | **0** | **0** | **1** | |

The gains:

| file | w1 | w2 |
|---|---|---|
| `QF_LIA/2019-ezsmt/incrementalScheduling/182-incremental_scheduling-17280-0` | unknown 24.12 s | sat 8.11 s |
| `QF_LIA/bofill-scheduling/SMT_random_LIA/ex20400_2600_100` | unknown 24.12 s | sat 8.11 s |
| `QF_LIA/bofill-scheduling/SMT_random_LIA/ex27000_2600_100` | unknown 24.12 s | sat 8.11 s |
| `QF_IDL/20210312-Bouvier/vlsat3_i08` | unknown 18.13 s | sat 20.93 s |
| `QF_LIA/checkpass_pwd/prp-0-19` | unknown 24.12 s | sat 11.12 s |
| `QF_IDL/ConnectedDominatingSet/rand_55_250_1235855873_0_k=8_sat.gph` | unknown 25.13 s | sat 12.93 s |

**Five of the six are files the brief did not name**, which is the more useful
half of this table: the group is not a fix for a hand-picked list, it is a
policy over a rung, and the rung has more traffic than the oracle's
`decided alone` column found. (The oracle runs one route per process on the flat
assertion view; it cannot see a route the shipped front door reaches with a
different query, which is the same blind spot its own README declares.)

### Where the wall clock goes, which is the whole cost story

A single per-division wall percentage hides the only distinction that matters,
so both completed sweeps are decomposed by outcome:

| division | population | files | wall delta at two workers |
|---|---|---:|---:|
| QF_LIA | lost at **both** worker counts | 77 | +88.8 s |
| QF_LIA | decided at **both** | 119 | **-52.1 s** |
| QF_IDL | lost at **both** | 44 | +39.8 s |
| QF_IDL | decided at **both** | 54 | +1.4 s (26 ms per file) |

**The cost is entirely on files we lose either way**, and it is the ladder
*spending* budget it previously left on the floor: on QF_IDL those files go from
~21.2 s to ~24.3 s because `dl-online` ends at 21 s and the ladder today gives
up with 2.6 s unspent. A lost file is charged the whole budget by PAR-2 and
killed at the wall by the harness whichever way it ends, so those seconds buy
nothing and cost nothing.

**On files we decide, two workers are FASTER in QF_LIA (-52.1 s over 119 files)
and flat in QF_IDL (+1.4 s over 54).** Across both divisions exactly **one**
decided file is more than half a second slower -- `wire.10.x.10.b.5.a.20_unsat`,
16.5 s -> 18.8 s. That single number is what a portfolio actually has to defend.
It is what the cooperative stop exists to hold down: without the stop every one
of those 173 decided files would have waited for the losing arm's deadline.

**Nothing was lost, nothing disagreed, nothing aborted, and no decided file got
materially slower.** That last column is the one a portfolio is supposed to
threaten — a losing arm holding the group open past the winner — and the
cooperative stop is why it is zero. Total wall clock is *down* slightly in
QF_LIA, because a file that returns in 8 s instead of spending 24 pays for the
contention everywhere else.

**Coverage is complete for both divisions** -- 200 of 200 QF_LIA, 100 of 100
QF_IDL, on frames that held steady end to end (QF_LIA load 1.67 -> 2.07, QF_IDL
1.59 -> 1.98); the rows are
the committed list in order, not a sample chosen after the fact, and the harness
writes each pair as it completes. A larger denominator can only add files; it
cannot retract the four gains or the zero losses already recorded.

## What the winning arm actually is, and why "three routes" was one route

The solo oracle records `lra-dpll`, `nra` and `qf-bv` all deciding the QF_IDL
and QF_LIA files. They are one computation behind three doors: on an `Int` query
`check_with_lra_dpll` and `check_with_nra` fall through to the bounded integer
blast, and their decline text says so —

```
lra-dpll  unknown  "no model within the bounded integer width 32; widen the bound"
nra       unknown  "no model within the bounded integer width 32; widen the bound"
```

on `0 < 2x < 2`, which is real-satisfiable and integer-unsatisfiable. Neither
relaxes integers to reals; both blast. So the arm to add is the blast, not
either of those names, and the shipped arm is the tree's own
`dispatch_int_blast_width_ladder` — whose `Sat` is replay-checked and whose
`Unsat` only fires on an integer-free residue. Calling `check_with_all_theories`
directly (as the solo prober does) would be a second hand-rolled copy of that
soundness reasoning.

This is the same shape the parent note recorded for `QF_ABV` — four "routes"
deciding two files turned out to be one computation through four entry points —
and it is worth stating as a rule: **a per-route oracle counts entry points, not
engines.** Before sizing a portfolio from one, check whether its rows are the
same code.

## Why a reservation cannot collect these files

The measured reason, per file:

- `182-incremental_scheduling`: the ladder spends **23,993 ms of 24,000 inside
  `lia-dpll`**, which declines. There is no slack to reserve. Any reserve big
  enough for the blast (8.7 s) comes straight out of the route that decides the
  rest of QF_LIA.
- `queen42-1`, `super_queen61-1`, `super_queen83-1`: `dl-online` takes
  **21.0 s** of the 24 s budget (`dl_probe_budget` plus the extended probe) and
  declines; `lia-dpll` then declines on an admission bound in 0.24 s; the ladder
  gives up at 21.4 s with 2.6 s unspent. The blast needs 16-17 s.

Two arms on two cores each get the whole budget. That is the whole argument, and
it is why the group is a group rather than a fifth `LadderSlice`.

## What the group does NOT collect, and the reason is a reserve above it

`super_queen61-1` and `super_queen83-1` are **not** collected -- measured, three
runs each, `unknown` at both worker counts -- and the reason is worth more than
the two files.

The group's clock is what is LEFT of the dispatcher's entry deadline. It has to
be: unclamped, the group would start at t = 21 s (after `dl-online`) and run its
arms for a further 24 s, answering at 45 s — past a wall the competition harness
enforces by killing the process, which scores as a loss whatever the arms found.
Clamped, the group inherits the 2.6 s `dl-online` left it, and 2.6 s does not
blast a 19,501-node query.

So on those two files the binding constraint is **`dl-online`'s reserve, one
rung above the group**, not the group's own scheduling. Collecting them needs
`dl-online` fused as a third arm — a second group, higher up — which is a
different change from this one and is left named rather than half-built.

That is the parent note's own thesis arriving from the other direction: *a
reserve is zero-sum over one clock.* Adding a portfolio at rung N does nothing
about a reserve at rung N-1 that has already spent the clock.

## The stack overflow, which no verdict comparison could have found

The first raced run of `super_queen61-1` did not return a verdict. It printed

```
thread '<unknown>' has overflowed its stack
fatal runtime error: stack overflow, aborting
```

and exited 134, where the sequential ladder on the same file returned `unknown`.

`smtcomp_cli` runs the whole solve on a 512 MiB worker precisely because a
deeply nested input otherwise turns a decline into an abort. `std::thread::scope`
hands a spawned thread the platform default — 2 MiB — and an arm runs the *same*
routes on the *same* query. `portfolio::ARM_STACK_BYTES` is now 256 MiB per arm
(a reservation, not residency; two arms cost the same address space as the one
worker the harness already creates), and
`an_arm_gets_a_deep_stack_not_the_platform_default` runs an arm that consumes
6 MiB of stack and requires a verdict back.

The general form: **an abort is worse than an `unknown` and is invisible to every
check that compares verdicts, because there is no verdict to compare.** A
portfolio's tests have to include at least one that fails by killing the test
binary.

## The degeneracy property, and why the obvious test for it is vacuous

The claim is *"with one worker the sequential path is byte-identical to the
pre-portfolio path"*. The obvious check — run a corpus at one worker and at two
and compare verdicts — **cannot establish it**: two paths agreeing on every
answer is exactly what a *correct* portfolio also looks like, so the comparison
passes whether the group ran or not.

So the property is enforced structurally (`dispatch_int_linear_refuters` does
not construct a group at one worker; it makes the call it always made) and
checked by **counting**: `portfolio_groups_run()` must not move across a batch of
integer queries at the default setting. That assertion dies the moment someone
"simplifies" the wiring into always building a one-arm group, which is the edit
the property exists to forbid.

The counter is thread-local, and that is load-bearing: the process-global first
version was moved by sibling test cases racing their own groups, and the failure
read as a broken degeneracy property rather than a broken instrument.

## Determinism, precisely

- **The verdict is stable.** Every decisive arm result is collected and the
  winner is chosen by **declared arm order**, never by finishing order. On a
  query both arms decide, the group returns `lia-dpll`'s verdict — the one the
  sequential ladder would have returned.
- **The attribution may vary.** Which arms reached a verdict before the group
  stopped them depends on the machine. A route trail from a multi-worker group
  is a record of this run, not a reproducible one. The trail is emitted in
  declared order so its shape is stable even though its contents are not.

Two arms returning **different** decisive verdicts is a soundness defect in one
of them and the group refuses to choose: it returns `SolverError::Backend`
naming both. The check is at top-level dispatch granularity — an arm is one
whole route invocation on one query, not a refinement round.

## Memory

A competition limit is per **process**, so N arms share one limit — `limit / N`
per arm, never `N x limit`. Each arm's `SolverConfig::memory_limit_mb` is set to
its share, so the per-arm encoding ceilings refuse at a size the arm can afford
beside its siblings. The process-wide sticky watchdog still samples the whole
process, so if the arms together exceed the limit it trips for **all** of them
and every arm declines with a `MemoryLimit` `unknown`. That is the conservative
direction — the group returns `unknown`, never a verdict — and it is why a group
stays at two or three arms rather than being sized to the core count.

`wchains140se` already aborts at 8 GiB with a single arm. Nothing here improves
that; at two arms it declines earlier, which is the same loss reported sooner.

## Cancellation, and why it needed a new primitive

Every route derives its deadline from `config.timeout` **at entry**, so a
coordinator had no channel into a running arm. That left two bad options: join
every arm (a wall-clock regression on every file the ladder already wins) or
abandon the losing threads — which bounds *time* and not *memory*, and an
abandoned route that keeps allocating is how one test in this repository reached
125 GB.

`axeyum_ir::stop` is a thread-local cooperative token. The 13 `past_deadline`
helpers in `axeyum-solver` now delegate to one authority instead of each owning a
copy, and the CDCL(T) driver and LIA DPLL loops consult it. `axeyum-cnf` — where
a bit-blasting arm spends its wall time — gets `interrupt::set_stop_hook` rather
than a dependency on the term IR: that crate must not learn about terms for one
`bool`. One source of truth, no new crate-graph edge.

Observing a stop can only turn a search into `unknown`, since it is read at sites
that already answer an expired deadline that way. The winner never has one
requested on it.

Measured effect of the stop, from the mutation table below: with the request
removed, the group's own liveness test goes from 0.00 s to 30.00 s. That is the
whole regression the mechanism prevents, on one test.

## The gate that went red, and why it was the frame and not the change

`cargo test -p axeyum-solver --test progress_frontier --features full` failed on
`frontier_bv_reduction` with

```
TIMING REGRESSION [bv_reduction]: pinned N=[12, 15, 18] took 2354.2 ms
calibrated, over the committed ceiling of 2264.3 ms
```

The same run reported `FRONTIER bv_reduction = 34 (baseline 30), PROGRESS`, so
it is a **timing** finding and not a capability one, and the arithmetic points
at one pin: `N=18` took 2138.9 ms against a committed 804.9 ms while `N=12` was
*faster* than committed (109 vs 167 ms) and `N=15` unchanged. A uniform slowdown
would move all three.

That is a shape, not a proof, so it was measured rather than argued. Re-run of
that one family alone, same commit, on a quiet host (`s5`, `taskset -c 8-15`):

```
FRONTIER bv_reduction = 34 (baseline 30), PROGRESS (+4 over baseline, ratchetable)
  reference frame: load 2.09 -> 2.06, scale 1.18x, comparable: true, ratchetable: true
TIMING bv_reduction = 1139.1 ms calibrated over pinned N=[12, 15, 18]
  (baseline median 1293.1 ms, ceiling 2264.3 ms)   verdict: ok
  pinned: N=12 100.3 ms, N=15 358.9 ms, N=18 679.9 ms
```

**1139.1 ms — below the baseline MEDIAN, half the ceiling, with the ratchet
enforced.** The failing run was taken on `s4` with another lane's sweep and a
workspace clippy resident: load 8.93 at the start, 10.06 at the end of the
family, 22.5 by the time the suite finished. The frame's own `comparable: true`
was computed from a calibration that happened to land in band *before* the load
climbed, which is the one thing the calibration cannot catch — it samples at the
ends, and this contention arrived in the middle.

Two consequences worth carrying:

- **`comparable: true` is a statement about the calibration samples, not about
  the run.** A run whose load doubles between the two samples can still be
  marked comparable. Read `load_start` and `load_end` yourself; if they differ by
  more than a little, the flag is describing something narrower than you want.
- The five `bench-results/frontier/*.json` frames this lane's runs rewrote are
  **reverted, not committed**. A contaminated frame committed as a baseline is
  how a roadmap floor gets ratcheted down on a bad reading, and this file names
  the incident where that happened.

## Gates at this commit

| gate | result |
|---|---|
| `check-clippy-complete.sh` | 840 of 840 workspace targets, 27 of 27 crates, **0 diagnostics** |
| `cargo fmt --all --check` | clean |
| `cargo doc --workspace --all-features --no-deps`, `RUSTDOCFLAGS=-D warnings` | clean |
| `cargo test -p axeyum-solver --lib --features full` | **1,662 passed, 0 failed** (an earlier run's single failure was `every_governing_constant_is_registered` demanding the two new constants; both are now in `config_registry`, and that gate is what forced them to be described rather than merely written) |
| `--test corpus_regression --features full` | 1 test, ok (nonzero count confirmed) |
| `--test portfolio_fused_group --features full` | 8 tests, ok |
| `--lib --features full portfolio::` | 9 tests, ok |
| `--test progress_frontier --features full` | 11 of 12; `frontier_bv_reduction` red on a contended frame and **ok on a clean one** (above) |
| `--features z3 --test qf_lra_differential_fuzz` | 5 tests, ok |
| `--features z3 --test simplex_lra_fallback_differential` | 1 test, ok |
| `--features z3 --test qf_uflra_differential_fuzz` | 1 test, ok |

The three z3 differentials are the only checks in this tree that compare our
verdicts against an independent solver, and they compile to ZERO tests without
`--features z3`. The counts above (5 / 1 / 1) are the documented expectation, so
the nonzero check is met rather than assumed. They are linear-REAL suites and
this change is in the integer-linear ladder, so what they cover here is the
shared `past_deadline` delegation the change routed through one authority --
not the group itself, which has no real-arithmetic arm.

## Mutations run

| mutation | expected to die | actually died |
|---|---|---|
| `int_linear_portfolio_workers() > 1` → `true` (always build a group) | the degeneracy count | `at_the_default_worker_count_no_fused_group_is_constructed_at_all` **and** `the_worker_guard_restores_the_previous_setting` — two tests, both asserting the same count, which is redundancy rather than a blind spot |
| winner chosen by finishing order rather than declared order | the determinism test | `two_arms_that_both_decide_yield_the_earlier_declared_one`, alone |
| never request a stop on the losing arms | the liveness test | `a_raced_group_returns_the_declared_order_winner_not_the_first_finisher`, alone — and the suite went from 0.00 s to 30.00 s |
| `ARM_STACK_BYTES` → 2 MiB (the platform default) | the deep-stack test | `an_arm_gets_a_deep_stack_not_the_platform_default`, alone, by SIGABRT |

## Reproducing

```sh
# one file, both arms, twice each
scripts/portfolio-ab.sh target/release/examples/smtcomp_cli <file-list> 24000 2 2 0-7

# the wiring's own tests (NONZERO count required; the suite is `full`-gated)
cargo test -p axeyum-solver --features full --test portfolio_fused_group
cargo test -p axeyum-solver --features full --lib portfolio::
```

`AXEYUM_PORTFOLIO_WORKERS=2` is the only switch. The default is 1.
