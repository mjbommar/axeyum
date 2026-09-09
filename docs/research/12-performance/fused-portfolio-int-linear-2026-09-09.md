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
- Measured yield at two workers: **one file converted reliably, one marginally**
  of the four in scope. Two more are blocked by a reserve ABOVE the group, and
  three of the brief's seven files are decided by the current tree with no
  portfolio at all.

## What the seven files actually are, re-measured on an idle host

Every row below is the shipped front door at the 24 s competition budget, twice
per arm, on `s5` (`taskset -c 0-7`, load 1.0 at both ends). "w1" is the shipped
default; "w2" is `AXEYUM_PORTFOLIO_WORKERS=2`.

| file | division | w1 | w2 | what it is |
|---|---|---|---|---|
| `182-incremental_scheduling-17280-0` | QF_LIA | unknown 24.1 s ×2 | **sat 7.9 / 8.1 s** | the group's case |
| `queen42-1` | QF_IDL | unknown 25.0 s ×2 | **sat 21.9 s**, unknown ×1 | the group's case, marginal |
| `super_queen61-1` | QF_IDL | unknown 21.2 s ×2 | not reached | blocked by `dl-online`'s reserve |
| `super_queen83-1` | QF_IDL | unknown 21.4 s ×2 | not reached | blocked by `dl-online`'s reserve |
| `hash_sat_08_05` | QF_UFLIA | **sat 18.4 s ×2** | sat 18.3 s ×2 | **already decided** |
| `fischer6-mutex-17` | QF_RDL | **unsat 15.8 / 16.1 s** | unsat 15.6 / 15.9 s | **already decided** |
| `orb06_900` | QF_RDL | **unsat 14.8 / 14.6 s** | unsat 15.1 s | **already decided** |

Three of the seven are not lost. The measurement that produced the brief was
taken on contended hosts — the oracle's own README says every timing in it is
advisory — and `hash_sat_08_05`, the file the earlier note called "the confirmed
middle-band case", is `sat` in 18.4 s on an idle box with no portfolio. That is
the same hazard the parent note already recorded at a larger scale ("141 of the
403 loss files are already decided"), reappearing four days later on a
seven-file list.

**Re-measure a loss list on the host you will report from, before building for
it.** Not because the earlier measurement was careless — it says so itself —
but because a list of losses is a claim with a short half-life in a tree this
active.

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

`super_queen61-1` and `super_queen83-1` are **not** collected, and the reason is
worth more than the two files.

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
