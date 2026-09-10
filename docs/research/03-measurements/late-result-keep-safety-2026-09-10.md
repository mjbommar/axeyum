# Is it safe to keep a QF_BV result that arrives after its deadline?

Roadmap item **3.9**, follow-on to
[`why-43-satisfiable-qfbv-miss-2026-09-10.md`](why-43-satisfiable-qfbv-miss-2026-09-10.md)
(lane B1). Lane D1, 2026-09-10, on `c35941f9b`.

B1 measured that `crates/axeyum-solver/src/sat_bv_backend.rs:327-333` discards a
**completed** SAT verdict because the clock passed *during the search that
produced it* — nine instances, two of them real SMT-LIB files through the
shipping front door, return `unknown` at a 10 s budget after spending 29-43 s and
`sat` at 300 s after spending the same time. B1 named the one thing that gates
the fix and did not run it:

> **Whether keeping a late result is safe under every route.** It is sound for
> `sat` on this path (replay against the original terms), and I did not examine
> the `unsat` side, the proof-carrying route, or the incremental façade.

This document is that examination. It is read out of the code, per verdict kind
and per route. **The conclusion is that keeping the result is safe, and that the
two things a reader would expect to be the risks — the `unsat` proof cost and
determinism — are both the opposite of the intuition.**

## The gate, and exactly what the fix is

```rust
// sat_bv_backend.rs:324-333
let mut sat_result =
    primary_sat_search(config, solve_formula, deadline, &mut stats, reduction);
stats.solve = solve_start.elapsed();
if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
    self.stats = Some(stats);
    return Ok(CheckResult::Unknown(UnknownReason {
        kind: UnknownKind::Timeout,
        detail: "pure-Rust BV backend timeout after SAT search".to_owned(),
    }));
}
```

The proposed change is to add one conjunct — fire only when there is **no
definite verdict to keep**:

```rust
if matches!(sat_result, SatResult::Unknown(_))
    && deadline.is_some_and(|deadline| Instant::now() >= deadline)
```

That is deliberately the smallest edit that answers the finding. Every
`SatResult::Unknown` sub-case keeps its present `UnknownKind::Timeout` and its
present detail string, so nothing downstream that reads either can move. Only
`Sat` and `Unsat` change, from *discarded* to *returned*.

**No test covers this gate.** `grep -rn "timeout after SAT search" crates/ tests/`
matches the source line and B1's note, nothing else. Deleting the gate outright
today kills zero tests. That is itself the reason a test has to land with the
change (below).

## 1. `sat` — the replay is the soundness gate, and it is not on the clock

The repository's hard rule is that every `sat` is checkable by evaluating the
**original** term against the lifted model. On this path that check is not a
convention; it is the only way a `Sat` can be returned.

`handle_sat_result` (`sat_bv_backend.rs:1975`) is the single construction site of
`CheckResult::Sat` in this function, and it cannot return one without running
`replay_model` first (`:2015`):

- `Ok(None)` — every original assertion evaluated to `Bool(true)`; the model is
  accepted.
- `Ok(Some(reason))` — the original term could not be *evaluated* (an `IrError`,
  e.g. an evaluator overflow). The model is **not accepted**; the caller returns
  a graceful `Unknown` (`:2017-2019`).
- `Err(..)` — an original assertion evaluated to `false`, or to a non-Boolean.
  That is a soundness alarm and surfaces as `SolverError::Backend`.

`replay_model` (`:2052`) has two arms and **both** consume the original terms:
with a `QueryPlan` it calls `plan.replay_original(arena, &assignment)`; without
one it loops the caller's `assertions` through the trust-anchor `eval` directly
(`:2072-2093`). There is no third arm, no "skip when the budget is gone", and no
`deadline` parameter anywhere in the function — `replay_model` cannot read the
clock because it is never given it.

**What replay covers:** the lifted model satisfies the original assertion terms
under the trust-anchor evaluator. That is a *total* check of the returned answer
against the question that was asked, and it is independent of everything
upstream of it — the bit-blasting, the Tseitin encoding, the CNF inprocessing
(subsumption/BVE) and its reconstruction stack, and the CDCL search itself could
each be wrong and a passing replay would still mean the returned model satisfies
the query.

**What replay does not cover:** it says nothing about `unsat`, and nothing about
`unknown`. It is a one-sided certificate — a witness. It also does not certify
*completeness* of the model: `complete_model` (`:2007`) fills symbols the
lowering never constrained, and replay only re-confirms the assertions, so a
symbol the query does not mention gets an arbitrary well-founded value. That is
the pre-existing contract and the clock does not touch it.

**Verdict: safe.** Wall-clock time is not an input to the replay, so a `sat`
that survives replay at t = 43 s carries exactly the assurance of one that
survives it at t = 4 s. The clock is not part of soundness on this route.

**Cost:** keeping a late `sat` does mean paying the model lift and the replay
*after* the deadline, because `handle_sat_result` sits below the gate. B1's own
tables bound this: on `pspace/ndist.b.20000` the backend row is total 28,038 ms
against solve 27,874 ms, so lift + replay is ~164 ms — against an overrun already
measured at 1.15x-8.01x of the budget. It is not skippable in any case: skipping
it would mean returning an unverified model, which this codebase does not do.

## 2. `unsat` — the proof check has ALREADY run when the gate is reached

The brief's hypothesis was that keeping a late `unsat` would mean *also* running
a DRAT check past the deadline, making it a cost question on top of a soundness
one. **It does not.** On the shipping path the proof check runs *inside*
`primary_sat_search`, i.e. strictly before the gate.

The chain, all in `sat_bv_backend.rs`:

- `primary_sat_search` (`:2297`) → `solve_with_native_cdcl` (`:2394`), passing
  `config.prove_unsat` as `check_proof`.
- On `ProofSolveOutcome::Unsat(proof)` with `check_proof` set (`:2413-2462`), the
  proof is verified **in place** — `link.check_unsat(original, formula, &proof,
  MAX_LINKED_PROOF_STEPS)` — and the result is stamped `SatProofStatus::Checked`.
  A proof that fails to check is conservatively downgraded to
  `SatResult::Unknown` right there.
- With `check_proof` unset the result is stamped `SatProofStatus::Unchecked` and
  nothing is verified (`:2416-2427`).

So by the time control reaches line 327, one of three things is already true:
the `unsat` is `Checked` (the check is paid, and it is inside `stats.solve`, as
`NativeCdclOutcome::proof_replay`'s own doc-comment records: *"nested within SAT
search time, not an additional sequential pipeline stage"*), or it is
`Unchecked` because the caller did not ask, or it is no longer an `unsat` at all.

`ensure_unsat_proof_checked` (`:2505`), which sits *below* the gate, is therefore
a no-op on every one of those three:

- `prove == false` → early return (`:2512`).
- `prove == true` and the status is `Checked` → `already_checked` early return
  (`:2515-2524`).
- the expensive re-derivation route (`verify_unsat_proof`, `:2557`, which
  re-solves the whole formula) is reachable only from an `Unsat` that is
  `Unchecked` **while** `prove` is set — a combination `solve_with_native_cdcl`
  does not produce. Its doc-comment names its caller: *"the batsat fallback (or
  any config still routing to batsat)"*, and that adapter is gone from the
  default build (ADR-1703).

**Verdict: safe, and free.** Keeping a late `unsat` adds no proof-checking work
at all — `CheckResult::Unsat` is returned by `handle_sat_result:2024` with no
further computation. The soundness question is likewise closed by construction:
a `Checked` `unsat` was verified against `encoding.formula()` (the formula this
backend built, not merely the inprocessed one it searched) before the clock was
ever re-read, and an unverifiable one was already downgraded.

The one honest caveat: with `prove_unsat` unset, a late `unsat` is `Unchecked` —
but so is a timely one. The keep does not lower assurance; it returns an answer
at exactly the assurance level the caller configured.

## 3. Incremental / warm sessions — the defect is not there, and the fix does not reach them

`IncrementalBvSolver` does not go through this code at all.
`grep -rn "SatBvBackend" crates/ --include=*.rs` finds no reference in
`incremental.rs`. The warm session runs its own SAT loop:
`solve_with_encoded_extra` (`incremental.rs:3752`) derives a deadline, and then
**checks it at the top of each refinement round, before the solve**
(`:3789-3795`), handing the round `deadline.saturating_duration_since(now)` and
calling `solve_cnf_profiled` → `IncrementalCnf::solve_with_limits`. The
`SatResult` that comes back is matched on directly (`:3798+`); there is no
post-search clock re-read and no discard.

That is the correct shape, and it is worth saying why: a deadline consulted
*before* committing to work is a budget; a deadline consulted *after* the work
completed is a tax on an answer already bought.

Consequences for this change:

- The warm push/pop contract is untouched. No warm state is mutated by the
  proposed edit, because the proposed edit is not on the warm path.
- The one place the two meet is `dpll_t.rs:264-279`, where `SkeletonSolver::new`
  picks a warm `IncrementalBvSolver` arm or a cold `SatBvBackend` arm for the
  same skeleton. The file's own comment states the invariant: *"the round's
  verdict cannot differ between them. Only the cost does."* Today that invariant
  is **violated by the gate** — the cold arm can discard a completed round
  verdict the warm arm would have kept, so the two arms can disagree on a
  boundary-crossing round. Removing the discard moves the cold arm towards the
  warm arm's behaviour, i.e. towards the documented invariant, not away from it.

**Verdict: safe. Not applicable, and the fix reduces a divergence rather than
introducing one.** No warm state is corrupted and no "a timed-out call left the
session unchanged" assumption is touched, because no warm call reaches the gate.

## 4. The portfolio — the verdict contract survives; the budget contract was already broken

There is exactly one multi-arm dispatcher, `FusedGroup` (`portfolio.rs:284`),
with one production call site (`run_int_linear_group`, `auto.rs:3268`) reached
from `dispatch_int_linear_refuters` (`auto.rs:3069`). Its default worker count is
**1** (`DEFAULT_INT_LINEAR_PORTFOLIO_WORKERS`, `auto.rs:3153`), and at one worker
no group is constructed at all — so the shipped default path is sequential and no
race exists. Its two arms are `lia-dpll` and `int-blast-ladder`
(`auto.rs:3228-3239`); `SatBvBackend` is reachable *underneath* the second, which
bit-blasts integers to bit-vectors.

Racing (`run_raced`, `portfolio.rs:393`): the coordinator drains **all**
`self.arms.len()` outcomes before choosing (`:471-487`) and `pick_winner`
(`:534`) scans by **declared** order, never finish order. A late arm therefore
cannot displace an earlier-declared one, and its answer is still fed to the
cross-arm disagreement gate, which raises `SolverError::Backend` on a genuine
`sat`/`unsat` conflict (`:557-565`). Turning a losing arm's discarded verdict
into a real one can, in principle, surface such a disagreement where today one
side said `unknown`. That is the right direction: it would be an existing
soundness bug being *reported* rather than a new one being created — and on the
`sat` side it cannot even be that, because a replayed `sat` is a witness.

Budget: the group has no deadline of its own (`rx.recv()` at `:473` is bare, the
joins at `:493-495` unconditional, and the stop tokens are cooperative), so group
wall time is `max(arm)`. In sequential mode `run_reserved:368-370` computes
`cumulative.saturating_sub(meter.spent())`, which an overrunning arm drives to
`Duration::ZERO`, starving the next arm. Both of these are **pre-existing and
independent of this change**: the overrun that starves the sibling is the *search
time*, which the gate does not shorten by one microsecond. What the gate does is
throw away the answer the overrun bought. The keep adds only the lift + replay on
a `sat` (~164 ms measured, §1).

The same is true of the other two budget-subdividing callers, and both are
strictly improved rather than harmed:

- `check_shared_guard_split` (`sat_bv_backend.rs:398`) gives each branch
  `remaining / remaining_branches`. If branch *k* overruns, branch *k+1* already
  gets a zero budget today. With the keep, branch *k* returning a late `sat`
  short-circuits the whole split to `sat` (`:437-448`, after its own independent
  `eval` of every original assertion — a **second** replay on top of §1's).
  Returning `unsat` leaves the starvation exactly as it is today.
- The lazy-SMT loop (`dpll_t.rs:439`) tests `past_deadline` at the **top** of
  each round, so a late `sat` costs at most one further `decide_cube` (itself
  deadline-bounded) before the loop bails — and may instead complete the answer.

**Verdict: safe.** No racing contract is broken and no budget is double-counted
by the keep. The budget defects that do exist in `portfolio.rs` are separate
findings, recorded here and not fixed by this lane.

## 5. Determinism — the keep makes the verdict *more* deterministic, not less

This is the question the brief flagged as subtlest, and the answer runs against
the intuition in the brief.

First, what the repository actually promises. `SolverConfig` carries two budgets
and documents exactly one of them as deterministic (`backend.rs:99-107`):

```rust
pub timeout: Option<Duration>,
/// Deterministic backend search budget; reproducible across machines and
/// preferred for bisecting blowups.
/// ...
pub resource_limit: Option<u64>,
```

`timeout` gets no such sentence, and could not: a wall-clock bound is
machine- and load-dependent by construction. The public determinism promise
("stable iteration order, explicit seeds, **explicit resource limits**") is
carried by `resource_limit`, which on this path becomes the CDCL core's
`max_conflicts` (`sat_bv_backend.rs:2402`) — a count, not a clock.

Second, the search trajectory. `solve_with_drat_proof_within`'s doc
(`proof_sat.rs:480-484`) states the invariant the current cadence exists to
protect: *"`deadline` is checked on a deterministic conflict cadence, so the
search trajectory up to the stopping point is identical to the unbounded run —
only whether it stops is time-dependent."* Nothing in the keep touches the
trajectory.

Third, the count that matters. Today the verdict depends on the wall clock at
**two** independent points:

1. inside the search, at `proof_sat.rs:3453` — whether the conflict-cadence
   deadline test fires;
2. after the search, at `sat_bv_backend.rs:327` — whether the clock passed
   during a search that already finished.

Removing (2) leaves (1). A verdict that depends on the clock at one point is
strictly more reproducible than one that depends on it at two, and (2) is the
worse of the two: it is a pure function of *how loaded the box was*, applied to a
search that already committed to an answer. Under (2), the same binary on the
same file with the same budget and the same seed returns `sat` on an idle host
and `unknown` on a busy one whenever the search time straddles the budget. That
is exactly "a result that varies with machine load", and it is the *present*
behaviour, not a risk of changing it.

On the measured class the improvement is total: B1 established that these
searches finish in **fewer than 256 conflicts**, so test (1) — which first fires
at conflict 1,024 — cannot fire at all. With (2) removed, the verdict on this
class becomes a pure function of `(formula, resource_limit)` with **no** clock
dependence whatsoever.

**Verdict: safe, and an improvement.** The keep strictly reduces the number of
points at which wall-clock time can change a verdict. It does not make the
`timeout` budget deterministic — nothing can — but it stops the budget from
converting a determined answer into an undetermined one.

## The gate is not one gate: a second discard sits one layer up

**This is the finding that changes the fix, and it is exactly the trap the item
warned about** — a change that only touches the site B1 named would be *inert on
the shipping front door*, while a green test suite said it worked.

`check_with_all_theories` (`combined.rs:61`) is the funnel every QF_BV front-door
route goes through (`auto.rs:5013`, `:5131` — the terminal `qf-bv` arm — plus
`auto.rs:6956`, `:7534`, `dpll_t.rs:299`, `:761`, `route_solo.rs:193`). It has
the **same defect**, and its version does not even look at the result first:

```rust
// combined.rs:133-137
let backend_config = config_with_remaining_deadline(config, deadline);
let result = backend.check(arena, int_blast.assertions(), &backend_config)?;
if past_deadline(deadline) {
    return Ok(timeout("combined-theory timeout after scalar backend"));
}
```

So on the front door there are **two** discards in series. Fixing only
`sat_bv_backend.rs:327` hands the kept verdict straight to `combined.rs:135`,
which throws it away again for the same reason. B1's front-door rows flip at
300 s because at 300 s *neither* gate fires; at 10 s both do.

And there are four more, on the path a kept `Sat` must then walk:
`combined.rs:162`, `:171`, `:183` (the three model projections) and `:208`
(inside the replay loop, per assertion). Each discards a `Sat` that has already
been decided. Leaving any of them in place also neuters the fix — a kept `sat`
would reach the replay loop, fail the very first `past_deadline`, and return
`timeout` anyway.

The boundary that resolves all five at once, and that this lane adopts: **once
the backend has returned a definite verdict, `check_with_all_theories` stops
consulting the deadline.** That is defensible because everything below that point
is the soundness anchor and nothing below it searches — three model projections
and one evaluation pass over the original assertions, all size-proportional,
already bounded by the query the caller submitted. Discarding their input does
not refund the time already spent; it only converts an answer into a non-answer.

## The decision has already been made once, in this codebase

`dispatch_reduced` (`auto.rs:2382`) — the preprocessed-dispatch route, and
`preprocess` defaults **on** — carries the identical fix already, with its
reasoning and its measurement written out at `auto.rs:2397-2411`:

> *"A DEFINITE verdict (Sat/Unsat) from the reduced solve is valid regardless of
> the wall clock — the deadline is a resource budget, not a correctness gate.
> Discarding a decided (and, for Sat, about-to-be-replay-checked) verdict just
> because the budget expired during the deciding route needlessly throws away a
> real answer: measured, `nia-bounded-blast` decides bounded nonlinear SATs like
> `nia-pythagorean` a hair past the budget, and the old unconditional
> `past_deadline` gate below turned that decided `sat` into `unknown`. Only an
> UNDECIDED (`Unknown`) result degrades to the timeout reason."*

Its shape is exactly the one proposed here:
`if matches!(result, CheckResult::Unknown(_)) && past_deadline(deadline)`.

So this is not a new principle being introduced; it is an accepted principle
that was applied at one layer and never propagated to the two below it. That
asymmetry is itself worth recording, which is why this lands as **ADR-1906**
rather than as a bare code change: stated once, with the per-route safety
argument above, and with the list of gates it governs, the next lane does not
have to re-derive it — and, more to the point, the next lane that *adds* a
post-solve deadline check has something to be inconsistent with.

For completeness, the other `past_deadline` gates in `auto.rs` that carry a
"timeout after X" reason (`:2520`, `:4970`, `:5653`, `:5676`, `:5701`) are **not**
this shape and are not touched: each fires after a route has already *declined*
(returned `Unknown`, or `None`), so there is no verdict in hand to discard. They
are ladder boundary checks — "the budget is gone, stop trying more routes" —
which is the correct use of a deadline.

## The interaction with the deadline-granularity fix, stated plainly

B1's second recommendation is to make the deadline cadence time-bearing so that a
propagation-bound search actually stops at its budget. **These two fixes point in
opposite directions on determinism, and that is worth being explicit about rather
than presenting them as unambiguously complementary.**

- The keep removes clock-dependence point (2), so *fewer* verdicts vary with load.
- A finer cadence makes clock-dependence point (1) fire where it never fired
  before, so *more* verdicts vary with load — but honestly, at the budget, and
  after paying only the budget.

They compose on the outcome the item cares about (decided counts at a stated
budget, and a budget that means something), and the composition is coherent: with
a real deadline, a search that is going to be cut off is cut off *before* it
finishes, and the keep then applies only to searches that genuinely completed
within a hair of the budget. Finer granularity makes late results rarer; it does
not make the keep worthless, because the granularity can never be perfect — any
cadence has a last check before the end.

The precedent for the granularity fix is already in the file, added for the
theory core and gated away from the Boolean one (`proof_sat.rs:3170-3181`):

> *"The Boolean core reads the clock on a conflict cadence, which a theory that
> propagates without ever conflicting never reaches. Read it on an iteration
> cadence too, at the same interval, so a CDCL(T) search is deadline-bounded on
> every path and not only on the conflicting one."*

That is B1's finding #2, written down and fixed for `T::HAS_THEORY` and left
unfixed for `NullTheory` — which is the configuration every QF_BV query uses.

## Summary

| route | keeping a late `sat` | keeping a late `unsat` |
|---|---|---|
| cold `SatBvBackend` (`check_with_replay_internal`) | **safe** — replay against original terms is unconditional and clock-free; costs ~164 ms of lift+replay | **safe and free** — the DRAT check already ran, inside the search, before the gate |
| `check_shared_guard_split` | **safe** — a second independent `eval` of every original assertion on top of the first | **safe** — starvation of later branches is unchanged |
| lazy SMT / DPLL(T) (`dpll_t.rs`) | **safe** — bounded by one more deadline-checked round; moves the cold arm towards the documented warm/cold invariant | **safe** — terminates the round loop immediately |
| `IncrementalBvSolver` | **not applicable** — does not reach this code; already checks its deadline before the solve | not applicable |
| `FusedGroup` portfolio | **safe** — declared-order winner, all outcomes drained, disagreement is a hard error | **safe** — same |
| `check_with_all_theories` (`combined.rs`) | **safe** — its own projection + replay is the anchor and does not search; but its five gates must move together or the fix is inert | **safe** — returns immediately, no further work |
| determinism | **improves** — removes one of two clock-dependence points | **improves** — same |

**Recommendation: keep the result.** Fire the gate only when there is no definite
verdict. Land it with the granularity fix, which is what makes the budget mean
something; the keep is what stops a budget overrun from also costing the answer.
