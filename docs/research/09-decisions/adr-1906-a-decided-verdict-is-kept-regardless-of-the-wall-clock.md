# ADR-1906: A decided verdict is kept regardless of the wall clock — the deadline is a resource budget, not a correctness gate

Status: accepted
Index-summary: Three gates re-read the clock AFTER a search had already produced a verdict and discarded it; measured, that turned 8 of 32 QF_BV instances from `sat` into `unknown` while spending 1.15x-8.01x of the budget anyway. A definite `Sat`/`Unsat` is now kept on every route and only an UNDECIDED result degrades to `unknown`. The safety analysis is per verdict kind and per route: `sat` is unconditionally replay-checked against the original terms with no clock input; a late `unsat`'s DRAT check has ALREADY run, inline inside the search, so keeping it is free; the incremental façade never reaches these gates; the portfolio picks by declared order and drains every arm; and determinism IMPROVES, because the keep removes one of the two points at which wall-clock time could change a verdict. Paired with a deadline cadence that a propagation-bound search can actually reach, since the budget was previously not enforced at all on this class. The decision had already been taken once, at `auto.rs`'s `dispatch_reduced`, and never propagated to the two layers below it.
Date: 2026-09-10

## Context

Roadmap item **3.9**. Lane B1 measured
([`why-43-satisfiable-qfbv-miss-2026-09-10.md`](../03-measurements/why-43-satisfiable-qfbv-miss-2026-09-10.md))
that on a measurable part of the satisfiable QF_BV miss class **we compute the
right answer and then throw it away**. Nine instances — two of them real SMT-LIB
files through the shipping front door, one of them outside the `pspace` family
that supplies the shape — returned `unknown` at a 10 s budget after spending
29-43 s, and returned `sat` at a 300 s budget after spending **the same time**.
The search never stopped; only the verdict was discarded.

Two facts make this worse than a missed opportunity:

1. **The overrun has already been paid** when the clock is re-read. Discarding
   the verdict does not recover a millisecond of it. Measured overrun of a 10 s
   budget on this class: **1.15x to 8.01x**.
2. **The budget was not being enforced during the search at all.** The CDCL core
   tested its deadline every `DEADLINE_CHECK_INTERVAL = 1_024` **conflicts**, and
   these searches finish in fewer than **256** conflicts at 12-51
   conflicts/second. The check could never fire once. So the budget was not an
   upper bound that was occasionally exceeded — it was ignored during the search
   and then applied retroactively, to the answer rather than to the work.

B1 named the question that gates the fix and did not run it: is keeping a late
result safe on each route? That analysis is
[`late-result-keep-safety-2026-09-10.md`](../03-measurements/late-result-keep-safety-2026-09-10.md)
and this ADR records what it decided.

## Decision

**A definite verdict is kept regardless of the wall clock. Only an UNDECIDED
result degrades to a timeout `unknown`.** The deadline is a resource budget — it
governs how much work we are willing to *start*, not whether an answer we
already hold is admissible.

Concretely, every post-solve gate takes the form

```rust
if matches!(result, /* undecided */) && past_deadline(deadline) { … }
```

and the gates that sit *below* a decided verdict, on the path its soundness
anchor must walk, are deleted rather than made unreachable.

Paired with it: **the deadline cadence gains an iteration term**, so a
propagation-bound search is bounded by the budget it was given instead of
overrunning it and then being punished for the overrun.

## The routes, and why the keep is safe on each

The full argument is in the measurement note; the load-bearing findings:

- **`sat`.** `handle_sat_result` cannot construct a `CheckResult::Sat` without
  `replay_model` first, and `replay_model` takes **no deadline parameter** — it
  cannot read the clock because it is never given it. Both its arms consume the
  *original* terms (a `QueryPlan::replay_original`, or a direct `eval` loop over
  the caller's assertions). A model that cannot be evaluated is conservatively
  refused; one that evaluates to `false` is a soundness alarm. So a late `sat`
  carries exactly the assurance of a timely one. What replay covers is a total
  check of the returned answer against the question asked; what it does not cover
  is `unsat`, `unknown`, and the values of symbols the query never mentions —
  none of which the clock touches.
- **`unsat`.** The intuition that keeping a late `unsat` means also running a
  DRAT check past the deadline is **wrong on this path**. The proof is verified
  *inline* inside `primary_sat_search` (`solve_with_native_cdcl`), before the gate
  is reached, and stamped `Checked`; the cost is already inside `stats.solve`.
  `ensure_unsat_proof_checked`, which sits below the gate, is a no-op on all
  three reachable states, and its expensive re-derivation route is reachable only
  from an `Unchecked` unsat under `prove_unsat` — a combination the native core
  does not produce (its doc-comment names batsat, gone since ADR-1703). Keeping a
  late `unsat` is therefore **free**.
- **Incremental / warm sessions.** `IncrementalBvSolver` does not reach this code
  at all; it checks its deadline at the **top** of each refinement round, before
  the solve, which is the correct shape. No warm state is touched and no
  "a timed-out call left the session unchanged" assumption is affected. The one
  place the two meet — `dpll_t.rs`'s cold/warm skeleton arms, whose own comment
  asserts "the round's verdict cannot differ between them, only the cost does" —
  is a divergence the keep **reduces**, because today only the cold arm discards.
- **The portfolio.** `FusedGroup` drains every arm's outcome before choosing and
  `pick_winner` scans by **declared** order, never finish order, so a late arm
  cannot displace an earlier one; a genuine cross-arm `sat`/`unsat` conflict is a
  hard `SolverError::Backend`. Its budget defects (a bare `recv()`, cooperative
  stop tokens, `saturating_sub` starvation in sequential mode) are real,
  pre-existing, and **untouched** by this decision: the overrun that starves a
  sibling is the search time, which the gate never shortened.
- **Determinism.** The keep makes the verdict *more* deterministic, not less. The
  repository's determinism promise is carried by `resource_limit`, documented as
  "Deterministic backend search budget; reproducible across machines", never by
  `timeout`, which gets no such sentence and could not. Today the verdict depends
  on the clock at **two** points — the in-search cadence and the post-search
  re-read; the keep removes the second and worse one, which is a pure function of
  how loaded the box was applied to a search that had already committed to an
  answer. Under the old behaviour the same binary, file, budget and seed returned
  `sat` on an idle host and `unknown` on a busy one.

## What changed, and where the boundary is

Three gates, in two files, plus the cadence:

1. `crates/axeyum-solver/src/sat_bv_backend.rs` — the post-SAT-search clock
   re-read. Now conditioned on `SatResult::Unknown`, so every `Unknown` sub-case
   keeps its exact `kind` and `detail`.
2. `crates/axeyum-solver/src/combined.rs` — the post-backend re-read in
   `check_with_all_theories`, which did not even inspect the result before
   discarding it. **This is the one that mattered for the shipped route**: this
   function is the funnel every QF_BV front-door arm in `auto.rs` goes through,
   so the two discards sit *in series* and fixing only (1) would have been inert
   on the front door.
3. The same file's four gates below a decided `Sat` — three model projections and
   one per-assertion check inside the replay loop. **Deleted**, not made
   unreachable: a guard that cannot fire is not a safety mechanism, it is
   unexecuted code claiming to be one. Leaving any of them would have neutered
   (2) anyway, since a kept `sat` would fail the very first clock read in the
   replay loop.
4. `crates/axeyum-cnf/src/proof_sat.rs` — the deadline is now tested on a
   search-loop **iteration** cadence as well as a conflict one. This is not a new
   mechanism: the identical fix already existed for `T::HAS_THEORY`, with the
   rationale "a theory that propagates without ever conflicting never reaches
   [the conflict cadence]". The scope was wrong, not the reasoning — a *Boolean*
   search that propagates without conflicting never reaches it either, and that
   describes an entire QF_BV family.

**The boundary, stated so the next change can be inconsistent with something.**
The gates that remain, and should remain, are the ones that fire when **no
verdict is in hand**: `combined.rs`'s three pre-solve gates (after array
elimination, after function elimination, after the integer bit-blast), the
backend's pre-solve gate, and every `auto.rs` ladder boundary check that runs
after a route has already *declined*. Those govern whether to start more work,
which is what a budget is for. The rule is not "ignore the deadline"; it is
**consult the deadline before committing to work, never after the work has
answered**.

## The decision had already been taken once

`dispatch_reduced` (`auto.rs`) — the preprocessed-dispatch route, and
`preprocess` defaults **on** — already carries this exact fix, in this exact
shape, with its own measurement (`nia-bounded-blast` deciding `nia-pythagorean`
a hair past the budget). It was applied at one layer and never propagated to the
two below it. Recording it as an ADR is the point: the principle now exists in
one greppable place instead of as a comment on one of the three sites that
needed it.

## Consequences

- **Accepted:** a caller that sets a 10 s budget can receive an answer at 80 s.
  That promise was **already** broken by 1.15x-8.01x before this change; what the
  gate added was losing the answer as well. The cadence fix (4) is what actually
  restores the promise, and the two are deliberately landed together for that
  reason.
- **Accepted:** a kept `sat` pays its model lift and replay past the deadline
  (~164 ms measured on `pspace/ndist.b.20000`). It is not skippable in any case —
  skipping it would mean returning an unverified model.
- **Not accepted, and not attempted:** any relaxation of the *pre*-solve gates,
  any change to the incremental contract, and any change to the portfolio's
  budget arithmetic.
- **Tension to keep in view:** the keep and the cadence pull in opposite
  directions on the *count* of clock-dependent verdicts. The keep removes a
  dependence point; a finer cadence makes the remaining one fire where it never
  fired before. They compose on the outcome — a budget that means something,
  and no answer thrown away — but they are not the same kind of improvement, and
  a future tuning of `DEADLINE_CHECK_INTERVAL` should be argued on that basis
  rather than as a pure win.
