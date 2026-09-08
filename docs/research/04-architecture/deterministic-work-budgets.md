# The budget primitive is wall-clock, and that is a foundation problem

**Status:** measured 2026-09-08. Facts are marked [M]; consequences I have NOT
yet demonstrated are marked [I] and must be tested before anyone builds on them.

## What is measured

[M] The budget primitive across the solver is a wall-clock instant. Counted on
`main` at `cbb178c55`:

| primitive | count |
|---|---:|
| functions taking `deadline: Option<Instant>` | 312 across 58 files |
| deterministic (conflict-budget) mentions in `axeyum-solver` | 5 |

[M] The SAT core's public entry is
`solve_with_drat_proof_with_limits(formula, deadline: Option<Instant>, max_conflicts: usize)`.
So a deterministic budget EXISTS at the core (`max_conflicts`) but the layers
above it overwhelmingly express limits as clock time.

[M] We already count the raw material for a deterministic work measure.
`SearchCounters` tracks `propagations`, `watch_visits`, `clause_visits`,
`resolutions` -- these are the same quantities a cache-miss-weighted "tick"
model is built from.

[M] `InprocessOptions::default()` is `Self::OFF`, and the shipping QF_BV route
calls entry points that skip inprocessing.

## Why this is a foundation problem, not a detail

A wall-clock budget is **not reproducible and not load-independent**. This
repository has already measured the consequence in another context: the same
commit on the same machine produced frontier counts of 35, 39 and 40 depending
only on machine load, which is why the ratchet now calibrates and can mark a run
NOT COMPARABLE.

Determinism is a public API promise here (see CLAUDE.md: "stable iteration
order, explicit seeds, explicit resource limits"). A pass whose amount of work
depends on how busy the host was is not an explicit resource limit.

## The inference that must be tested before it is believed

[I] **Part of the reason inprocessing "does not pay off inside 24s" may be that
we cannot budget it precisely.** Under a wall-clock cutoff on a shared machine,
a pass gets a different amount of work every run; it can be halted mid-pass
having paid the setup cost (building occurrence lists) without collecting the
benefit. That would show up exactly as "costs more than it saves".

This is an INFERENCE. It predicts something checkable: inprocessing's
cost/benefit should be much noisier across repeated identical runs than search
alone, and the variance should track host load. **Test it before building on
it.** The alternative explanation -- the passes are simply too expensive at any
budget -- is equally consistent with "switched off", and the two call for
different work.

## The shape of the fix, if the inference holds

A deterministic work budget as a SHARED primitive, not another per-pass limit
struct. The repository already has at least seven ad-hoc limit types
(`ImcLimits`, `PdrLimits`, `PdrLiaLimits`, `ImcLiaLimits`, `ImcLraLimits`,
`CheckBudget` x2, `MemoryBudget`), which is the duplication that a real
abstraction would remove.

Requirements it must satisfy:

1. **Deterministic.** Derived from counted work, never from a clock.
2. **Composable.** A parent budget can hand a child a bounded sub-budget and
   learn what was spent, so a schedule can allocate across passes.
3. **Reusable across divisions.** The 12 divisions must be able to budget
   theory propagation, rewriting and preprocessing with the same primitive --
   otherwise it is a SAT-only fix wearing a general name.
4. **Observable.** Spending is attributable to the pass that consumed it. Route
   attribution already established that naming the LAST pass to run is wrong on
   348 of 350 files we lose.
5. **Cheap to check.** A budget test on a hot path must not itself cost more
   than it saves; the check must be a counter comparison, not a syscall.

Wall-clock deadlines do not disappear -- a hard external timeout is still
wall-clock by nature. The change is that INTERNAL allocation decisions ("how
much vivification should this formula get?") stop depending on the clock.
