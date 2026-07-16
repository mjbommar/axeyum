# ADR-0194: Incremental model-lift attribution

Status: accepted
Date: 2026-07-16

## Context

ADR-0193 moves original replay from 38.82% to 7.14% of the profiled
SurfacePen internal total. The residual `model_lift` timer becomes the largest
named stage, but it currently combines three different operations: forward
recomputation of every retained AIG node from SAT inputs, validation and symbol
assignment reconstruction, and completion/projection/filtering of the public
model across arena symbols. Optimizing any one without attribution would be
another blind client-path change at a soundness-sensitive boundary.

## Decision

Add observational-only `IncrementalModelLiftStats` to the opt-in incremental
profile and nest it under `IncrementalBvStats::model_lift_work`.

The profile records three durations nested within `model_lift`:
`aig_recompute`, `assignment_reconstruct`, and `model_completion`. It also
records cumulative counts for AIG nodes recomputed, symbol-bit bindings
scanned, assignment symbols produced, arena symbols scanned, and completed
public model values. `delta_since` is saturating and component-wise, matching
the existing incremental stats contract.

Ordinary constructors leave every new field at zero. Enabling profiling adds
clock reads and diagnostic counts but selects no model, replay, lowering, CNF,
SAT, cache, or warm-admission policy. The existing aggregate `model_lift`
timer and `total_time` definition remain unchanged.

## Evidence

The public incremental-stats test proves that one SAT check reports all three
positive subphase durations, exact retained-AIG and 64-bit symbol-input work,
one reconstructed/completed symbol, and a subphase-time sum no greater than
the existing aggregate timer. A repeated check reports a fresh exact delta.
The ordinary-constructor test proves the complete attribution struct remains
zero when profiling is disabled. The focused all-feature test and strict
all-target/all-feature `axeyum-solver` Clippy pass under the 4 GiB wrapper.

## Alternatives

Optimizing the apparent duplicate AIG validation immediately was rejected
because the current aggregate cannot prove whether validation, forward
recomputation, or model completion dominates real formulas. Reusing partial
models or omitting default completion was rejected because Glaurung consumes
model values and original replay requires a complete, checkable assignment.
Always-on counters were rejected because the measurement surface must not tax
ordinary solvers.

## Consequences

Glaurung must carry this exact map in the next warm-profile schema and its
strict summarizer before a model-lift optimization is selected. The first real
v6 profile should compare time per AIG node, symbol bit, arena symbol, and
completed value. Removing validation or narrowing reconstruction remains
unauthorized until that profile identifies the responsible work and a replay-
preserving API boundary is separately decided.
