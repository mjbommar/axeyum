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

Glaurung `e031f03` and Axeyum `21aa983a` carry the exact map as warm-profile
schema v6 and validate it fail-closed. The first real SurfacePen lineage run
decides and agrees on all 2,551 checks (2,282 SAT / 269 UNSAT), with zero
unknown splits or replay failures. Of 175.049 ms in `model_lift`, complete
model construction consumes 165.192 ms (94.37%), assignment reconstruction
and validation 7.146 ms (4.08%), and retained-AIG recomputation 2.427 ms
(1.39%). The run recomputes 1,414,029 AIG nodes, scans 290,336 symbol-bit
inputs, and produces exactly 5,066 reconstructed and completed symbol values.

This rejects the suspected duplicate AIG traversal as the next lever. Source
inspection identifies an exact scalar boundary to test next: the warm-theory
completion pipeline collects user array-select terms by walking every active
original assertion even when the active and one-shot array/UF projection sets
are all empty. A follow-up change must causally gate only that no-theory work;
it must still complete every user symbol and retain mandatory original replay.

## Alternatives

Optimizing the apparent duplicate AIG validation immediately was rejected
because the current aggregate cannot prove whether validation, forward
recomputation, or model completion dominates real formulas. Reusing partial
models or omitting default completion was rejected because Glaurung consumes
model values and original replay requires a complete, checkable assignment.
Always-on counters were rejected because the measurement surface must not tax
ordinary solvers.

## Consequences

Glaurung carries the exact map in warm-profile schema v6 and its strict
summarizer. Removing validation or narrowing reconstruction remains
unauthorized. The profile instead selects an exact scalar-only bypass of empty
warm-theory projection work for a separately tested and measured decision.
