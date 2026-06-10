# Rewriting And Canonicalization

Status: draft
Last updated: 2026-06-10

## Purpose

Define the simplification layer before solver calls.

## Scope

In scope:

- Local rewrites, canonical forms, constant folding, and optional e-graph exploration.

Out of scope:

- Complete rewrite rule library.

## Core Claims

- Most solver performance is won or lost before the backend sees a query.
- Deterministic cheap rewrites should be the default hot path.
- Equality saturation is useful for exploration but should not be the first default
  representation for every query.
- Rewrites must preserve sorts and model-liftability.

## Rewrite Classes

- Boolean identities.
- Bit-vector identities.
- Constant folding.
- Extract/concat normalization.
- Extension/truncation cancellation.
- Comparator normalization.
- ITE simplification.
- N-ary flattening and sorting for associative/commutative ops.

## Examples

```text
x + 0 -> x
x xor 0 -> x
x xor x -> 0
x and all_ones -> x
ite(true, a, b) -> a
ite(c, x, x) -> x
extract(extract(x, h1, l1), h2, l2) -> extract(x, l1 + h2, l1 + l2)
```

## Design Implications

- Separate always-on canonicalization from expensive query preprocessing.
- Rewriter output should be hash-consed.
- Each rewrite should be testable independently.
- Add a differential test harness against external solvers for rewrite soundness.

## Risks

- Aggressive rewrites can create larger terms.
- Rewrites can be correct for mathematical integers but wrong for fixed-width BV.
- Provenance can be lost if side tables are not updated.

## Open Questions

- [ ] Should rewrite rules be data-driven or implemented as Rust pattern code?
- [ ] Should an e-graph optimizer be optional behind a feature flag?
- [ ] How should rewrite fuel and size limits be configured?

## Source Pointers

- egg: https://github.com/egraphs-good/egg
- Z3 simplifier architecture reference: https://github.com/Z3Prover/z3

