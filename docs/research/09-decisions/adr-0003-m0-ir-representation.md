# ADR-0003: M0 IR Representation Choices

Status: accepted
Date: 2026-06-10

## Context

Milestone M0 requires concrete choices the research notes left open: how BV
constant values are stored, whether sorts are interned from day one, and how
the M0 operator set is split between Bool and BV families. These are
API-visible, so they are recorded here rather than made silently.

## Decision

1. **BV widths are 1..=128 in M0**, with constant values stored as `u128`
   masked to width. Wider bit-vectors are a later extension (arbitrary
   precision or limb arrays); the width cap is enforced at term build time
   with a typed error, so lifting it later is additive.
2. **`Sort` is a `Copy` enum (`Bool`, `BitVec(width)`), not an interned
   `SortId`, until recursive sorts (arrays) arrive.** Interning pays off
   only when sorts nest; a Copy enum keeps M0 APIs simpler. The public
   builder surface does not expose this choice in a way that blocks
   re-introducing `SortId` alongside it later.
3. **Bool and BV operator families are distinct** (`BoolNot` vs `BvNot`,
   etc.), implementing the standing "Bool and BV(1) are distinct" claim.
   `Eq` and `Ite` are polymorphic with same-sort checks. `Extract` carries
   its `hi`/`lo` parameters in the operator, not as term arguments.
4. **Concat results must fit the width cap**; violations are build-time
   errors, never runtime values (consistent with the bv-semantics note's
   static-error rule).

## Evidence

u128 covers every benchmark class M0 through Phase 5 targets (machine-word
widths dominate QF_BV practice); the SMT-LIB QF_BV corpus does contain wider
vectors, which is acceptable: corpus ingestion (Phase 2) reports unsupported
widths as clean errors and skips, and the cap's removal is additive.

## Alternatives

- Arbitrary-precision constants now (`Vec<u64>` limbs or a bigint crate):
  rejected for M0 — complicates the evaluator and every mask operation
  before any client needs it.
- Interned `SortId` now: rejected — speculative until Array sorts exist.

## Consequences

- Easier: evaluator and constant folding are simple masked `u128` math.
- Harder: Phase 2 corpus runs must classify "unsupported width" separately
  from failures; lifting the cap touches constant storage and evaluator.
- Revisit: when Array sorts land (Phase 7) for interning; when corpus
  ingestion shows material wide-BV coverage gaps for the cap.
