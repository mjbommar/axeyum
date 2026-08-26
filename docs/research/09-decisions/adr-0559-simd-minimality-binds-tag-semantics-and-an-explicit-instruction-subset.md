# ADR-0559: SIMD minimality binds tag semantics and an explicit instruction subset

Status: accepted
Date: 2026-08-26
Index-summary: Prove bounded SIMD shuffle minimality over distinct provenance tags and a named instruction subset

## Context

The SIMD open-problem lane requires both positive instruction sequences and lower-bound
certificates. Testing concrete byte vectors is insufficient: equal byte values can hide an
incorrect permutation. An instruction-count lower bound is also meaningless unless it names
the exact ISA operations, operand forms, zeroing behavior, lane restrictions, and target.
Axeyum had SAT/DRAT machinery but no typed SIMD semantic boundary.

## Decision

Add `axeyum_search::simd` with exact byte-provenance semantics for an intentionally small
unary AVX2 language:

- `vpshufb`, with 128-bit lane-local selection and control-bit-7 zeroing; and
- same-source `vperm2i128`, with low/high/zero selection for each 128-bit output half.

A YMM value contains 32 distinct optional input tags, not concrete bytes. Sequence replay
therefore establishes the complete byte permutation and any produced zeros in one run.

For a one-instruction query, Axeyum computes exact family eligibility: `vpshufb` controls are
independent per output byte, while `vperm2i128` selectors are independent per output half.
A two-selector CNF requires exactly one family and forbids every ineligible family. The pure
Rust proof-producing SAT core emits DRAT; the independent backward checker must accept the
serialized/reparsed proof before the result is credited.

The first calibration target is global reversal of 32 byte tags. Lane-local reversal by
`vpshufb`, followed by a half swap using `vperm2i128` immediate `0x01`, is a two-instruction
witness. Neither family can realize the target alone, so the checked lower bound is two.

## Evidence

- Six semantic/proof controls cover exact replay, lane locality, high-bit zeroing, independent
  family ineligibility, DRAT text round-trip/checking, proof truncation, target mutation, and
  malformed provenance.
- The emitted query has two variables and four clauses. Its DRAT proof is re-read from text
  and checked against the emitted DIMACS formula.
- A separate C intrinsic oracle executes the exact controls on AVX2 hardware and compares all
  32 output bytes against the reversal target.

## Alternatives

### Claim all AVX2 shuffles

Rejected. Blend, unpack, align, variable permute, load/store, and multi-source forms are not
modeled. The result must remain scoped to the two named unary forms until each added family
has semantics, model lifting, and negative controls.

### Test random concrete vectors

Rejected. Random testing can validate an implementation but cannot replace provenance-tag
semantics or establish a universal byte permutation.

### Trust analytical inspection without SAT evidence

Rejected for the research artifact. The analytical eligibility test is simple and complete,
but the lane exists to exercise Axeyum's proof-producing finite-domain path end to end.

## Consequences

- Axeyum gains reusable typed semantics for building larger shuffle synthesis encodings.
- The calibration establishes only subset-relative minimality and makes no novelty claim.
- Expanding toward the open problem requires multi-instruction control variables, model
  lifting, and additional ISA families under the same explicit semantic contract.
