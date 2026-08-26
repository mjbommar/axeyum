# ADR-0569: Multiplicative synthesis orders complete AND operands

Status: accepted
Date: 2026-08-26
Index-summary: Completely remove per-gate operand-swap symmetry in multiplicative circuit synthesis

## Context

ADR-0561's opt-in symmetry breaker compares only the first primary-input coefficient of
each pair of affine AND operands. It removes one subset of the commutativity symmetry but
leaves most pairs duplicated. The same selector layout feeds truth-table CNF, direct ANF CNF,
and portable Boolean-ANF equation routes, so a reduction that silently differs between them
would undermine backend comparisons.

Zhang--Huang already specify the complete reduction: order the full coefficient vectors
lexicographically. Their Section 5.1 explicitly derives it from commutativity and reports it
inside the improved multiplicative-complexity encoding. This is prior art, not a new method.

## Decision

Add `lexicographic_operand_order` to `MultiplicativeEncodingOptions`. For every AND gate,
require the complete left affine coefficient vector to be lexicographically greater than or
equal to the right vector, with `false < true`. The option subsumes the older
`partial_operand_order`; when both are true, only the complete constraint is emitted.

The truth-table and direct-ANF CNFs use a deterministic Tseitin prefix-equality comparator.
The portable ANF system emits the equivalent equations

```text
prefix_equal(i) * (1 + left_i) * right_i = 0
```

at every position, with the prefix represented algebraically. Existing resource admission
therefore also bounds any polynomial growth. Witness pinning swaps operands into the selected
orientation before adding units, rather than rejecting an equivalent circuit.

Default and partial-order encodings retain their byte serialization. The PRIMATEs driver
exposes `none`, `first`, and `lex` modes and reports the selected reduction explicitly.

## Evidence

- Exhaustive enumeration of all 64 pairs of three-bit vectors agrees exactly with concrete
  lexicographic comparison.
- All sixteen two-input Boolean functions retain their exact zero/one-AND boundary under the
  full reduction in both CNF backends; the portable ANF route is exercised by the same option.
- A deliberately reversed one-AND witness is canonicalized, solved, lifted, and independently
  replayed.
- The published PRIMATEs-inverse eight-AND circuit pins 222 selectors in a
  9,454-variable / 32,240-clause full-order formula, solves, lifts, and replays every row.
- Regenerating the retained MC=6 first-coefficient formula gives the exact prior SHA-256
  `619917ff...6908`.
- The full-order MC=6 formula has 6,406 variables / 21,901 clauses. CaDiCaL 3.0.1 reached the
  300-second hard limit with `UNKNOWN`, no model, and no proof.

## Consequences

Axeyum completely removes the independent `2^k` operand-orientation symmetry while preserving
the bounded multiplicative-complexity question and positive-witness replay. The extra prefix
variables and clauses can still hurt a solver; the measured control did not finish, so no
performance claim is generalized from the structural reduction.

The PRIMATEs-inverse interval remains `[7,8]` in this work. A timeout is not a reproduction of
the published MC=6 lower-bound computation, and MC=7 has not been attempted. Current arXiv,
web, and Google Scholar/SerpAPI searches through 2026-08-26 found no later endpoint closure;
Scholar still reports eight citations but returns an empty cited-by result, so currency
language remains conditional rather than exhaustive.
