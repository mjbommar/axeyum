# ADR-0447: Shared executable Nat division state

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R3 and R4.7.

## Context

ADR-0419--0425 provide a constructive relational Euclidean-division library,
and ADR-0446 provides proved computational Nat equality. Research-facing
algorithms also need quotient and remainder terms that reduce on closed input.
Defining those projections independently would duplicate their recursive state
transition and leave two implementations that could drift.

Pinned Lean 4.30 makes Nat division total: `n / 0 = 0` and `n % 0 = n`, with
public operations ordered `(dividend, divisor)`. Its implementation also keeps
quotient and remainder updates coupled. The reusable lesson from the Rado
development is to expose a general checked computation boundary rather than
hide a host-language comparison or target-specific witness generator in the
proof route.

## Decision

Add one reducible shared state:

```text
Nat.divModState : Nat -> Nat -> Bool -> Nat
```

Its arguments are divisor, dividend, and selector. `true` selects the quotient;
`false` selects the remainder. The Boolean function is an internal product
encoding, avoiding a Nat-specific pair type and Prop-to-Type elimination.

The state recurses structurally first on the divisor. At divisor zero it returns
quotient zero and remainder dividend. For divisor `succ k`, it folds over the
dividend from state `(0, 0)`. A step tests the prior remainder against `k` with
proved `Nat.beq`; equality increments the quotient and resets the remainder,
while inequality preserves the quotient and increments the remainder.

Expose the conventional projections:

```text
Nat.div : Nat -> Nat -> Nat
Nat.mod : Nat -> Nat -> Nat
```

in Lean-compatible `(dividend, divisor)` order, plus checked zero and successor
equations `div_zero`, `mod_zero`, `zero_div`, `zero_mod`, `div_succ`, and
`mod_succ`. No axiom, choice operator, host arithmetic, or trusted literal
shortcut is added.

## Evidence

Closed controls compute both public projections and both selectors of the
shared state for `0/0`, `5/0`, `0/3`, `2/5`, `5/2`, `6/2`, and `11/2`. They
cover exact division, a nonzero remainder, a dividend below the divisor, and
both total zero-divisor results. Every structural equation infers. Mutations
claiming `5 / 2 = 3` and `5 % 2 = 0` are rejected with
`DeclarationValueMismatch`.

The three definitions and six theorems join the promised-name,
deterministic-render, zero-axiom, strict all-feature Clippy, full kernel test,
warning-denied rustdoc, and pinned Lean replay gates.

## Consequences

Nat clients can compute quotient and remainder from one definitionally shared
state with the same total surface semantics as Lean. The representation is
general-purpose and can support gcd, valuation, normalization, and
algorithm-adjacent proofs without adding a target-specific primitive.

This decision does not yet identify the computed projections with the existing
`Nat.divMod` relation, so it does not by itself complete R4.7. The next increment
must prove the positive-divisor relational specification; only that theorem may
transfer the established uniqueness, floor, congruence, and divisibility laws
to executable `Nat.div` and `Nat.mod`.
