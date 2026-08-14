# ADR-0448: Checked executable Nat division specification

Status: accepted

Date: 2026-08-14

Requirements: [Lean kernel requirements](../../plan/lean-kernel-requirements-2026-08-13.md), R4.7.

## Context

ADR-0419--0425 established constructive relational Euclidean division with
existence, uniqueness, floor, divisibility, and congruence laws. ADR-0447 added
computing quotient and remainder projections from one shared recursive state.
Those two layers were intentionally not identified: numeral tests alone cannot
justify applying a theorem proved about `Nat.divMod` to `Nat.div` or `Nat.mod`.

The Rado proof experience exposed this exact kind of boundary. The case tree,
Bézout witness, and decomposition could be authored externally, but axeyum
correctly returned `unknown` where reusable checked library structure was
missing. A host comparison or a few agreeing examples would conceal the same
gap here. The computation must carry a checked invariant that reaches the
existing general-purpose theorem library.

## Decision

Add the zero-axiom theorem

```text
Nat.div_mod_exec : forall k n,
  Nat.divMod (Nat.succ k) n
    (Nat.div n (Nat.succ k))
    (Nat.mod n (Nat.succ k))
```

Quantifying the divisor as a successor represents positivity constructively and
avoids a redundant proof argument. The proof inducts on the dividend and uses
the same `Nat.beq` rollover condition as `Nat.divModState`.

In the rollover branch, `beq = true` is reflected to equality of the prior
remainder and divisor predecessor. The quotient increments, the remainder
resets to zero, and the reconstruction equation is transported through the
successor step. In the non-rollover branch, the prior relational bound gives
`remainder <= predecessor`; order decomposition yields either strictness or
equality. Equality contradicts `beq = false` through the proved completeness of
`Nat.beq`; strictness supplies the next remainder bound. Both branches construct
the `Nat.divMod` conjunction directly.

The small Boolean equality symmetry and transitivity terms used by the
contradiction are themselves built from `Eq.rec`; they add no declaration or
trusted primitive.

## Evidence

The theorem infers at `5 / 2`, and its exact result type is checked against the
executable quotient and remainder expressions. The established
`div_mod_bounds` theorem consumes that proof, demonstrating that floor laws now
apply to executable division. At `6 / 2`,
`div_mod_remainder_eq_zero_iff_dvd` consumes the executable relation, connecting
the computed zero remainder to divisibility. Divisor one is covered explicitly.

A mutation reuses the valid `5 / 2` proof while swapping the executable quotient
and remainder in the claimed relation; the kernel rejects it with
`DeclarationValueMismatch`. The theorem also joins promised-name,
deterministic-render, zero-axiom, strict all-feature Clippy, full kernel test,
warning-denied rustdoc, and pinned Lean replay gates.

## Consequences

Positive executable Nat division is no longer a parallel unchecked algorithm:
all existing relational uniqueness, floor, congruence, and divisibility results
can be instantiated with `Nat.div` and `Nat.mod`. Together with ADR-0419--0425
and ADR-0446--0447, this meets the constructive R4.7 division requirement.

The divisor-zero values remain total computational conventions and correctly
have no `Nat.divMod` proof, whose remainder-bound relation requires a positive
divisor. The next number-theory layer should define executable Euclidean gcd
from this certified remainder operation, using the already checked
well-founded-recursion foundation, before attempting Bézout or Gauss.
