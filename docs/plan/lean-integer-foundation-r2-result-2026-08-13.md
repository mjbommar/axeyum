# Lean integer-foundation R2 result

Date: 2026-08-13

Status: **decision complete; no theorem credit added**

Authority: [Lean kernel requirements](lean-kernel-requirements-2026-08-13.md),
R2; [ADR-0388](../research/09-decisions/adr-0388-retain-axiomatized-int-and-use-nat-deficits-for-rado.md).

## Result

R2 is closed by an explicit split between solver reconstruction and
publication mathematics. The existing `Int` prelude remains an axiomatized
34-assumption profile for integer certificate reconstruction. It is not a
construction of the integers and no result using it may be described as
axiom-free.

The Rado `thm:rigid` lane will not use that profile. Its first target remains
the novel, separable `M = N+1` half, reformulated over Nat with actual and
canonical prefix widths `A_j` and `C_j`. The invariant `A_j <= C_j` is the
subtraction-free form of the paper's signed `E_j <= 0` induction. The
one-unit-overrun and core cases use the paper's same divisibility triggers to
exclude prefix equality via `a | 1`.

This result chooses the proof foundation; it does not claim the width lemma,
prefix induction, or rigidity theorem is formalized.

## Corrected quotient boundary

The R2 audit found that the requirements document's original alternative was
not Lean-conformant. Lean 4.30 has a four-member privileged quotient package,
not a five-member package. `Quot.sound` is a separate axiom. Therefore a
quotient-constructed Int would remove the 34 Int-profile assumptions but would
not be absolutely axiom-free. The requirements now state that exact boundary.

ADR-0365 remains proposed because its pinned-Lean M4 differential is still
open. R2 neither accepts it nor adds `Quot.sound` without its own consumer and
evidence.

## Publication check

The current `../axeyum-rado-paper` text describes only the existing 14-theorem
Nat export as having no `sorry` and no axiom, and explicitly states that real
Lean has not checked it. `thm:rigid` is not credited to that export. No paper
edit is needed for R2; a future theorem using `Int` would have to state all 34
assumptions in its claim, while the selected Nat route preserves the current
boundary.

## Exit mapping

- **R2.1:** met by accepted ADR-0388; Int stays axiomatized, while ADR-0365 and
  its four-member quotient package remain separately gated.
- **R2.2:** met by ADR-0388 and the generated ledger's machine-validated policy
  link.
- **R2.3:** met for the current paper because no credited publication theorem
  uses `int_prelude`; ADR-0388 makes the 34-assumption disclosure mandatory for
  any future one.

## Next mathematical action

Implement the smallest dependency-ordered Nat library needed by `thm:sharp`
first (R7.1), then the Rado width/congruence slice needed by the Nat prefix
invariant. Do not start `thm:main` before the R4.7--R4.9 Euclidean, gcd, Bezout,
and valuation spine exists.
