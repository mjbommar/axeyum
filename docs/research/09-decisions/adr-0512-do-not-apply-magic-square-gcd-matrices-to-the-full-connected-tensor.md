# ADR-0512: Do not apply magic-square gcd matrices to the full connected tensor

Status: accepted
Date: 2026-08-19
Index-summary: Restrict gcd-matrix arguments to genuine two-sided product equations; the connected cumulant has a larger character-tuple constraint

## Context

ADR-0511 constructs the signed convolution-order tensor.  The proposed next
step was to classify its cells with the gcd matrices used in moment estimates
for multiplicative character sums.

The primary identity in Gorodetsky's number-theory discussion counts solutions
to a two-sided product equation.  Its gcd matrix reconstructs factors in

```text
f_1 ... f_r = g_1 ... g_s.
```

That identity arises after averaging powers of one character and its complex
conjugate.  It is not the Fourier expansion of Axeyum's full spatial fourth
moment.

## Decision

Do not label the connected-order cells by magic-square/gcd strata unless a
separate exact reduction to a two-sided product equation is first proved.
For the current finite abelian class group,

```text
sum_e D_e^4
 = |E_ell|^(-3) sum_(chi_1 chi_2 chi_3 chi_4=1)
     Dhat(chi_1)Dhat(chi_2)Dhat(chi_3)Dhat(chi_4).
```

The four characters vary independently subject to one product constraint.
The one-character/conjugate configurations to which the standard gcd matrix
applies occupy pairing-like diagonals, while `K_4` is designed to subtract the
three Wick pairings and retain the connected complement.

## Evidence

Gorodetsky's Section 4 explicitly introduces the gcd matrix for solutions of a
product equation and reconstructs its factors by the Vaughan--Wooley inductive
gcd process.  ADR-0511 independently shows that the full connected tensor has
large alternating cross-order cells; it is not recovered from one averaged
absolute fourth power.

## Consequences

- A direct magic-square implementation would classify the wrong object and is
  rejected before code or theorem credit.
- Gcd data may still be useful inside a rigorously isolated diagonal sector.
- The exact-conductor martingale remains a faithful representation of the
  entire connected cumulant.  The next bounded diagnostic is therefore a
  local Carleson/square-function ledger on every Witt cylinder.
- The endpoint theorem remains open.
