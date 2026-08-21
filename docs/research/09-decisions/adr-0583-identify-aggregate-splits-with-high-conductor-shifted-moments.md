# ADR-0583: Identify aggregate splits with high-conductor shifted moments

Status: accepted
Date: 2026-08-21
Index-summary: Rewrite each aggregate identity-path split as one low-twist correlation of only the unresolved high Hayes conductors

## Context

ADR-0582 combines the retained Haar levels into one nonnegative mass on the
coarse quotient.  The resulting path is substantially weaker than separate
levelwise localization, but its proposed three-quarter contractions must not
be mistaken for a generic martingale theorem.  They need an arithmetic
description which retains the cancellation already built into conditional
variance.

Let `G=E_ell`, `Q=E_c`, `K=ker(G->Q)`, and `R=|K|`.  Write `D(g)` for the
centered degree-`n` Mangoldt population.  For `q in Q`, define

```text
w(q) = R sum_(g in qK) D(g)^2 - (sum_(g in qK) D(g))^2.       (W)
```

This is `R` times the conditional variance in the coarse cylinder `q`.  In
particular, `w(1)=A_c`, `sum_q w(q)=A_0`, and the aggregate path mass is

```text
A_i = sum_(q maps to 1 in E_i) w(q).                         (A)
```

## Decision

Use finite-group Fourier orthogonality before attempting another analytic
bound.  With unnormalised transform
`\hat D(psi)=sum_g D(g) conjugate(psi(g))`, every character `eta` of `Q`
satisfies the exact identity

```text
\hat w(eta)
 = 2^(-c) sum_(psi in dual(G), cond(psi)>c)
       \hat D(psi) conjugate(\hat D(psi eta^(-1))).       (HM)
```

Indeed, Fourier expansion of the first term in `(W)` sums over every `psi`.
The second term is the same convolution restricted to characters inflated
from `Q`; subtraction removes that complete low--low block.  Multiplication by
the low-conductor `eta` preserves `cond(psi)>c`, so no boundary term remains.
For high `psi`, `\hat D(psi)` is the usual degree-`n` Hayes Mangoldt character
sum, equivalently a Frobenius trace power.

Subgroup orthogonality applied to `(A)` now gives

```text
2^i A_i = sum_(cond(eta)<=i) \hat w(eta),
2^i A_i - 2^(i-1) A_(i-1) = sum_(cond(eta)=i) \hat w(eta).  (HL)
```

Thus every observed aggregate contraction is one **signed exact-conductor
layer** of the high-conductor shifted second moment `(HM)`.  The CAS records
the right side of `(HL)` as `signed_fourier_layer_sum`, reconstructed from
nonnegative spatial masses without numerical roots of unity.  Translation's
proved half split makes this integer exactly zero at level `2^v_2(n)`.

This is narrower than the earlier full squared-discrepancy `(CDL)` object.
The latter contains both low- and high-conductor autocorrelations whose
separate bounds were shown to be useless; `(HM)` has already canceled the
entire low block and retains exactly the top spectrum used by `(REL)`.

## Literature boundary

The closest variance theorems do not prove `(HM)` in this regime.
Keating--Rudnick and Rodgers evaluate short-interval variances in a large-field
limit, not at fixed `q=2` with conductor growing.  Andrade--Yiasemides obtain
fixed-field moments of central `L`-values for growing polynomial moduli, but
not a fixed high power of `L'/L` under a low-conductor twist.  Sawin's refined
random-matrix model predicts the required decorrelation but is a model rather
than an estimate for this Hayes family:

- <https://arxiv.org/abs/1204.0708>
- <https://arxiv.org/abs/1609.02967>
- <https://arxiv.org/abs/1901.06295>
- <https://arxiv.org/abs/2409.02876>

## Evidence

- `exact_identity_energy_paths_are_nested_and_reconstruct_local_mass` checks
  `(HL)` as an exact integer identity on every retained level and on the
  aggregate path for both endpoint parities through `ell=14`.
- `translation_forces_the_first_odd_binomial_identity_split` checks that the
  forced layer sum is zero as well as checking equality of the spatial halves.
- The conditional-variance CLI emits every signed layer integer next to its
  parent and child masses.
- The 140 three-quarter-balanced fleet comparisons in ADR-0582 remain finite
  diagnostics.  Neither `(HM)` nor `(HL)` supplies cancellation by itself.

## Consequences

- A proof attempt should target a low-twist correlation of the high Hayes
  trace-power family, preserving its signed sum across the exact conductor
  layer.  Reintroducing the canceled low characters or taking absolute values
  character by character is a regression.
- Generic support, Cauchy, and individual-Weil bounds remain trivial on
  `(HM)`.  A useful theorem must exploit decorrelation of
  `\hat D(psi)` and `\hat D(psi eta)` for low nontrivial `eta`.
- The paper continues to state only `(REL)`.  This ADR identifies the exact
  spectral content of the selected bridge; it does not prove the missing
  contraction or Lemire's conjecture.
