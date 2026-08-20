# ADR-0537: Distinguish pointwise Witt monodromy from the constrained fourth cumulant

Status: accepted
Date: 2026-08-20
Index-summary: Reconstruct the diagonal character fourth moment and prove that Katz monodromy controls a different contraction from the Hayes cumulant

## Context

Katz constructs the universal `L`-sheaf over primitive characters of the
truncated big-Witt group and proves that its geometric monodromy contains
`SL(n-1)` in characteristic two for `n>=4`.  This explains why ordinary
pointwise moments of the character Frobenius classes have unitary/Wick main
terms.  His Theorem 8.1, however, fixes `n` and lets the finite field grow.
The proof bounds nontrivial Weyl sums by `C(p,n,Xi)/sqrt(q)`, where `C` is a
sum of compactly supported Betti numbers; the paper explicitly supplies no
uniform bound in growing `n` for the representations needed here.

The Lemire cumulant has an additional algebraic mismatch: it is not the
ordinary pointwise fourth moment over characters.

## Decision

Add `ClassPopulationDistribution::character_fourth_moment_comparison` with an
explicit quadratic work admission.  For `D_e=N_e-mu` and its Fourier transform
`S_chi`, it reconstructs

```text
P_4 = sum_chi |S_chi|^4
    = 2^ell sum_h (sum_e D_e D_(e+h))^2
```

from exact spatial autocorrelations.  It separately computes

```text
Q_4 = sum_(chi_1 chi_2 chi_3 chi_4=1) product_i S_(chi_i)
    = 2^(3ell) M_4
```

as the identity value of the fourfold character convolution.  It also retains
the Parseval contraction

```text
P_2 = sum_chi S_chi S_(chi^-1) = 2^ell M_2
```

and checks `Q_4-3P_2^2=2^(2ell)K_4` exactly.  Thus all three Wick projectors
are explicit rather than implicit in the cumulant formula.  The level-seven odd
endpoint pins `P_4 != Q_4`; a resource mutation one cell below `2^(2ell)` is
required to decline before work.

## Consequences

- Katz's `SL` monodromy and its ordinary fourth invariant control `P_4`, a
  diagonal character contraction.  They do not control the full
  product-constrained `Q_4` or its connected pairing subtraction.
- A relevant monodromy theorem would need a convolutional/constrained
  four-design statement over the character group, uniform over `F_2` while
  conductor, sheaf rank, trace power, and representation complexity grow.
- Even such a theorem needs effective Betti bounds at that scale.  The
  existing fixed-conductor, growing-field equidistribution theorem supplies
  neither requirement and grants no endpoint credit.
