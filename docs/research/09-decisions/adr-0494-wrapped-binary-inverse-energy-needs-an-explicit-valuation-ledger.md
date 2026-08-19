# ADR-0494: Prove wrapped binary inverse energy with an explicit valuation ledger

Status: accepted
Date: 2026-08-19
Index-summary: Reprove the fourth inverse-energy bound for the binary prime-power modulus with explicit valuation, lift, divisor, and loss accounting

## Context

The no-wrap rational-collision theorem in ADR-0493 applies to modulus degree
`r=ell+1` only when `3d<r`.  Bagshaw Type-I Case 2 reaches the boundary
`m=r/3`, and the balanced Type-II ranges extend beyond it.  The favorable
zero-loss exponent line in the existing diagnostics therefore still depended
on an internally unproved energy input.

Bagshaw's 2024 Lemma 3.14 is characteristic-free, but its proof imports the
pointwise inverse-sum estimate in Lemma 5.3 of his 2023 paper.  The LaTeX
source confirms that this estimate uses polynomial Diophantine approximation
and divisor counting, not the odd-characteristic Kloosterman bound.  It also
contains a harmless transcription error in the displayed premise
(`bar(x_1)+bar(x_1)` instead of `bar(x_1)+bar(x_2)`), so Axeyum should retain
an independent special-modulus proof.

## Decision

Add `binary_prime_power_inverse_additive_energy_bound` to
`axeyum-cas::gf2_hayes`.  For

```text
U_m={A in GF(2)[x]: deg A<m, A(0)=1},   1<=m<=r,
```

it proves an explicit bound for the additive energy of `U_m^(-1)` modulo
`x^r` as follows.

For a nonzero inverse sum `a`, put `s=v_x(a)`.  Since all interval elements
are units, `s=v_x(A+B)`, and the exact number of ordered pairs in this stratum
is

```text
2^(2m-s-2),                 1<=s<m.
```

Put

```text
k=min(r-s-1,ceil((r+m)/2)).
```

The top-`k` coefficient map `u -> au mod x^r` has `k` equations and `k+1`
unknown coefficients.  Hence a nonzero `u` of degree at most `k` exists for
which `v=au mod x^r` has degree at most `r-k-1`.  Because `k<r-s`, `v` is
nonzero.  Clearing denominators and lifting gives

```text
(vA+u)(vB+u)=u^2+t v x^r.
```

There are at most `2^L` lift polynomials, where

```text
L=max(0,k+m-r,2m-k-2).
```

The polynomial on the right is nonzero.  If `h=v_x(u)`, its two summands
have valuations `2h` and at least `r+s+h`; these differ because `h<r-s`.
Every solution therefore injects into an ordered factorization of a nonzero
polynomial of degree at most

```text
D=2 max(k,r-k+m-2).
```

Splitting irreducibles at degree `R` gives the explicit divisor envelope

```text
tau(P) <= (D+1)^(2^(R+1)) 2^floor(D/(R+1)),
R=max(1,floor(log2(D)/2)).
```

The CAS multiplies these three exact factors for every `s` and adds the
diagonal energy `|U_m|^2`.  No finite table, odd-characteristic theorem, or
unrecorded epsilon is used.

Also add `binary_bilinear_explicit_prime_power_energy_exponent`.  It feeds the
ceiling exponents of these concrete `BigUint` energy envelopes into the
characteristic-free `k=2` Hölder ledger, then adds a caller-supplied rational
analytic-loss reserve.  The older generic exponent operation remains a
conditional substitution tool.

## Asymptotic consequence

Uniformly for `m<=r`, `D=O(r)` and the displayed divisor exponent is `o(r)`.
If `k=ceil((r+m)/2)`, then

```text
L=max(0,ceil((3m-r)/2)).
```

The remaining strata have `k=r-s-1`; after multiplication by their exact
pair populations, their base exponent is at most `max(2m,4m-r)+O(1)`, which
is bounded by `max(2m,(7m-r)/2)+O(1)` because `m<=r`.  Summing the `m-1`
strata is another subexponential factor.  Therefore the report proves

```text
E_inv(x^r,m) <= 2^(2m+o(r)) + 2^((7m-r)/2+o(r))
```

over `GF(2)`, including `3m=r`.  This is the internal special-modulus version
of the energy input used by Bagshaw Cases 2--4 and the balanced Type-II
argument.

## Evidence

For every `3<=r<=9` and `2<=m<r`, the explicit envelope dominates Axeyum's
independent exact Walsh/collision energy table.  The tests also require the
valuation-stratum populations to sum to `|U_m|(|U_m|-1)` and exercise the
previously missing boundary `(r,m)=(9,3)`.  A separate bilinear test shows
that the finite divisor envelope at this small boundary does **not** close the
target; adding a half-bit reserve worsens the exact deficit by a half bit.

## Consequences

- Bagshaw Case 2 and balanced Type II no longer depend on an external
  characteristic assumption or an unproved energy lemma.
- Zero-loss exponent diagnostics remain non-credit-bearing until the explicit
  divisor envelope and a chosen epsilon/constants reserve fit inside the
  endpoint margin.
- The central Lemire blocker remains cancellation across the signed Möbius
  convolution; this theorem supplies a valid input but does not provide that
  cancellation by itself.
