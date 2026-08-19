# ADR-0500: Classify inverse-shift support by truncated Artin--Schreier kernels

Status: accepted
Date: 2026-08-19
Index-summary: Reduce every inverse-coset shift collision to an affine binary Artin--Schreier equation and prove its exact kernel dimension

## Context

ADR-0499 decomposes the signed simultaneous-coset energy into shifts

```text
sum_(h in W_d) sum_f mu(f)mu(f+h)
  1_(f^(-1)+(f+h)^(-1) in W_d).
```

The diagonal is known exactly, but the support of each nonzero shift had only
been enumerated.  A useful Berlekamp bound must distinguish the algebraic
stationary fibres from the Möbius signs on those fibres.

## Decision

Classify the support before attempting character cancellation.  For a
nonzero shift `h` and inverse difference

```text
w=f^(-1)+(f+h)^(-1)=h/(f(f+h)) mod x^(ell+1),
```

both `h` and `w` have the same valuation `v`.  Write `h=x^v h_0` and
`w=x^v w_0`, with `h_0,w_0` units.  Cancelling `x^v` gives the affine
Artin--Schreier equation

```text
f^2+h f = h_0 w_0^(-1) mod x^(ell+1-v).              (AS)
```

In `R_r=GF(2)[x]/x^r`, the associated linear map is
`L_h(z)=z^2+h z=z(z+h)`.  If `v=ord_x(h)<r`, then

```text
dim_GF(2) ker L_h = v+1        if 2v<r,
                     floor(r/2) if 2v>=r.             (KD)
```

If `h=0 mod x^r`, the second line applies.  To prove `(KD)`, when `2v<r`
the equation `ord(z)+ord(z+h)>=r` leaves exactly the two disjoint cosets
`x^(r-v)R_r` and `h+x^(r-v)R_r`, each of size `2^v`.  When `2v>=r`, its
solutions are exactly `x^ceil(r/2)R_r`.

Expose `(KD)` as `binary_artin_schreier_kernel_report`.  For a degree-`k`
endpoint shift and interval degree `d`, also attach to every nonzero shift the
proved unsigned support ceiling

```text
#support(h) <= 2^(k+d-ell-1+kappa(ell+1-v,v)),        (SB)
```

capped by the full input population.  Here the factors count inverse
differences `w`, solutions of `(AS)`, the `v` discarded residue coefficients,
and coefficients above the modulus.  The exact report rejects if enumeration
ever exceeds `(SB)`.

## Evidence

The unit test exhausts every `h,z` in `GF(2)[x]/x^r` for `1<=r<=12` and
checks the kernel formula directly.  The endpoint energy control through
`ell=9` independently checks `(SB)` for every shift while reconstructing the
signed and unsigned energies.

These controls test the implementation.  The proof is the valuation split
above; finite enumeration is not used to extrapolate it.

## Alternatives

- Treat inverse-coset equality as an opaque nonlinear constraint: rejected;
  cancellation of the common valuation makes it an additive equation.
- Bound the shift support only by the full polynomial population: retained as
  a cap but rejected as the primary report because it discards the exact
  kernel rank.
- Infer the conjectural Möbius square-root bound from `(KD)`: rejected.  The
  kernel classifies support, not the Berlekamp signs on a nonempty affine
  fibre.

## Consequences

- The remaining local conjecture is now a character-sum problem on explicit
  affine Artin--Schreier fibres, rather than an unclassified inverse equation.
- Any future Berlekamp-rank or Artin--Schreier--Witt argument can use the exact
  stationary dimension and must beat the proved unsigned ceiling.
- This lemma does not close the endpoint tail or low block by itself.
