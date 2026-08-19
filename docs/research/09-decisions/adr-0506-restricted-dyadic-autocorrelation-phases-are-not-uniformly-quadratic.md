# ADR-0506: Restricted dyadic autocorrelation phases are not uniformly quadratic

Status: accepted
Date: 2026-08-19
Index-summary: Reject a fibrewise quadratic Gauss-sum proof and preserve cancellation across exact Artin--Schreier fibre parameters

## Context

ADR-0505 proves that the unrestricted discriminant phase has maximal Boolean
degree, while leaving open the possibility that the inverse-coset
Artin--Schreier equations reduce every relevant phase to a quadratic form.
That would prove cancellation separately on each exact affine fibre.

For a nonzero coefficient shift `h`, the degree signs cancel and
multiplicativity of the dyadic Kronecker character gives

```text
mu(f)mu(f+h)=chi_8(Disc(F)Disc(F+h)).
```

## Decision

Expose `binary_dyadic_autocorrelation_fibre_report`.  Group every contributing
pair by high-coefficient input coset, exact shift, and exact inverse
difference; recover and check affine binary coordinates; compute the unique
`Z/8` ANF of the product discriminant; and require its dyadic character to
reconstruct every existing signed shift correlation.

Reject a uniform fibrewise quadratic theorem.  Preserve the signed sum across
fibre parameters as the next analytic object instead of taking absolute
values fibre by fibre.

## Evidence

At `(ell,k,d)=(9,11,8)`, all `18,884` nonempty exact fibres are verified
affine and contain `130,048` points.  There are `16,587` at-most-quadratic
phases, but the `2,297` nonquadratic fibres contain `61,264` points and attain
support degree seven on a seven-dimensional fibre.  Thus the exception is not
sparse.

The nonquadratic signed correlation is `-202`, compared with `8,622` after
taking absolute values fibrewise; the complete off-diagonal correlation is
`-68`.  These finite values do not prove a bound, but they show exactly where
the observed cancellation is destroyed.

## Consequences

- A quadratic Gauss-sum lemma may handle many fibres but cannot be the uniform
  local theorem by itself.
- The next dyadic estimate must aggregate shifts and inverse differences,
  ideally after grouping their 2-typical Witt blocks, before applying an
  absolute-value inequality.
- The exact affine and phase machinery remains reusable for checking such an
  aggregate identity; no endpoint theorem credit is granted.
