# ADR-0508: Compute the connected Witt spectrum before absolute values

Status: accepted
Date: 2026-08-19
Index-summary: Embed every valuation layer by blockwise Verschiebung and Fourier transform their signed union before testing conductor support or rank

## Context

ADR-0507 shows that separate valuation-layer estimates discard essential
cancellation.  The connected candidate keeps the complete off-diagonal sum,
but it does not yet explain that cancellation.  A characteristic-two
Heisenberg or low-coordinate character argument first needs one common Witt
object rather than unrelated quotient-level parameters.

For a normalized parameter at valuation `v`, its natural group is
`E_(ell-v)`.  In an odd-indexed 2-typical block, write the source and target
orders as `2^L` and `2^M`.  The blockwise Verschiebung embedding is

```text
c mod 2^L  |->  2^(M-L)c mod 2^M.
```

Taking the product over all odd blocks gives an injective homomorphism into
`E_ell`.

## Decision

Extend the dyadic autocorrelation report with one connected signed Witt
spectrum.  Embed every `(v,h_0/w_0)` correlation by blockwise Verschiebung,
combine collisions in `E_ell`, and only then compute:

- occupied support and absolute mass;
- exact spatial and spectral second moments;
- the exact spectral fourth moment through the group-autocorrelation identity;
- modular Fourier support under both native NTT primes, classified by exact
  principal-unit conductor.

Retain the full product-discriminant residue histogram modulo eight at every
embedded Witt class as well.  Fourier transform each of the four primitive
additive phases `zeta_8^(j r)`, for `j=1,3,5,7`, and check the dyadic Gauss
identity character by character against the signed transform.  This is the
phase-resolved input required by a future central-extension experiment; it is
not itself a cocycle.

The two modular transforms are exact finite-field reductions.  A nonzero
reduction proves that the corresponding cyclotomic transform is nonzero;
simultaneous modular vanishing remains only a diagnostic and is labelled as
such.  Exhaustive controls check that the blockwise embedding is injective and
additive through level six, and that general character conductors have the
expected populations.

## Evidence

At `(ell,k,d)=(9,11,8)`, the `214` normalized parameters embed into `184`
occupied Witt classes.  Their absolute mass drops from `3956` to `3776`, and
their signed total remains `-68`.  The exact moments are

```text
spatial M2    =       126568
spectral M2   =     64802816
spectral M4   = 20409844301824.
```

Every one of the `512` characters is nonzero modulo both transform primes;
the exact-conductor populations are `1,1,2,4,...,256`, with no zero-test
disagreement.

The phase-resolved residue totals are

```text
[52596, 28796, 0, 0, 19792, 28864, 0, 0].
```

For each primitive multiplier `1,3,5,7`, all `512` additive-phase transforms
are nonzero modulo both native primes, again with no zero-test disagreement.
Their checked Gauss combination reconstructs the signed transform at every
character.  A mutation of one phase-transform entry is rejected.

## Consequences

- Sparse Fourier support or wholesale imprimitive-character vanishing cannot
  explain the pinned connected cancellation.  The stronger phase-resolved
  experiment also rules out obtaining sparsity merely by replacing the real
  sign with any one of its four primitive modulo-eight additive phases.
- A Fomenko-style reduction, if viable, must identify low-complexity values or
  factors rather than a small support set.
- The connected spectrum alone does **not** define a Heisenberg commutator.
  In the characteristic-two model of
  [Ito--Takeuchi--Tsushima](https://arxiv.org/abs/2505.22036), the alternating
  form comes from an explicit central-extension cocycle in the group law.  A
  valid rank test here must first retain the phase/fibre variables, propose a
  cocycle, and check associativity plus the commutator identity.
- The phase-resolved connected Witt object now exists.  The next Heisenberg
  experiment must retain the affine-fibre variables and construct a checked
  central extension, not take a formal second difference of either the
  integer-valued spectrum or one of the additive-phase spectra.
- These are bounded diagnostics; no endpoint theorem credit is granted.
