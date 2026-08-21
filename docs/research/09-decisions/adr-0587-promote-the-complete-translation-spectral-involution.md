# ADR-0587: Promote the complete translation spectral involution

Status: accepted
Date: 2026-08-21
Index-summary: Prove the full Hayes-class translation functional equation and price all characters it forces to vanish

## Context

ADR-0581 uses `F(x) -> F(x+1)` only at the first odd binomial index
`2^v_2(n)`, where it interchanges two children of the identity path.  The same
translation acts on the complete principal-unit group, so a character-level
functional equation can potentially annihilate more than that one aggregate
layer.  This structure had been derived in the read-only AC-bridge experiment,
but was not part of the bounded Axeyum CAS or fact ledger.

For the truncated reciprocal class `u(t)` of a monic degree-`n` polynomial,
direct reciprocal substitution gives

```text
sigma(u)(t) = c tau(u)(t),
c=(1+t)^n,
tau(u)(t)=u(t/(1+t))                         mod t^(ell+1).       (T)
```

In characteristic two, `t/(1+t)` is an involution and
`tau(c)=c^(-1)`.  Hence `tau` is a group automorphism and `sigma` is an affine
involution.

## Decision

Add `hayes_translation_spectral_involution`.  It constructs every admitted
principal unit in canonical Witt coordinates, evaluates `(T)`, checks `tau`
against every canonical generator and every group element, checks both
involutions, and verifies that `sigma` permutes the exact degree-`n` Mangoldt
class populations.

Let

```text
K={tau(g)g^(-1):g in G_ell}.
```

Because `G_ell` is abelian, the displayed map is a homomorphism, so the
enumerated image is already a subgroup.  The `tau`-fixed dual characters are
exactly the dual of `G_ell/K`.  Reindexing the degree-`n` Mangoldt sum and the
squared class discrepancy by `sigma` proves

```text
S_n(chi)       = chi(c) S_n(chi o tau),
D2hat_n(chi)   = chi(c) D2hat_n(chi o tau).                (FE)
```

Thus a fixed character with `chi(c)=-1` makes both coefficients zero.

The quotient order is universal, not an experimental fit.  On the additive
space of truncated tails,

```text
tau(t^i)=t^i(1+t)^(-i).
```

For each odd `i<ell`, `(tau-1)t^i` has first nonzero term `t^(i+1)`.
These `floor(ell/2)` distinct leading terms make `tau-1` have at least that
rank.  Conversely `z=t^2/(1+t)` is fixed, so
`z,z^2,...,z^floor(ell/2)` give `floor(ell/2)` independent fixed tails; when
`ell` is odd, the additional top term `t^ell` is fixed modulo `t^(ell+1)`.
Thus the fixed tail dimension is `ceil(ell/2)` and the rank is
`floor(ell/2)`.  Since `g -> tau(g)g^(-1)` has kernel equal to the fixed
principal units,

```text
|K|=2^floor(ell/2),       |G_ell/K|=2^ceil(ell/2).       (COUNT)
```

The CAS now treats `(COUNT)` as a fail-closed invariant.

The parity dichotomy is exact.  If `n` is even, put
`g=(1+t)^(n/2)`; then `tau(g)g^(-1)=c^(-1)`, so `c in K` and no fixed
character has negative evaluation.  If `n` is odd, the first-coordinate sign
character is `tau`-fixed and sends `c` to `-1`, so `c notin K`; exactly half
of the fixed dual has negative evaluation.  The bounded report returns this
exact vanishing count and fails closed if the parity criterion disagrees with
the constructed quotient.

## Evidence

- `translation_spectral_involution_checks_the_complete_character_group`
  checks every class and canonical generator at both Lemire endpoint parities
  for `2<=ell<=8`.
- At `ell=8`, `|K|=16` and the fixed dual has order `16`; degree `17` forces
  eight fixed characters to vanish, whereas degree `18` forces none.
- `translation_spectral_involution_declines_invalid_or_limited_domains`
  checks the positive-degree and group-order refusal paths.
- The universal identities `(T)`, `(FE)`, and the parity dichotomy are the
  algebraic proof.  Exhaustive populations are independent mutation controls.

## Consequences

- The translation theorem is now a typed, replayable Axeyum capability rather
  than an untracked experiment.
- It strictly generalizes the one-character odd-endpoint zero, but does not
  supply `(WITT-LOW)`: the forced odd vanishing family is a shrinking fraction
  of each growing conductor layer, and the even endpoint receives no forced
  character zero.
- Further symmetry arguments should compose with `(FE)` on the complete dual
  rather than count the ADR-0581 split again.
- `(REL)` and Lemire's conjecture remain open.
