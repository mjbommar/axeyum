# ADR-0563: Retain the proper-power margin in the weak fourth-moment target

Status: accepted
Date: 2026-08-20
Index-summary: Replace the overstrong connected-kurtosis target by the exact weak endpoint threshold without confusing positive Mangoldt mass with an irreducible

## Context

The connected target `R_0<=4`, equivalently `K_4<=M_2^2`, is close to the
observed Gaussian scale but much stronger than endpoint positivity requires.
A review sweep proposed the weaker condition

```text
M_4 < mu^4,                 mu=2^(n-ell).
```

The exponential slack in that observation is real, but the displayed
condition is not yet an irreducibility theorem.  It proves only `N_n(1)>0`
for the Mangoldt-weighted identity-class population.  At the odd endpoint the
exact identity is

```text
N_n(1)=1+n I_n(1),
```

so the bad case `I_n(1)=0`, `N_n(1)=1` remains positive.  At the even endpoint
all proper prime powers must likewise be removed.

## Decision

Expose `WeakFourthMomentEndpointLedger` with the exact sufficient threshold

```text
M_4 < (mu-P_n)^4,                                  (W4)
```

where `P_n=1` at the odd endpoint and `P_n` is the repository's proved
square-plus-higher-power upper bound at the even endpoint.  Since
`max_e |N_n(e)-mu|^4<=M_4`, `(W4)` gives
`N_n(1)>P_n`, hence a shaped irreducible.

Retain `mu^4` in the report under the explicit name
`positivity_only_fourth_moment_threshold`; never label it sufficient for
irreducibility.  Also retain the proved second-moment factor

```text
Sigma(ell)=sum_(j=2)^ell 2^(j-1)(j-1)^2
          =2^ell(ell^2-4ell+6)-6
```

and the exact rational root-kurtosis target

```text
R_0 < 2^ell (mu-P_n)^4 / (mu Sigma(ell))^2.          (WR)
```

The operation checks only these implications.  It does not prove `(W4)` or
`(WR)`.

## Evidence

At the degree-400 handoff, `(WR)` allows root-ratio exponents approximately

```text
(ell,n)       log2 allowed R_0
(200,401)       171.482426
(200,402)       173.482426.
```

Thus the strategic conclusion of the sweep survives correction: the old
target `R_0<=4` is stronger than necessary by roughly `2^169` at the first
odd symbolic row.  Relative to the trivial `R_0<=2^ell`, the true demand is
only a polynomial-size saving (about 28.5 bits at `(200,401)`).

The proper-power correction is operationally visible at small levels.  With
the proved even upper bound there is no positive reserve at `ell=8,9,10`;
the eventual strong-target crossover is `ell=15` on the odd side and
`ell=17` on the even side, not the review sweep's positivity-only even value
`ell=11`.  The separate finite certificates through degree 400 make these
small thresholds irrelevant to the eventual proof, but they are important
mutation controls for the implication.

The exact `(ell,n)=(8,17)` distribution already satisfies `(W4)` even though
it fails the older `|D_e|<=2^ell` diagnostic.  This demonstrates that the
new ledger is materially weaker, not a renaming of the old target.

## Consequences

- The live analytic target is the weak, proper-power-aware fourth moment
  `(W4)`, not Gaussian fourth-cumulant domination.
- Previously rejected mechanisms must be re-audited against the polynomial
  saving from trivial kurtosis actually required by `(WR)`.
- A proof of `M_4<mu^4` alone must not be credited as a Lemire proof.
- No universal fourth-moment bound is established by this ADR.
