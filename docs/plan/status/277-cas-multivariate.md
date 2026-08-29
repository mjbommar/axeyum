# Lane: cas-multivariate — the arity survey behind row 3's multivariate blocker

<!-- plan-section: lane-status -->

**Your lane's block (`IN PROGRESS (arity survey landed; representation choice
and one reconstruction to follow)`, cas-multivariate, 2026-08-29).**

## Step 0: the sizing in `docs/plan/status/274-cas-row-three.md` re-verified

`python3 scripts/validate-facts.py` at lane start:

    cas-certificate: 35 total -- kernel-reconstructed 7, cas-internal 28

Unchanged. The cluster breakdown (NRA geometry 10, WZ 9, gf2 4,
real-algebraic 4, partial fractions 1) matches.

## The arity survey — measured from the committed certificates, not from prose

`artifacts/geometry-certificates/*.json` carry the actual `MvPoly` data. Read
directly:

| certificate | coords | sat vars | generators | conclusions | total vars | max total degree | max terms in one poly | total terms |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| thales-right-angle-in-semicircle | 6 | 0 | 1 | 1 | 6 | 2 | 8 | 17 |
| medians-concurrent | 8 | 0 | 2 | 1 | 8 | 2 | 10 | 32 |
| orthocentre-altitudes-concurrent | 8 | 0 | 2 | 1 | 8 | 2 | 8 | 26 |
| parallelogram-diagonals-bisect | 8 | 1 | 3 | 2 | 9 | 3 | 8 | 47 |
| centroid-divides-medians | 8 | 1 | 3 | 2 | 9 | 3 | 10 | 55 |
| rhombus-diagonals-perpendicular | 8 | 1 | 4 | 1 | 9 | 3 | 12 | 73 |
| pappus-hexagon | 18 | 1 | 9 | 1 | 19 | 3 | 10 | 137 |
| euler-line | 10 | 1 | 5 | 1 | 11 | 6 | 74 | 331 |
| simson-line | 14 | 3 | 10 | 1 | 17 | 9 | 324 | 1992 |
| varignon-midpoint-parallelogram | 0 | 0 | 0 | 2 | 0 | 0 | 0 | 0 |

**The brief's cheaper alternative — "the geometry cluster may be entirely 2- or
3-variable, so a bivariate/trivariate bridge unblocks the same facts" — is
REFUTED.** The minimum arity is **6** (Thales) and the maximum is **19**
(Pappus, including its saturation variable). No fixed small arity covers even
two of the ten. A fixed-arity bridge is not the cheaper option here.

## Two of the ten carry NOTHING to reconstruct, and that is a finding

The obligation a geometry certificate states is
`conclusion = Σᵢ cofactorᵢ · generatorᵢ` **between polynomials already in the
CAS's canonical `MvPoly` form**. For two certificates that identity is empty:

- **varignon-midpoint-parallelogram** — `generators: []`, and BOTH conclusion
  polynomials are `{"terms": []}`, the zero polynomial. There is no identity;
  the CAS's normalization into canonical form already discharged it. A kernel
  reconstruction of the *certificate as stated* would be `0 = 0`.
- **thales-right-angle-in-semicircle** — one generator, one conclusion, and the
  single cofactor is the constant `1`. The conclusion polynomial is
  **byte-identical** to the generator polynomial. The kernel obligation is
  `refl`.

This matters for how the remaining 18 should be sized: the reconstructible
content of a geometry certificate is not uniform across the cluster, and the
two facts that look cheapest by term count are cheapest because the certificate
carries no content, not because the theorem is easy. The real modelling work —
that `(bx+cx)/2 − (ax+bx)/2` *is* the polynomial the certificate names — happens
in `axeyum_cas::geometry`'s construction of the `MvPoly`, upstream of anything
the certificate serialises, and reconstruction does not reach it.

**Cheapest genuinely non-vacuous identity: `orthocentre-altitudes-concurrent`**
— 8 variables, 2 generators, both cofactors CONSTANT rationals, 8-term
conclusion, total degree 2. `medians-concurrent` is the same shape at 10 terms.
Those two are the only ones with constant cofactors; the other six need
polynomial × polynomial.

<!-- plan-section: landed-changes -->

| 2026-08-29 | (this commit) | arity survey of the 10 geometry certificates; fixed-arity alternative refuted (arities 6–19); varignon and thales identified as carrying vacuous identities |
