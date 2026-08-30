# Lane: cas-multivariate — the multivariate CAS→kernel bridge, and the arity survey that shaped it

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (multivariate bridge landed with one reconstructed
fact; kernel-reconstructed 7 → 8; the arity survey refutes the fixed-arity
alternative for geometry and CONFIRMS it for WZ, so the two clusters do NOT
share one dependency)`, cas-multivariate, 2026-08-29).**

## Step 0: the sizing in `docs/plan/status/274-cas-row-three.md` re-verified

`python3 scripts/validate-facts.py` at lane start:

    cas-certificate: 35 total -- kernel-reconstructed 7, cas-internal 28

Unchanged, and the cluster breakdown (NRA geometry 10, WZ 9, gf2 4,
real-algebraic 4, partial fractions 1) matches.

## The arity survey — measured from the certificates, not from the fact statements

### Geometry (10): arities 6–19. **The fixed-arity alternative is REFUTED.**

`artifacts/geometry-certificates/*.json` carry the actual `MvPoly` data:

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

No small fixed arity covers even two of the ten. A bivariate/trivariate bridge
buys nothing here.

Detail moved to [`../notes/277-cas-multivariate.md`](../notes/277-cas-multivariate.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | `94292a1fb` | arity survey of the 10 geometry certificates; fixed-arity alternative refuted for geometry (arities 6–19); varignon and thales identified as carrying vacuous identities |
| 2026-08-29 | `1cd4aa0ab` | `rat_prelude/cas_geometry_bridge_tests.rs` — the multivariate bridge: representation choice, `prove_scale`/`prove_merge`, translator tests green |
| 2026-08-29 | (this commit) | `F:geometry-orthocentre-cofactor-identity-kernel-checked` — the first multivariate CAS→kernel reconstruction, symbolic in 8 variables, axiom-free, mutation-verified both halves; cas-certificate kernel-reconstructed 7 → 8 |
