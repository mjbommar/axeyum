# Lane: cas-prove-mul — polynomial × polynomial cofactors for the CAS→kernel geometry bridge

<!-- plan-section: lane-status -->

**Your lane's block (`IN PROGRESS (step 0 re-measured; the "8 more geometry
certificates" sizing is WRONG — five of the eight also need the fractional
literal cast, so prove_mul alone unblocks THREE)`, cas-prove-mul, 2026-08-29).**

## Step 0: re-measured before building on it

`python3 scripts/validate-facts.py` at lane start:

    2154 facts checked, 0 errors
    cas-certificate: 36 total -- kernel-reconstructed 8, cas-internal 28

Unchanged from `docs/plan/status/277-cas-multivariate.md`. The arity survey in
that lane's table also re-verified against `artifacts/geometry-certificates/`
and reproduces exactly.

## The correction: `prove_mul` does NOT unblock eight certificates

Lane 277 sized "geometry, non-constant cofactors" at **8**, and separately
listed `medians-concurrent` as the one blocked on a fractional-literal cast.
Measured per certificate — counting terms whose serialised `coefficient`
denominator is not `1` — the two blockers **overlap on five certificates**:

| certificate | terms | non-integer coeffs | max cofactor terms | non-constant cofactors | blocked on |
| --- | --- | --- | --- | --- | --- |
| orthocentre-altitudes-concurrent | 26 | 0 | 1 | 0 | (landed) |
| thales-right-angle-in-semicircle | 17 | 0 | 1 | 0 | vacuous identity |
| varignon-midpoint-parallelogram | 0 | 0 | 0 | 0 | vacuous identity |
| medians-concurrent | 32 | **24** | 1 | 0 | fractional cast only |
| **rhombus-diagonals-perpendicular** | **79** | **0** | **12** | **4** | **`prove_mul` only** |
| pappus-hexagon | 145 | 0 | 10 | 9 | `prove_mul` only |
| simson-line | 2010 | 0 | 324 | 10 | `prove_mul` only |
| parallelogram-diagonals-bisect | 53 | **24** | 4 | 6 | `prove_mul` **and** fractional cast |
| centroid-divides-medians | 61 | **16** | 4 | 6 | `prove_mul` **and** fractional cast |
| euler-line | 337 | **272** | 74 | 5 | `prove_mul` **and** fractional cast |

So `prove_mul` alone unblocks **three**, not eight. And
`parallelogram-diagonals-bisect` — the certificate lane 277 named as the
cheapest next target on term count — is **not reachable with `prove_mul`
alone**: every one of its cofactors and both of its conclusions carry `±1/2`
coefficients, so it needs the same cast `medians-concurrent` and
`F:cas-partial-fractions-mixed-general-case` are blocked on.

The cheapest certificate that `prove_mul` alone reaches is
**`rhombus-diagonals-perpendicular`**: 9 variables (8 coordinates plus the
saturation variable `Zinv0`), 4 generators, 1 conclusion, all-integer
coefficients, cofactors of 12/8/6/8 terms. That is this lane's target.

<!-- plan-section: landed-changes -->

| 2026-08-29 | (this commit) | step 0 re-measurement: the "8 more geometry certificates" sizing corrected to 3; `parallelogram-diagonals-bisect` needs the fractional cast too, `rhombus-diagonals-perpendicular` is the cheapest `prove_mul`-only target |
