# Lane: cas-geometry-pair — centroid-divides-medians and parallelogram-diagonals-bisect, kernel-reconstructed

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (kernel-reconstructed 11 -> 13; verified rather
than trusted the "already generic enough" claim -- it held for the
proof-emitting layer, but neither certificate's two-conclusions shape was
in the handoff's sizing; next cheapest cas-internal targets are
thales-right-angle-in-semicircle and varignon-midpoint-parallelogram, both
VACUOUS or near-vacuous identities cheaper than anything landed this
session)`, cas-geometry-pair, 2026-08-30).**

## Step 0: verified the "already generic enough" claim rather than trusting it

`docs/plan/status/322-cas-partial-fractions.md` named `centroid-divides-medians`
and `parallelogram-diagonals-bisect` as the next cheapest `cas-internal`
targets, and said the partial-fractions lane's new
`prove_poly_combination_rat` (and its three layers) were "already generic
enough to cover them ... they just need a `GeometryCertificate`-shaped parts
list instead of its `(numerator, cofactor)` one."

**The claim held at the proof-emitting layer, with zero new proof code.**
`prove_poly_combination_rat` was widened from module-private to
`pub(super)` in `cas_partial_fractions_bridge_tests.rs` (one-line change) and
called directly with `(cofactor, generator)` `RatPoly` pairs read from each
certificate. Nothing about `prove_head_product_rat`/`prove_term_mul_rat`/
`prove_poly_mul_rat`/`prove_poly_combination_rat` needed touching.

**What the handoff did NOT mention: both certificates have TWO conclusions
each** (centroid: `3P.x`/`3P.y`; parallelogram: midpoint-x/midpoint-y
agreement), and no existing module reconstructs more than one conclusion per
certificate. This needed two separate kernel theorems per certificate — an
ordinary application of the existing machinery, not new proof-emitting code,
but real additional test-writing and kernel-checking work the sizing table
did not surface.

Detail moved to [`../notes/327-cas-geometry-pair.md`](../notes/327-cas-geometry-pair.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | `9ae10bb01` | draft: `rat_prelude/cas_geometry_pair_bridge_tests.rs` -- not yet compiled (committed within first 10 tool calls per lane protocol) |
| 2026-08-30 | `0859c3992` | fix: module now compiles (missing `NatOps` import, `axiom_footprint`'s real `Vec<NameId>` return type) |
| 2026-08-30 | `b2d42508f` | fix: numeric checks -- wrong assumption about WHERE fractions live per certificate, plus a vacuous negative control |
| 2026-08-30 | `4f45e630a` | feat: kernel-reconstruct both certificates; register both sibling facts; `cas-certificate` kernel-reconstructed 11 -> 13 |
