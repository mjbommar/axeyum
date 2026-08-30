# Lane: cas-partial-fractions — the univariate partial-fraction bridge, and correcting a stale sizing

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (kernel-reconstructed 10 -> 11; the "cast only"
sizing in docs/plan/status/317-cas-fractional-cast.md was WRONG for this
target -- see below; next cheapest cas-internal targets are
centroid-divides-medians / parallelogram-diagonals-bisect, cast+prove_mul,
both landed but not yet combined)`, cas-partial-fractions, 2026-08-30).**

## Step 0: verified the handoff rather than trusting it

`docs/plan/status/317-cas-fractional-cast.md` named
`F:cas-partial-fractions-mixed-general-case` "the cast only -- next lane's
cheapest target", in the same table as three `GeometryCertificate` facts
(`centroid-divides-medians`, `parallelogram-diagonals-bisect`, `euler-line`).

**That characterisation does not survive reading the fact.** Read directly:
`axeyum_cas::partial_fractions::PartialFractionCertificate` is a completely
different CAS module from `axeyum_cas::geometry_certify::GeometryCertificate`
-- no `cofactors`/`generators`/`conclusions` shape, no existing translator, and
(per the fact's own `notes` field, written 2026-08-27) "no kernel-side
partial-fraction route exists at all in this kernel." The "cast only" sizing
appears to have been carried over from the geometry facts in the same table
without checking that this one belongs to an unrelated module.

What was ACTUALLY needed, beyond the landed fractional cast:

1. A brand-new translator (`dense_to_rat_poly`) for this certificate's
   `Vec<Rational>`-dense, single-variable representation -- no
   `GeometryCertificate`-shaped translator applies to it.
2. A `Rational`-coefficient generalisation of
   `cas_geometry_mul_bridge_tests`'s `i128`-only polynomial x polynomial
   machinery (`prove_head_product`/`prove_term_mul`/`prove_poly_mul`/
   `prove_poly_combination`), because the quadratic factor's numerator
   (`Cx+D`) is genuinely non-constant -- the constant-cofactor-only
   `prove_scale_rat`/`prove_merge_rat`/`prove_const_combination_rat` the
   fractional-cast lane built cannot express that multiplication.

Detail moved to [`../notes/322-cas-partial-fractions.md`](../notes/322-cas-partial-fractions.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | `f781973b9` | draft: `rat_prelude/cas_partial_fractions_bridge_tests.rs` -- not yet compiled (committed within first 10 tool calls per lane protocol) |
| 2026-08-30 | `24c5e1eb7` | feat: kernel-reconstruct `F:cas-partial-fractions-mixed-general-case` (compiles, 4/4 tests green, both mutation guards verified) |
| 2026-08-30 | `d2a954587` | fix: clippy `doc_markdown` unbalanced backticks |
| 2026-08-30 | `f07c07346` | fact: register `F:cas-partial-fractions-mixed-general-case-kernel-checked`, `cas-certificate` kernel-reconstructed 10 -> 11 |
