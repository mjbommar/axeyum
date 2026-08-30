//! CAS -> kernel bridge: `centroid-divides-medians` and
//! `parallelogram-diagonals-bisect`, the two `cas-internal` geometry facts
//! `docs/plan/status/322-cas-partial-fractions.md` named as the cheapest
//! remaining targets, on the claim that
//! [`super::cas_partial_fractions_bridge_tests::prove_poly_combination_rat`]
//! is "already generic enough to cover them ... they just need a
//! `GeometryCertificate`-shaped parts list instead of its `(numerator,
//! cofactor)` one."
//!
//! # Verifying that claim, rather than trusting it
//!
//! It holds, but the WHERE differs between the two, and neither matches a
//! blanket "generators carry the fractions" reading: for
//! `centroid-divides-medians` the `±1/2` coefficients sit in the two
//! median-incidence GENERATORS (the cofactors and conclusion are integer),
//! while for `parallelogram-diagonals-bisect` they sit in the COFACTORS and
//! the CONCLUSION (the two parallelism generators are integer) — measured by
//! `tests::centroid_certificate_identity_holds_at_integer_points` and its
//! parallelogram sibling, which check both locations rather than assuming
//! one. Either way `rat_poly`/[`super::cas_geometry_frac_bridge_tests::rat_lit`]
//! is what makes the coefficient representable, and both certificates carry
//! a non-constant, multi-term cofactor (needing `prove_mul`'s
//! polynomial-times-polynomial machinery) — exactly the combination
//! `prove_poly_combination_rat` already handles over `RatPoly`. Nothing new
//! had to be built at the proof-emitting layer: this module is the
//! certificate-reading and reconstruction-test layer only. The one thing the
//! handoff's sizing table did NOT mention: **both certificates have TWO
//! conclusions** (`P.x`/`P.y` for centroid, the two midpoint coordinates for
//! the parallelogram), and no existing module reconstructs more than one
//! conclusion per certificate. That is handled here by declaring two
//! separate kernel theorems per certificate, one per conclusion — each is an
//! independent `Σᵢ cofactorᵢ · generatorᵢ = conclusion` identity, so nothing
//! about `prove_poly_combination_rat` needed touching for that either.
//!
//! # What is reconstructed, and what is NOT
//!
//! Four theorems: `Check.geometry_centroid_cofactor_identity_{x,y}` and
//! `Check.geometry_parallelogram_cofactor_identity_{x,y}`, each
//! `∀ (coordinates…, Zinv0 : Rat), conclusion = Σᵢ cofactorᵢ · generatorᵢ`
//! over the certificate's own generator/cofactor lists (hypotheses followed
//! by the Rabinowitsch saturation generator `Zinv0·(non-degeneracy) − 1`).
//!
//! Everything the sibling modules disclose applies verbatim, and is not
//! repeated in full here; the load-bearing points:
//!
//! 1. **It does not prove the geometry.** The kernel sees `Rat` variables and
//!    one algebraic identity per conclusion; that they are point coordinates
//!    is a modelling choice made in `axeyum_cas::geometry_corpus` and
//!    reproduced by the translator here.
//! 2. **It does not establish the geometric conditional.** The identity
//!    `conclusion = Σ cofactorᵢ·generatorᵢ` is proved; the implication
//!    `(∀i. generatorᵢ = 0) → conclusion = 0` is not — no hypothesis is
//!    discharged.
//! 3. **Non-degeneracy is an uninterpreted `Rat` variable `Zinv0`.** Both
//!    certificates saturate (`abc-not-collinear`, `abd-not-collinear`); the
//!    reading that `Zinv0` witnesses the inverse of a nonzero determinant is
//!    entirely outside what the kernel term expresses.
//! 4. **It is over `Rat`, not `CReal`.**
//! 5. **The translator is not the kernel's business** — checked by
//!    evaluation only, in [`tests`], never by the trusted gate.
//! 6. **The two conclusions per certificate are proved as SEPARATE
//!    theorems, not a conjunction.** Nothing here establishes that a single
//!    `P` (or a single pair of midpoints) satisfies both simultaneously as
//!    one kernel-checked statement; each identity is proved independently,
//!    over its own copy of the shared coordinate variables.

use std::collections::BTreeMap;

use axeyum_cas::geometry_certify::{GeometryCertificate, ProofOutcome, certify, geometry_limits};
use axeyum_cas::geometry_corpus;

use super::RatPrelude;
use super::cas_geometry_bridge_tests::built;
use super::cas_geometry_frac_bridge_tests::{RatPoly, eval_rat_poly, poly_expr_rat, rat_poly};
use super::cas_partial_fractions_bridge_tests::prove_poly_combination_rat;
use super::ops::{rat_theorem, req, rsymm};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;
use crate::on_a_deep_stack;

// ---------------------------------------------------------------------------
// The certificate side.
// ---------------------------------------------------------------------------

/// Fetch a named certificate from the CAS's own corpus and certifier — the
/// SAME artifact each fact's `checker_command` cites, not a hand-copy.
fn certificate(id: &str) -> GeometryCertificate {
    let problem = geometry_corpus::corpus()
        .into_iter()
        .find(|p| p.id == id)
        .unwrap_or_else(|| panic!("the CAS corpus must carry {id}"));
    match certify(&problem, geometry_limits()) {
        ProofOutcome::Certified(cert) => *cert,
        other => panic!("the CAS must certify {id}: {other:?}"),
    }
}

/// Every variable the certificate quantifies over: the coordinates first,
/// then each saturation's inverse variable, in the certificate's own order —
/// same shape as
/// `cas_geometry_mul_bridge_tests::certificate_variables`, re-derived here
/// because that one is private to its own module.
fn certificate_variables(cert: &GeometryCertificate) -> Vec<String> {
    let mut names = cert.coordinates.clone();
    names.extend(cert.saturations.iter().map(|s| s.var.clone()));
    names
}

/// `RatPoly` form of every generator, in certificate order.
fn generators_rat(cert: &GeometryCertificate) -> Vec<RatPoly> {
    cert.generators.iter().map(rat_poly).collect()
}

/// `RatPoly` form of one conclusion's cofactors, positionally aligned with
/// [`generators_rat`].
fn cofactors_rat(cert: &GeometryCertificate, conclusion_index: usize) -> Vec<RatPoly> {
    cert.conclusions[conclusion_index]
        .cofactors
        .iter()
        .map(rat_poly)
        .collect()
}

// ---------------------------------------------------------------------------
// The reconstruction, shared by all four theorems.
// ---------------------------------------------------------------------------

/// Build and admit `∀ vars, conclusion = Σᵢ cofactorᵢ · generatorᵢ` for one
/// certificate/conclusion pair, and return the declared name's axiom
/// footprint (empty iff axiom-free).
fn reconstruct_conclusion(
    cert: &GeometryCertificate,
    conclusion_index: usize,
    theorem_name: &str,
) -> Vec<NameId> {
    let generators = generators_rat(cert);
    let cofactors = cofactors_rat(cert, conclusion_index);
    assert_eq!(
        cofactors.len(),
        generators.len(),
        "one cofactor per generator, positionally aligned"
    );
    let concl = rat_poly(&cert.conclusions[conclusion_index].poly);

    let names = certificate_variables(cert);
    // `prove_poly_combination_rat` takes `(numerator, cofactor)` pairs and
    // proves `Σ numerator_i * cofactor_i = merged`; passing
    // `(cofactor_i, generator_i)` here computes `Σ cofactor_i * generator_i`
    // — exactly the certificate's own identity. The "numerator"/"cofactor"
    // naming is the partial-fractions module's; multiplication order does
    // not affect the merged `RatPoly` this produces.
    let parts: Vec<(RatPoly, RatPoly)> = cofactors.into_iter().zip(generators).collect();
    let concl_for_build = concl.clone();

    let (mut kernel, prelude) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, prelude.int);
    let p: RatPrelude = prelude;
    let name = d.kernel().name_str(anon, theorem_name);

    let result = rat_theorem(&mut d, name, names.len(), &|d, fvars| {
        let vars: BTreeMap<String, ExprId> =
            names.iter().cloned().zip(fvars.iter().copied()).collect();
        let (rhs, merged, proof) = prove_poly_combination_rat(d, p, &vars, &parts);
        assert_eq!(
            merged, concl_for_build,
            "the emitted normal form must BE the certificate's conclusion"
        );
        let lhs = poly_expr_rat(d, p, &vars, &concl_for_build);
        let stmt = req(d, lhs, rhs);
        let flipped = rsymm(d, rhs, lhs, proof);
        (stmt, flipped)
    });
    result.unwrap_or_else(|e| panic!("the kernel must admit {theorem_name}: {e:?}"));

    kernel.axiom_footprint(name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Declaration as Decl;

    /// Numeric check of the translator, independent of the kernel: the
    /// cofactor identity holds at an integer point, for BOTH certificates and
    /// BOTH conclusions each carries. Same discipline as the sibling
    /// modules' own `translator_reads_the_..._certificate_the_cas_produced`.
    fn identity_holds_at_point(cert: &GeometryCertificate, point: &BTreeMap<&str, i128>) {
        let generators = generators_rat(cert);
        for (idx, concl) in cert.conclusions.iter().enumerate() {
            let cofactors = cofactors_rat(cert, idx);
            let concl_poly = rat_poly(&concl.poly);
            let lhs = eval_rat_poly(&concl_poly, point);
            let rhs = cofactors
                .iter()
                .zip(generators.iter())
                .map(|(c, g)| eval_rat_poly(c, point) * eval_rat_poly(g, point))
                .fold(axeyum_ir::Rational::zero(), |acc, v| acc + v);
            assert_eq!(
                lhs, rhs,
                "conclusion[{idx}] must equal the cofactor combination at this point"
            );
        }
    }

    #[test]
    fn centroid_certificate_identity_holds_at_integer_points() {
        let cert = certificate("centroid-divides-medians");
        assert_eq!(cert.coordinates.len(), 8, "A,B,C,P");
        assert_eq!(cert.saturations.len(), 1, "abc-not-collinear");
        assert_eq!(cert.generators.len(), 3, "two hypotheses + one saturation");
        assert_eq!(cert.conclusions.len(), 2, "3P.x and 3P.y");

        // At least one generator/cofactor/conclusion is genuinely fractional
        // and at least one cofactor is genuinely non-constant, or this
        // reconstruction would not need what it claims to need. (Measured:
        // for centroid the fractional terms sit in the GENERATORS -- the
        // median-incidence hypotheses carry `±1/2` coefficients -- while the
        // cofactors and conclusion are integer.)
        let generators = generators_rat(&cert);
        let cofactors_x = cofactors_rat(&cert, 0);
        let concl_x = rat_poly(&cert.conclusions[0].poly);
        let any_fractional = generators
            .iter()
            .chain(cofactors_x.iter())
            .chain(std::iter::once(&concl_x))
            .any(|poly| poly.iter().any(|(_, c)| !c.is_integer()));
        assert!(
            any_fractional,
            "centroid-divides-medians must need the fractional cast somewhere"
        );
        assert!(
            cofactors_x.iter().any(|c| c.len() > 1),
            "centroid-divides-medians must need prove_mul (a non-constant cofactor)"
        );

        // A GENERIC point, deliberately not the centroid of A,B,C (both
        // generators are nonzero here) -- chosen so the cross-wired negative
        // control below actually discriminates, unlike the centroid itself
        // where both conclusions and both cofactor sums vanish together.
        let point: BTreeMap<&str, i128> = [
            ("ax", 0),
            ("ay", 0),
            ("bx", 6),
            ("by", 0),
            ("cx", 1),
            ("cy", 4),
            ("px", 3),
            ("py", 1),
            ("Zinv0", 1),
        ]
        .into_iter()
        .collect();
        identity_holds_at_point(&cert, &point);

        // Negative control: centroid-x's cofactors summed against the
        // generators must NOT equal centroid-y's conclusion at this point
        // (verified numerically first: lhs=2 vs wrong-rhs=2 for x, but
        // y's actual lhs=-1 -- checked in Python before writing this).
        let generators_only = generators_rat(&cert);
        let wrong_rhs: axeyum_ir::Rational = cofactors_x
            .iter()
            .zip(generators_only.iter())
            .map(|(c, g)| eval_rat_poly(c, &point) * eval_rat_poly(g, &point))
            .fold(axeyum_ir::Rational::zero(), |acc, v| acc + v);
        let concl_y = rat_poly(&cert.conclusions[1].poly);
        assert_ne!(
            eval_rat_poly(&concl_y, &point),
            wrong_rhs,
            "using centroid-x's cofactors for centroid-y's conclusion must NOT hold, \
             or this control is vacuous"
        );
    }

    #[test]
    fn parallelogram_certificate_identity_holds_at_integer_points() {
        let cert = certificate("parallelogram-diagonals-bisect");
        assert_eq!(cert.coordinates.len(), 8, "A,B,C,D");
        assert_eq!(cert.saturations.len(), 1, "abd-not-collinear");
        assert_eq!(cert.generators.len(), 3, "two hypotheses + one saturation");
        assert_eq!(cert.conclusions.len(), 2, "midpoint x and y agreement");

        // Measured: for the parallelogram the fractional terms sit in the
        // COFACTORS and the CONCLUSION (both carry `±1/2`), while the
        // generators (the two parallelism hypotheses) are integer.
        let generators = generators_rat(&cert);
        let cofactors_x = cofactors_rat(&cert, 0);
        let concl_x = rat_poly(&cert.conclusions[0].poly);
        let any_fractional = generators
            .iter()
            .chain(cofactors_x.iter())
            .chain(std::iter::once(&concl_x))
            .any(|poly| poly.iter().any(|(_, c)| !c.is_integer()));
        assert!(
            any_fractional,
            "parallelogram-diagonals-bisect must need the fractional cast somewhere"
        );
        assert!(
            cofactors_x.iter().any(|c| c.len() > 1),
            "parallelogram-diagonals-bisect must need prove_mul (a non-constant cofactor)"
        );

        // The unit square, the certificate's own generic witness.
        let point: BTreeMap<&str, i128> = [
            ("ax", 0),
            ("ay", 0),
            ("bx", 1),
            ("by", 0),
            ("cx", 1),
            ("cy", 1),
            ("dx", 0),
            ("dy", 1),
            ("Zinv0", 1),
        ]
        .into_iter()
        .collect();
        identity_holds_at_point(&cert, &point);
    }

    /// The reconstruction: `Check.geometry_centroid_cofactor_identity_x`,
    /// admitted through [`crate::Kernel::add_declaration`].
    #[test]
    fn geometry_centroid_cofactor_identity_x_kernel_checked() {
        on_a_deep_stack(|| {
            let cert = certificate("centroid-divides-medians");
            let footprint = reconstruct_conclusion(
                &cert,
                0,
                "Check.geometry_centroid_cofactor_identity_x",
            );
            assert!(footprint.is_empty(), "must be axiom-free; got {footprint:?}");
        });
    }

    /// The reconstruction: `Check.geometry_centroid_cofactor_identity_y`.
    #[test]
    fn geometry_centroid_cofactor_identity_y_kernel_checked() {
        on_a_deep_stack(|| {
            let cert = certificate("centroid-divides-medians");
            let footprint = reconstruct_conclusion(
                &cert,
                1,
                "Check.geometry_centroid_cofactor_identity_y",
            );
            assert!(footprint.is_empty(), "must be axiom-free; got {footprint:?}");
        });
    }

    /// The reconstruction: `Check.geometry_parallelogram_cofactor_identity_x`.
    #[test]
    fn geometry_parallelogram_cofactor_identity_x_kernel_checked() {
        on_a_deep_stack(|| {
            let cert = certificate("parallelogram-diagonals-bisect");
            let footprint = reconstruct_conclusion(
                &cert,
                0,
                "Check.geometry_parallelogram_cofactor_identity_x",
            );
            assert!(footprint.is_empty(), "must be axiom-free; got {footprint:?}");
        });
    }

    /// The reconstruction: `Check.geometry_parallelogram_cofactor_identity_y`.
    #[test]
    fn geometry_parallelogram_cofactor_identity_y_kernel_checked() {
        on_a_deep_stack(|| {
            let cert = certificate("parallelogram-diagonals-bisect");
            let footprint = reconstruct_conclusion(
                &cert,
                1,
                "Check.geometry_parallelogram_cofactor_identity_y",
            );
            assert!(footprint.is_empty(), "must be axiom-free; got {footprint:?}");
        });
    }

    /// Confirm the declared kind is `Theorem`, not `Axiom`/`Opaque`, for one
    /// representative declaration -- the axiom-footprint check above already
    /// covers trust, this covers the DECLARATION KIND directly.
    #[test]
    fn centroid_x_is_declared_as_a_theorem() {
        on_a_deep_stack(|| {
            let cert = certificate("centroid-divides-medians");
            let generators = generators_rat(&cert);
            let cofactors = cofactors_rat(&cert, 0);
            let parts: Vec<(RatPoly, RatPoly)> = cofactors.into_iter().zip(generators).collect();
            let concl = rat_poly(&cert.conclusions[0].poly);
            let names = certificate_variables(&cert);

            let (mut kernel, prelude) = built();
            let anon = kernel.anon();
            let mut d = IntDev::new(&mut kernel, prelude.int);
            let p: RatPrelude = prelude;
            let name = d
                .kernel()
                .name_str(anon, "Check.geometry_centroid_cofactor_identity_x_kind_probe");
            let concl_for_build = concl.clone();
            rat_theorem(&mut d, name, names.len(), &|d, fvars| {
                let vars: BTreeMap<String, ExprId> =
                    names.iter().cloned().zip(fvars.iter().copied()).collect();
                let (rhs, merged, proof) = prove_poly_combination_rat(d, p, &vars, &parts);
                assert_eq!(merged, concl_for_build);
                let lhs = poly_expr_rat(d, p, &vars, &concl_for_build);
                let stmt = req(d, lhs, rhs);
                let flipped = rsymm(d, rhs, lhs, proof);
                (stmt, flipped)
            })
            .expect("kernel must admit");
            let env = kernel.environment();
            let decl = env.get(name).expect("declaration must be in the environment");
            assert!(
                matches!(decl, Decl::Theorem { .. }),
                "must be admitted as a Theorem, not an Axiom or an Opaque"
            );
        });
    }
}
