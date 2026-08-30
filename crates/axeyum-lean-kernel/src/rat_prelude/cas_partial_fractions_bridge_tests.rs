//! CAS -> kernel bridge, the **univariate partial-fraction** slice:
//! `F:cas-partial-fractions-mixed-general-case`.
//!
//! `docs/plan/status/317-cas-fractional-cast.md` named this fact "the cast
//! only -- next lane's cheapest target". That claim does NOT survive reading
//! the fact: `axeyum_cas::partial_fractions::PartialFractionCertificate` is
//! not a [`axeyum_cas::geometry_certify::GeometryCertificate`] at all --
//! there is no `cofactors`/`generators`/`conclusions` shape here, no existing
//! translator, and no reconstruction of any kind in this kernel before this
//! module. What actually blocked it was the SAME two things
//! `centroid-divides-medians`/`parallelogram-diagonals-bisect` are blocked
//! on -- the fractional cast (landed, [`super::cas_geometry_frac_bridge_tests::rat_lit`])
//! AND a `Rational`-coefficient generalisation of
//! [`super::cas_geometry_mul_bridge_tests`]'s polynomial-times-polynomial
//! machinery (that module is `i128`-coefficient only) -- **plus** a brand
//! new translator, because this certificate's shape has never been read by
//! this kernel before. See "What this module actually needed" below for the
//! measured size of that gap.
//!
//! # The concrete instance
//!
//! `F:cas-partial-fractions-mixed-general-case` names
//! `partial_fractions::tests::mixed_general_case`:
//! `p(x) = x+1`, `q(x) = (x-1)^2(x^2+1)` (a repeated linear factor and an
//! irreducible quadratic in one denominator), produced by the real producer
//! ([`mixed_general_case_certificate`] calls
//! [`axeyum_cas::partial_fractions::partial_fractions`] directly, the same
//! function the fact's `checker_command` exercises -- nothing here is
//! hand-copied). Solving gives exact rationals `A = -1/2`, `B = 1`,
//! `C = 1/2`, `D = -1/2` for `p/q = A/(x-1) + B/(x-1)^2 + (Cx+D)/(x^2+1)`.
//!
//! # What is reconstructed, and what is NOT
//!
//! [`crate::Kernel::add_declaration`] admits exactly the CLEARED-DENOMINATOR
//! coefficient-matching identity the checker's own comment names
//! (`partial_fractions.rs:426`, `"p = whole*q + leading * Sigma(numerator *
//! cofactor)"`), specialised to this instance's `whole = 0` and `leading =
//! 1` (both asserted, not assumed -- see [`mixed_general_case_body`]):
//!
//! ```text
//! forall x : Rat,
//!   x + 1 = (-1/2)*((x-1)*(x^2+1)) + 1*(x^2+1) + ((1/2)*x + (-1/2))*((x-1)*(x-1))
//! ```
//!
//! Five things this does NOT establish, mirroring the sibling geometry
//! modules' own disclosed scope:
//!
//! 1. **It does not prove the rational-function equality the fact's `formal`
//!    field states.** That statement existentially quantifies `A,B,C,D` and
//!    carries a `q(x) != 0` hypothesis; what is proved here is the cleared-
//!    denominator polynomial identity at the certificate's own CONCRETE
//!    `A,B,C,D`, unconditionally over all `x` (no hypothesis needed, since
//!    clearing denominators removes the restriction) -- the same relocation
//!    the geometry facts make for their "implication" (item 2 in their own
//!    module docs).
//! 2. **None of the checker's four structural guards are reconstructed**:
//!    the power-set guard (powers are exactly `{1,..,mult}` per factor), the
//!    numerator-degree-below-factor-degree guard, the pairwise-coprimality
//!    guard (needs a GCD computation, not an identity), and the
//!    q-reconstruction identity (`q = leading * product(factor^mult)`) --
//!    this module proves only the coefficient-matching identity.
//! 3. **`whole` and `leading` are exercised only at their trivial values**
//!    (`whole = 0`, `leading = 1`) for this instance; nothing here measures
//!    a non-trivial `whole*q` term or a `leading != 1` scale.
//! 4. **It is over `Rat`, not `CReal`.** A rational-coefficient identity
//!    holds in every commutative ring with the right elements.
//! 5. **The translator is checked by evaluation only**
//!    ([`tests::translator_agrees_with_the_dense_evaluator_at_a_point`]),
//!    never by the trusted gate -- the kernel never sees a `Vec<Rational>`.
//!
//! # What this module actually needed (the size of the "cast only" error)
//!
//! | piece | status before this lane | needed here |
//! | --- | --- | --- |
//! | fractional-literal cast (`rat_lit`) | landed (fractional-cast lane) | reused verbatim |
//! | `Rational`-coefficient poly x poly (`prove_*_rat` below) | did NOT exist -- `cas_geometry_mul_bridge_tests` is `i128`-only | built here: [`prove_head_product_rat`], [`prove_term_mul_rat`], [`prove_poly_mul_rat`], [`prove_poly_combination_rat`] |
//! | translator from `PartialFractionCertificate` to this kernel's `RatPoly` | did NOT exist -- no `GeometryCertificate` shape to reuse | built here: [`dense_to_rat_poly`] plus the local coefficient-matching reconstruction in [`mixed_general_case_body`] |
//!
//! Coefficient-independent monomial machinery
//! ([`super::cas_geometry_mul_bridge_tests::prove_mono_mul`],
//! `mul_left_comm`, `factors_expr`, `rat_zero_mul`, `mono_factors`,
//! `mul_mono`) needed no change at all and is reused as-is, widened from
//! module-private to `pub(super)` for this file to reach it -- the sorted-
//! merge argument that module's doc gives for MULTIPLE variables degenerates
//! correctly to the single variable `"x"` this module ever binds (every
//! comparison in the merge is between two copies of the same string, and the
//! `<=` branch handles equality and strict order identically, so nothing
//! here special-cases the univariate case).

use axeyum_cas::partial_fractions::{
    PartialFractionCertificate, partial_fractions, verify_partial_fraction_certificate,
};
use axeyum_ir::Rational;
use axeyum_ir::poly;
use std::collections::BTreeMap;

use super::RatPrelude;
use super::cas_geometry_bridge_tests::{Mono, built, mono_expr};
use super::cas_geometry_frac_bridge_tests::{
    RatPoly, RatTerm, eval_rat_poly, poly_expr_rat, prove_merge_rat, rat_lit, term_expr_rat,
};
use super::cas_geometry_mul_bridge_tests::{
    factors_expr, mono_factors, mul_left_comm, mul_mono, prove_mono_mul, rat_zero_mul,
};
use super::ops::{radd, rat_theorem, rchain, rcongr, req, rmul, rrefl, rsymm};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::on_a_deep_stack;

// ---------------------------------------------------------------------------
// The translator: dense `Vec<Rational>` (LSB-first, single variable "x") ->
// this kernel's sparse `RatPoly`.
// ---------------------------------------------------------------------------

/// `Vec<Rational>` (LSB-first, as [`axeyum_ir::poly`] and
/// `axeyum_cas::partial_fractions` both represent a univariate polynomial) ->
/// [`RatPoly`] over the single variable `"x"`. Total: unlike the multivariate
/// `int_poly`/`rat_poly` translators this never declines, and unlike them
/// there is only ever one variable, so `Mono` is always `vec![]` (the
/// constant term) or `vec![("x".to_string(), k)]` for `k >= 1` -- already in
/// ascending order, since `RatPoly`'s sort compares `Mono`s lexicographically
/// and an empty vector sorts before every non-empty one, and two
/// single-variable-name entries compare by exponent.
pub(super) fn dense_to_rat_poly(coeffs: &[Rational]) -> RatPoly {
    coeffs
        .iter()
        .enumerate()
        .filter(|(_, c)| !c.is_zero())
        .map(|(k, &c)| {
            let mono: Mono = if k == 0 {
                Vec::new()
            } else {
                vec![("x".to_string(), u32::try_from(k).expect("degree fits u32"))]
            };
            (mono, c)
        })
        .collect()
}

// ---------------------------------------------------------------------------
// The two proof-emitting primitives this module needed and the sibling
// modules did not have: `Rational`-coefficient polynomial x polynomial.
// ---------------------------------------------------------------------------

/// `term_expr_rat(a) * term_expr_rat(b) = term_expr_rat(a . b)` for two
/// single [`RatTerm`]s -- the `Rational`-coefficient generalisation of
/// [`super::cas_geometry_mul_bridge_tests::prove_head_product`].
///
/// Four rewrites instead of six: `mul_assoc` reversed to expose the left
/// monomial, `mul_left_comm` to lift the right coefficient out, `mul_assoc`
/// forward to pair the two coefficients, then -- where the `i128` case needed
/// `Rat.ofInt_mul` plus an `rrefl` collapse -- a SINGLE `rrefl` ascribes
/// `a_rat * b_rat` directly to the canonical `rat_lit(a.1 * b.1)`, the same
/// replacement [`super::cas_geometry_frac_bridge_tests::prove_scale_rat`] and
/// `prove_merge_rat` already make (the kernel's own `Rat.mul` computation on
/// two literals is what checks it).
fn prove_head_product_rat(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    a: &RatTerm,
    b: &RatTerm,
) -> (RatTerm, ExprId) {
    let a_rat = rat_lit(d, a.1);
    let a_mono = mono_expr(d, p, vars, &a.0);
    let b_rat = rat_lit(d, b.1);
    let b_mono = mono_expr(d, p, vars, &b.0);

    let a_e = rmul(d, a_rat, a_mono);
    let b_e = rmul(d, b_rat, b_mono);
    let start = rmul(d, a_e, b_e);

    // 1. (ca * m1) * (cb * m2) = ca * (m1 * (cb * m2))
    let inner1 = rmul(d, a_mono, b_e);
    let mid1 = rmul(d, a_rat, inner1);
    let step1 = d.lemma(p.mul_assoc, &[a_rat, a_mono, b_e]);

    // 2. m1 * (cb * m2) = cb * (m1 * m2)
    let (swapped, swap_proof) = mul_left_comm(d, p, a_mono, b_rat, b_mono);
    let mid2 = rmul(d, a_rat, swapped);
    let step2 = rcongr(d, inner1, swapped, swap_proof, &|d, t| rmul(d, a_rat, t));

    // 3. ca * (cb * (m1 * m2)) = (ca * cb) * (m1 * m2)
    let monos = rmul(d, a_mono, b_mono);
    let coeffs = rmul(d, a_rat, b_rat);
    let mid3 = rmul(d, coeffs, monos);
    let assoc3 = d.lemma(p.mul_assoc, &[a_rat, b_rat, monos]);
    let step3 = rsymm(d, mid3, mid2, assoc3);

    // 4. (ca_rat * cb_rat) collapses, by the kernel's own `Rat.mul`
    //    computation, straight to the canonical literal `rat_lit(a.1*b.1)`.
    let product_val = a.1 * b.1;
    let canon_coeff = rat_lit(d, product_val);
    let mid4 = rmul(d, canon_coeff, monos);
    let step4 = rrefl(d, mid4);

    // 5. m1 * m2 = canonical monomial (coefficient-independent; reused as-is).
    let a_factors = mono_factors(&a.0);
    let b_factors = mono_factors(&b.0);
    let (merged_factors, mono_proof) = prove_mono_mul(d, p, vars, &a_factors, &b_factors);
    let merged_mono_e = factors_expr(d, p, vars, &merged_factors);
    let mid5 = rmul(d, canon_coeff, merged_mono_e);
    let step5 = rcongr(d, monos, merged_mono_e, mono_proof, &|d, t| {
        rmul(d, canon_coeff, t)
    });

    // 6. the final term, by construction, IS the canonical `term_expr_rat`.
    let product: RatTerm = (mul_mono(&a.0, &b.0), product_val);
    let end = term_expr_rat(d, p, vars, &product);
    let step6 = rrefl(d, end);

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, step2),
            (mid3, step3),
            (mid4, step4),
            (mid5, step5),
            (end, step6),
        ],
    );
    debug_assert_eq!(
        merged_factors,
        mono_factors(&product.0),
        "the merged factor list must be the product monomial's own"
    );
    (product, proof)
}

/// `term_expr_rat(t) * poly_expr_rat(b) = poly_expr_rat(t . b)`, the
/// `Rational`-coefficient generalisation of
/// [`super::cas_geometry_mul_bridge_tests::prove_term_mul`].
fn prove_term_mul_rat(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    t: &RatTerm,
    b: &[RatTerm],
) -> (RatPoly, ExprId) {
    let t_e = term_expr_rat(d, p, vars, t);
    let Some((b_head, b_rest)) = b.split_first() else {
        return (Vec::new(), d.lemma(p.mul_zero, &[t_e]));
    };

    let b_head_e = term_expr_rat(d, p, vars, b_head);
    let b_rest_e = poly_expr_rat(d, p, vars, b_rest);
    let b_e = radd(d, b_head_e, b_rest_e);
    let start = rmul(d, t_e, b_e);

    // 1. X * (h + B') = X*h + X*B'
    let x_head = rmul(d, t_e, b_head_e);
    let x_rest = rmul(d, t_e, b_rest_e);
    let mid1 = radd(d, x_head, x_rest);
    let step1 = d.lemma(p.left_distrib, &[t_e, b_head_e, b_rest_e]);

    // 2. X*h = the canonical product term.
    let (product, product_proof) = prove_head_product_rat(d, p, vars, t, b_head);
    let product_e = term_expr_rat(d, p, vars, &product);
    let mid2 = radd(d, product_e, x_rest);
    let step2 = rcongr(d, x_head, product_e, product_proof, &|d, t| {
        radd(d, t, x_rest)
    });

    // 3. give the head term `poly_expr_rat`'s `+ 0` terminator.
    let product_poly = vec![product];
    let product_poly_e = poly_expr_rat(d, p, vars, &product_poly);
    let add_zero = d.lemma(p.add_zero, &[product_e]);
    let terminated = rsymm(d, product_poly_e, product_e, add_zero);
    let mid3 = radd(d, product_poly_e, x_rest);
    let step3 = rcongr(d, product_e, product_poly_e, terminated, &|d, t| {
        radd(d, t, x_rest)
    });

    // 4. recurse on the tail, then merge.
    let (tail_poly, tail_proof) = prove_term_mul_rat(d, p, vars, t, b_rest);
    let tail_poly_e = poly_expr_rat(d, p, vars, &tail_poly);
    let mid4 = radd(d, product_poly_e, tail_poly_e);
    let step4 = rcongr(d, x_rest, tail_poly_e, tail_proof, &|d, t| {
        radd(d, product_poly_e, t)
    });

    let (merged, merge_proof) = prove_merge_rat(d, p, vars, &product_poly, &tail_poly);
    let end = poly_expr_rat(d, p, vars, &merged);

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, step2),
            (mid3, step3),
            (mid4, step4),
            (end, merge_proof),
        ],
    );
    (merged, proof)
}

/// **`prove_poly_mul_rat`**: `poly_expr_rat(a) * poly_expr_rat(b) =
/// poly_expr_rat(a . b)`, the `Rational`-coefficient generalisation of
/// [`super::cas_geometry_mul_bridge_tests::prove_poly_mul`].
fn prove_poly_mul_rat(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    a: &[RatTerm],
    b: &[RatTerm],
) -> (RatPoly, ExprId) {
    let b_e = poly_expr_rat(d, p, vars, b);
    let Some((a_head, a_rest)) = a.split_first() else {
        return (Vec::new(), rat_zero_mul(d, p, b_e));
    };

    let a_head_e = term_expr_rat(d, p, vars, a_head);
    let a_rest_e = poly_expr_rat(d, p, vars, a_rest);
    let a_e = radd(d, a_head_e, a_rest_e);
    let start = rmul(d, a_e, b_e);

    // 1. (h + A') * B = h*B + A'*B
    let head_times = rmul(d, a_head_e, b_e);
    let rest_times = rmul(d, a_rest_e, b_e);
    let mid1 = radd(d, head_times, rest_times);
    let step1 = d.lemma(p.right_distrib, &[a_head_e, a_rest_e, b_e]);

    let (head_poly, head_proof) = prove_term_mul_rat(d, p, vars, a_head, b);
    let head_poly_e = poly_expr_rat(d, p, vars, &head_poly);
    let mid2 = radd(d, head_poly_e, rest_times);
    let step2 = rcongr(d, head_times, head_poly_e, head_proof, &|d, t| {
        radd(d, t, rest_times)
    });

    let (rest_poly, rest_proof) = prove_poly_mul_rat(d, p, vars, a_rest, b);
    let rest_poly_e = poly_expr_rat(d, p, vars, &rest_poly);
    let mid3 = radd(d, head_poly_e, rest_poly_e);
    let step3 = rcongr(d, rest_times, rest_poly_e, rest_proof, &|d, t| {
        radd(d, head_poly_e, t)
    });

    let (merged, merge_proof) = prove_merge_rat(d, p, vars, &head_poly, &rest_poly);
    let end = poly_expr_rat(d, p, vars, &merged);

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, step1),
            (mid2, step2),
            (mid3, step3),
            (end, merge_proof),
        ],
    );
    (merged, proof)
}

/// `Sigma_i (poly_expr_rat(numerator_i) . poly_expr_rat(cofactor_i)) =
/// poly_expr_rat(Sigma_i numerator_i . cofactor_i)` for POLYNOMIAL
/// numerators and cofactors, the `Rational`-coefficient generalisation of
/// [`super::cas_geometry_mul_bridge_tests::prove_poly_combination`].
pub(super) fn prove_poly_combination_rat(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    parts: &[(RatPoly, RatPoly)],
) -> (ExprId, RatPoly, ExprId) {
    let ((numerator, cofactor), rest) = parts
        .split_first()
        .expect("prove_poly_combination_rat: at least one term is required");
    let numerator_e = poly_expr_rat(d, p, vars, numerator);
    let cofactor_e = poly_expr_rat(d, p, vars, cofactor);
    let head_e = rmul(d, numerator_e, cofactor_e);
    let (product, product_proof) = prove_poly_mul_rat(d, p, vars, numerator, cofactor);
    let product_e = poly_expr_rat(d, p, vars, &product);

    if rest.is_empty() {
        return (head_e, product, product_proof);
    }

    let (tail_e, tail_poly, tail_proof) = prove_poly_combination_rat(d, p, vars, rest);
    let start = radd(d, head_e, tail_e);
    let tail_poly_e = poly_expr_rat(d, p, vars, &tail_poly);

    let mid1 = radd(d, product_e, tail_e);
    let step1 = rcongr(d, head_e, product_e, product_proof, &|d, t| {
        radd(d, t, tail_e)
    });
    let mid2 = radd(d, product_e, tail_poly_e);
    let step2 = rcongr(d, tail_e, tail_poly_e, tail_proof, &|d, t| {
        radd(d, product_e, t)
    });

    let (merged, merge_proof) = prove_merge_rat(d, p, vars, &product, &tail_poly);
    let merged_e = poly_expr_rat(d, p, vars, &merged);

    let (_, proof) = rchain(
        d,
        start,
        &[(mid1, step1), (mid2, step2), (merged_e, merge_proof)],
    );
    (start, merged, proof)
}

// ---------------------------------------------------------------------------
// The certificate side: the real producer, and the checker's own
// coefficient-matching recipe re-derived on the Rust side (untrusted,
// prepares the data the kernel will be asked to check).
// ---------------------------------------------------------------------------

/// `partial_fractions::tests::mixed_general_case`'s certificate, produced by
/// the real [`axeyum_cas::partial_fractions::partial_fractions`] -- not
/// hand-copied.
fn mixed_general_case_certificate() -> PartialFractionCertificate {
    let p = vec![Rational::integer(1), Rational::integer(1)]; // x + 1
    let lin_sq = vec![
        Rational::integer(1),
        Rational::integer(-2),
        Rational::integer(1),
    ]; // (x-1)^2
    let quad = vec![
        Rational::integer(1),
        Rational::integer(0),
        Rational::integer(1),
    ]; // x^2+1
    let q = poly::ratpoly_mul(&lin_sq, &quad).expect("ratpoly_mul must not overflow");
    partial_fractions(&p, &q).expect("the CAS must certify mixed_general_case")
}

/// `factor^exp` by repeated [`poly::ratpoly_mul`]; `exp == 0` gives `[1]`.
/// A local re-derivation of `partial_fractions.rs`'s own private `poly_pow`
/// (not reachable from here -- it is not `pub`), transcribed from the
/// checker's own documented recipe (`partial_fractions.rs:426-442`), not
/// from the producer's.
fn poly_pow(base: &[Rational], exp: u32) -> Vec<Rational> {
    let mut acc = vec![Rational::integer(1)];
    for _ in 0..exp {
        acc = poly::ratpoly_mul(&acc, base).expect("poly_pow: overflow");
    }
    acc
}

/// The product, over every factor except index `skip`, of `factor^mult`. A local
/// re-derivation of `partial_fractions.rs`'s own private `product_excluding`,
/// for the same reason as [`poly_pow`].
fn product_excluding(factors: &[(Vec<Rational>, u32)], skip: usize) -> Vec<Rational> {
    let mut acc = vec![Rational::integer(1)];
    for (idx, (factor, mult)) in factors.iter().enumerate() {
        if idx == skip {
            continue;
        }
        acc =
            poly::ratpoly_mul(&acc, &poly_pow(factor, *mult)).expect("product_excluding: overflow");
    }
    acc
}

/// Group `cert.terms` by their `factor`, recovering each group's multiplicity
/// as its term count -- the same grouping
/// `verify_partial_fraction_certificate` performs internally, re-derived here
/// because the certificate does not carry `(factor, multiplicity)` pairs
/// directly.
fn factors_with_mult(cert: &PartialFractionCertificate) -> Vec<(Vec<Rational>, u32)> {
    let mut groups: Vec<(Vec<Rational>, u32)> = Vec::new();
    for term in &cert.terms {
        match groups.iter_mut().find(|(f, _)| *f == term.factor) {
            Some((_, mult)) => *mult += 1,
            None => groups.push((term.factor.clone(), 1)),
        }
    }
    groups
}

/// For every term, `(numerator, cofactor)` as dense `Vec<Rational>` pairs,
/// where `cofactor = product_excluding(i) * factor_i^(mult_i - power)` --
/// exactly the checker's own `p = whole*q + leading*Sigma(numerator*cofactor)`
/// recipe, specialised to `leading = 1` (asserted, not assumed).
fn numerator_cofactor_pairs(
    cert: &PartialFractionCertificate,
) -> Vec<(Vec<Rational>, Vec<Rational>)> {
    assert_eq!(
        cert.leading,
        Rational::integer(1),
        "this instance's leading scalar must be 1 (q is monic); the general \
         `leading != 1` case is not exercised here"
    );
    let groups = factors_with_mult(cert);
    let mut pairs = Vec::with_capacity(cert.terms.len());
    for (i, (factor, mult)) in groups.iter().enumerate() {
        let cofactor_excl = product_excluding(&groups, i);
        for term in cert.terms.iter().filter(|t| t.factor == *factor) {
            let remaining_power = mult - term.power;
            let remaining = poly_pow(factor, remaining_power);
            let cofactor = poly::ratpoly_mul(&cofactor_excl, &remaining).expect("overflow");
            pairs.push((term.numerator.clone(), cofactor));
        }
    }
    pairs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Declaration as Decl;

    /// The producer's own certificate is genuinely checkable by its own
    /// independent checker -- the same fact `checker_command` this bridge
    /// reconstructs a fragment of.
    #[test]
    fn the_producer_certificate_is_accepted_by_the_independent_checker() {
        let cert = mixed_general_case_certificate();
        assert_eq!(verify_partial_fraction_certificate(&cert), Some(true));
        assert_eq!(cert.terms.len(), 3);
    }

    /// The translator, checked against NUMBERS -- same discipline as every
    /// sibling bridge module's translator test.
    #[test]
    fn translator_agrees_with_the_dense_evaluator_at_a_point() {
        let cert = mixed_general_case_certificate();
        let sparse_p = dense_to_rat_poly(&cert.p);
        let point: BTreeMap<&str, i128> = [("x", 3)].into_iter().collect();
        let dense_val = poly::eval_rat_poly(&cert.p, Rational::integer(3)).unwrap();
        let sparse_val = eval_rat_poly(&sparse_p, &point);
        assert_eq!(dense_val, sparse_val);
        assert_eq!(dense_val, Rational::integer(4), "x+1 at x=3 is 4");
    }

    /// The Rust-side coefficient-matching reconstruction, checked
    /// numerically before any kernel term is built: `Sigma(numerator_i *
    /// cofactor_i) == p`, exactly (not merely at a sample point).
    #[test]
    fn coefficient_matching_reconstruction_equals_p_exactly() {
        let cert = mixed_general_case_certificate();
        assert!(
            poly::rat_trim(cert.whole.clone()).is_empty(),
            "this instance's whole part must be the zero polynomial (deg p < deg q)"
        );
        let pairs = numerator_cofactor_pairs(&cert);
        assert_eq!(pairs.len(), 3, "one pair per (factor, power) term");

        let mut sum: Vec<Rational> = Vec::new();
        for (numerator, cofactor) in &pairs {
            let contribution = poly::ratpoly_mul(numerator, cofactor).unwrap();
            sum = poly::ratpoly_add(&sum, &contribution).unwrap();
        }
        let sum = poly::rat_trim(sum);
        assert_eq!(sum, poly::rat_trim(cert.p.clone()));

        // Negative control, discriminating in a SMALL term: perturb the
        // first pair's numerator by +1 and confirm the reconstruction no
        // longer matches p.
        let mut wrong_pairs = pairs.clone();
        wrong_pairs[0].0[0] = wrong_pairs[0].0[0]
            .checked_add(Rational::integer(1))
            .unwrap();
        let mut wrong_sum: Vec<Rational> = Vec::new();
        for (numerator, cofactor) in &wrong_pairs {
            let contribution = poly::ratpoly_mul(numerator, cofactor).unwrap();
            wrong_sum = poly::ratpoly_add(&wrong_sum, &contribution).unwrap();
        }
        assert_ne!(
            poly::rat_trim(wrong_sum),
            poly::rat_trim(cert.p.clone()),
            "a perturbed numerator must NOT reconstruct p, or this control is vacuous"
        );
    }

    /// The reconstruction: `Check.cas_partial_fractions_mixed_general_case`,
    /// admitted through [`crate::Kernel::add_declaration`].
    ///
    /// See the module doc for the five things this does NOT establish.
    #[test]
    fn cas_partial_fractions_mixed_general_case_kernel_checked() {
        on_a_deep_stack(cas_partial_fractions_mixed_general_case_body);
    }

    fn cas_partial_fractions_mixed_general_case_body() {
        let cert = mixed_general_case_certificate();
        assert_eq!(verify_partial_fraction_certificate(&cert), Some(true));
        assert!(poly::rat_trim(cert.whole.clone()).is_empty());
        let pairs = numerator_cofactor_pairs(&cert);

        let parts: Vec<(RatPoly, RatPoly)> = pairs
            .iter()
            .map(|(num, cof)| (dense_to_rat_poly(num), dense_to_rat_poly(cof)))
            .collect();
        let p_for_build = dense_to_rat_poly(&cert.p);

        let (mut kernel, prelude) = built();
        let anon = kernel.anon();
        let mut d = IntDev::new(&mut kernel, prelude.int);
        let p = prelude;

        let name = d
            .kernel()
            .name_str(anon, "Check.cas_partial_fractions_mixed_general_case");

        let result = rat_theorem(&mut d, name, 1, &|d, fvars| {
            let vars: BTreeMap<String, ExprId> =
                std::iter::once(("x".to_string(), fvars[0])).collect();
            let (rhs, merged, proof) = prove_poly_combination_rat(d, p, &vars, &parts);
            assert_eq!(
                merged, p_for_build,
                "the emitted normal form must BE the certificate's p"
            );
            let lhs = poly_expr_rat(d, p, &vars, &p_for_build);
            let stmt = req(d, lhs, rhs);
            let flipped = rsymm(d, rhs, lhs, proof);
            (stmt, flipped)
        });
        result.expect("the kernel must admit the coefficient-matching identity");

        // The trusted gate's own record: a Theorem, and axiom-free.
        let env = kernel.environment();
        let decl = env
            .get(name)
            .expect("the declaration must be in the environment");
        assert!(
            matches!(decl, Decl::Theorem { .. }),
            "must be admitted as a Theorem, not an Axiom or an Opaque"
        );
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "the identity must be axiom-free; footprint was {footprint:?}"
        );
    }
}
