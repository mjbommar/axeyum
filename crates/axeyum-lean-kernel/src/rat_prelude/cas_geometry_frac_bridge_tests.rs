//! CAS -> kernel bridge, the **fractional-literal** slice: a general
//! `Rat.ofRat`-style cast, plus the reconstruction it unblocks.
//!
//! [`super::cas_geometry_bridge_tests`] and [`super::cas_geometry_mul_bridge_tests`]
//! both decline any certificate with a non-integer coefficient — `int_poly`
//! calls [`super::cas_ivt_bridge_tests::rational_to_int`], which returns `None`
//! on anything but a whole number. `docs/plan/status/314-cas-prove-mul.md`
//! measured the resulting gap at three certificates and one sibling fact
//! needing this cast; this module builds it and reconstructs the cheapest of
//! the three: `medians-concurrent` (32 terms, cofactors constant `-1`, and
//! **24 of its 32 terms carry a `±1/2` coefficient** — no non-constant
//! cofactor, so `prove_mul` is not needed here at all).
//!
//! # The cast: `Rat.normalize`, not a new declaration
//!
//! `Rat.normalize n d h` (`ops.rs`) already exists — it takes an `Int`
//! numerator, a `Nat` denominator and a proof `1 <= d`, and reduces to lowest
//! terms internally. That is exactly a `Rat.ofRat`-style cast; nothing needed
//! declaring. [`rat_lit`] is the one-line builder this bridge lacked:
//! `Rat.normalize (int_lit num) (nat_lit den) (nat_le_lit 1 den)` for a
//! [`Rational`]'s own canonical `(numerator, denominator)` pair.
//!
//! # Why the polynomial machinery needs almost no new proof content
//!
//! `int_prelude_tests.rs::rat_normalize_reduces_two_quarters_to_one_half` and
//! its `rat_add_renormalises`/`rat_mul_renormalises` neighbours already
//! establish, for CONCRETE literals, that `Rat.add`/`Rat.mul` fully
//! renormalise through `def_eq` — "no lemma needed", in that suite's own
//! words. Every coefficient this module ever combines is such a literal
//! (built by [`rat_lit`] from a certificate's own `Rational`), so
//! [`prove_scale_rat`] and [`prove_merge_rat`] need exactly the same shape as
//! [`super::cas_geometry_bridge_tests::prove_scale`]/`prove_merge`, with the
//! `Rat.ofInt_mul`/`Rat.ofInt_add`-then-`rrefl` collapse of those replaced by
//! a SINGLE `rrefl` ascription straight to the canonical `rat_lit` — the
//! kernel's own `Rat.mul`/`Rat.add` computation is what checks it, one level
//! up from how `prove_scale`'s own final step already lets `Int.mul`/`Int.add`
//! collapse to a literal.
//!
//! The zero-drop case (two terms on the same monomial cancelling) is
//! `prove_merge`'s `mul_comm`/`mul_zero`/`zero_add` route, unchanged in
//! shape: the only new burden on the kernel's `def_eq` is that the cancelling
//! sum is now a genuine `Rat.add` of two normalised fractions rather than an
//! `Int.add` of two literals, and the same renormalisation precedent covers
//! it.
//!
//! # What this does NOT establish
//!
//! Everything the parent modules disclaim applies verbatim to this
//! certificate too:
//!
//! 1. **It does not prove the geometry.** The kernel sees eight `Rat`
//!    variables and one algebraic identity; that they are point coordinates
//!    and that the two generators are "P collinear with A, midpoint(BC)" /
//!    "P collinear with B, midpoint(CA)" is a modelling choice made in
//!    `axeyum_cas::geometry_corpus` and reproduced by the translator here.
//! 2. **It does not establish the geometric conditional.** The theorem is the
//!    identity `f = -g0 - g1`; the implication `(g0=0 ∧ g1=0) -> f=0` is one
//!    `Rat` rewrite away and is not taken.
//! 3. **No non-degeneracy condition appears** — this certificate's
//!    `saturations` is empty (unlike `rhombus-diagonals-perpendicular`), so
//!    there is nothing to relocate on that front, and the identity holds
//!    unconditionally over all eight coordinates.
//! 4. **It is over `Rat`, not `CReal`.** A rational-coefficient identity holds
//!    in every ℚ-algebra.
//! 5. **The translator is not the kernel's business.** [`rat_poly`] reading
//!    the `MvPoly` correctly is checked by evaluation at integer points
//!    (`tests::translator_reads_the_medians_certificate_the_cas_produced`),
//!    never by the trusted gate — the kernel never sees an `MvPoly` or a
//!    `Rational`.
//! 6. **The cast itself is untested at genuinely large denominators.** Every
//!    denominator this certificate needs is `1` or `2`; nothing here measures
//!    whether `Rat.normalize`'s `def_eq` renormalisation stays cheap at the
//!    larger denominators `euler-line`'s cofactors would need. `CLAUDE.md`'s
//!    numeral-magnitude gotcha applies: this kernel's `Nat` arithmetic is
//!    unary, so cost is superlinear in the largest magnitude FORMED, and a
//!    cross-multiplied denominator product is exactly such a magnitude.

use std::collections::BTreeMap;

use axeyum_cas::geometry_certify::{GeometryCertificate, ProofOutcome, certify, geometry_limits};
use axeyum_cas::geometry_corpus;
use axeyum_ir::Rational;

use super::RatPrelude;
use super::cas_geometry_bridge_tests::{Mono, add_left_comm, built, mono_expr};
use super::cas_ivt_bridge_tests::{int_lit, nat_le_lit};
use super::ops::{normalize, radd, rat_theorem, rchain, rcongr, req, rmul, rrefl, rsymm, rzero};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::on_a_deep_stack;

// ---------------------------------------------------------------------------
// The translator: `MvPoly` -> RATIONAL-coefficient sparse form.
// ---------------------------------------------------------------------------

/// One polynomial term with its EXACT `Rational` coefficient — the
/// fractional-coefficient generalisation of
/// `cas_geometry_bridge_tests::IntPoly`'s `(Mono, i128)`.
pub(super) type RatTerm = (Mono, Rational);

/// A polynomial as [`RatTerm`]s, sorted by monomial, with no zero coefficient
/// stored. Unlike `int_poly`, [`rat_poly`] never declines: every `Rational` is
/// representable, which is the entire point of this module.
pub(super) type RatPoly = Vec<RatTerm>;

/// `MvPoly` -> [`RatPoly`]. Total, unlike
/// `cas_geometry_bridge_tests::int_poly`.
pub(super) fn rat_poly(poly: &axeyum_cas::mvpoly::MvPoly) -> RatPoly {
    let mut terms: RatPoly = poly
        .terms()
        .filter(|(_, coeff)| !coeff.is_zero())
        .map(|(mono, coeff)| {
            let key: Mono = mono
                .powers()
                .map(|(name, exp)| (name.to_owned(), exp))
                .collect();
            (key, *coeff)
        })
        .collect();
    terms.sort_by(|a, b| a.0.cmp(&b.0));
    terms
}

/// `a + b` on [`RatPoly`]s: a sorted merge dropping any monomial whose
/// combined coefficient is zero. Mirrors [`prove_merge_rat`]'s recursion
/// exactly, so the two cannot disagree about the answer.
pub(super) fn add_poly_rat(a: &[RatTerm], b: &[RatTerm]) -> RatPoly {
    let (mut i, mut j) = (0usize, 0usize);
    let mut out: RatPoly = Vec::new();
    while i < a.len() && j < b.len() {
        match a[i].0.cmp(&b[j].0) {
            std::cmp::Ordering::Less => {
                out.push(a[i].clone());
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(b[j].clone());
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                let sum = a[i].1 + b[j].1;
                if !sum.is_zero() {
                    out.push((a[i].0.clone(), sum));
                }
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}

/// `k · p` on [`RatPoly`]s, for NONZERO `k`.
fn scale_poly_rat(k: Rational, poly: &[RatTerm]) -> RatPoly {
    assert!(!k.is_zero(), "scale_poly_rat: k must be nonzero");
    poly.iter().map(|(m, c)| (m.clone(), k * *c)).collect()
}

/// Evaluate a [`RatPoly`] at an integer assignment. Used ONLY by the
/// translator's own discrimination test, never in a proof.
pub(super) fn eval_rat_poly(poly: &[RatTerm], point: &BTreeMap<&str, i128>) -> Rational {
    let mut total = Rational::zero();
    for (mono, coeff) in poly {
        let mut term = *coeff;
        for (var, exp) in mono {
            let value = Rational::integer(
                *point
                    .get(var.as_str())
                    .expect("eval_rat_poly: every variable must be assigned"),
            );
            for _ in 0..*exp {
                term = term * value;
            }
        }
        total = total + term;
    }
    total
}

// ---------------------------------------------------------------------------
// Kernel-side term builders.
// ---------------------------------------------------------------------------

/// `Rat.normalize (int_lit num) (nat_lit den) (nat_le_lit 1 den)` — the
/// general fractional-literal cast: a `Rational`'s own canonical
/// `(numerator, denominator)` pair, embedded directly. This is what
/// `docs/plan/status/277-cas-multivariate.md` and
/// `docs/plan/status/314-cas-prove-mul.md` both called the missing
/// `Rat.ofRat`-style cast.
pub(super) fn rat_lit(d: &mut IntDev<'_>, r: Rational) -> ExprId {
    let num_int = int_lit(d, r.numerator());
    let den_u32 = u32::try_from(r.denominator()).expect("rat_lit: denominator must fit in a u32");
    let den_nat = d.num(den_u32);
    let proof = nat_le_lit(d, 1, den_u32);
    normalize(d, num_int, den_nat, proof)
}

/// One term as `rat_lit(coefficient) * monomial`.
pub(super) fn term_expr_rat(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    term: &RatTerm,
) -> ExprId {
    let coeff = rat_lit(d, term.1);
    let mono = mono_expr(d, p, vars, &term.0);
    rmul(d, coeff, mono)
}

/// A polynomial as a right-nested `Rat.add` of its terms, terminated in
/// `Rat.zero` — same shape as
/// `cas_geometry_bridge_tests::poly_expr`, over [`RatTerm`]s.
pub(super) fn poly_expr_rat(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    poly: &[RatTerm],
) -> ExprId {
    let mut acc = rzero(d, p);
    for term in poly.iter().rev() {
        let term_e = term_expr_rat(d, p, vars, term);
        acc = radd(d, term_e, acc);
    }
    acc
}

// ---------------------------------------------------------------------------
// The two proof-emitting primitives, generalised to `Rational` coefficients.
// ---------------------------------------------------------------------------

/// `k_rat · poly_expr_rat(poly) = poly_expr_rat(k · poly)`, for a NONZERO `k`.
///
/// Same recursive shape as
/// [`super::cas_geometry_bridge_tests::prove_scale`]: `left_distrib` splits
/// the head, `mul_assoc` (reversed) regroups `k · (c · m)` into `(k·c) · m`,
/// and then — where the int-case needed `Rat.ofInt_mul` plus an `rrefl`
/// collapse — a SINGLE `rrefl` ascribes `k_rat * coeff_rat` directly to the
/// canonical `rat_lit(k * c)`, relying on the same `Rat.mul` renormalisation
/// `int_prelude_tests::rat_mul_renormalises_two_thirds_times_three_halves_to_one`
/// already establishes for literals.
fn prove_scale_rat(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    k: Rational,
    k_rat: ExprId,
    poly: &[RatTerm],
) -> (RatPoly, ExprId) {
    let Some((head, rest)) = poly.split_first() else {
        let base = d.lemma(p.mul_zero, &[k_rat]);
        return (Vec::new(), base);
    };

    let head_e = term_expr_rat(d, p, vars, head);
    let rest_e = poly_expr_rat(d, p, vars, rest);
    let sum_e = radd(d, head_e, rest_e);
    let start = rmul(d, k_rat, sum_e);

    // 1. k * (t + S') = k*t + k*S'
    let k_head = rmul(d, k_rat, head_e);
    let k_rest = rmul(d, k_rat, rest_e);
    let mid1 = radd(d, k_head, k_rest);
    let step1 = d.lemma(p.left_distrib, &[k_rat, head_e, rest_e]);

    // 2. k * (c * m) = (k * c) * m
    let coeff_rat = rat_lit(d, head.1);
    let mono = mono_expr(d, p, vars, &head.0);
    let k_coeff = rmul(d, k_rat, coeff_rat);
    let assoc_target = rmul(d, k_coeff, mono);
    let assoc = d.lemma(p.mul_assoc, &[k_rat, coeff_rat, mono]);
    let assoc_rev = rsymm(d, assoc_target, k_head, assoc);
    let mid2 = radd(d, assoc_target, k_rest);
    let step2 = rcongr(d, k_head, assoc_target, assoc_rev, &|d, t| {
        radd(d, t, k_rest)
    });

    // 3. (k * c) collapses, by the kernel's own `Rat.mul` computation, to the
    //    canonical literal `rat_lit(k*c)` — one `rrefl` ascription.
    let scaled_head_val = k * head.1;
    let canon_coeff = rat_lit(d, scaled_head_val);
    let canon_head = rmul(d, canon_coeff, mono);
    let mid3 = radd(d, canon_head, k_rest);
    let step3 = rrefl(d, mid3);

    // 4. recurse on the tail.
    let (scaled_rest, tail_proof) = prove_scale_rat(d, p, vars, k, k_rat, rest);
    let scaled_rest_e = poly_expr_rat(d, p, vars, &scaled_rest);
    let end = radd(d, canon_head, scaled_rest_e);
    let step4 = rcongr(d, k_rest, scaled_rest_e, tail_proof, &|d, t| {
        radd(d, canon_head, t)
    });

    let (_, proof) = rchain(
        d,
        start,
        &[(mid1, step1), (mid2, step2), (mid3, step3), (end, step4)],
    );

    let mut scaled = vec![(head.0.clone(), scaled_head_val)];
    scaled.extend(scaled_rest);
    (scaled, proof)
}

/// `poly_expr_rat(a) + poly_expr_rat(b) = poly_expr_rat(a + b)` — a sorted
/// merge over the shared monomial basis, generalising
/// [`super::cas_geometry_bridge_tests::prove_merge`] to `Rational`
/// coefficients.
///
/// The `Equal` case's coefficient combination is `right_distrib` (reversed),
/// then — same replacement as [`prove_scale_rat`] — a single `rrefl` collapses
/// `ca_rat + cb_rat` to `rat_lit(ca+cb)` directly, or (when the combined
/// coefficient is zero) the SAME `mul_comm`/`mul_zero`/`zero_add` route the
/// int-case's zero-drop uses, unchanged in shape: `ca_rat + cb_rat` now
/// renormalises through a genuine `Rat.add` of two fractions rather than an
/// `Int.add` of two literals, and the same `def_eq` precedent covers it.
pub(super) fn prove_merge_rat(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    a: &[RatTerm],
    b: &[RatTerm],
) -> (RatPoly, ExprId) {
    let a_e = poly_expr_rat(d, p, vars, a);
    let b_e = poly_expr_rat(d, p, vars, b);

    let Some((a_head, a_rest)) = a.split_first() else {
        let proof = d.lemma(p.zero_add, &[b_e]);
        return (b.to_vec(), proof);
    };
    let Some((b_head, b_rest)) = b.split_first() else {
        let proof = d.lemma(p.add_zero, &[a_e]);
        return (a.to_vec(), proof);
    };

    let a_head_e = term_expr_rat(d, p, vars, a_head);
    let a_rest_e = poly_expr_rat(d, p, vars, a_rest);
    let b_head_e = term_expr_rat(d, p, vars, b_head);
    let b_rest_e = poly_expr_rat(d, p, vars, b_rest);
    let start = radd(d, a_e, b_e);

    match a_head.0.cmp(&b_head.0) {
        std::cmp::Ordering::Less => {
            let inner = radd(d, a_rest_e, b_e);
            let mid = radd(d, a_head_e, inner);
            let step1 = d.lemma(p.add_assoc, &[a_head_e, a_rest_e, b_e]);

            let (merged_rest, tail) = prove_merge_rat(d, p, vars, a_rest, b);
            let merged_rest_e = poly_expr_rat(d, p, vars, &merged_rest);
            let end = radd(d, a_head_e, merged_rest_e);
            let step2 = rcongr(d, inner, merged_rest_e, tail, &|d, t| radd(d, a_head_e, t));

            let (_, proof) = rchain(d, start, &[(mid, step1), (end, step2)]);
            let mut merged = vec![a_head.clone()];
            merged.extend(merged_rest);
            (merged, proof)
        }
        std::cmp::Ordering::Greater => {
            let (mid, step1) = add_left_comm(d, p, a_e, b_head_e, b_rest_e);
            let inner = radd(d, a_e, b_rest_e);

            let (merged_rest, tail) = prove_merge_rat(d, p, vars, a, b_rest);
            let merged_rest_e = poly_expr_rat(d, p, vars, &merged_rest);
            let end = radd(d, b_head_e, merged_rest_e);
            let step2 = rcongr(d, inner, merged_rest_e, tail, &|d, t| radd(d, b_head_e, t));

            let (_, proof) = rchain(d, start, &[(mid, step1), (end, step2)]);
            let mut merged = vec![b_head.clone()];
            merged.extend(merged_rest);
            (merged, proof)
        }
        std::cmp::Ordering::Equal => {
            let a_rest_plus_b = radd(d, a_rest_e, b_e);
            let mid1 = radd(d, a_head_e, a_rest_plus_b);
            let step1 = d.lemma(p.add_assoc, &[a_head_e, a_rest_e, b_e]);

            let (swapped, swap_proof) = add_left_comm(d, p, a_rest_e, b_head_e, b_rest_e);
            let mid2 = radd(d, a_head_e, swapped);
            let step2 = rcongr(d, a_rest_plus_b, swapped, swap_proof, &|d, t| {
                radd(d, a_head_e, t)
            });

            let rests = radd(d, a_rest_e, b_rest_e);
            let heads = radd(d, a_head_e, b_head_e);
            let mid3 = radd(d, heads, rests);
            let assoc = d.lemma(p.add_assoc, &[a_head_e, b_head_e, rests]);
            let step3 = rsymm(d, mid3, mid2, assoc);

            // ca*m + cb*m = (ca+cb)*m via right_distrib (reversed).
            let ca_rat = rat_lit(d, a_head.1);
            let cb_rat = rat_lit(d, b_head.1);
            let mono = mono_expr(d, p, vars, &a_head.0);
            let coeff_sum = radd(d, ca_rat, cb_rat);
            let distrib_target = rmul(d, coeff_sum, mono);
            let distrib = d.lemma(p.right_distrib, &[ca_rat, cb_rat, mono]);
            let distrib_rev = rsymm(d, distrib_target, heads, distrib);
            let mid4 = radd(d, distrib_target, rests);
            let step4 = rcongr(d, heads, distrib_target, distrib_rev, &|d, t| {
                radd(d, t, rests)
            });

            let combined = a_head.1 + b_head.1;
            let (merged_rest, tail) = prove_merge_rat(d, p, vars, a_rest, b_rest);
            let merged_rest_e = poly_expr_rat(d, p, vars, &merged_rest);

            if combined.is_zero() {
                // coeff_sum * m = m * coeff_sum = m * Rat.zero = Rat.zero,
                // then 0 + R = R. Same route as the int-case's zero-drop;
                // `coeff_sum` renormalises to `Rat.zero` through `Rat.add`'s
                // own `def_eq` computation rather than `Int.add`'s.
                let zero_c = rzero(d, p);
                let flipped = rmul(d, mono, coeff_sum);
                let comm = d.lemma(p.mul_comm, &[coeff_sum, mono]);
                let mul_zero = d.lemma(p.mul_zero, &[mono]);
                let (_, kill) = rchain(d, distrib_target, &[(flipped, comm), (zero_c, mul_zero)]);
                let mid5 = radd(d, zero_c, rests);
                let step5 = rcongr(d, distrib_target, zero_c, kill, &|d, t| radd(d, t, rests));
                let step6 = d.lemma(p.zero_add, &[rests]);
                let step7 = tail;

                let (_, proof) = rchain(
                    d,
                    start,
                    &[
                        (mid1, step1),
                        (mid2, step2),
                        (mid3, step3),
                        (mid4, step4),
                        (mid5, step5),
                        (rests, step6),
                        (merged_rest_e, step7),
                    ],
                );
                (merged_rest, proof)
            } else {
                let canon_head = (a_head.0.clone(), combined);
                let canon_head_e = term_expr_rat(d, p, vars, &canon_head);
                let mid5 = radd(d, canon_head_e, rests);
                let step5 = rrefl(d, mid5);

                let end = radd(d, canon_head_e, merged_rest_e);
                let step6 = rcongr(d, rests, merged_rest_e, tail, &|d, t| {
                    radd(d, canon_head_e, t)
                });

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
                let mut merged = vec![canon_head];
                merged.extend(merged_rest);
                (merged, proof)
            }
        }
    }
}

/// `Sigma_i (rat_lit(k_i) * poly_expr_rat(P_i)) = poly_expr_rat(Sigma_i k_i*P_i)`
/// for CONSTANT cofactors `k_i` (here: `Rational`s, not `i128`s) — the
/// `Rational` generalisation of
/// [`super::cas_geometry_bridge_tests::prove_const_combination`].
fn prove_const_combination_rat(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    vars: &BTreeMap<String, ExprId>,
    parts: &[(Rational, RatPoly)],
) -> (ExprId, RatPoly, ExprId) {
    let ((k, poly), rest) = parts
        .split_first()
        .expect("prove_const_combination_rat: at least one generator is required");
    let k_rat = rat_lit(d, *k);
    let poly_e = poly_expr_rat(d, p, vars, poly);
    let head_e = rmul(d, k_rat, poly_e);
    let (scaled, scale_proof) = prove_scale_rat(d, p, vars, *k, k_rat, poly);
    let scaled_e = poly_expr_rat(d, p, vars, &scaled);

    if rest.is_empty() {
        return (head_e, scaled, scale_proof);
    }

    let (tail_e, tail_poly, tail_proof) = prove_const_combination_rat(d, p, vars, rest);
    let start = radd(d, head_e, tail_e);
    let tail_poly_e = poly_expr_rat(d, p, vars, &tail_poly);

    let mid1 = radd(d, scaled_e, tail_e);
    let step1 = rcongr(d, head_e, scaled_e, scale_proof, &|d, t| radd(d, t, tail_e));
    let mid2 = radd(d, scaled_e, tail_poly_e);
    let step2 = rcongr(d, tail_e, tail_poly_e, tail_proof, &|d, t| {
        radd(d, scaled_e, t)
    });

    let (merged, merge_proof) = prove_merge_rat(d, p, vars, &scaled, &tail_poly);
    let merged_e = poly_expr_rat(d, p, vars, &merged);

    let (_, proof) = rchain(
        d,
        start,
        &[(mid1, step1), (mid2, step2), (merged_e, merge_proof)],
    );
    (start, merged, proof)
}

// ---------------------------------------------------------------------------
// The certificate side.
// ---------------------------------------------------------------------------

/// Produce `medians-concurrent`'s certificate from the CAS's own corpus and
/// certifier — the SAME artifact `F:geometry-medians-concurrent` cites.
fn medians_certificate() -> GeometryCertificate {
    let problem = geometry_corpus::corpus()
        .into_iter()
        .find(|p| p.id == "medians-concurrent")
        .expect("the CAS corpus must carry medians-concurrent");
    match certify(&problem, geometry_limits()) {
        ProofOutcome::Certified(cert) => *cert,
        other => panic!("the CAS must certify medians-concurrent: {other:?}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Declaration as Decl;

    /// The translator, checked against NUMBERS rather than asserted — same
    /// discipline as
    /// `cas_geometry_bridge_tests::translator_reads_the_certificate_the_cas_produced`.
    ///
    /// The certificate's own generic witness (`A=(0,0)`, `B=(4,0)`, `C=(1,3)`,
    /// `P` on the actual centroid-adjacent median intersection) is not needed
    /// here: both hypotheses are identities that MUST hold for ALL `P`, so any
    /// point discriminates as long as the three polynomials do not all vanish
    /// there and their combination is checked, not merely their individual
    /// values.
    #[test]
    fn translator_reads_the_medians_certificate_the_cas_produced() {
        let cert = medians_certificate();
        assert_eq!(cert.coordinates.len(), 8, "eight coordinates");
        assert!(
            cert.saturations.is_empty(),
            "medians-concurrent needs no non-degeneracy condition"
        );
        assert_eq!(cert.generators.len(), 2, "two median-incidence hypotheses");
        assert_eq!(cert.conclusions.len(), 1, "one conclusion");

        let g0 = rat_poly(&cert.generators[0]);
        let g1 = rat_poly(&cert.generators[1]);
        let concl = rat_poly(&cert.conclusions[0].poly);
        assert_eq!((g0.len(), g1.len(), concl.len()), (10, 10, 10));

        // Both cofactors are the constant -1 -- an INTEGER, even though the
        // generators and conclusion are not. `medians-concurrent` needs the
        // fractional cast for its GENERATORS, not for a fractional cofactor.
        let cofactors: Vec<Rational> = cert.conclusions[0]
            .cofactors
            .iter()
            .map(|c| {
                let terms = rat_poly(c);
                assert_eq!(terms.len(), 1, "cofactor must be a single constant term");
                assert!(terms[0].0.is_empty(), "cofactor must be CONSTANT");
                terms[0].1
            })
            .collect();
        assert_eq!(
            cofactors,
            vec![Rational::integer(-1), Rational::integer(-1)],
            "both cofactors are the constant -1"
        );

        // At least a quarter of each generator's terms are genuinely
        // fractional -- this IS the cast's reason for existing. Without it
        // `int_poly` would decline every one of these three polynomials.
        let fractional_terms =
            |poly: &RatPoly| poly.iter().filter(|(_, c)| !c.is_integer()).count();
        assert_eq!(fractional_terms(&g0), 8, "eight `±1/2` terms in g0");
        assert_eq!(fractional_terms(&g1), 8, "eight `±1/2` terms in g1");
        assert_eq!(fractional_terms(&concl), 8, "eight `±1/2` terms in concl");

        // A point discriminating the three polynomials (chosen so P is NOT on
        // either median, hence not on the third by the identity -g0-g1 either
        // -- all three are nonzero and distinct).
        let point: BTreeMap<&str, i128> = [
            ("ax", 0),
            ("ay", 0),
            ("bx", 4),
            ("by", 0),
            ("cx", 1),
            ("cy", 3),
            ("px", 5),
            ("py", 5),
        ]
        .into_iter()
        .collect();
        let (v0, v1, vc) = (
            eval_rat_poly(&g0, &point),
            eval_rat_poly(&g1, &point),
            eval_rat_poly(&concl, &point),
        );
        assert_ne!(v0, Rational::zero());
        assert_ne!(v1, Rational::zero());
        assert_ne!(v0, v1, "the point must discriminate g0 from g1");

        // The identity itself, checked numerically: conclusion = -g0 - g1.
        assert_eq!(vc, -v0 - v1, "the cofactor identity holds at the point");
    }

    /// The [`RatPoly`] arithmetic [`prove_scale_rat`] and [`prove_merge_rat`]
    /// each mirror, checked independently of the kernel — including the
    /// ZERO-drop, which the medians identity exercises exactly twice (`ax*by`
    /// and `ay*bx` cancel between `-g0` and `-g1`).
    #[test]
    fn rat_poly_arithmetic_drops_cancelling_monomials() {
        let cert = medians_certificate();
        let g0 = rat_poly(&cert.generators[0]);
        let g1 = rat_poly(&cert.generators[1]);
        let concl = rat_poly(&cert.conclusions[0].poly);

        let neg_g0 = scale_poly_rat(Rational::integer(-1), &g0);
        let neg_g1 = scale_poly_rat(Rational::integer(-1), &g1);
        assert_eq!(neg_g0.len(), 10);
        assert_eq!(neg_g1.len(), 10);

        let combined = add_poly_rat(&neg_g0, &neg_g1);
        assert_eq!(
            combined.len(),
            10,
            "twelve unique monomials across g0/g1 (eight shared, two each \
             exclusive); two of the eight shared ones (ax*by, ay*bx) cancel \
             exactly, leaving ten"
        );
        assert_eq!(combined, concl, "-g0 - g1 IS the conclusion polynomial");

        // Negative control, and it must differ in a SMALL term: swapping the
        // sign of ONE cofactor gives +g0 - g1, a different polynomial.
        let wrong = add_poly_rat(&g0, &neg_g1);
        assert_ne!(
            wrong, concl,
            "+g0 - g1 must NOT equal the conclusion, or the test above is vacuous"
        );
    }

    /// The reconstruction: `Check.geometry_medians_cofactor_identity`,
    /// admitted through [`crate::Kernel::add_declaration`].
    ///
    /// See the module doc for the six things this does NOT establish.
    #[test]
    fn geometry_medians_cofactor_identity_kernel_checked() {
        on_a_deep_stack(geometry_medians_cofactor_identity_body);
    }

    fn geometry_medians_cofactor_identity_body() {
        let cert = medians_certificate();
        let g0 = rat_poly(&cert.generators[0]);
        let g1 = rat_poly(&cert.generators[1]);
        let concl = rat_poly(&cert.conclusions[0].poly);
        let cofactors: Vec<Rational> = cert.conclusions[0]
            .cofactors
            .iter()
            .map(|c| {
                let terms = rat_poly(c);
                assert_eq!(terms.len(), 1, "cofactor must be a single constant term");
                assert!(terms[0].0.is_empty(), "cofactor must be CONSTANT");
                terms[0].1
            })
            .collect();

        let names: Vec<String> = cert.coordinates.clone();
        assert_eq!(
            names,
            vec!["ax", "ay", "bx", "by", "cx", "cy", "px", "py"],
            "the coordinate ORDER is the certificate's, not this test's"
        );

        let (mut kernel, prelude) = built();
        let anon = kernel.anon();
        let mut d = IntDev::new(&mut kernel, prelude.int);
        let p = prelude;

        let name = d
            .kernel()
            .name_str(anon, "Check.geometry_medians_cofactor_identity");

        let parts: Vec<(Rational, RatPoly)> =
            vec![(cofactors[0], g0.clone()), (cofactors[1], g1.clone())];
        let concl_for_build = concl.clone();

        let result = rat_theorem(&mut d, name, names.len(), &|d, fvars| {
            let vars: BTreeMap<String, ExprId> =
                names.iter().cloned().zip(fvars.iter().copied()).collect();
            let (rhs, merged, proof) = prove_const_combination_rat(d, p, &vars, &parts);
            assert_eq!(
                merged, concl_for_build,
                "the emitted normal form must BE the certificate's conclusion"
            );
            let lhs = poly_expr_rat(d, p, &vars, &concl_for_build);
            let stmt = req(d, lhs, rhs);
            let flipped = rsymm(d, rhs, lhs, proof);
            (stmt, flipped)
        });
        result.expect("the kernel must admit the medians cofactor identity");

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
