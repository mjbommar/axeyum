//! CAS -> kernel bridge, slice 4: the exact polynomial EVT's **derivative
//! sign bracket** for `axeyum-cas`'s `extremum::ExtremumCertificate` —
//! reconstructing a different part of the SAME certificate
//! `cas_evt_bridge_tests` already brackets at the endpoints.
//!
//! # Scope, stated up front (mirrors the IVT and EVT-endpoint siblings'
//! discipline)
//!
//! `F:cas-extremum-irrational-argmax` names the full certificate for
//! `p(x) = x^3 - 6x` on `[-3, 2]`: the argmax is the irrational critical
//! point `-sqrt(2)`, established by differentiating `p` exactly (the
//! derivative is `3x^2 - 6`), Sturm-isolating EVERY real root of `p'`,
//! filtering to the interior of `(-3, 2)`, and comparing against both
//! endpoints.
//! `F:cas-evt-endpoint-exclusion-cubic-kernel-checked` reconstructed the
//! LAST of those steps (the interior point beats both endpoints). This
//! module reconstructs a DIFFERENT, EARLIER step: that `p'` genuinely
//! changes sign over `(-2, -1)` — the bracket containing the true argmax
//! `-sqrt(2) ~ -1.41421`. That is:
//!
//! - `p'(-2) = 6 > 0` and `p'(-1) = -3 < 0`, for `p' = 3x^2 - 6` (`cert.deriv`
//!   itself, not a hand-picked polynomial — see the test's own assertion) —
//!   pure exact `Rat` arithmetic, reduced from `Rat.polyEval` exactly like
//!   `cas_ivt_bridge_tests`'s sign bracket, reusing that module's engine
//!   verbatim.
//!
//! What this module does **not** attempt, and why the claim is deliberately
//! weaker than it might look:
//!
//! - **It is not IVT itself.** A sign change of `p'` on `(-2,-1)` implies (by
//!   the intermediate value theorem) that `p'` has a root there, hence that
//!   `p` has a critical point there — but that IMPLICATION is not
//!   reconstructed through this kernel. This module states only the two
//!   inequalities the implication would need, the same discipline
//!   `cas_ivt_bridge_tests` follows for `x^3-2`'s own sign bracket.
//! - **It does not claim the root is `-sqrt(2)`, or even that it is
//!   irrational.** Nothing here names a real number at all; both evaluation
//!   points are rational.
//! - **It does not reconstruct Sturm completeness.** `critical_points` being
//!   the COMPLETE interior root set of `p'` (not merely "some element is in
//!   `(-2,-1)`") remains `cas-internal`, checked only by
//!   `extremum::verify_extremum_certificate` — exactly as
//!   `F:cas-extremum-irrational-argmax`'s own evidence notes already state.
//! - **It does not touch the OTHER critical point** (`sqrt(2)`, a local
//!   minimum on this interval, not the argmax) at all.
//! - **It does not, by itself, establish that this bracket's root is the
//!   argmax.** Combined with the endpoint-exclusion sibling fact (interior
//!   beats both endpoints) it narrows "where the maximum could be attained"
//!   further, but the two facts are independent kernel-reconstructions of
//!   independent parts of one certificate, not a chain that composes into a
//!   kernel proof of the full `ExtremumCertificate` — that composition is
//!   itself unaddressed future work.
//!
//! So `F:cas-extremum-deriv-sign-bracket-kernel-checked` is a SIBLING fact to
//! `F:cas-extremum-irrational-argmax`, the same relationship
//! `F:cas-ivt-sign-bracket-cbrt2-kernel-checked` has to
//! `F:cas-ivt-cbrt2-in-1-2`: folding this evidence into the Sturm-backed fact
//! would make `classify_cas_certificate_fact` mislabel the WHOLE certificate
//! — differentiation, Sturm isolation, and completeness included — as
//! kernel-reconstructed.
//!
//! # The construction
//!
//! `cert.deriv` for `p = x^3-6x` is `[-6, 0, 3]` (LSB-first: `-6 + 0*x + 3*x^2`),
//! taken directly from the CAS's own `ExtremumCertificate` rather
//! than hand-differentiated — the translator asserts this equality before
//! building anything kernel-side, so a wrong CAS derivative would fail the
//! test at that assertion, not silently propagate. `p'(-2) = 3*4-6 = 6` and
//! `p'(-1) = 3*1-6 = -3`, computed by hand twice (per
//! `docs/plan/status/223-cas-reconstruct.md`'s warning that
//! `Kernel::add_declaration` type-checks a proof term but cannot by itself
//! tell a constant is wrong) and cross-checked against the untrusted `i128`
//! Horner evaluator below. Both reduce to
//! [`cas_ivt_bridge_tests::zero_lt_via_nat_le`] /
//! [`cas_ivt_bridge_tests::lt_zero_via_true`] — the exact two lemmas the
//! sign-bracket bridge already built and kernel-checked. No new
//! `rat_prelude` lemma, kernel primitive, or proof pattern is needed; this
//! module only supplies the derivative's coefficients and the two evaluation
//! points, reusing [`cas_ivt_bridge_tests::poly_eval_to_of_int`] /
//! [`cas_ivt_bridge_tests::n_term_polynomial`] / [`cas_ivt_bridge_tests::int_lit`]
//! / [`cas_ivt_bridge_tests::of_int`] / [`cas_ivt_bridge_tests::rational_to_int`]
//! verbatim (all already `pub(crate)` for this exact reuse pattern, per
//! `CLAUDE.md`'s note on the cost of two proofs of one fact).

use axeyum_cas::extremum::{ExtremumCertificate, polynomial_extremum};
use axeyum_ir::Rational;

use super::cas_ivt_bridge_tests::{
    built, int_lit, lt_zero_via_true, n_term_polynomial, of_int, poly_eval_to_of_int,
    rational_to_int, zero_lt_via_nat_le,
};
use super::ops::{rlt, rpoly_eval, rzero};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::on_a_deep_stack;

/// Translate an [`ExtremumCertificate`]'s `deriv` to `i128`s. Declines
/// (`None`) on a non-integer coefficient, mirroring
/// `cas_ivt_bridge_tests::sign_bracket_to_int`'s own restriction.
/// Deliberately drops everything else in the certificate (`poly`, `a`, `b`,
/// `critical_points`, `argmax`, `max_value`) — out of this slice's scope, see
/// module doc.
fn deriv_to_int(cert: &ExtremumCertificate) -> Option<Vec<i128>> {
    cert.deriv.iter().copied().map(rational_to_int).collect()
}

/// `coeffs` evaluated at integer `x` by plain `i128` Horner (untrusted
/// producer side — the kernel independently re-derives the same value
/// through `Rat.polyEval` below, so a wrong value here fails closed at
/// `Kernel::add_declaration`, not silently).
fn eval_i128(coeffs: &[i128], x: i128) -> i128 {
    let mut acc: i128 = 0;
    for &c in coeffs.iter().rev() {
        acc = acc * x + c;
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Declaration as Decl;

    /// `p(x) = x^3 - 6x` on `[-3, 2]` — the SAME certificate
    /// `F:cas-extremum-irrational-argmax` and
    /// `F:cas-evt-endpoint-exclusion-cubic-kernel-checked` both cite, so this
    /// reconstructs a further piece of that certificate, not a hand-picked
    /// easier one.
    #[test]
    fn extremum_deriv_sign_bracket_kernel_checked() {
        on_a_deep_stack(extremum_deriv_sign_bracket_kernel_checked_body);
    }

    fn extremum_deriv_sign_bracket_kernel_checked_body() {
        let (mut kernel, prelude) = built();
        let anon = kernel.anon();

        // The CAS's own "fast search" half, entirely independent of anything
        // below: produce the SAME certificate the sibling facts cite.
        let poly = vec![
            Rational::integer(0),
            Rational::integer(-6),
            Rational::integer(0),
            Rational::integer(1),
        ];
        let cert = polynomial_extremum(&poly, Rational::integer(-3), Rational::integer(2))
            .expect("the CAS must produce an extremum certificate for x^3-6x on [-3,2]");
        assert_eq!(
            axeyum_cas::extremum::verify_extremum_certificate(&cert),
            Some(true)
        );
        // Sanity: the bracket (-2,-1) genuinely contains the argmax
        // candidate this module reconstructs a sign change around.
        assert_eq!(
            cert.critical_points[0].rational_value(),
            None,
            "sanity: the argmax candidate must be genuinely irrational (-sqrt(2))"
        );

        // The translator: certificate -> integer derivative coefficients.
        // Asserted equal to the CAS's OWN cert.deriv before building
        // anything kernel-side -- not hand-differentiated.
        let deriv_coeffs =
            deriv_to_int(&cert).expect("3x^2-6 is integer-valued: translator must accept");
        assert_eq!(
            deriv_coeffs,
            vec![-6, 0, 3],
            "translator: cert.deriv for x^3-6x -> [-6,0,3] (i.e. 3x^2-6)"
        );

        // Untrusted-side arithmetic (checked, not trusted): p'(-2) = 6,
        // p'(-1) = -3.
        let deriv_at_neg2 = eval_i128(&deriv_coeffs, -2);
        let deriv_at_neg1 = eval_i128(&deriv_coeffs, -1);
        assert_eq!(deriv_at_neg2, 6, "p'(-2) = 3*4 - 6 = 6");
        assert_eq!(deriv_at_neg1, -3, "p'(-1) = 3*1 - 6 = -3");

        let mut d = IntDev::new(&mut kernel, prelude.int);
        let p = prelude;

        // Build the coefficient function ONCE, shared by both endpoints.
        let coeffs_int: Vec<ExprId> = deriv_coeffs.iter().map(|&n| int_lit(&mut d, n)).collect();
        let coeffs_rat: Vec<ExprId> = coeffs_int.iter().map(|&i| of_int(&mut d, p, i)).collect();
        let c = n_term_polynomial(&mut d, p, &coeffs_rat);
        let n_lit = d.num(u32::try_from(coeffs_int.len()).expect("fits"));

        // --- 0 < p'(-2) = 6 -------------------------------------------------
        let neg2_int = int_lit(&mut d, -2);
        let neg2_rat = of_int(&mut d, p, neg2_int);
        let (total_neg2, eq_neg2) =
            poly_eval_to_of_int(&mut d, p, c, &coeffs_int, &coeffs_rat, neg2_rat, neg2_int);
        let eval_neg2 = rpoly_eval(&mut d, p, c, n_lit, neg2_rat);
        // p'(-2) = 6 exactly -- `zero_lt_via_nat_le`'s `hi` must be the EXACT
        // reduced value, not a round "safe" upper bound (see the IVT
        // sibling's own doc for why `Nat.le 1 6` and `Nat.le 1 8` are
        // different, non-defeq propositions).
        let proof_left = zero_lt_via_nat_le(&mut d, p, eval_neg2, total_neg2, eq_neg2, 6);
        let zero_left = rzero(&mut d, p);
        let stmt_left = rlt(&mut d, p, zero_left, eval_neg2);

        let name_left = d
            .kernel()
            .name_str(anon, "Check.extremum_deriv_sign_bracket_left");
        let admitted_left = d.kernel().add_declaration(Decl::Theorem {
            name: name_left,
            uparams: vec![],
            ty: stmt_left,
            value: proof_left,
        });
        assert!(
            admitted_left.is_ok(),
            "0 < p'(-2) for p' = 3x^2-6, reconstructed through Rat.polyEval, \
             must kernel-check: {admitted_left:?}"
        );

        // --- p'(-1) < 0, i.e. -3 -------------------------------------------
        let neg1_int = int_lit(&mut d, -1);
        let neg1_rat = of_int(&mut d, p, neg1_int);
        let (total_neg1, eq_neg1) =
            poly_eval_to_of_int(&mut d, p, c, &coeffs_int, &coeffs_rat, neg1_rat, neg1_int);
        let eval_neg1 = rpoly_eval(&mut d, p, c, n_lit, neg1_rat);
        let proof_right = lt_zero_via_true(&mut d, p, eval_neg1, total_neg1, eq_neg1);
        let zero_right = rzero(&mut d, p);
        let stmt_right = rlt(&mut d, p, eval_neg1, zero_right);

        let name_right = d
            .kernel()
            .name_str(anon, "Check.extremum_deriv_sign_bracket_right");
        let admitted_right = d.kernel().add_declaration(Decl::Theorem {
            name: name_right,
            uparams: vec![],
            ty: stmt_right,
            value: proof_right,
        });
        assert!(
            admitted_right.is_ok(),
            "p'(-1) < 0 for p' = 3x^2-6, reconstructed through Rat.polyEval, \
             must kernel-check: {admitted_right:?}"
        );

        // --- negative control: SAME proof, WRONG (swapped) statement -------
        //
        // Mirrors the IVT and EVT-endpoint siblings' own negative controls:
        // reuse a TRUE proof term verbatim and ascribe it against a FALSE
        // statement's type, exercising `Kernel::add_declaration`'s own type
        // check rather than asking any decision procedure to "prove" a
        // falsehood. `0 < p'(-2)` is TRUE; `p'(-2) < 0` is FALSE.
        let zero_wrong = rzero(&mut d, p);
        let false_stmt = rlt(&mut d, p, eval_neg2, zero_wrong);
        let name_wrong = d
            .kernel()
            .name_str(anon, "Check.extremum_deriv_sign_bracket_wrong");
        let admitted_wrong = d.kernel().add_declaration(Decl::Theorem {
            name: name_wrong,
            uparams: vec![],
            ty: false_stmt,
            value: proof_left,
        });
        assert!(
            admitted_wrong.is_err(),
            "the proof of 0 < p'(-2) must be REJECTED against the FALSE \
             statement p'(-2) < 0: {admitted_wrong:?}"
        );
    }
}
