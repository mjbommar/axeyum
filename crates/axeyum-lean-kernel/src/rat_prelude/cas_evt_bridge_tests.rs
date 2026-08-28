//! CAS -> kernel bridge, slice 3: EVT **endpoint exclusion** for
//! `axeyum-cas`'s `extremum::ExtremumCertificate` — sized by
//! `docs/plan/status/223-cas-reconstruct.md` as "needing no new kernel
//! machinery at all", verified here rather than taken on that write-up's
//! word.
//!
//! # Scope, stated up front (mirrors `cas_ivt_bridge_tests`'s own discipline)
//!
//! [`ExtremumCertificate`] (`crates/axeyum-cas/src/extremum.rs`) carries
//! several claims, and this module reconstructs **only one**: that the
//! interior point `x = -1` beats BOTH endpoints of `[a, b]`, i.e. the
//! certificate's maximum is not attained at an endpoint. That is:
//!
//! - `p(-1) > p(a)` and `p(-1) > p(b)`, for `p = x^3 - 6x`, `a = -3`, `b = 2`
//!   — pure exact `Rat` arithmetic, reduced from `Rat.polyEval` exactly like
//!   `cas_ivt_bridge_tests`'s sign bracket.
//!
//! What this module does **not** attempt (identical exclusions to the IVT
//! bridge, for the identical reason — no kernel machinery for them exists
//! yet): that `-1` is anywhere near the true irrational argmax `-sqrt(2)`;
//! that `-sqrt(2)` is a critical point of `p'` at all (would need `Rat`
//! polynomial differentiation reconstructed in the kernel); and the Sturm
//! count establishing `critical_points` is complete (the same large lift
//! `cas_ivt_bridge_tests`'s module doc sizes). So this is deliberately a
//! WEAKER statement than the full `ExtremumCertificate`: "the maximum is
//! interior, not at either endpoint" (witnessed by a single interior point
//! that already beats both endpoints), not "the maximum is exactly
//! `-sqrt(2)`". `F:cas-extremum-irrational-argmax` (the full certificate, its
//! own evidence deliberately kept `cas-internal` — see that fact's `notes`)
//! is left untouched; this is a SIBLING fact, for the same reason
//! `F:cas-ivt-sign-bracket-cbrt2-kernel-checked` is a sibling of
//! `F:cas-ivt-cbrt2-in-1-2` rather than an edit to it — folding this evidence
//! into the Sturm-backed fact would make `classify_cas_certificate_fact`
//! mislabel the WHOLE certificate as kernel-reconstructed.
//!
//! # The construction
//!
//! Shift `p` by each endpoint's value rather than proving a `>` directly:
//! `q := p - p(a)` and `r := p - p(b)` (both computed on the untrusted
//! producer side, in plain `i128` — if either is wrong the reduced constant
//! below will not match the asserted bound and `Kernel::add_declaration`
//! rejects, exactly the guard `docs/plan/status/223-cas-reconstruct.md`
//! mutation-verified for the IVT sibling). Then `p(-1) > p(a)` is the SAME
//! proposition as `0 < q(-1)`, and `p(-1) > p(b)` as `0 < r(-1)` — so both
//! reduce to [`cas_ivt_bridge_tests::zero_lt_via_nat_le`], the exact engine
//! the sign-bracket bridge already built and kernel-checked. No new
//! `rat_prelude` lemma, kernel primitive, or proof pattern is needed here;
//! this module only supplies the two shifted coefficient vectors and reuses
//! [`cas_ivt_bridge_tests::poly_eval_to_of_int`] /
//! [`cas_ivt_bridge_tests::n_term_polynomial`] / [`cas_ivt_bridge_tests::int_lit`]
//! / [`cas_ivt_bridge_tests::of_int`] verbatim (all made `pub(crate)` for
//! exactly this reuse, rather than re-derived beside the original — see
//! `CLAUDE.md`'s note on the cost of two proofs of one fact).
//!
//! # Computed by hand, twice (per `docs/plan/status/223-cas-reconstruct.md`'s
//! own warning that the trusted gate cannot tell a value is wrong)
//!
//! `p = x^3 - 6x`: `p(-3) = -27 - 6*(-3) = -27 + 18 = -9`;
//! `p(2) = 8 - 12 = -4`; `p(-1) = -1 + 6 = 5`.
//! `q = p - p(-3) = p + 9`, coefficients (LSB-first) `[9, -6, 0, 1]`;
//! `q(-1) = -1 + 6 + 9 = 14` (`= p(-1) - p(-3) = 5 - (-9) = 14`, checks).
//! `r = p - p(2) = p + 4`, coefficients `[4, -6, 0, 1]`;
//! `r(-1) = -1 + 6 + 4 = 9` (`= p(-1) - p(2) = 5 - (-4) = 9`, checks).
//! Both positive, so `x = -1` beats both endpoints and the maximum on
//! `[-3, 2]` is interior. These are exactly the constants
//! `docs/plan/status/223-cas-reconstruct.md` sized (`14`, `9`).

use axeyum_cas::extremum::{ExtremumCertificate, polynomial_extremum};
use axeyum_ir::Rational;

use super::cas_ivt_bridge_tests::{
    built, int_lit, n_term_polynomial, of_int, poly_eval_to_of_int, rational_to_int,
    zero_lt_via_nat_le,
};
use super::ops::{rlt, rpoly_eval, rzero};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::on_a_deep_stack;

/// Translate an [`ExtremumCertificate`]'s `poly`/`a`/`b` to `i128`s.
/// Declines (`None`) on a non-integer value, mirroring
/// `cas_ivt_bridge_tests::sign_bracket_to_int`'s own restriction. Deliberately
/// drops `critical_points`/`argmax`/`max_value` — out of this slice's scope
/// (see module doc).
fn poly_ab_to_int(cert: &ExtremumCertificate) -> Option<(Vec<i128>, i128, i128)> {
    let coeffs: Vec<i128> = cert
        .poly
        .iter()
        .copied()
        .map(rational_to_int)
        .collect::<Option<_>>()?;
    let a = rational_to_int(cert.a)?;
    let b = rational_to_int(cert.b)?;
    Some((coeffs, a, b))
}

/// `p` evaluated at integer `x` by plain `i128` Horner (untrusted producer
/// side — the kernel independently re-derives the same value through
/// `Rat.polyEval` below, so a wrong value here fails closed at
/// `Kernel::add_declaration`, not silently).
fn eval_i128(coeffs: &[i128], x: i128) -> i128 {
    let mut acc: i128 = 0;
    for &c in coeffs.iter().rev() {
        acc = acc * x + c;
    }
    acc
}

/// Shift `coeffs`' constant term by `-value_at_endpoint`, giving the
/// coefficients of `p - p(endpoint)`.
fn shift_by(coeffs: &[i128], value_at_endpoint: i128) -> Vec<i128> {
    let mut shifted = coeffs.to_vec();
    shifted[0] -= value_at_endpoint;
    shifted
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Declaration as Decl;

    /// `p(x) = x^3 - 6x` on `[-3, 2]` — `F:cas-extremum-irrational-argmax`'s
    /// own instance (`extremum::tests::irrational_argmax`), so this
    /// reconstructs the SAME certificate the sibling fact cites, not a
    /// hand-picked easier one.
    #[test]
    fn evt_endpoint_exclusion_kernel_checked() {
        on_a_deep_stack(evt_endpoint_exclusion_kernel_checked_body);
    }

    fn evt_endpoint_exclusion_kernel_checked_body() {
        let (mut kernel, prelude) = built();
        let anon = kernel.anon();

        // The CAS's own "fast search" half, entirely independent of anything
        // below: produce the SAME certificate `F:cas-extremum-irrational-argmax`
        // cites (x^3 - 6x on [-3, 2], irrational argmax -sqrt(2)).
        let poly = vec![
            Rational::integer(0),
            Rational::integer(-6),
            Rational::integer(0),
            Rational::integer(1),
        ];
        let cert = polynomial_extremum(&poly, Rational::integer(-3), Rational::integer(2))
            .expect("the CAS must produce an extremum certificate for x^3-6x on [-3,2]");
        // Sanity, matching `extremum::tests::irrational_argmax`'s own
        // assertions exactly (both roots of p' = 3x^2-6 are interior to
        // [-3,2]; the argmax picks the LEFT one, -sqrt(2)).
        assert_eq!(
            axeyum_cas::extremum::verify_extremum_certificate(&cert),
            Some(true)
        );
        assert_eq!(
            cert.argmax,
            axeyum_cas::extremum::ExtremumLocation::Critical(0)
        );
        assert_eq!(
            cert.critical_points[0].rational_value(),
            None,
            "sanity: the argmax must be genuinely irrational"
        );

        // The translator: certificate -> integer (poly, a, b).
        let (p_coeffs, a_int, b_int) = poly_ab_to_int(&cert)
            .expect("x^3-6x and the bracket [-3,2] are integer-valued: translator must accept");
        assert_eq!(
            p_coeffs,
            vec![0, -6, 0, 1],
            "translator: x^3-6x -> [0,-6,0,1]"
        );
        assert_eq!((a_int, b_int), (-3, 2));

        // Untrusted-side arithmetic (checked, not trusted): p(-3) = -9,
        // p(2) = -4, so q = p+9 = [9,-6,0,1] and r = p+4 = [4,-6,0,1].
        let p_at_a = eval_i128(&p_coeffs, a_int);
        let p_at_b = eval_i128(&p_coeffs, b_int);
        assert_eq!(p_at_a, -9, "p(-3) = -27 - 6*(-3) = -9");
        assert_eq!(p_at_b, -4, "p(2) = 8 - 12 = -4");

        let q_coeffs = shift_by(&p_coeffs, p_at_a);
        let r_coeffs = shift_by(&p_coeffs, p_at_b);
        assert_eq!(q_coeffs, vec![9, -6, 0, 1]);
        assert_eq!(r_coeffs, vec![4, -6, 0, 1]);

        let mut d = IntDev::new(&mut kernel, prelude.int);
        let p = prelude;
        let neg_one: i128 = -1;

        // --- 0 < q(-1) = 14, i.e. p(-1) > p(-3) --------------------------
        let q_coeffs_int: Vec<ExprId> = q_coeffs.iter().map(|&n| int_lit(&mut d, n)).collect();
        let q_coeffs_rat: Vec<ExprId> =
            q_coeffs_int.iter().map(|&i| of_int(&mut d, p, i)).collect();
        let q_c = n_term_polynomial(&mut d, p, &q_coeffs_rat);
        let x_int = int_lit(&mut d, neg_one);
        let x_rat = of_int(&mut d, p, x_int);
        let (total_q, eq_q) =
            poly_eval_to_of_int(&mut d, p, q_c, &q_coeffs_int, &q_coeffs_rat, x_rat, x_int);
        let n_lit_q = d.num(u32::try_from(q_coeffs_int.len()).expect("fits"));
        let eval_q = rpoly_eval(&mut d, p, q_c, n_lit_q, x_rat);
        // q(-1) = 14 exactly -- `zero_lt_via_nat_le`'s `hi` must be the
        // EXACT reduced value (see module doc's hand computation), not a
        // round "safe" bound.
        let proof_q = zero_lt_via_nat_le(&mut d, p, eval_q, total_q, eq_q, 14);
        let zero_q = rzero(&mut d, p);
        let stmt_q = rlt(&mut d, p, zero_q, eval_q);

        let name_q = d
            .kernel()
            .name_str(anon, "Check.evt_endpoint_exclusion_lower_leg");
        let admitted_q = d.kernel().add_declaration(Decl::Theorem {
            name: name_q,
            uparams: vec![],
            ty: stmt_q,
            value: proof_q,
        });
        assert!(
            admitted_q.is_ok(),
            "0 < q(-1) = 14 (i.e. p(-1) > p(-3)) for p = x^3-6x on [-3,2], \
             reconstructed through Rat.polyEval, must kernel-check: {admitted_q:?}"
        );

        // --- 0 < r(-1) = 9, i.e. p(-1) > p(2) -----------------------------
        let r_coeffs_int: Vec<ExprId> = r_coeffs.iter().map(|&n| int_lit(&mut d, n)).collect();
        let r_coeffs_rat: Vec<ExprId> =
            r_coeffs_int.iter().map(|&i| of_int(&mut d, p, i)).collect();
        let r_c = n_term_polynomial(&mut d, p, &r_coeffs_rat);
        let x_int2 = int_lit(&mut d, neg_one);
        let x_rat2 = of_int(&mut d, p, x_int2);
        let (total_r, eq_r) =
            poly_eval_to_of_int(&mut d, p, r_c, &r_coeffs_int, &r_coeffs_rat, x_rat2, x_int2);
        let n_lit_r = d.num(u32::try_from(r_coeffs_int.len()).expect("fits"));
        let eval_r = rpoly_eval(&mut d, p, r_c, n_lit_r, x_rat2);
        let proof_r = zero_lt_via_nat_le(&mut d, p, eval_r, total_r, eq_r, 9);
        let zero_r = rzero(&mut d, p);
        let stmt_r = rlt(&mut d, p, zero_r, eval_r);

        let name_r = d
            .kernel()
            .name_str(anon, "Check.evt_endpoint_exclusion_upper_leg");
        let admitted_r = d.kernel().add_declaration(Decl::Theorem {
            name: name_r,
            uparams: vec![],
            ty: stmt_r,
            value: proof_r,
        });
        assert!(
            admitted_r.is_ok(),
            "0 < r(-1) = 9 (i.e. p(-1) > p(2)) for p = x^3-6x on [-3,2], \
             reconstructed through Rat.polyEval, must kernel-check: {admitted_r:?}"
        );

        // --- negative control: SAME proof, WRONG (swapped) statement ------
        //
        // Mirrors `cas_ivt_bridge_tests`'s own negative control: reuse a TRUE
        // proof term verbatim and ascribe it against a FALSE statement's
        // type, exercising `Kernel::add_declaration`'s own type check rather
        // than asking any decision procedure to "prove" a falsehood.
        // `0 < q(-1)` is TRUE (q(-1) = 14); `q(-1) < 0` is FALSE.
        let zero_wrong = rzero(&mut d, p);
        let false_stmt = rlt(&mut d, p, eval_q, zero_wrong);
        let name_wrong = d
            .kernel()
            .name_str(anon, "Check.evt_endpoint_exclusion_wrong");
        let admitted_wrong = d.kernel().add_declaration(Decl::Theorem {
            name: name_wrong,
            uparams: vec![],
            ty: false_stmt,
            value: proof_q,
        });
        assert!(
            admitted_wrong.is_err(),
            "the proof of 0 < q(-1) must be REJECTED against the FALSE \
             statement q(-1) < 0: {admitted_wrong:?}"
        );
    }
}
