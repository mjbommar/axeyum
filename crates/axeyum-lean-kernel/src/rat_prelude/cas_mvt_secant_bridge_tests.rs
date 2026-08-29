//! CAS -> kernel bridge, slice 5: the exact polynomial MVT's **secant
//! endpoints**, `p(a) = 27` and `p(b) = 0` for `axeyum-cas`'s
//! `mvt::MvtCertificate` — reconstructing the two evaluations that determine
//! the certificate's `slope` field, not the witness Rolle's argument names.
//!
//! # Scope, stated up front (mirrors the IVT/EVT siblings' discipline)
//!
//! `F:cas-mvt-cubic-witness-sqrt3` names the full certificate for
//! `p(x) = x^3` on `[0, 3]`: the secant slope is `9`, and the certificate
//! names the exact irrational witness `c = sqrt(3)` where `p'(c) = 9`, found
//! via a Rolle reduction and Sturm-isolated root search. This module
//! reconstructs neither the witness nor Rolle's argument — only the two
//! rational endpoint evaluations the slope is computed FROM:
//!
//! - `p(3) = 27` and `p(0) = 0`, for `p = x^3` (`cert.poly`/`cert.a`/`cert.b`
//!   themselves, not hand-picked values) — pure exact `Rat` arithmetic,
//!   reduced from `Rat.polyEval` by the SAME engine
//!   `cas_ivt_bridge_tests::poly_eval_to_of_int` already builds and
//!   kernel-checks, reused verbatim here for an `Eq` conclusion instead of
//!   the `Lt` conclusions the IVT/EVT siblings need.
//!
//! What this module does **not** attempt, and why the claim is deliberately
//! weaker than it might look:
//!
//! - **It does not compute the slope itself.** `(p(3) - p(0)) / (3 - 0) = 9`
//!   is elementary arithmetic on the two reconstructed values (27 and 0) and
//!   is not separately admitted through this kernel — no `Rat` division
//!   reconstruction exists here, and none is claimed.
//! - **It says nothing about Rolle's theorem, the witness `c = sqrt(3)`, or
//!   its Sturm-isolated bracket.** Those remain `cas-internal`, checked only
//!   by `mvt::verify_mvt_certificate` — exactly as
//!   `F:cas-mvt-cubic-witness-sqrt3`'s own evidence notes already state.
//! - **It does not reconstruct `deriv`/`g`/`deriv_g`** (the Rolle reduction
//!   `g(x) = p(x) - p(a) - slope*(x-a)` and its derivative) at all.
//!
//! So `F:cas-mvt-secant-endpoints-kernel-checked` is a SIBLING fact to
//! `F:cas-mvt-cubic-witness-sqrt3`, the same relationship the IVT and EVT
//! sign-bracket facts have to their own Sturm-backed originals: folding this
//! evidence into the full certificate's fact would make
//! `classify_cas_certificate_fact` mislabel the WHOLE certificate — Rolle's
//! argument and the Sturm count included — as kernel-reconstructed.
//!
//! # The construction
//!
//! `Eq Rat (polyEval c n x) target` falls straight out of
//! [`cas_ivt_bridge_tests::poly_eval_to_of_int`] with no wrapper needed (no
//! `zero_lt_via_nat_le`/`lt_zero_via_true` — this module's conclusions are
//! equalities, not inequalities, so the sign-bracket engine's extra step is
//! unnecessary): `target` is built directly as `Rat.ofInt` applied to the
//! SAME arithmetic chain the evaluation reduces to, so the returned proof's
//! own inferred type already IS the declaration's ascribed type — no
//! `def_eq`-only ascription risk, unlike the sign-bracket siblings' literal
//! `hi`/`lo` bounds.

use axeyum_cas::mvt::{MvtCertificate, polynomial_mvt};
use axeyum_ir::Rational;

use super::cas_ivt_bridge_tests::{
    built, int_lit, n_term_polynomial, of_int, poly_eval_to_of_int, rational_to_int,
};
use super::ops::{req, rpoly_eval};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::on_a_deep_stack;

/// Translate an [`MvtCertificate`]'s `poly`/`a`/`b` to `i128`s. Declines
/// (`None`) on a non-integer value. Deliberately drops `slope`, `g`,
/// `deriv_g`, `c` — out of this slice's scope, see module doc.
fn poly_ab_to_int(cert: &MvtCertificate) -> Option<(Vec<i128>, i128, i128)> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Declaration as Decl;

    /// `p(x) = x^3` on `[0, 3]` — the SAME certificate
    /// `F:cas-mvt-cubic-witness-sqrt3` cites, so this reconstructs a piece of
    /// that certificate, not a hand-picked easier one.
    #[test]
    fn mvt_secant_endpoints_kernel_checked() {
        on_a_deep_stack(mvt_secant_endpoints_kernel_checked_body);
    }

    fn mvt_secant_endpoints_kernel_checked_body() {
        let (mut kernel, prelude) = built();
        let anon = kernel.anon();

        // The CAS's own "fast search" half, entirely independent of anything
        // below: produce the SAME certificate `F:cas-mvt-cubic-witness-sqrt3`
        // cites (x^3 on [0,3], irrational witness sqrt(3)).
        let poly = vec![
            Rational::integer(0),
            Rational::integer(0),
            Rational::integer(0),
            Rational::integer(1),
        ];
        let cert = polynomial_mvt(&poly, Rational::integer(0), Rational::integer(3))
            .expect("the CAS must produce an MVT certificate for x^3 on [0,3]");
        assert_eq!(axeyum_cas::mvt::verify_mvt_certificate(&cert), Some(true));
        assert_eq!(
            cert.slope,
            Rational::integer(9),
            "sanity: the secant slope this fact's two evaluations determine is 9"
        );

        // The translator: certificate -> integer (poly, a, b). Asserted equal
        // to the CAS's own fields before building anything kernel-side.
        let (p_coeffs, a_int, b_int) = poly_ab_to_int(&cert)
            .expect("x^3 and the bracket [0,3] are integer-valued: translator must accept");
        assert_eq!(p_coeffs, vec![0, 0, 0, 1], "translator: x^3 -> [0,0,0,1]");
        assert_eq!((a_int, b_int), (0, 3));

        let mut d = IntDev::new(&mut kernel, prelude.int);
        let p = prelude;

        // Build the coefficient function ONCE, shared by both endpoints.
        let coeffs_int: Vec<ExprId> = p_coeffs.iter().map(|&n| int_lit(&mut d, n)).collect();
        let coeffs_rat: Vec<ExprId> = coeffs_int.iter().map(|&i| of_int(&mut d, p, i)).collect();
        let c = n_term_polynomial(&mut d, p, &coeffs_rat);

        // --- p(3) = 27 -------------------------------------------------------
        let b_int_lit = int_lit(&mut d, b_int);
        let b_rat = of_int(&mut d, p, b_int_lit);
        let (total_b, eq_b) =
            poly_eval_to_of_int(&mut d, p, c, &coeffs_int, &coeffs_rat, b_rat, b_int_lit);
        let target_b = of_int(&mut d, p, total_b);
        let n_lit = d.num(u32::try_from(coeffs_int.len()).expect("fits"));
        let eval_b_expr = rpoly_eval(&mut d, p, c, n_lit, b_rat);
        let stmt_b = req(&mut d, eval_b_expr, target_b);

        let name_b = d.kernel().name_str(anon, "Check.mvt_secant_p_at_b");
        let admitted_b = d.kernel().add_declaration(Decl::Theorem {
            name: name_b,
            uparams: vec![],
            ty: stmt_b,
            value: eq_b,
        });
        assert!(
            admitted_b.is_ok(),
            "p(3) = 27 for p = x^3, reconstructed through Rat.polyEval, must \
             kernel-check: {admitted_b:?}"
        );

        // --- p(0) = 0 --------------------------------------------------------
        let a_int_lit = int_lit(&mut d, a_int);
        let a_rat = of_int(&mut d, p, a_int_lit);
        let (total_a, eq_a) =
            poly_eval_to_of_int(&mut d, p, c, &coeffs_int, &coeffs_rat, a_rat, a_int_lit);
        let target_a = of_int(&mut d, p, total_a);
        let n_lit_a = d.num(u32::try_from(coeffs_int.len()).expect("fits"));
        let eval_a_expr = rpoly_eval(&mut d, p, c, n_lit_a, a_rat);
        let stmt_a = req(&mut d, eval_a_expr, target_a);

        let name_a = d.kernel().name_str(anon, "Check.mvt_secant_p_at_a");
        let admitted_a = d.kernel().add_declaration(Decl::Theorem {
            name: name_a,
            uparams: vec![],
            ty: stmt_a,
            value: eq_a,
        });
        assert!(
            admitted_a.is_ok(),
            "p(0) = 0 for p = x^3, reconstructed through Rat.polyEval, must \
             kernel-check: {admitted_a:?}"
        );

        // --- negative control: SAME proof, WRONG (off-by-one) statement -----
        //
        // Mirrors the IVT/EVT siblings' own negative controls: reuse a TRUE
        // proof term verbatim and ascribe it against a FALSE statement's
        // type, exercising `Kernel::add_declaration`'s own type check rather
        // than asking any decision procedure to "prove" a falsehood.
        // `p(3) = 27` is TRUE; `p(3) = 28` is FALSE.
        let wrong_int = int_lit(&mut d, 28);
        let wrong_target = of_int(&mut d, p, wrong_int);
        let false_stmt = req(&mut d, eval_b_expr, wrong_target);
        let name_wrong = d.kernel().name_str(anon, "Check.mvt_secant_p_at_b_wrong");
        let admitted_wrong = d.kernel().add_declaration(Decl::Theorem {
            name: name_wrong,
            uparams: vec![],
            ty: false_stmt,
            value: eq_b,
        });
        assert!(
            admitted_wrong.is_err(),
            "the proof of p(3) = 27 must be REJECTED against the FALSE \
             statement p(3) = 28: {admitted_wrong:?}"
        );
    }
}
