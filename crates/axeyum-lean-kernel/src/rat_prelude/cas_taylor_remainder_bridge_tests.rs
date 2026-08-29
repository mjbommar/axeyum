//! CAS -> kernel bridge, slice 6: the exact polynomial Taylor-with-Lagrange-
//! remainder theorem's **left-hand side**, `p(b) - T_n(b) = 16`, for
//! `axeyum-cas`'s `taylor::TaylorCertificate` — reconstructing the two
//! evaluations that determine the remainder the witness `xi` is supposed to
//! explain, not the witness or the Lagrange identity itself.
//!
//! # Scope, stated up front (mirrors the MVT/IVT/EVT siblings' discipline)
//!
//! `F:cas-taylor-quartic-lagrange-witness` names the full certificate for
//! `p(x) = x^4`, center `a = 0`, degree `n = 1`, evaluation point `b = 2`:
//! the Taylor polynomial `T_1` is identically zero (`p'(0) = 0`), the exact
//! remainder is `p(2) - T_1(2) = 16`, and the certificate names the exact
//! irrational witness `xi = sqrt(2/3)` where the Lagrange identity holds.
//! This module reconstructs neither the witness, the generalized-Rolle
//! argument, nor the Lagrange identity itself — only the two rational
//! evaluations the remainder's LEFT-hand side is built FROM:
//!
//! - `p(2) = 16`, for `p = x^4` (`cert.poly`/`cert.a`/`cert.b` themselves,
//!   not hand-picked values) — pure exact `Rat` arithmetic, reduced from
//!   `Rat.polyEval` by the SAME engine
//!   `cas_ivt_bridge_tests::poly_eval_to_of_int` already builds and
//!   kernel-checks.
//! - `T_1(2) = 0`, for `T_1` the CAS's own `cert.taylor_poly` — which for
//!   this instance trims to the EMPTY polynomial (`p'(0) = 0`, so every
//!   coefficient the construction would add is skipped; see
//!   `taylor::build_taylor_and_deriv`'s own `if !c_k.is_zero()` guard). This
//!   sub-claim is therefore trivial by construction (the zero polynomial
//!   evaluates to zero everywhere), and this module says so rather than
//!   dressing it up: it is reconstructed through the SAME machinery as the
//!   `p(2)=16` claim purely for uniformity with this batch's other bridges,
//!   not because it needed independent verification.
//!
//! What this module does **not** attempt, and why the claim is deliberately
//! weaker than it might look:
//!
//! - **It does not compute the remainder quotient or subtraction.**
//!   `p(2) - T_1(2) = 16 - 0 = 16` is elementary arithmetic on the two
//!   reconstructed values and is not separately admitted through this
//!   kernel.
//! - **It says nothing about the generalized-Rolle argument, `p'' = 12x^2`,
//!   the witness `xi = sqrt(2/3)`, or its Sturm-isolated bracket.** Those
//!   remain `cas-internal`, checked only by `taylor::verify_taylor_certificate`
//!   — exactly as `F:cas-taylor-quartic-lagrange-witness`'s own evidence
//!   notes already state.
//! - **It does not reconstruct `deriv_np1`** (the `(n+1)`-th derivative) at
//!   all.
//! - **It is unrelated to `rat_prelude::taylor`'s `Rat.taylor_deg1`**, which
//!   `F:cas-taylor-quartic-lagrange-witness`'s own notes already flag as
//!   materially weaker (degree <= 1 only, no remainder, no witness) and not
//!   a reconstruction of this certificate. This module does not change that
//!   assessment; it reconstructs a narrow rational sub-claim alongside it,
//!   not the general theorem.
//!
//! So `F:cas-taylor-remainder-lhs-kernel-checked` is a SIBLING fact to
//! `F:cas-taylor-quartic-lagrange-witness`, the same relationship the
//! IVT/EVT/MVT sign-bracket-or-endpoint facts have to their own Sturm-backed
//! originals: folding this evidence into the full certificate's fact would
//! make `classify_cas_certificate_fact` mislabel the WHOLE certificate — the
//! generalized-Rolle argument and the Sturm count included — as
//! kernel-reconstructed.
//!
//! # The construction
//!
//! Identical recipe to `cas_mvt_secant_bridge_tests`: `Eq Rat (polyEval c n
//! x) target` falls straight out of
//! [`cas_ivt_bridge_tests::poly_eval_to_of_int`] with no wrapper needed (both
//! conclusions here are equalities). `cert.taylor_poly` trims to the empty
//! vector for this instance, and `n_term_polynomial` requires at least one
//! coefficient, so this module pads it to a single `Rat.zero` coefficient
//! before building — still the SAME polynomial (the empty and
//! single-zero-coefficient representations denote the same function), just
//! in the shape the shared engine needs.

use axeyum_cas::taylor::{TaylorCertificate, polynomial_taylor};
use axeyum_ir::Rational;

use super::cas_ivt_bridge_tests::{
    built, int_lit, n_term_polynomial, of_int, poly_eval_to_of_int, rational_to_int,
};
use super::ops::{req, rpoly_eval};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::on_a_deep_stack;

/// Translate a [`TaylorCertificate`]'s `poly`/`a`/`b` to `i128`s, and
/// `taylor_poly` to `i128`s PADDED to at least one entry (`[0]` if the
/// trimmed polynomial is empty — the zero polynomial). Declines (`None`) on
/// a non-integer value. Deliberately drops `n`, `deriv_np1`, `xi` — out of
/// this slice's scope, see module doc.
fn cert_to_int(cert: &TaylorCertificate) -> Option<(Vec<i128>, Vec<i128>, i128, i128)> {
    let poly: Vec<i128> = cert
        .poly
        .iter()
        .copied()
        .map(rational_to_int)
        .collect::<Option<_>>()?;
    let mut taylor: Vec<i128> = cert
        .taylor_poly
        .iter()
        .copied()
        .map(rational_to_int)
        .collect::<Option<_>>()?;
    if taylor.is_empty() {
        taylor.push(0);
    }
    let a = rational_to_int(cert.a)?;
    let b = rational_to_int(cert.b)?;
    Some((poly, taylor, a, b))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Declaration as Decl;

    /// `p(x) = x^4`, `a = 0`, `n = 1`, `b = 2` — the SAME certificate
    /// `F:cas-taylor-quartic-lagrange-witness` cites, so this reconstructs a
    /// piece of that certificate, not a hand-picked easier one.
    #[test]
    fn taylor_remainder_lhs_kernel_checked() {
        on_a_deep_stack(taylor_remainder_lhs_kernel_checked_body);
    }

    fn taylor_remainder_lhs_kernel_checked_body() {
        let (mut kernel, prelude) = built();
        let anon = kernel.anon();

        // The CAS's own "fast search" half, entirely independent of anything
        // below: produce the SAME certificate
        // `F:cas-taylor-quartic-lagrange-witness` cites (x^4, a=0, n=1, b=2,
        // irrational witness sqrt(2/3)).
        let poly = vec![
            Rational::integer(0),
            Rational::integer(0),
            Rational::integer(0),
            Rational::integer(0),
            Rational::integer(1),
        ];
        let cert = polynomial_taylor(&poly, Rational::integer(0), 1, Rational::integer(2))
            .expect("the CAS must produce a Taylor certificate for x^4 at a=0,n=1,b=2");
        assert_eq!(
            axeyum_cas::taylor::verify_taylor_certificate(&cert),
            Some(true)
        );

        // The translator: certificate -> integer (poly, taylor_poly padded,
        // a, b). Asserted equal to the CAS's own fields before building
        // anything kernel-side.
        let (p_coeffs, t_coeffs, a_int, b_int) = cert_to_int(&cert)
            .expect("x^4, the zero Taylor polynomial, and a=0/b=2 are integer-valued: translator must accept");
        assert_eq!(
            p_coeffs,
            vec![0, 0, 0, 0, 1],
            "translator: x^4 -> [0,0,0,0,1]"
        );
        assert_eq!(
            t_coeffs,
            vec![0],
            "translator: T_1 (identically zero for this instance) padded to [0]"
        );
        assert_eq!((a_int, b_int), (0, 2));

        let mut d = IntDev::new(&mut kernel, prelude.int);
        let p = prelude;

        // --- p(2) = 16 -------------------------------------------------------
        let p_coeffs_int: Vec<ExprId> = p_coeffs.iter().map(|&n| int_lit(&mut d, n)).collect();
        let p_coeffs_rat: Vec<ExprId> =
            p_coeffs_int.iter().map(|&i| of_int(&mut d, p, i)).collect();
        let pc = n_term_polynomial(&mut d, p, &p_coeffs_rat);
        let b_int_lit = int_lit(&mut d, b_int);
        let b_rat = of_int(&mut d, p, b_int_lit);
        let (total_p, eq_p) = poly_eval_to_of_int(
            &mut d,
            p,
            pc,
            &p_coeffs_int,
            &p_coeffs_rat,
            b_rat,
            b_int_lit,
        );
        let target_p = of_int(&mut d, p, total_p);
        let n_lit_p = d.num(u32::try_from(p_coeffs_int.len()).expect("fits"));
        let eval_p_expr = rpoly_eval(&mut d, p, pc, n_lit_p, b_rat);
        let stmt_p = req(&mut d, eval_p_expr, target_p);

        let name_p = d.kernel().name_str(anon, "Check.taylor_remainder_p_at_b");
        let admitted_p = d.kernel().add_declaration(Decl::Theorem {
            name: name_p,
            uparams: vec![],
            ty: stmt_p,
            value: eq_p,
        });
        assert!(
            admitted_p.is_ok(),
            "p(2) = 16 for p = x^4, reconstructed through Rat.polyEval, must \
             kernel-check: {admitted_p:?}"
        );

        // --- T_1(2) = 0 (trivial: T_1 is the zero polynomial) ---------------
        let t_coeffs_int: Vec<ExprId> = t_coeffs.iter().map(|&n| int_lit(&mut d, n)).collect();
        let t_coeffs_rat: Vec<ExprId> =
            t_coeffs_int.iter().map(|&i| of_int(&mut d, p, i)).collect();
        let tc = n_term_polynomial(&mut d, p, &t_coeffs_rat);
        let b_int_lit2 = int_lit(&mut d, b_int);
        let b_rat2 = of_int(&mut d, p, b_int_lit2);
        let (total_t, eq_t) = poly_eval_to_of_int(
            &mut d,
            p,
            tc,
            &t_coeffs_int,
            &t_coeffs_rat,
            b_rat2,
            b_int_lit2,
        );
        let target_t = of_int(&mut d, p, total_t);
        let n_lit_t = d.num(u32::try_from(t_coeffs_int.len()).expect("fits"));
        let eval_t_expr = rpoly_eval(&mut d, p, tc, n_lit_t, b_rat2);
        let stmt_t = req(&mut d, eval_t_expr, target_t);

        let name_t = d.kernel().name_str(anon, "Check.taylor_remainder_t1_at_b");
        let admitted_t = d.kernel().add_declaration(Decl::Theorem {
            name: name_t,
            uparams: vec![],
            ty: stmt_t,
            value: eq_t,
        });
        assert!(
            admitted_t.is_ok(),
            "T_1(2) = 0 for the zero Taylor polynomial T_1, reconstructed \
             through Rat.polyEval, must kernel-check: {admitted_t:?}"
        );

        // --- negative control: SAME proof, WRONG (off-by-one) statement -----
        //
        // `p(2) = 16` is TRUE; `p(2) = 17` is FALSE.
        let wrong_int = int_lit(&mut d, 17);
        let wrong_target = of_int(&mut d, p, wrong_int);
        let false_stmt = req(&mut d, eval_p_expr, wrong_target);
        let name_wrong = d
            .kernel()
            .name_str(anon, "Check.taylor_remainder_p_at_b_wrong");
        let admitted_wrong = d.kernel().add_declaration(Decl::Theorem {
            name: name_wrong,
            uparams: vec![],
            ty: false_stmt,
            value: eq_p,
        });
        assert!(
            admitted_wrong.is_err(),
            "the proof of p(2) = 16 must be REJECTED against the FALSE \
             statement p(2) = 17: {admitted_wrong:?}"
        );
    }
}
