//! Additive congruence family closing five `ml430-nat-modeq-*` mirrors:
//! left/right cancellation of a shared congruence addend, the two `iff`
//! wrappers built from it plus the existing two-hypothesis `mod_eq_add`, and
//! the coprime-order flip of multiplicative cancellation.
//!
//! `Nat.modEq d a b := ∃ u v, a + d*u = b + d*v` (declared in `modular.rs`).
//! Unlike multiplicative cancellation (`euler.rs`'s `mod_eq_cancel`, which
//! genuinely needs coprimality/Bezout), additive cancellation modulo `d`
//! needs no side condition at all: `modEq d (a+k) (b+k) → modEq d a b` is
//! already built in `euler.rs` as the private helper
//! `cancel_common_right_addend` (used there to finish `mod_eq_cancel`) and
//! `rewrite_mod_eq` (transport a `modEq` across an `Eq` on each endpoint).
//! Both are exported `pub(super)` from `euler.rs` and reused here rather
//! than re-derived, so the only new existential-elimination term in this
//! file is none at all -- everything below composes already-checked lemmas.
//!
//! - [`declare_mod_eq_add_cancel`] builds:
//!   - `Nat.mod_eq_add_left_cancel  : modEq n a b → modEq n (a+c) (b+d) → modEq n c d`
//!     (`a≡b [MOD n] → a+c≡b+d [MOD n] → c≡d [MOD n]`, `F:ml430-nat-modeq-add-left-cancel`)
//!   - `Nat.mod_eq_add_right_cancel : modEq n c d → modEq n (a+c) (b+d) → modEq n a b`
//!     (`c≡d [MOD n] → a+c≡b+d [MOD n] → a≡b [MOD n]`, `F:ml430-nat-modeq-add-right-cancel`)
//!   - `Nat.mod_eq_add_iff_left  : modEq n a b → (modEq n (a+c) (b+d) ↔ modEq n c d)`
//!     (`F:ml430-nat-modeq-add-iff-left`), `mp` is `mod_eq_add_left_cancel`,
//!     `mpr` is the existing `mod_eq_add`.
//!   - `Nat.mod_eq_add_iff_right : modEq n c d → (modEq n (a+c) (b+d) ↔ modEq n a b)`
//!     (`F:ml430-nat-modeq-add-iff-right`), mirror of the above.
//!   - `Nat.mod_eq_cancel_left : gcd m c = 1 → modEq m (c*a) (c*b) → modEq m a b`
//!     (`F:ml430-nat-modeq-cancel-left-of-coprime`) -- same content as
//!     `euler.rs`'s `mod_eq_cancel`, whose coprimality hypothesis is stated
//!     `gcd c n = 1` (the modulus on the right); this mirror's Mathlib
//!     source states it `m.gcd c = 1` (the modulus on the left), so the
//!     hypothesis is transported one step across `gcd_comm` before handing
//!     it to `mod_eq_cancel` unchanged.

use super::NatPrelude;
use super::euler::{cancel_common_right_addend, rewrite_mod_eq};
use super::ops::{NatDev, NatOps};
use crate::KernelError;
use crate::expr::ExprId;

/// `modEq n a b → modEq n (a+c) (b+d) → modEq n c d`, by shifting `h1` to
/// `modEq n (c+a) (c+b)` (`mod_eq_add_left`), reassociating `h2` to
/// `modEq n (c+a) (d+b)` (`add_comm` on each endpoint via `rewrite_mod_eq`),
/// chaining the two through `mod_eq_symm`/`mod_eq_trans` to
/// `modEq n (c+b) (d+b)`, and peeling the shared right addend `b`
/// (`cancel_common_right_addend`).
fn build_add_left_cancel(d: &mut NatDev<'_>, p: &NatPrelude, values: &[ExprId]) -> (ExprId, ExprId) {
    let p = *p;
    let (modulus, a, b, c, dd) = (values[0], values[1], values[2], values[3], values[4]);
    let ac = d.add(a, c);
    let bd = d.add(b, dd);
    let h1_ty = d.mod_eq(modulus, a, b);
    let h2_ty = d.mod_eq(modulus, ac, bd);
    let concl = d.mod_eq(modulus, c, dd);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let ca = d.add(c, a);
    let db = d.add(dd, b);
    let eq_ac = d.lemma(p.add_comm, &[a, c]);
    let eq_bd = d.lemma(p.add_comm, &[b, dd]);
    let h2p = rewrite_mod_eq(d, modulus, ac, bd, ca, db, eq_ac, eq_bd, h2);

    let s1 = d.lemma(p.mod_eq_add_left, &[modulus, a, b, c, h1]);
    let cb = d.add(c, b);
    let s1s = d.lemma(p.mod_eq_symm, &[modulus, ca, cb, s1]);
    let s2 = d.lemma(p.mod_eq_trans, &[modulus, cb, ca, db, s1s, h2p]);
    let result = cancel_common_right_addend(d, &p, modulus, c, dd, b, s2);

    let inner_ty = d.arrow(h2_ty, concl);
    let stmt = d.arrow(h1_ty, inner_ty);
    let inner_proof = d.lam_fv(h2_fv, h2_ty, result);
    let proof = d.lam_fv(h1_fv, h1_ty, inner_proof);
    (stmt, proof)
}

/// `modEq n c d → modEq n (a+c) (b+d) → modEq n a b`, the mirror of
/// [`build_add_left_cancel`]: shift `h1` to `modEq n (c+a) (d+a)`
/// (`mod_eq_add_right`), reassociate to `modEq n (a+c) (a+d)`, chain through
/// `h2` to `modEq n (a+d) (b+d)`, and peel the shared right addend `d`.
fn build_add_right_cancel(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    values: &[ExprId],
) -> (ExprId, ExprId) {
    let p = *p;
    let (modulus, a, b, c, dd) = (values[0], values[1], values[2], values[3], values[4]);
    let ac = d.add(a, c);
    let bd = d.add(b, dd);
    let h1_ty = d.mod_eq(modulus, c, dd);
    let h2_ty = d.mod_eq(modulus, ac, bd);
    let concl = d.mod_eq(modulus, a, b);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let ca = d.add(c, a);
    let da = d.add(dd, a);
    let ad = d.add(a, dd);
    let eq_ca = d.lemma(p.add_comm, &[c, a]);
    let eq_da = d.lemma(p.add_comm, &[dd, a]);
    let s1 = d.lemma(p.mod_eq_add_right, &[modulus, c, dd, a, h1]);
    let s1p = rewrite_mod_eq(d, modulus, ca, da, ac, ad, eq_ca, eq_da, s1);
    let s1s = d.lemma(p.mod_eq_symm, &[modulus, ac, ad, s1p]);
    let s2 = d.lemma(p.mod_eq_trans, &[modulus, ad, ac, bd, s1s, h2]);
    let result = cancel_common_right_addend(d, &p, modulus, a, b, dd, s2);

    let inner_ty = d.arrow(h2_ty, concl);
    let stmt = d.arrow(h1_ty, inner_ty);
    let inner_proof = d.lam_fv(h2_fv, h2_ty, result);
    let proof = d.lam_fv(h1_fv, h1_ty, inner_proof);
    (stmt, proof)
}

pub(super) fn declare_mod_eq_add_cancel(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    // mod_eq_add_left_cancel : modEq n a b → modEq n (a+c) (b+d) → modEq n c d
    d.theorem(p.mod_eq_add_left_cancel, 5, &|d, v| build_add_left_cancel(d, &p, v))?;

    // mod_eq_add_right_cancel : modEq n c d → modEq n (a+c) (b+d) → modEq n a b
    d.theorem(p.mod_eq_add_right_cancel, 5, &|d, v| {
        build_add_right_cancel(d, &p, v)
    })?;

    // mod_eq_add_iff_left : modEq n a b → (modEq n (a+c) (b+d) ↔ modEq n c d)
    d.theorem(p.mod_eq_add_iff_left, 5, &|d, values| {
        let (modulus, a, b, c, dd) = (values[0], values[1], values[2], values[3], values[4]);
        let h1_ty = d.mod_eq(modulus, a, b);
        let ac = d.add(a, c);
        let bd = d.add(b, dd);
        let lhs_ty = d.mod_eq(modulus, ac, bd);
        let rhs_ty = d.mod_eq(modulus, c, dd);

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);

        let mp = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let body = d.lemma(
                p.mod_eq_add_left_cancel,
                &[modulus, a, b, c, dd, h1, h2],
            );
            d.lam_fv(h2_fv, lhs_ty, body)
        };
        let mpr = {
            let h3_fv = d.fresh_fvar();
            let h3 = d.kernel().fvar(h3_fv);
            let body = d.lemma(p.mod_eq_add, &[modulus, a, b, c, dd, h1, h3]);
            d.lam_fv(h3_fv, rhs_ty, body)
        };
        let target = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);
        let iff_proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        let stmt = d.arrow(h1_ty, target);
        let proof = d.lam_fv(h1_fv, h1_ty, iff_proof);
        (stmt, proof)
    })?;

    // mod_eq_add_iff_right : modEq n c d → (modEq n (a+c) (b+d) ↔ modEq n a b)
    d.theorem(p.mod_eq_add_iff_right, 5, &|d, values| {
        let (modulus, a, b, c, dd) = (values[0], values[1], values[2], values[3], values[4]);
        let h1_ty = d.mod_eq(modulus, c, dd);
        let ac = d.add(a, c);
        let bd = d.add(b, dd);
        let lhs_ty = d.mod_eq(modulus, ac, bd);
        let rhs_ty = d.mod_eq(modulus, a, b);

        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);

        let mp = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let body = d.lemma(
                p.mod_eq_add_right_cancel,
                &[modulus, a, b, c, dd, h1, h2],
            );
            d.lam_fv(h2_fv, lhs_ty, body)
        };
        let mpr = {
            let h3_fv = d.fresh_fvar();
            let h3 = d.kernel().fvar(h3_fv);
            let body = d.lemma(p.mod_eq_add, &[modulus, a, b, c, dd, h3, h1]);
            d.lam_fv(h3_fv, rhs_ty, body)
        };
        let target = d.const_app(p.logic.iff, &[lhs_ty, rhs_ty]);
        let iff_proof = d.const_app(p.logic.iff_intro, &[lhs_ty, rhs_ty, mp, mpr]);
        let stmt = d.arrow(h1_ty, target);
        let proof = d.lam_fv(h1_fv, h1_ty, iff_proof);
        (stmt, proof)
    })?;

    // mod_eq_cancel_left : gcd m c = 1 → modEq m (c*a) (c*b) → modEq m a b
    //
    // `euler.rs`'s `mod_eq_cancel` states coprimality `gcd c n = 1`; this
    // mirror's Mathlib source states `m.gcd c = 1`. Transport the hypothesis
    // across `gcd_comm` and hand it to `mod_eq_cancel` unchanged -- no new
    // existential reasoning, only a rewritten equation.
    d.theorem(p.mod_eq_cancel_left, 4, &|d, values| {
        let (modulus, a, b, c) = (values[0], values[1], values[2], values[3]);
        let one = d.num(1);
        let gcd_mc = d.gcd(modulus, c);
        let gcd_cm = d.gcd(c, modulus);
        let coprime_ty = d.eq(gcd_mc, one);
        let ca = d.mul(c, a);
        let cb = d.mul(c, b);
        let hyp2_ty = d.mod_eq(modulus, ca, cb);
        let concl = d.mod_eq(modulus, a, b);

        let cop_fv = d.fresh_fvar();
        let cop = d.kernel().fvar(cop_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);

        let comm_eq = d.lemma(p.gcd_comm, &[modulus, c]);
        let comm_eq_rev = d.symm(gcd_mc, gcd_cm, comm_eq);
        let transported = d.trans(gcd_cm, gcd_mc, one, comm_eq_rev, cop);
        let result = d.lemma(p.mod_eq_cancel, &[modulus, c, a, b, transported, h2]);

        let inner_ty = d.arrow(hyp2_ty, concl);
        let stmt = d.arrow(coprime_ty, inner_ty);
        let inner_proof = d.lam_fv(h2_fv, hyp2_ty, result);
        let proof = d.lam_fv(cop_fv, coprime_ty, inner_proof);
        (stmt, proof)
    })?;

    Ok(())
}
