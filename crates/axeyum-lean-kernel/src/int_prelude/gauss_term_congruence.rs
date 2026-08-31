//! Gauss's-lemma connecting theorem, item 1 (ADR-1070/ADR-1130): the
//! per-term congruence
//!
//! ```text
//! a·k ≡ ε_k · gaussFold(pp, a, k)   [pp],   ε_k := if gaussSignNeg pp a k
//!                                                 then -1 else 1
//! ```
//!
//! stated over `Int` because `ε_k` is, with the `Nat`-side content supplied
//! by `nat_prelude/gauss_lemma.rs`'s two branch theorems
//! (`Nat.gauss_fold_modeq_of_sign_false`,
//! `Nat.gauss_fold_add_modeq_zero_of_sign_true`) and lifted by
//! `Int.modEq_of_nat_modEq`.
//!
//! ## Why the `Nat` side is two statements and not one
//!
//! `Nat` has no negation, so "`a·k ≡ −gaussFold [pp]`" cannot be said there
//! at all. The negative branch is therefore stated ADDITIVELY —
//! `modEq pp (a·k + gaussFold) 0` — and this file turns the sum into the
//! negation with one shift: `Int.ModEq.add_right` by `−gaussFold`, then
//! `Int.add_neg_cancel_right` (`(x+y)+(−y) = x`) on the left and
//! `add_comm`/`add_zero` on the right. That is exactly why the `Nat`
//! statement puts `a·k` on the LEFT of the sum: `add_neg_cancel_right`
//! consumes `(x+y)+(−y)`, and `(y+x)+(−y)` would need a commutation first.
//!
//! ## What is free by defeq, and what is not
//!
//! Three bridges cost nothing here, and each was checked rather than
//! assumed:
//!
//! - `Int.mul (ofNat a) (ofNat k) ≡ ofNat (Nat.mul a k)` at SYMBOLIC `a`,
//!   `k` — `Int.mul`'s case split dispatches on the outer `Int` constructor
//!   only (ADR-1070's own correction to its predecessor's sizing). Same for
//!   `Int.add`.
//! - `Int.zero ≡ Int.ofNat Nat.zero` — `Int.zero`'s `Definition` body is
//!   literally that (`int_prelude/defs.rs`), so the `Nat` bridge's `ofNat 0`
//!   right-hand side needs no rewrite.
//! - `Nat.leastResidue pp a k ≡ Nat.mod (Nat.mul a k) pp` — its definition,
//!   used on the `Nat` side.
//!
//! What is NOT free is the selector: `bool_select_int (gaussSignNeg …) (−1)
//! 1` only ι-reduces once the condition is a literal, which is what the
//! `Or (… = true) (… = false)` case split supplies, through `prod.rs`'s
//! existing `select_int_true`/`select_int_false`.
//!
//! ## What this does NOT reach
//!
//! The final assembly (item 3) lives in `gauss_assembly.rs`; this file
//! proves one term of the product and says nothing about the product.

use super::modeq::imodeq;
use super::ops::IntDev;
use super::prod::{bool_select_int, select_int_false, select_int_true};
use crate::KernelError;
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// `Or (Eq Bool b true) (Eq Bool b false)` at `b` — a per-file local copy of
/// `euler_assembly.rs`'s private `bool_true_or_false_int` (this
/// development's standing per-file-copy convention for small `Bool`
/// plumbing; see `nat_prelude/euler.rs`'s doc comment on the same choice).
fn bool_true_or_false_int(d: &mut IntDev<'_>, b: ExprId) -> ExprId {
    let p = d.int();
    let bool_ty = d.bool_ty();
    let true_ = d.bool_true();
    let false_ = d.bool_false();
    let motive = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let true_inner = d.bool_true();
        let false_inner = d.bool_false();
        let is_true = d.bool_eq(x, true_inner);
        let is_false = d.bool_eq(x, false_inner);
        let body = d.const_app(p.logic.or, &[is_true, is_false]);
        d.lam_fv(x_fv, bool_ty, body)
    };
    let case_true = {
        let is_true = d.bool_eq(true_, true_);
        let is_false = d.bool_eq(true_, false_);
        let refl_true = d.bool_refl(true_);
        d.const_app(p.logic.or_inl, &[is_true, is_false, refl_true])
    };
    let case_false = {
        let is_true = d.bool_eq(false_, true_);
        let is_false = d.bool_eq(false_, false_);
        let refl_false = d.bool_refl(false_);
        d.const_app(p.logic.or_inr, &[is_true, is_false, refl_false])
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    d.apply(bool_rec, &[motive, case_false, case_true, b])
}

/// `Int.gaussTermModEq : ∀ pp a k, Lt zero pp →
///   ModEq (ofNat pp) (mul (ofNat a) (ofNat k))
///     (mul (bool_select_int (Nat.gaussSignNeg pp a k) (neg one) one)
///          (ofNat (Nat.gaussFold pp a k)))`
///
/// See the module doc for the two-branch route.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_gauss_term_mod_eq(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();

    d.theorem(p.gauss_term_mod_eq, 3, &|d, v| {
        let (pp, a, k) = (v[0], v[1], v[2]);

        let zero_nat = d.zero();
        let pos_ty = d.lt(zero_nat, pp);

        let n_int = d.of_nat(pp);
        let a_int = d.of_nat(a);
        let k_int = d.of_nat(k);
        let lhs = d.imul(a_int, k_int);

        let test = d.const_app(p.nat.gauss_sign_neg, &[pp, a, k]);
        let one_i = d.ione();
        let neg_one = d.ineg(one_i);
        let sel = bool_select_int(d, test, neg_one, one_i);
        let fold_nat = d.const_app(p.nat.gauss_fold, &[pp, a, k]);
        let g = d.of_nat(fold_nat);
        let rhs = d.imul(sel, g);
        let concl = imodeq(d, n_int, lhs, rhs);
        let stmt = d.arrow(pos_ty, concl);

        let pos_fv = d.fresh_fvar();
        let pos = d.kernel().fvar(pos_fv);

        // The `ofNat`-of-a-`Nat`-product form the `Nat` bridge produces;
        // defeq `lhs`, so the kernel accepts a proof stated at either.
        let ak_nat = d.mul(a, k);
        let x = d.of_nat(ak_nat);

        let true_v = d.bool_true();
        let false_v = d.bool_false();
        let ty_true = d.bool_eq(test, true_v);
        let ty_false = d.bool_eq(test, false_v);
        let cases = bool_true_or_false_int(d, test);

        // --------------------------------------------------------------
        // Branch `gaussSignNeg = true`: `gaussFold = pp - leastResidue`,
        // and the `Nat` fact is the additive one.
        // --------------------------------------------------------------
        let on_true = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            let sum_nat = d.add(ak_nat, fold_nat);
            let nat_fn = d.lemma(p.nat.gauss_fold_add_modeq_zero_of_sign_true, &[pp, a, k]);
            let nat_pf = d.apply(nat_fn, &[pos, h]);
            // nat_pf : Nat.modEq pp (a*k + gaussFold) 0

            let zero_n = d.zero();
            let bridge_fn = d.lemma(p.mod_eq_of_nat_mod_eq, &[pp, sum_nat, zero_n]);
            let hz = d.apply(bridge_fn, &[nat_pf, pos]);
            // hz : ModEq n_int (ofNat sum_nat) (ofNat 0), and `ofNat
            // sum_nat` is defeq `add x g` while `ofNat 0` is defeq
            // `Int.zero` (its own `Definition` body).

            let x_plus_g = d.iadd(x, g);
            let zero_i = d.izero();
            let neg_g = d.ineg(g);

            let s1 = d.lemma(p.mod_eq_add_right, &[n_int, x_plus_g, zero_i, neg_g, hz]);
            let lhs_s1 = d.iadd(x_plus_g, neg_g);
            let rhs_s1 = d.iadd(zero_i, neg_g);
            // s1 : ModEq n_int ((x+g)+(-g)) (0+(-g))

            let e1 = d.const_app(p.add_neg_cancel_right, &[x, g]);
            // e1 : Eq Int ((x+g)+(-g)) x
            let s2 = d.int_eq_rewrite(lhs_s1, x, e1, s1, &|d, t| imodeq(d, n_int, t, rhs_s1));

            let neg_g_plus_zero = d.iadd(neg_g, zero_i);
            let comm = d.const_app(p.add_comm, &[zero_i, neg_g]);
            let az = d.const_app(p.add_zero, &[neg_g]);
            let (_e, e2) = d.ichain(rhs_s1, &[(neg_g_plus_zero, comm), (neg_g, az)]);
            // e2 : Eq Int (0+(-g)) (-g)
            let s3 = d.int_eq_rewrite(rhs_s1, neg_g, e2, s2, &|d, t| imodeq(d, n_int, x, t));
            // s3 : ModEq n_int x (-g)

            let mul_negone_g = d.imul(neg_one, g);
            let nom = d.const_app(p.neg_one_mul, &[g]); // Eq (mul (-1) g) (-g)
            let nom_rev = d.isymm(mul_negone_g, neg_g, nom);
            let s4 = d.int_eq_rewrite(neg_g, mul_negone_g, nom_rev, s3, &|d, t| {
                imodeq(d, n_int, x, t)
            });
            // s4 : ModEq n_int x (mul (-1) g)

            let sel_eq = select_int_true(d, test, neg_one, one_i, h); // Eq sel (-1)
            let sel_eq_rev = d.isymm(sel, neg_one, sel_eq);
            d.int_eq_rewrite(neg_one, sel, sel_eq_rev, s4, &|d, t| {
                let r = d.imul(t, g);
                imodeq(d, n_int, x, r)
            })
        };

        // --------------------------------------------------------------
        // Branch `gaussSignNeg = false`: `gaussFold` IS the least residue.
        // --------------------------------------------------------------
        let on_false = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
            let nat_fn = d.lemma(p.nat.gauss_fold_modeq_of_sign_false, &[pp, a, k]);
            let nat_pf = d.apply(nat_fn, &[pos, h]);
            // nat_pf : Nat.modEq pp (a*k) (gaussFold pp a k)

            let bridge_fn = d.lemma(p.mod_eq_of_nat_mod_eq, &[pp, ak_nat, fold_nat]);
            let hb = d.apply(bridge_fn, &[nat_pf, pos]);
            // hb : ModEq n_int x g

            let mul_one_g = d.imul(one_i, g);
            let om = d.const_app(p.one_mul, &[g]); // Eq (mul one g) g
            let om_rev = d.isymm(mul_one_g, g, om); // Eq g (mul one g)
            let s1 = d.int_eq_rewrite(g, mul_one_g, om_rev, hb, &|d, t| imodeq(d, n_int, x, t));
            // s1 : ModEq n_int x (mul one g)

            let sel_eq = select_int_false(d, test, neg_one, one_i, h); // Eq sel one
            let sel_eq_rev = d.isymm(sel, one_i, sel_eq);
            d.int_eq_rewrite(one_i, sel, sel_eq_rev, s1, &|d, t| {
                let r = d.imul(t, g);
                imodeq(d, n_int, x, r)
            })
        };

        let body = d.or_elim(ty_true, ty_false, concl, cases, on_true, on_false);
        let proof = d.lam_fv(pos_fv, pos_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}
