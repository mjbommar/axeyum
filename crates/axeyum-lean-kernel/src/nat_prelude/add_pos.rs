//! `Nat.add_pos_right` — Mathlib's `∀ {b : ℕ} (a : ℕ), 0 < b → 0 < a + b`.
//!
//! A case split on `b` (via `NatOps::induct`, the `_ih` unused): at `zero`
//! the hypothesis `Lt zero zero` is impossible, discharged by
//! [`NatPrelude::not_lt_zero`] instantiated at `zero`; at `succ k`,
//! `add a (succ k)` is definitionally `succ (add a k)` (`Nat.add` recurses on
//! its RIGHT argument — see `defs.rs::declare_arithmetic`), so the conclusion
//! is exactly [`NatOps::zero_lt_succ`] applied to `add a k`, independent of
//! the hypothesis. Same shape as `order_more.rs`'s `zero_lt_of_ne_zero`.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;

/// `False.rec (fun _ => target) false_proof : target`, mirroring
/// `order_more.rs`'s private `ex_falso` (not reused across files: it is six
/// lines and `pub(super)` there would widen an otherwise-local helper).
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// Declare `Nat.add_pos_right : ∀ (b a : Nat), Lt zero b → Lt zero (add a b)`.
pub(super) fn declare_add_pos(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    d.theorem(p.add_pos_right, 2, &|d, v| {
        let (b, a) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId, a: ExprId| {
            let zero = d.zero();
            let lt_zero_x = d.lt(zero, x);
            let sum = d.add(a, x);
            let concl = d.lt(zero, sum);
            d.arrow(lt_zero_x, concl)
        };
        let stmt = motive(d, b, a);
        let proof = d.induct(
            &|d, x| motive(d, x, a),
            &|d| {
                let zero = d.zero();
                let lt_zero_zero = d.lt(zero, zero);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let refuted = d.lemma(p.not_lt_zero, &[zero]); // Not (Lt zero zero)
                let absurd = d.apply(refuted, &[h]);
                let target = {
                    let sum = d.add(a, zero);
                    d.lt(zero, sum)
                };
                let body = ex_falso(d, &p, target, absurd);
                d.lam_fv(h_fv, lt_zero_zero, body)
            },
            &|d, k, _ih| {
                let sk = d.succ(k);
                let zero = d.zero();
                let lt_zero_sk = d.lt(zero, sk);
                let h_fv = d.fresh_fvar();
                let sum_k = d.add(a, k);
                let body = d.zero_lt_succ(sum_k); // Lt zero (succ sum_k)
                d.lam_fv(h_fv, lt_zero_sk, body)
            },
            b,
        );
        (stmt, proof)
    })?;

    Ok(())
}
