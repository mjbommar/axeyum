//! Five more `Nat` order/beq lemmas, under their exact Lean-core flat names,
//! built on top of [`declare_no_confusion`](super::no_confusion) and
//! [`declare_order_extra`](super::order_extra) landing first.
//!
//! `Nat.lt_of_not_le` and `Nat.lt_or_ge` both reduce to one shared fact,
//! [`le_or_gt`]: `∀ a b, Or (Le a b) (Lt b a)`, proved by the same double
//! induction as `Nat.le_total` (`order.rs`) with the right branch
//! strengthened from `Le b a` to the strict `Lt b a`. This is genuinely
//! constructive — `Nat.le` is decidable via the induction below, not via
//! excluded middle — so it needs no classical axiom.
//!
//! `Nat.ne_of_beq_eq_false` needed no new `Bool.noConfusion` machinery: the
//! existing `false_true_elim` (`ops.rs`) already discriminates
//! `Bool.false = Bool.true`, which is exactly what bridging `beq a b = false`
//! against `beq_eq_true_of_eq` produces.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::linarith::nat as linarith;

/// `False.rec (fun _ => target) false_proof : target` — ex falso into an
/// arbitrary target from a proof of `False`, the same construction used
/// inline throughout `order_extra.rs`'s `sub_lt`.
fn ex_falso(d: &mut NatDev<'_>, p: &NatPrelude, target: ExprId, false_proof: ExprId) -> ExprId {
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
    let level_zero = d.kernel().level_zero();
    let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
    d.apply(rec, &[motive, false_proof])
}

/// `Or ppos qpos → Or qpos ppos`, via `Or.elim`.
fn or_swap(d: &mut NatDev<'_>, p: &NatPrelude, ppos: ExprId, qpos: ExprId, h: ExprId) -> ExprId {
    let logic = p.logic;
    let target = d.const_app(logic.or, &[qpos, ppos]);
    let minor1 = {
        let hp_fv = d.fresh_fvar();
        let hp = d.kernel().fvar(hp_fv);
        let body = d.const_app(logic.or_inr, &[qpos, ppos, hp]);
        d.lam_fv(hp_fv, ppos, body)
    };
    let minor2 = {
        let hq_fv = d.fresh_fvar();
        let hq = d.kernel().fvar(hq_fv);
        let body = d.const_app(logic.or_inl, &[qpos, ppos, hq]);
        d.lam_fv(hq_fv, qpos, body)
    };
    d.const_app(logic.or_elim, &[ppos, qpos, target, h, minor1, minor2])
}

/// `Or (Le a b) (Lt b a)`, by the same double induction as `Nat.le_total`
/// (`order.rs`): induct on `a`, generalizing over `b`; the right branch is
/// strengthened from `Le b a` to the strict `Lt b a`, which is available
/// uniformly at the successor step (`zero_lt_succ`, then `le_succ_succ`
/// lifting the inner induction hypothesis).
fn le_or_gt(d: &mut NatDev<'_>, p: &NatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let logic = p.logic;
    let total = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
        let xy = d.le(x, y);
        let yx = d.lt(y, x);
        d.const_app(logic.or, &[xy, yx])
    };
    let motive_a = |d: &mut NatDev<'_>, x: ExprId| {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let body = total(d, x, y);
        d.pi_fv(y_fv, nat, body)
    };
    let all_from_zero = |d: &mut NatDev<'_>| {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let zero = d.zero();
        let left = d.le(zero, y);
        let right = d.lt(y, zero);
        let bound = d.lemma(p.zero_le, &[y]);
        let body = d.const_app(logic.or_inl, &[left, right, bound]);
        d.lam_fv(y_fv, nat, body)
    };
    let step_a = |d: &mut NatDev<'_>, x: ExprId, ih: ExprId| {
        let sx = d.succ(x);
        let motive_b = |d: &mut NatDev<'_>, y: ExprId| total(d, sx, y);
        let at_zero = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let left = d.le(sx, zero);
            let right = d.lt(zero, sx);
            let bound = d.zero_lt_succ(x);
            d.const_app(logic.or_inr, &[left, right, bound])
        };
        let step_b = |d: &mut NatDev<'_>, y: ExprId, _inner_ih: ExprId| {
            let sy = d.succ(y);
            let xy = d.le(x, y);
            let yx = d.lt(y, x);
            let old_total = d.apply(ih, &[y]);
            let sxy = d.le(sx, sy);
            let syx = d.lt(sy, sx);
            let target = d.const_app(logic.or, &[sxy, syx]);
            let old_total_ty = d.const_app(logic.or, &[xy, yx]);
            let motive = d
                .kernel()
                .lam(anon, old_total_ty, target, BinderInfo::Default);
            let left_minor = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let lifted = d.lemma(p.le_succ_succ, &[x, y, h]);
                let body = d.const_app(logic.or_inl, &[sxy, syx, lifted]);
                d.lam_fv(h_fv, xy, body)
            };
            let right_minor = {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                // h : Lt y x, defeq to Le (succ y) x = Le sy x.
                let lifted = d.lemma(p.le_succ_succ, &[sy, x, h]);
                let body = d.const_app(logic.or_inr, &[sxy, syx, lifted]);
                d.lam_fv(h_fv, yx, body)
            };
            d.const_app(
                logic.or_rec,
                &[xy, yx, motive, left_minor, right_minor, old_total],
            )
        };
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let body = d.induct(&motive_b, &at_zero, &step_b, y);
        d.lam_fv(y_fv, nat, body)
    };
    let all_b = d.induct(&motive_a, &all_from_zero, &step_a, a);
    d.apply(all_b, &[b])
}

pub(super) fn declare_order_more(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    // lt_of_not_le : ∀ a b, Not (Le a b) → Lt b a
    d.theorem(p.lt_of_not_le, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let le_ab = d.le(a, b);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let not_le_ty = d.arrow(le_ab, false_ty);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let lt_ba = d.lt(b, a);
        let tri = le_or_gt(d, &p, a, b); // Or (Le a b) (Lt b a)
        let body = d.const_app(p.logic.or_resolve_left, &[le_ab, lt_ba, tri, h]);
        let stmt = d.arrow(not_le_ty, lt_ba);
        let proof = d.lam_fv(h_fv, not_le_ty, body);
        (stmt, proof)
    })?;

    // lt_or_ge : ∀ a b, Or (Lt a b) (Le b a)   (`a ≥ b` unfolds to `Le b a`)
    d.theorem(p.lt_or_ge, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let lt_ab = d.lt(a, b);
        let le_ba = d.le(b, a);
        let swapped = le_or_gt(d, &p, b, a); // Or (Le b a) (Lt a b)
        let proof = or_swap(d, &p, le_ba, lt_ab, swapped); // Or (Lt a b) (Le b a)
        let stmt = d.const_app(p.logic.or, &[lt_ab, le_ba]);
        (stmt, proof)
    })?;

    // le_of_lt_add_one : ∀ a b, Lt a (add b (succ zero)) → Le a b
    linarith::declare(d, &p, p.le_of_lt_add_one, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let one = d.num(1);
        let b1 = d.add(b, one);
        let hyp = d.lt(a, b1);
        (vec![hyp], d.le(a, b))
    })?;

    // zero_lt_of_ne_zero : ∀ n, Not (Eq Nat n zero) → Lt zero n
    // A case split (not real recursion) on `n`: at zero the hypothesis
    // refutes `Eq.refl zero` directly (ex falso); at `succ j` the conclusion
    // is `zero_lt_succ j`, independent of the hypothesis.
    d.theorem(p.zero_lt_of_ne_zero, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let zero = d.zero();
            let eqn = d.eq(x, zero);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let ne = d.arrow(eqn, false_ty);
            let lt_zero_x = d.lt(zero, x);
            d.arrow(ne, lt_zero_x)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                let eqn_ty = d.eq(zero, zero);
                let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                let ne_ty = d.arrow(eqn_ty, false_ty);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let refl_zero = d.refl(zero);
                let absurd = d.apply(h, &[refl_zero]);
                let target = d.lt(zero, zero);
                let body = ex_falso(d, &p, target, absurd);
                d.lam_fv(h_fv, ne_ty, body)
            },
            &|d, j, _ih| {
                let sj = d.succ(j);
                let zero = d.zero();
                let eqn_ty = d.eq(sj, zero);
                let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                let ne_ty = d.arrow(eqn_ty, false_ty);
                let h_fv = d.fresh_fvar();
                let body = d.zero_lt_succ(j);
                d.lam_fv(h_fv, ne_ty, body)
            },
            n,
        );
        (stmt, proof)
    })?;

    // ne_of_beq_eq_false : ∀ a b, beq a b = false → Not (Eq Nat a b)
    // Assume a = b; then `beq_eq_true_of_eq` gives `beq a b = true`, which
    // together with the hypothesis `beq a b = false` yields
    // `Bool.false = Bool.true` (via `bool_symm`/`bool_trans`), discharged by
    // the existing `false_true_elim` discriminator. No `Bool.noConfusion`
    // needed.
    d.theorem(p.ne_of_beq_eq_false, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let beq_ab = d.beq(a, b);
        let false_b = d.bool_false();
        let true_b = d.bool_true();
        let hyp1_ty = d.bool_eq(beq_ab, false_b);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let eq_ab_ty = d.eq(a, b);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let h3 = d.lemma(p.beq_eq_true_of_eq, &[a, b, h2]); // beq a b = true
        let flipped_h1 = d.bool_symm(beq_ab, false_b, h1); // false = beq a b
        let contradiction_eq = d.bool_trans(false_b, beq_ab, true_b, flipped_h1, h3); // false = true
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let absurd = d.false_true_elim(false_ty, contradiction_eq);
        let not_eq_ty = d.arrow(eq_ab_ty, false_ty);
        let inner = d.lam_fv(h2_fv, eq_ab_ty, absurd);
        let stmt = d.arrow(hyp1_ty, not_eq_ty);
        let proof = d.lam_fv(h1_fv, hyp1_ty, inner);
        (stmt, proof)
    })?;

    Ok(())
}
