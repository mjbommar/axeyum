//! Additional order/pred/sub lemmas, under their exact Lean-core flat names.
//!
//! These close out `F:nat-order-lemma-census`'s twenty-name list: the
//! imported corpus's type closure resolves proofs against Lean-core's own
//! `Nat.*` names, and several of ours differ (a constructor `Nat.le.refl`
//! vs. the flat theorem `Nat.le_refl`, or a differently spelled theorem like
//! `le_succ_succ` vs. `succ_le_succ`). Each lemma here is proved
//! independently against [`declare_order`](super::order::declare_order)'s
//! definitions rather than aliased, since a `theorem` in this kernel is a
//! [`Declaration::Theorem`](crate::env::Declaration::Theorem) bound to
//! exactly one checked proof term.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::linarith::nat as linarith;

pub(super) fn declare_order_extra(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    // le_refl_thm : ∀ n, Le n n  (Nat.le_refl, the flat name for the
    // Nat.le.refl constructor `le_refl`).
    linarith::declare(d, &p, p.le_refl_thm, 1, &|d, v| {
        let n = v[0];
        (vec![], d.le(n, n))
    })?;

    // le_succ : ∀ n, Le n (succ n)
    linarith::declare(d, &p, p.le_succ, 1, &|d, v| {
        let n = v[0];
        let sn = d.succ(n);
        (vec![], d.le(n, sn))
    })?;

    // succ_le_succ : ∀ n m, Le n m → Le (succ n) (succ m)  (Nat.succ_le_succ,
    // the Lean-core name for `le_succ_succ`).
    linarith::declare(d, &p, p.succ_le_succ, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let hyp = d.le(n, m);
        let sn = d.succ(n);
        let sm = d.succ(m);
        (vec![hyp], d.le(sn, sm))
    })?;

    // le_of_lt_succ : ∀ n m, Lt n (succ m) → Le n m
    linarith::declare(d, &p, p.le_of_lt_succ, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let sm = d.succ(m);
        let hyp = d.lt(n, sm);
        (vec![hyp], d.le(n, m))
    })?;

    // lt_succ_self : ∀ n, Lt n (succ n)
    linarith::declare(d, &p, p.lt_succ_self, 1, &|d, v| {
        let n = v[0];
        let sn = d.succ(n);
        (vec![], d.lt(n, sn))
    })?;

    // lt_succ_of_le : ∀ n m, Le n m → Lt n (succ m)
    linarith::declare(d, &p, p.lt_succ_of_le, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let hyp = d.le(n, m);
        let sm = d.succ(m);
        (vec![hyp], d.lt(n, sm))
    })?;

    // lt_add_one : ∀ n, Lt n (add n (succ zero))
    linarith::declare(d, &p, p.lt_add_one, 1, &|d, v| {
        let n = v[0];
        let one = d.num(1);
        let sum = d.add(n, one);
        (vec![], d.lt(n, sum))
    })?;

    // not_succ_le_self : ∀ n, Not (Le (succ n) n)
    // `Lt n n` unfolds to exactly `Le (succ n) n`, so `lt_irrefl` applies as-is.
    d.theorem(p.not_succ_le_self, 1, &|d, v| {
        let n = v[0];
        let sn = d.succ(n);
        let hyp_ty = d.le(sn, n);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let proof = d.lemma(p.lt_irrefl, &[n]);
        let stmt = d.arrow(hyp_ty, false_ty);
        (stmt, proof)
    })?;

    // le_succ_of_le : ∀ n m, Le n m → Le n (succ m)  (the Lean-core flat name
    // for what the `le_step` constructor gives directly).
    linarith::declare(d, &p, p.le_succ_of_le, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let hyp = d.le(n, m);
        let sm = d.succ(m);
        (vec![hyp], d.le(n, sm))
    })?;

    // zero_lt_succ : ∀ n, Lt zero (succ n)
    linarith::declare(d, &p, p.zero_lt_succ, 1, &|d, v| {
        let n = v[0];
        let zero = d.zero();
        let sn = d.succ(n);
        (vec![], d.lt(zero, sn))
    })?;

    // pred_le : ∀ n, Le (pred n) n
    d.theorem(p.pred_le, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let px = d.pred(x);
            d.le(px, x)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                d.const_app(p.le_refl, &[zero])
            },
            &|d, j, _ih| {
                let refl_j = d.const_app(p.le_refl, &[j]);
                d.const_app(p.le_step, &[j, j, refl_j])
            },
            n,
        );
        (stmt, proof)
    })?;

    // pred_le_pred : ∀ n m, Le n m → Le (pred n) (pred m)
    // Induction on the derivation (`m` as the recursor's index), reusing
    // `pred_le` in the step case exactly as `le_of_succ_le_succ` reuses
    // `le_trans`.
    d.theorem(p.pred_le_pred, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let nat = d.nat_ty();
        let anon = d.anon_name();
        let pn = d.pred(n);
        let hyp_ty = d.le(n, m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // motive := fun (x : Nat) (_ : Le n x) => Le (pred n) (pred x)
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let px = d.pred(x);
            let body = d.le(pn, px);
            let dom = d.le(n, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.const_app(p.le_refl, &[pn]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(n, x);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let px = d.pred(x);
            let ih_ty = d.le(pn, px);
            let pred_le_x = d.lemma(p.pred_le, &[x]);
            let body = d.lemma(p.le_trans, &[pn, px, x, ih, pred_le_x]);
            let l_ih = d.lam_fv(ih_fv, ih_ty, body);
            let l_hx = d.lam_fv(hx_fv, hx_ty, l_ih);
            d.lam_fv(x_fv, nat, l_hx)
        };
        let proof = d.const_app(p.le_rec, &[n, motive, minor_refl, minor_step, m, h]);
        let pm = d.pred(m);
        let concl = d.le(pn, pm);
        let stmt = d.arrow(hyp_ty, concl);
        let value = d.lam_fv(h_fv, hyp_ty, proof);
        (stmt, value)
    })?;

    // sub_le : ∀ n m, Le (sub n m) n
    d.theorem(p.sub_le, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let sub_nx = d.sub(n, x);
            d.le(sub_nx, n)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| d.const_app(p.le_refl, &[n]),
            &|d, j, ih| {
                let sub_nj = d.sub(n, j);
                let pred_sub_nj = d.pred(sub_nj);
                let pred_le_step = d.lemma(p.pred_le, &[sub_nj]);
                d.lemma(p.le_trans, &[pred_sub_nj, sub_nj, n, pred_le_step, ih])
            },
            m,
        );
        (stmt, proof)
    })?;

    // succ_sub_succ_eq_sub : ∀ n m, sub (succ n) (succ m) = sub n m
    // (Lean-core name for `succ_sub_succ`; a thin restatement under a
    // second name a Lean-core-style reader would search for, not a second
    // proof: reuses `succ_sub_succ`'s own proof term directly rather than
    // re-deriving it by induction, so there is exactly one proof of this
    // fact for the kernel to keep sound. shape_search's `--duplicates`
    // still reports the pair, because it compares admitted *types*, not
    // proof terms.)
    d.theorem(p.succ_sub_succ_eq_sub, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let sn = d.succ(n);
        let sm = d.succ(m);
        let lhs = d.sub(sn, sm);
        let rhs = d.sub(n, m);
        let stmt = d.eq(lhs, rhs);
        let proof = d.lemma(p.succ_sub_succ, &[n, m]);
        (stmt, proof)
    })?;

    // sub_lt : ∀ n m, Lt zero n → Lt zero m → Lt (sub n m) n
    //
    // Case-split (not full induction) on both `n` and `m`. The boundary
    // cases (`n = 0`, or `n = succ n'` with `m = 0`) are eliminated by the
    // standard `Lt zero zero` contradiction (`not_succ_le_zero`); the live
    // case `n = succ n'`, `m = succ m'` rewrites `sub (succ n') (succ m')`
    // to `sub n' m'` via `succ_sub_succ`, then closes with `sub_le` lifted
    // through `le_succ_succ`. Neither positivity hypothesis's *value* is
    // needed in the live case — only their presence, to make the two
    // impossible cases dischargeable — so the proof is not shaped like
    // Lean's own (which threads them further); it establishes the same
    // statement from our own definitions.
    d.theorem(p.sub_lt, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let nat = d.nat_ty();
        let anon = d.anon_name();
        let zero = d.zero();
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);

        let inner_stmt = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
            let pos_x = d.lt(zero, x);
            let pos_y = d.lt(zero, y);
            let sub_xy = d.sub(x, y);
            let concl = d.lt(sub_xy, x);
            let with_pos_y = d.arrow(pos_y, concl);
            d.arrow(pos_x, with_pos_y)
        };

        // motive_n(x) := ∀ y, Lt 0 x → Lt 0 y → Lt (sub x y) x
        let motive_n = |d: &mut NatDev<'_>, x: ExprId| {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = inner_stmt(d, x, y);
            d.pi_fv(y_fv, nat, body)
        };

        let base_n = |d: &mut NatDev<'_>| {
            // ∀ y, Lt 0 0 → Lt 0 y → Lt (sub 0 y) 0
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let pos_zero = d.lt(zero, zero);
            let h1_fv = d.fresh_fvar();
            let h1 = d.kernel().fvar(h1_fv);
            let pos_y = d.lt(zero, y);
            let h2_fv = d.fresh_fvar();
            let sub_0y = d.sub(zero, y);
            let target = d.lt(sub_0y, zero);
            let impossible = d.lemma(p.not_succ_le_zero, &[zero, h1]);
            let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
            let level_zero = d.kernel().level_zero();
            let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
            let body = d.apply(rec, &[motive, impossible]);
            let with_h2 = d.lam_fv(h2_fv, pos_y, body);
            let with_h1 = d.lam_fv(h1_fv, pos_zero, with_h2);
            d.lam_fv(y_fv, nat, with_h1)
        };

        let step_n = |d: &mut NatDev<'_>, np: ExprId, _ih_n: ExprId| {
            let snp = d.succ(np);
            let pos_snp = d.lt(zero, snp);

            // motive_m(y) := Lt 0 y → Lt (sub (succ np) y) (succ np)
            let motive_m = |d: &mut NatDev<'_>, y: ExprId| {
                let pos_y = d.lt(zero, y);
                let sub_val = d.sub(snp, y);
                let concl = d.lt(sub_val, snp);
                d.arrow(pos_y, concl)
            };

            let base_m = |d: &mut NatDev<'_>| {
                // Lt 0 0 → Lt (sub (succ np) 0) (succ np)
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let pos_zero = d.lt(zero, zero);
                let sub_val = d.sub(snp, zero);
                let target = d.lt(sub_val, snp);
                let impossible = d.lemma(p.not_succ_le_zero, &[zero, h2]);
                let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
                let level_zero = d.kernel().level_zero();
                let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                let body = d.apply(rec, &[motive, impossible]);
                d.lam_fv(h2_fv, pos_zero, body)
            };

            let step_m = |d: &mut NatDev<'_>, mp: ExprId, _ih_m: ExprId| {
                let smp = d.succ(mp);
                let h2_fv = d.fresh_fvar();
                let pos_smp = d.lt(zero, smp);
                // sub (succ np) (succ mp) = sub np mp
                let rewrite = d.lemma(p.succ_sub_succ, &[np, mp]);
                let sub_np_mp = d.sub(np, mp);
                let sub_snp_smp = d.sub(snp, smp);
                let rewrite_rev = d.symm(sub_snp_smp, sub_np_mp, rewrite);
                // Le (sub np mp) np, lifted to Lt (sub np mp) (succ np)
                let bounded = d.lemma(p.sub_le, &[np, mp]);
                let lifted = d.lemma(p.le_succ_succ, &[sub_np_mp, np, bounded]);
                // transport along `rewrite_rev : sub np mp = sub (succ np) (succ mp)`
                let transport_motive = d.eq_motive(sub_np_mp, &|d, value| d.lt(value, snp));
                let body = d.transport(
                    sub_np_mp,
                    transport_motive,
                    lifted,
                    sub_snp_smp,
                    rewrite_rev,
                );
                d.lam_fv(h2_fv, pos_smp, body)
            };

            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body_for_y = d.induct(&motive_m, &base_m, &step_m, y);
            let h1_fv = d.fresh_fvar();
            let with_h1 = d.lam_fv(h1_fv, pos_snp, body_for_y);
            d.lam_fv(y_fv, nat, with_h1)
        };

        let all_m = d.induct(&motive_n, &base_n, &step_n, n);
        let proof = d.apply(all_m, &[m]);
        let stmt = inner_stmt(d, n, m);
        (stmt, proof)
    })?;

    Ok(())
}
