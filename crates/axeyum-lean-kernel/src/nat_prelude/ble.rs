//! Boolean `≤` (`Nat.ble`) and the checked bridge to the `Prop`-valued
//! `Nat.le` — the hardest cluster of `F:nat-order-lemma-census`'s twenty
//! names, left for last as the task instructions suggest.
//!
//! `Nat.ble` is the executable analogue of the already-declared `Nat.beq`
//! ([`declare_boolean_equality`](super::defs::declare_boolean_equality)): a
//! structural recursion on both arguments, by the same double-`Nat.rec`
//! construction, with `ble zero _ ≡ true`, `ble (succ _) zero ≡ false`, and
//! `ble (succ x) (succ y) ≡ ble x y`, all definitionally.

use super::NatPrelude;
use super::ops::{NatDev, NatOps, cases_lt_or_ge};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

pub(super) fn declare_boolean_le(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let bool_ty = d.bool_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let nat_to_bool = d.arrow(nat, bool_ty);
    let bool_motive = d.kernel().lam(anon, nat, bool_ty, BinderInfo::Default);

    // ble zero y ≡ true, for every y (unlike `beq`, no inner recursion on `y`
    // is needed: the zero row is the constant `true` function).
    let zero_minor = {
        let y_fv = d.fresh_fvar();
        let true_ = d.bool_true();
        d.lam_fv(y_fv, nat, true_)
    };

    // ble (succ x) y: false at zero; at succ y, recurse on x and y.
    let succ_minor = {
        let x_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let y_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let y = d.kernel().fvar(y_fv);
        let step = {
            let predecessor_fv = d.fresh_fvar();
            let predecessor = d.kernel().fvar(predecessor_fv);
            let unused_ih_fv = d.fresh_fvar();
            let body = d.apply(ih, &[predecessor]);
            let with_ih = d.lam_fv(unused_ih_fv, bool_ty, body);
            d.lam_fv(predecessor_fv, nat, with_ih)
        };
        let false_ = d.bool_false();
        let rec = d.kernel().const_(p.rec, vec![one]);
        let body = d.apply(rec, &[bool_motive, false_, step, y]);
        let with_y = d.lam_fv(y_fv, nat, body);
        let with_ih = d.lam_fv(ih_fv, nat_to_bool, with_y);
        d.lam_fv(x_fv, nat, with_ih)
    };

    let outer_motive = d.kernel().lam(anon, nat, nat_to_bool, BinderInfo::Default);
    let x_fv = d.fresh_fvar();
    let y_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y = d.kernel().fvar(y_fv);
    let rec = d.kernel().const_(p.rec, vec![one]);
    let row = d.apply(rec, &[outer_motive, zero_minor, succ_minor, x]);
    let body = d.apply(row, &[y]);
    let value = {
        let with_y = d.lam_fv(y_fv, nat, body);
        d.lam_fv(x_fv, nat, with_y)
    };
    let over_right = d.arrow(nat, bool_ty);
    let ty = d.arrow(nat, over_right);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.ble,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })?;

    // ble_self_eq_true : ∀ n, ble n n = true
    d.theorem(p.ble_self_eq_true, 1, &|d, v| {
        let value = v[0];
        let lhs = d.ble(value, value);
        let true_ = d.bool_true();
        let stmt = d.bool_eq(lhs, true_);
        let proof = d.induct(
            &|d, n| {
                let lhs = d.ble(n, n);
                let true_ = d.bool_true();
                d.bool_eq(lhs, true_)
            },
            &|d| {
                let true_ = d.bool_true();
                d.bool_refl(true_)
            },
            &|_d, _n, ih| ih,
            value,
        );
        (stmt, proof)
    })?;

    // ble_succ_eq_true : ∀ n m, ble n m = true → ble n (succ m) = true
    //
    // Induction on `n`, with `m` generalized. The base case (`n = 0`) is
    // trivial (`ble 0 _ ≡ true` regardless of the hypothesis); the step case
    // (`n = succ n'`) case-splits on `m`: `m = 0` makes the hypothesis
    // `false = true` (absurd, via `false_true_elim`), and `m = succ m'`
    // reduces (definitionally, on both sides) to the outer induction
    // hypothesis applied at `m'`.
    d.theorem(p.ble_succ_eq_true, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let nat = d.nat_ty();

        let hyp_concl = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
            let true_ = d.bool_true();
            let sy = d.succ(y);
            let hyp = {
                let lhs = d.ble(x, y);
                d.bool_eq(lhs, true_)
            };
            let concl = {
                let lhs = d.ble(x, sy);
                d.bool_eq(lhs, true_)
            };
            d.arrow(hyp, concl)
        };

        // motive_n(x) := ∀ y, ble x y = true → ble x (succ y) = true
        let motive_n = |d: &mut NatDev<'_>, x: ExprId| {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = hyp_concl(d, x, y);
            d.pi_fv(y_fv, nat, body)
        };

        let base_n = |d: &mut NatDev<'_>| {
            // ∀ y, ble 0 y = true → ble 0 (succ y) = true; the conclusion is
            // definitionally `true = true`, independent of the hypothesis.
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let zero = d.zero();
            let hyp_ty = {
                let lhs = d.ble(zero, y);
                let true_ = d.bool_true();
                d.bool_eq(lhs, true_)
            };
            let h_fv = d.fresh_fvar();
            let true_ = d.bool_true();
            let body = d.bool_refl(true_);
            let with_h = d.lam_fv(h_fv, hyp_ty, body);
            d.lam_fv(y_fv, nat, with_h)
        };

        let step_n = |d: &mut NatDev<'_>, np: ExprId, ih_n: ExprId| {
            let snp = d.succ(np);
            // motive_m(y) := ble (succ np) y = true → ble (succ np) (succ y) = true
            let motive_m = |d: &mut NatDev<'_>, y: ExprId| hyp_concl(d, snp, y);

            let base_m = |d: &mut NatDev<'_>| {
                // ble (succ np) 0 = true → ble (succ np) 1 = true, discharged
                // from the false premise `ble (succ np) 0 ≡ false`.
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let zero = d.zero();
                let hyp_ty = {
                    let lhs = d.ble(snp, zero);
                    let true_ = d.bool_true();
                    d.bool_eq(lhs, true_)
                };
                let szero = d.succ(zero);
                let target = {
                    let lhs = d.ble(snp, szero);
                    let true_ = d.bool_true();
                    d.bool_eq(lhs, true_)
                };
                let body = d.false_true_elim(target, h);
                d.lam_fv(h_fv, hyp_ty, body)
            };

            let step_m = |d: &mut NatDev<'_>, mp: ExprId, _ih_m: ExprId| {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let smp = d.succ(mp);
                let hyp_ty = {
                    let lhs = d.ble(snp, smp);
                    let true_ = d.bool_true();
                    d.bool_eq(lhs, true_)
                };
                // h : ble (succ np) (succ mp) = true, defeq to ble np mp = true;
                // ih_n mp h : ble np (succ mp) = true, defeq to the goal
                // ble (succ np) (succ (succ mp)) = true.
                let body = d.apply(ih_n, &[mp, h]);
                d.lam_fv(h_fv, hyp_ty, body)
            };

            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = d.induct(&motive_m, &base_m, &step_m, y);
            d.lam_fv(y_fv, nat, body)
        };

        let all_m = d.induct(&motive_n, &base_n, &step_n, n);
        let proof = d.apply(all_m, &[m]);
        let stmt = hyp_concl(d, n, m);
        (stmt, proof)
    })?;

    // ble_eq_true_of_le : ∀ n m, Le n m → ble n m = true
    // Induction on the derivation, mirroring `Nat.le`'s own two constructors:
    // `Le.refl` closes with `ble_self_eq_true`, `Le.step` with `ble_succ_eq_true`.
    d.theorem(p.ble_eq_true_of_le, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let nat = d.nat_ty();
        let anon = d.anon_name();
        let hyp_ty = d.le(n, m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let at_ty = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs = d.ble(n, x);
            let true_ = d.bool_true();
            d.bool_eq(lhs, true_)
        };
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(n, x);
            let body = at_ty(d, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.lemma(p.ble_self_eq_true, &[n]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(n, x);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let ih_ty = at_ty(d, x);
            let body = d.lemma(p.ble_succ_eq_true, &[n, x, ih]);
            let l_ih = d.lam_fv(ih_fv, ih_ty, body);
            let l_hx = d.lam_fv(hx_fv, hx_ty, l_ih);
            d.lam_fv(x_fv, nat, l_hx)
        };
        let body = d.const_app(p.le_rec, &[n, motive, minor_refl, minor_step, m, h]);
        let concl = at_ty(d, m);
        let stmt = d.arrow(hyp_ty, concl);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // le_of_ble_eq_true : ∀ n m, ble n m = true → Le n m
    //
    // The converse: induction on `n` with `m` generalized, building an
    // actual `Le` derivation. The base case is `zero_le`; the step case
    // case-splits on `m` exactly as `ble_succ_eq_true` does, discharging
    // `m = 0` as absurd and closing `m = succ m'` with `le_succ_succ` lifted
    // over the outer induction hypothesis.
    d.theorem(p.le_of_ble_eq_true, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let nat = d.nat_ty();

        let hyp_concl = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
            let lhs = d.ble(x, y);
            let true_ = d.bool_true();
            let hyp = d.bool_eq(lhs, true_);
            let concl = d.le(x, y);
            d.arrow(hyp, concl)
        };

        let motive_n = |d: &mut NatDev<'_>, x: ExprId| {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = hyp_concl(d, x, y);
            d.pi_fv(y_fv, nat, body)
        };

        let base_n = |d: &mut NatDev<'_>| {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let zero = d.zero();
            let hyp_ty = {
                let lhs = d.ble(zero, y);
                let true_ = d.bool_true();
                d.bool_eq(lhs, true_)
            };
            let h_fv = d.fresh_fvar();
            let body = d.lemma(p.zero_le, &[y]);
            let with_h = d.lam_fv(h_fv, hyp_ty, body);
            d.lam_fv(y_fv, nat, with_h)
        };

        let step_n = |d: &mut NatDev<'_>, np: ExprId, ih_n: ExprId| {
            let snp = d.succ(np);
            let motive_m = |d: &mut NatDev<'_>, y: ExprId| hyp_concl(d, snp, y);

            let base_m = |d: &mut NatDev<'_>| {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let zero = d.zero();
                let hyp_ty = {
                    let lhs = d.ble(snp, zero);
                    let true_ = d.bool_true();
                    d.bool_eq(lhs, true_)
                };
                let target = d.le(snp, zero);
                let body = d.false_true_elim(target, h);
                d.lam_fv(h_fv, hyp_ty, body)
            };

            let step_m = |d: &mut NatDev<'_>, mp: ExprId, _ih_m: ExprId| {
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let smp = d.succ(mp);
                let hyp_ty = {
                    let lhs = d.ble(snp, smp);
                    let true_ = d.bool_true();
                    d.bool_eq(lhs, true_)
                };
                let smaller = d.apply(ih_n, &[mp, h]);
                let body = d.lemma(p.le_succ_succ, &[np, mp, smaller]);
                d.lam_fv(h_fv, hyp_ty, body)
            };

            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = d.induct(&motive_m, &base_m, &step_m, y);
            d.lam_fv(y_fv, nat, body)
        };

        let all_m = d.induct(&motive_n, &base_n, &step_n, n);
        let proof = d.apply(all_m, &[m]);
        let stmt = hyp_concl(d, n, m);
        (stmt, proof)
    })?;

    // not_le_of_not_ble_eq_true : ∀ n m, Not (ble n m = true) → Not (Le n m)
    // The direct contrapositive of `ble_eq_true_of_le`.
    d.theorem(p.not_le_of_not_ble_eq_true, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let true_ = d.bool_true();
        let ble_nm = d.ble(n, m);
        let ble_eq_true = d.bool_eq(ble_nm, true_);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let not_ble = d.arrow(ble_eq_true, false_ty);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let le_nm = d.le(n, m);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let derived = d.lemma(p.ble_eq_true_of_le, &[n, m, h2]);
        let contradiction = d.apply(h1, &[derived]);
        let inner = d.lam_fv(h2_fv, le_nm, contradiction);
        let not_le = d.arrow(le_nm, false_ty);
        let stmt = d.arrow(not_ble, not_le);
        let proof = d.lam_fv(h1_fv, not_ble, inner);
        (stmt, proof)
    })?;

    // lt_of_ble_eq_false : ∀ n m, ble n m = false → Lt m n
    //
    // The false side of the bridge, in the STRICT form. `Nat` had
    // `le_of_ble_eq_true` and no false-side twin at all, and three consumers
    // worked around that separately (ADR-1558 §4, ADR-1562 §4). The strict
    // conclusion is the one the echelon searches need: `ble rows r = false` is
    // the only place a row index is known to be in range, and `Lt r rows` is
    // what a `MapsInto` hypothesis takes. Deriving `Le` first and strengthening
    // afterwards is not possible, so the split is `lt_or_ge` rather than
    // `le_total`: its left disjunct IS the conclusion, and its right disjunct
    // `Le n m` contradicts the hypothesis through `ble_eq_true_of_le`.
    d.theorem(p.lt_of_ble_eq_false, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let ble_nm = d.ble(n, m);
        let false_ = d.bool_false();
        let hyp_ty = d.bool_eq(ble_nm, false_);
        let concl = d.lt(m, n);

        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // `lt_or_ge m n : Or (Lt m n) (Le n m)`.
        let body = cases_lt_or_ge(
            d,
            &p,
            m,
            n,
            &|d, _| d.lt(m, n),
            &|_d, _, hlt| hlt,
            &|d, _, hle| {
                let htrue = d.lemma(p.ble_eq_true_of_le, &[n, m, hle]);
                let true_ = d.bool_true();
                let false_ = d.bool_false();
                let ble_nm = d.ble(n, m);
                let symm_h = d.bool_symm(ble_nm, false_, h);
                let false_eq_true = d.bool_trans(false_, ble_nm, true_, symm_h, htrue);
                let target = d.lt(m, n);
                d.false_true_elim(target, false_eq_true)
            },
        );

        let stmt = d.arrow(hyp_ty, concl);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    Ok(())
}
