//! The order relation `Nat.le` and everything proved about it.
//!
//! An indexed `Prop`-valued inductive with a kernel-generated recursor, plus
//! monotonicity, totality, and the well-founded strict order.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.le`, reducible strict order, and the checked order theorems.
pub(super) fn declare_order(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();

    // Le : Nat → Nat → Prop, with the first argument a PARAMETER and the second
    // an INDEX (Lean's own `Nat.le` has exactly this shape).
    let le_ty = {
        let inner = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
        d.kernel().pi(anon, nat, inner, BinderInfo::Default)
    };
    // Le.refl : Π (n : Nat), Le n n
    let refl_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.le(n, n);
        d.pi_fv(n_fv, nat, body)
    };
    // Le.step : Π (n m : Nat), Le n m → Le n (succ m)
    let step_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let hyp = d.le(n, m);
        let sm = d.succ(m);
        let concl = d.le(n, sm);
        let arrow = d.kernel().pi(anon, hyp, concl, BinderInfo::Default);
        let over_m = d.pi_fv(m_fv, nat, arrow);
        d.pi_fv(n_fv, nat, over_m)
    };
    d.kernel().add_inductive(
        p.le,
        &[],
        1,
        le_ty,
        &[(p.le_refl, refl_ty), (p.le_step, step_ty)],
    )?;

    // lt n m := Le (succ n) m
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let sn = d.succ(n);
        let body = d.le(sn, m);
        let value = {
            let inner = d.lam_fv(m_fv, nat, body);
            d.lam_fv(n_fv, nat, inner)
        };
        let ty = {
            let inner = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            d.kernel().pi(anon, nat, inner, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.lt,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // inClosedInterval lower upper value := Le lower value ∧ Le value upper
    {
        let lower_fv = d.fresh_fvar();
        let lower = d.kernel().fvar(lower_fv);
        let upper_fv = d.fresh_fvar();
        let upper = d.kernel().fvar(upper_fv);
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);
        let lower_bound = d.le(lower, value);
        let upper_bound = d.le(value, upper);
        let body = d.const_app(p.logic.and, &[lower_bound, upper_bound]);
        let definition = {
            let with_value = d.lam_fv(value_fv, nat, body);
            let with_upper = d.lam_fv(upper_fv, nat, with_value);
            d.lam_fv(lower_fv, nat, with_upper)
        };
        let ty = {
            let with_value = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            let with_upper = d.kernel().pi(anon, nat, with_value, BinderInfo::Default);
            d.kernel().pi(anon, nat, with_upper, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.in_closed_interval,
            uparams: vec![],
            ty,
            value: definition,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // zero_le : ∀ n, Le zero n   (induction on n, using only the constructors)
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let z = d.zero();
            d.le(z, x)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.const_app(p.le_refl, &[z])
            },
            &|d, j, ih| {
                let z = d.zero();
                d.const_app(p.le_step, &[z, j, ih])
            },
            n,
        );
        let ty = d.pi_fv(n_fv, nat, stmt);
        let value = d.lam_fv(n_fv, nat, proof);
        d.declare_theorem(p.zero_le, ty, value)?;
    }

    // le_succ_succ : ∀ n m, Le n m → Le (succ n) (succ m)
    // — induction on the DERIVATION, i.e. elimination with the generated Le.rec.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp = d.le(n, m);
        let sn = d.succ(n);
        let sm = d.succ(m);
        let concl = d.le(sn, sm);

        // motive := fun (x : Nat) (_ : Le n x) => Le (succ n) (succ x)
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let sx = d.succ(x);
            let body = d.le(sn, sx);
            let dom = d.le(n, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        // minor for Le.refl : motive n (Le.refl n) = Le (succ n) (succ n)
        let minor_refl = d.const_app(p.le_refl, &[sn]);
        // minor for Le.step : Π (x : Nat) (hx : Le n x), motive x hx → motive (succ x) …
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(n, x);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let sx = d.succ(x);
            let ih_ty = d.le(sn, sx);
            let body = d.const_app(p.le_step, &[sn, sx, ih]);
            let l_ih = d.lam_fv(ih_fv, ih_ty, body);
            let l_hx = d.lam_fv(hx_fv, hx_ty, l_ih);
            d.lam_fv(x_fv, nat, l_hx)
        };
        let applied = d.const_app(p.le_rec, &[n, motive, minor_refl, minor_step, m, h]);

        let ty = {
            let arrow = d.kernel().pi(anon, hyp, concl, BinderInfo::Default);
            let over_m = d.pi_fv(m_fv, nat, arrow);
            d.pi_fv(n_fv, nat, over_m)
        };
        let value = {
            let l_h = d.lam_fv(h_fv, hyp, applied);
            let l_m = d.lam_fv(m_fv, nat, l_h);
            d.lam_fv(n_fv, nat, l_m)
        };
        d.declare_theorem(p.le_succ_succ, ty, value)?;
    }

    // le_trans : ∀ a b c, Le a b → Le b c → Le a c
    // — elimination on the SECOND derivation, with `b` as the recursor's parameter.
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let h1_ty = d.le(a, b);
        let h2_ty = d.le(b, c);
        let concl = d.le(a, c);

        // motive := fun (x : Nat) (_ : Le b x) => Le a x
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let body = d.le(a, x);
            let dom = d.le(b, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        // refl case: motive b (Le.refl b) = Le a b, which is exactly `h1`.
        let minor_refl = h1;
        // step case: fun x hx ih => Le.step a x ih
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(b, x);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let ih_ty = d.le(a, x);
            let body = d.const_app(p.le_step, &[a, x, ih]);
            let l_ih = d.lam_fv(ih_fv, ih_ty, body);
            let l_hx = d.lam_fv(hx_fv, hx_ty, l_ih);
            d.lam_fv(x_fv, nat, l_hx)
        };
        let applied = d.const_app(p.le_rec, &[b, motive, minor_refl, minor_step, c, h2]);

        let ty = {
            let t = d.kernel().pi(anon, h2_ty, concl, BinderInfo::Default);
            let t = d.pi_fv(h1_fv, h1_ty, t);
            let t = d.pi_fv(c_fv, nat, t);
            let t = d.pi_fv(b_fv, nat, t);
            d.pi_fv(a_fv, nat, t)
        };
        let value = {
            let v = d.lam_fv(h2_fv, h2_ty, applied);
            let v = d.lam_fv(h1_fv, h1_ty, v);
            let v = d.lam_fv(c_fv, nat, v);
            let v = d.lam_fv(b_fv, nat, v);
            d.lam_fv(a_fv, nat, v)
        };
        d.declare_theorem(p.le_trans, ty, value)?;
    }

    // monotone_of_le_succ : adjacent monotonicity implies full monotonicity.
    // Eliminate the order derivation; each step chains the accumulated result
    // with the supplied adjacent-step proof.
    {
        let fn_ty = d.arrow(nat, nat);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let adjacent_fv = d.fresh_fvar();
        let adjacent = d.kernel().fvar(adjacent_fv);
        let adjacent_ty = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let fn_n = d.kernel().app(f, n);
            let sn = d.succ(n);
            let fn_sn = d.kernel().app(f, sn);
            let body = d.le(fn_n, fn_sn);
            d.pi_fv(n_fv, nat, body)
        };
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let h_ty = d.le(a, b);
        let fa = d.kernel().app(f, a);
        let fb = d.kernel().app(f, b);
        let conclusion = d.le(fa, fb);
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_ty = d.le(a, x);
            let fx = d.kernel().app(f, x);
            let body = d.le(fa, fx);
            let inner = d.kernel().lam(anon, hx_ty, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.const_app(p.le_refl, &[fa]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(a, x);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let fx = d.kernel().app(f, x);
            let sx = d.succ(x);
            let fsx = d.kernel().app(f, sx);
            let ih_ty = d.le(fa, fx);
            let adjacent_x = d.kernel().app(adjacent, x);
            let body = d.const_app(p.le_trans, &[fa, fx, fsx, ih, adjacent_x]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let proof = d.const_app(p.le_rec, &[a, motive, minor_refl, minor_step, b, h]);
        let ty = {
            let out = d.kernel().pi(anon, h_ty, conclusion, BinderInfo::Default);
            let out = d.pi_fv(b_fv, nat, out);
            let out = d.pi_fv(a_fv, nat, out);
            let out = d.pi_fv(adjacent_fv, adjacent_ty, out);
            d.pi_fv(f_fv, fn_ty, out)
        };
        let value = {
            let out = d.lam_fv(h_fv, h_ty, proof);
            let out = d.lam_fv(b_fv, nat, out);
            let out = d.lam_fv(a_fv, nat, out);
            let out = d.lam_fv(adjacent_fv, adjacent_ty, out);
            d.lam_fv(f_fv, fn_ty, out)
        };
        d.declare_theorem(p.monotone_of_le_succ, ty, value)?;
    }

    // le_of_succ_le_succ : ∀ n m, Le (succ n) (succ m) → Le n m
    //
    // Eliminate the derivation with the predecessor-style family
    //   P 0        = False
    //   P (succ x) = Le n x.
    // The step case can ignore its induction hypothesis: from
    // `Le (succ n) x`, transitivity with `Le n (succ n)` gives `Le n x`.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let sn = d.succ(n);
        let sm = d.succ(m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp = d.le(sn, sm);
        let concl = d.le(n, m);

        let predecessor_family = |d: &mut NatDev<'_>, x: ExprId| {
            let type_motive = d.kernel().lam(anon, nat, prop, BinderInfo::Default);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let step = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let ignored_fv = d.fresh_fvar();
                let body = d.le(n, j);
                let inner = d.lam_fv(ignored_fv, prop, body);
                d.lam_fv(j_fv, nat, inner)
            };
            let one = d.level_one();
            let rec = d.kernel().const_(p.rec, vec![one]);
            d.apply(rec, &[type_motive, false_ty, step, x])
        };

        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(sn, x);
            let body = predecessor_family(d, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.const_app(p.le_refl, &[n]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(sn, x);
            let hx = d.kernel().fvar(hx_fv);
            let ih_fv = d.fresh_fvar();
            let ih_ty = predecessor_family(d, x);
            let n_refl = d.const_app(p.le_refl, &[n]);
            let n_le_sn = d.const_app(p.le_step, &[n, n, n_refl]);
            let body = d.lemma(p.le_trans, &[n, sn, x, n_le_sn, hx]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let proof = d.const_app(p.le_rec, &[sn, motive, minor_refl, minor_step, sm, h]);
        let ty = {
            let arrow = d.kernel().pi(anon, hyp, concl, BinderInfo::Default);
            let over_m = d.pi_fv(m_fv, nat, arrow);
            d.pi_fv(n_fv, nat, over_m)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, hyp, proof);
            let with_m = d.lam_fv(m_fv, nat, with_h);
            d.lam_fv(n_fv, nat, with_m)
        };
        d.declare_theorem(p.le_of_succ_le_succ, ty, value)?;
    }

    // le_add_right : ∀ n k, Le n (add n k)   (induction on k; both cases are
    // definitional, since `add n zero ≡ n` and `add n (succ j) ≡ succ (add n j)`)
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let nx = d.add(n, x);
            d.le(n, nx)
        };
        let stmt = motive(d, k);
        let proof = d.induct(
            &motive,
            &|d| d.const_app(p.le_refl, &[n]),
            &|d, j, ih| {
                let nj = d.add(n, j);
                d.const_app(p.le_step, &[n, nj, ih])
            },
            k,
        );
        let ty = {
            let t = d.pi_fv(k_fv, nat, stmt);
            d.pi_fv(n_fv, nat, t)
        };
        let value = {
            let v = d.lam_fv(k_fv, nat, proof);
            d.lam_fv(n_fv, nat, v)
        };
        d.declare_theorem(p.le_add_right, ty, value)?;
    }

    // lt_or_eq_of_le : ∀ a b, Le a b → Or (Lt a b) (Eq Nat a b)
    // Elimination on the order derivation: reflexivity gives equality, while
    // every step lifts the prior bound to a strict successor bound.
    d.theorem(p.lt_or_eq_of_le, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let hyp_ty = d.le(a, b);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let result = |d: &mut NatDev<'_>, x: ExprId| {
            let strict = d.lt(a, x);
            let equal = d.eq(a, x);
            d.const_app(p.logic.or, &[strict, equal])
        };
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(a, x);
            let body = result(d, x);
            let with_hx = d.lam_fv(hx_fv, hx_ty, body);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let minor_refl = {
            let strict = d.lt(a, a);
            let equal = d.eq(a, a);
            let refl = d.refl(a);
            d.const_app(p.logic.or_inr, &[strict, equal, refl])
        };
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv);
            let hx_ty = d.le(a, x);
            let ih_fv = d.fresh_fvar();
            let ih_ty = result(d, x);
            let sx = d.succ(x);
            let strict = d.lt(a, sx);
            let equal = d.eq(a, sx);
            let lifted = d.lemma(p.le_succ_succ, &[a, x, hx]);
            let body = d.const_app(p.logic.or_inl, &[strict, equal, lifted]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let body = d.const_app(p.le_rec, &[a, motive, minor_refl, minor_step, b, hyp]);
        let conclusion = result(d, b);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(hyp_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // lt_of_lt_of_le : ∀ a b c, Lt a b → Le b c → Lt a c
    d.theorem(p.lt_of_lt_of_le, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let strict_ty = d.lt(a, b);
        let strict_fv = d.fresh_fvar();
        let strict = d.kernel().fvar(strict_fv);
        let bound_ty = d.le(b, c);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let sa = d.succ(a);
        let body = d.lemma(p.le_trans, &[sa, b, c, strict, bound]);
        let conclusion = d.lt(a, c);
        let stmt = {
            let with_bound = d.arrow(bound_ty, conclusion);
            d.arrow(strict_ty, with_bound)
        };
        let proof = {
            let with_bound = d.lam_fv(bound_fv, bound_ty, body);
            d.lam_fv(strict_fv, strict_ty, with_bound)
        };
        (stmt, proof)
    })?;

    // lt_of_le_of_lt : ∀ a b c, Le a b → Lt b c → Lt a c
    d.theorem(p.lt_of_le_of_lt, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let bound_ty = d.le(a, b);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let strict_ty = d.lt(b, c);
        let strict_fv = d.fresh_fvar();
        let strict = d.kernel().fvar(strict_fv);
        let sa = d.succ(a);
        let sb = d.succ(b);
        let lifted = d.lemma(p.le_succ_succ, &[a, b, bound]);
        let body = d.lemma(p.le_trans, &[sa, sb, c, lifted, strict]);
        let conclusion = d.lt(a, c);
        let stmt = {
            let with_strict = d.arrow(strict_ty, conclusion);
            d.arrow(bound_ty, with_strict)
        };
        let proof = {
            let with_strict = d.lam_fv(strict_fv, strict_ty, body);
            d.lam_fv(bound_fv, bound_ty, with_strict)
        };
        (stmt, proof)
    })?;

    // le_total : ∀ a b, Or (Le a b) (Le b a)
    // Structural induction on both naturals; the successor/successor branch
    // maps the smaller comparison through `le_succ_succ`.
    d.theorem(p.le_total, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let logic = p.logic;
        let total = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
            let xy = d.le(x, y);
            let yx = d.le(y, x);
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
            let right = d.le(y, zero);
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
                let right = d.le(zero, sx);
                let bound = d.lemma(p.zero_le, &[sx]);
                d.const_app(logic.or_inr, &[left, right, bound])
            };
            let step_b = |d: &mut NatDev<'_>, y: ExprId, _inner_ih: ExprId| {
                let sy = d.succ(y);
                let xy = d.le(x, y);
                let yx = d.le(y, x);
                let old_total = d.apply(ih, &[y]);
                let sxy = d.le(sx, sy);
                let syx = d.le(sy, sx);
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
                    let lifted = d.lemma(p.le_succ_succ, &[y, x, h]);
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
        let proof = d.apply(all_b, &[b]);
        (total(d, a, b), proof)
    })?;

    // not_succ_le_zero : ∀ n, Not (Le (succ n) zero)
    // Eliminate a hypothetical derivation into a family that is `False` only
    // at index zero and `True` at every successor index.
    d.theorem(p.not_succ_le_zero, 1, &|d, v| {
        let n = v[0];
        let sn = d.succ(n);
        let zero = d.zero();
        let hyp_ty = d.le(sn, zero);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let true_ty = d.kernel().const_(p.logic.true_, vec![]);
        let family = |d: &mut NatDev<'_>, x: ExprId| {
            let motive = d.kernel().lam(anon, nat, prop, BinderInfo::Default);
            let step = {
                let j_fv = d.fresh_fvar();
                let ih_fv = d.fresh_fvar();
                let body = true_ty;
                let with_ih = d.lam_fv(ih_fv, prop, body);
                d.lam_fv(j_fv, nat, with_ih)
            };
            let one = d.level_one();
            let rec = d.kernel().const_(p.rec, vec![one]);
            d.apply(rec, &[motive, false_ty, step, x])
        };
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(sn, x);
            let body = family(d, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.kernel().const_(p.logic.true_intro, vec![]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(sn, x);
            let ih_fv = d.fresh_fvar();
            let ih_ty = family(d, x);
            let body = d.kernel().const_(p.logic.true_intro, vec![]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let body = d.const_app(p.le_rec, &[sn, motive, minor_refl, minor_step, zero, h]);
        let stmt = d.arrow(hyp_ty, false_ty);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // lt_irrefl : ∀ n, Not (Lt n n)
    d.theorem(p.lt_irrefl, 1, &|d, v| {
        let n = v[0];
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let strict = d.lt(x, x);
            d.arrow(strict, false_ty)
        };
        let base = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let strict = d.lt(zero, zero);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = d.lemma(p.not_succ_le_zero, &[zero, h]);
            d.lam_fv(h_fv, strict, body)
        };
        let step = |d: &mut NatDev<'_>, x: ExprId, ih: ExprId| {
            let sx = d.succ(x);
            let strict = d.lt(sx, sx);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let reduced = d.lemma(p.le_of_succ_le_succ, &[sx, x, h]);
            let body = d.apply(ih, &[reduced]);
            d.lam_fv(h_fv, strict, body)
        };
        let body = d.induct(&motive, &base, &step, n);
        (motive(d, n), body)
    })?;

    // le_antisymm : ∀ a b, Le a b → Le b a → Eq a b
    // Induct over both endpoints. Mixed zero/successor branches eliminate the
    // impossible bound; the successor/successor branch inverts both bounds
    // and lifts the induction hypothesis through `succ`.
    d.theorem(p.le_antisymm, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let antisymm_at = |d: &mut NatDev<'_>, x: ExprId| {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let xy = d.le(x, y);
            let yx = d.le(y, x);
            let equality = d.eq(x, y);
            let reverse = d.arrow(yx, equality);
            let body = d.arrow(xy, reverse);
            d.pi_fv(y_fv, nat, body)
        };
        let at_zero = |d: &mut NatDev<'_>| {
            let motive_y = |d: &mut NatDev<'_>, y: ExprId| {
                let zero = d.zero();
                let zy = d.le(zero, y);
                let yz = d.le(y, zero);
                let equality = d.eq(zero, y);
                let reverse = d.arrow(yz, equality);
                d.arrow(zy, reverse)
            };
            let y_zero = |d: &mut NatDev<'_>| {
                let zero = d.zero();
                let zz = d.le(zero, zero);
                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();
                let body = d.refl(zero);
                let with_h2 = d.lam_fv(h2_fv, zz, body);
                d.lam_fv(h1_fv, zz, with_h2)
            };
            let y_step = |d: &mut NatDev<'_>, y: ExprId, _ih: ExprId| {
                let zero = d.zero();
                let sy = d.succ(y);
                let zsy = d.le(zero, sy);
                let syz = d.le(sy, zero);
                let target = d.eq(zero, sy);
                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let impossible = d.lemma(p.not_succ_le_zero, &[y, h2]);
                let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
                let level_zero = d.kernel().level_zero();
                let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                let body = d.apply(rec, &[motive, impossible]);
                let with_h2 = d.lam_fv(h2_fv, syz, body);
                d.lam_fv(h1_fv, zsy, with_h2)
            };
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = d.induct(&motive_y, &y_zero, &y_step, y);
            d.lam_fv(y_fv, nat, body)
        };
        let step_a = |d: &mut NatDev<'_>, x: ExprId, ih: ExprId| {
            let sx = d.succ(x);
            let motive_y = |d: &mut NatDev<'_>, y: ExprId| {
                let sxy = d.le(sx, y);
                let ysx = d.le(y, sx);
                let equality = d.eq(sx, y);
                let reverse = d.arrow(ysx, equality);
                d.arrow(sxy, reverse)
            };
            let y_zero = |d: &mut NatDev<'_>| {
                let zero = d.zero();
                let sxz = d.le(sx, zero);
                let zsx = d.le(zero, sx);
                let target = d.eq(sx, zero);
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);
                let h2_fv = d.fresh_fvar();
                let impossible = d.lemma(p.not_succ_le_zero, &[x, h1]);
                let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
                let level_zero = d.kernel().level_zero();
                let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                let body = d.apply(rec, &[motive, impossible]);
                let with_h2 = d.lam_fv(h2_fv, zsx, body);
                d.lam_fv(h1_fv, sxz, with_h2)
            };
            let y_step = |d: &mut NatDev<'_>, y: ExprId, _inner_ih: ExprId| {
                let sy = d.succ(y);
                let sxsy = d.le(sx, sy);
                let sysx = d.le(sy, sx);
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let xy = d.lemma(p.le_of_succ_le_succ, &[x, y, h1]);
                let yx = d.lemma(p.le_of_succ_le_succ, &[y, x, h2]);
                let smaller = d.apply(ih, &[y, xy, yx]);
                let body = d.congr(x, y, smaller, &|d, value| d.succ(value));
                let with_h2 = d.lam_fv(h2_fv, sysx, body);
                d.lam_fv(h1_fv, sxsy, with_h2)
            };
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = d.induct(&motive_y, &y_zero, &y_step, y);
            d.lam_fv(y_fv, nat, body)
        };
        let all_b = d.induct(&antisymm_at, &at_zero, &step_a, a);
        let proof = d.apply(all_b, &[b]);
        let ab = d.le(a, b);
        let ba = d.le(b, a);
        let conclusion = d.eq(a, b);
        let reverse = d.arrow(ba, conclusion);
        let stmt = d.arrow(ab, reverse);
        (stmt, proof)
    })?;

    // lt_well_founded : WellFounded Nat.lt
    // Ordinary Nat induction builds accessibility. At `succ n`, every
    // predecessor `m` satisfies `m ≤ n`; strict predecessors descend through
    // `Acc.inv`, while equality transports the induction hypothesis to `m`.
    let (lt_well_founded_ty, lt_well_founded_value) = {
        let one = d.level_one();
        let relation = d.kernel().const_(p.lt, vec![]);
        let acc_at = |d: &mut NatDev<'_>, value: ExprId| {
            let acc = d.kernel().const_(p.logic.acc, vec![one]);
            d.apply(acc, &[nat, relation, value])
        };
        let motive = |d: &mut NatDev<'_>, value: ExprId| acc_at(d, value);
        let base = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let predecessor_fv = d.fresh_fvar();
            let related_fv = d.fresh_fvar();
            let predecessor = d.kernel().fvar(predecessor_fv);
            let related = d.kernel().fvar(related_fv);
            let relation_ty = d.lt(predecessor, zero);
            let impossible = d.lemma(p.not_succ_le_zero, &[predecessor, related]);
            let target = acc_at(d, predecessor);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let false_motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
            let zero_level = d.kernel().level_zero();
            let false_rec = d.kernel().const_(p.logic.false_rec, vec![zero_level]);
            let body = d.apply(false_rec, &[false_motive, impossible]);
            let with_related = d.lam_fv(related_fv, relation_ty, body);
            let field = d.lam_fv(predecessor_fv, nat, with_related);
            let intro = d.kernel().const_(p.logic.acc_intro, vec![one]);
            d.apply(intro, &[nat, relation, zero, field])
        };
        let step = |d: &mut NatDev<'_>, n: ExprId, accessible_n: ExprId| {
            let sn = d.succ(n);
            let predecessor_fv = d.fresh_fvar();
            let related_fv = d.fresh_fvar();
            let predecessor = d.kernel().fvar(predecessor_fv);
            let related = d.kernel().fvar(related_fv);
            let relation_ty = d.lt(predecessor, sn);
            let predecessor_le_n = d.lemma(p.le_of_succ_le_succ, &[predecessor, n, related]);
            let split = d.lemma(p.lt_or_eq_of_le, &[predecessor, n, predecessor_le_n]);
            let strict_ty = d.lt(predecessor, n);
            let equal_ty = d.eq(predecessor, n);
            let target = acc_at(d, predecessor);
            let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
            let split_motive = d.kernel().lam(anon, split_ty, target, BinderInfo::Default);
            let strict_minor = {
                let strict_fv = d.fresh_fvar();
                let strict = d.kernel().fvar(strict_fv);
                let inverse = d.kernel().const_(p.logic.acc_inv, vec![one]);
                let body = d.apply(
                    inverse,
                    &[nat, relation, n, predecessor, accessible_n, strict],
                );
                d.lam_fv(strict_fv, strict_ty, body)
            };
            let equal_minor = {
                let equal_fv = d.fresh_fvar();
                let equal = d.kernel().fvar(equal_fv);
                let reverse = d.symm(predecessor, n, equal);
                let transport_motive = d.eq_motive(n, &|d, value| acc_at(d, value));
                let body = d.transport(n, transport_motive, accessible_n, predecessor, reverse);
                d.lam_fv(equal_fv, equal_ty, body)
            };
            let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
            let selected = d.apply(
                or_rec,
                &[
                    strict_ty,
                    equal_ty,
                    split_motive,
                    strict_minor,
                    equal_minor,
                    split,
                ],
            );
            let with_related = d.lam_fv(related_fv, relation_ty, selected);
            let field = d.lam_fv(predecessor_fv, nat, with_related);
            let intro = d.kernel().const_(p.logic.acc_intro, vec![one]);
            d.apply(intro, &[nat, relation, sn, field])
        };
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);
        let accessible = d.induct(&motive, &base, &step, value);
        let proof = d.lam_fv(value_fv, nat, accessible);
        let well_founded = d.kernel().const_(p.logic.well_founded, vec![one]);
        let stmt = d.apply(well_founded, &[nat, relation]);
        (stmt, proof)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.lt_well_founded,
        uparams: vec![],
        ty: lt_well_founded_ty,
        value: lt_well_founded_value,
        hint: ReducibilityHint::Regular(6),
    })?;

    // le_intro : ∀ a b k, a+k=b → Le a b
    d.theorem(p.le_intro, 3, &|d, v| {
        let (a, b, k) = (v[0], v[1], v[2]);
        let sum = d.add(a, k);
        let hyp_ty = d.eq(sum, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let bound = d.lemma(p.le_add_right, &[a, k]);
        let motive = d.eq_motive(sum, &|d, x| d.le(a, x));
        let body = d.transport(sum, motive, bound, b, h);
        let conclusion = d.le(a, b);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // le_dest : ∀ a b, Le a b → Exists (fun k => a+k=b)
    d.theorem(p.le_dest, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let one = d.level_one();
        let exists_at = |d: &mut NatDev<'_>, x: ExprId| {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sum = d.add(a, k);
            let body = d.eq(sum, x);
            let pred = d.lam_fv(k_fv, nat, body);
            let exists = d.kernel().const_(p.logic.exists_, vec![one]);
            d.apply(exists, &[nat, pred])
        };
        let hyp_ty = d.le(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(a, x);
            let body = exists_at(d, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = {
            let zero = d.zero();
            let pred = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sum = d.add(a, k);
                let body = d.eq(sum, a);
                d.lam_fv(k_fv, nat, body)
            };
            let witness = d.refl(a);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            d.apply(intro, &[nat, pred, zero, witness])
        };
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(a, x);
            let ih_fv = d.fresh_fvar();
            let ih_ty = exists_at(d, x);
            let ih = d.kernel().fvar(ih_fv);
            let sx = d.succ(x);
            let target = exists_at(d, sx);
            let target_motive = d.kernel().lam(anon, ih_ty, target, BinderInfo::Default);
            let source_pred = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sum = d.add(a, k);
                let body = d.eq(sum, x);
                d.lam_fv(k_fv, nat, body)
            };
            let witness_minor = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sum = d.add(a, k);
                let e_fv = d.fresh_fvar();
                let e_ty = d.eq(sum, x);
                let e = d.kernel().fvar(e_fv);
                let sk = d.succ(k);
                let lifted = d.congr(sum, x, e, &|d, value| d.succ(value));
                let target_pred = {
                    let j_fv = d.fresh_fvar();
                    let j = d.kernel().fvar(j_fv);
                    let target_sum = d.add(a, j);
                    let body = d.eq(target_sum, sx);
                    d.lam_fv(j_fv, nat, body)
                };
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let body = d.apply(intro, &[nat, target_pred, sk, lifted]);
                let with_e = d.lam_fv(e_fv, e_ty, body);
                d.lam_fv(k_fv, nat, with_e)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(rec, &[nat, source_pred, target_motive, witness_minor, ih]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let body = d.const_app(p.le_rec, &[a, motive, minor_refl, minor_step, b, h]);
        let conclusion = exists_at(d, b);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // add_le_add_left : ∀ c a b, Le a b → Le (add c a) (add c b)
    // Eliminate the bound derivation; `add` recurses on exactly its index.
    d.theorem(p.add_le_add_left, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let hyp_ty = d.le(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ca = d.add(c, a);
        let cb = d.add(c, b);
        let conclusion = d.le(ca, cb);
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(a, x);
            let cx = d.add(c, x);
            let body = d.le(ca, cx);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.const_app(p.le_refl, &[ca]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(a, x);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let cx = d.add(c, x);
            let ih_ty = d.le(ca, cx);
            let body = d.const_app(p.le_step, &[ca, cx, ih]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let body = d.const_app(p.le_rec, &[a, motive, minor_refl, minor_step, b, h]);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // add_lt_add_left : ∀ c a b, Lt a b → Lt (c+a) (c+b)
    d.theorem(p.add_lt_add_left, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let strict_ty = d.lt(a, b);
        let strict_fv = d.fresh_fvar();
        let strict = d.kernel().fvar(strict_fv);
        let sa = d.succ(a);
        let body = d.lemma(p.add_le_add_left, &[c, sa, b, strict]);
        let ca = d.add(c, a);
        let cb = d.add(c, b);
        let conclusion = d.lt(ca, cb);
        let stmt = d.arrow(strict_ty, conclusion);
        let proof = d.lam_fv(strict_fv, strict_ty, body);
        (stmt, proof)
    })?;

    // add_le_add_right : ∀ c a b, Le a b → Le (a+c) (b+c)
    d.theorem(p.add_le_add_right, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let hyp_ty = d.le(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ca = d.add(c, a);
        let cb = d.add(c, b);
        let ac = d.add(a, c);
        let bc = d.add(b, c);
        let shifted = d.lemma(p.add_le_add_left, &[c, a, b, h]);
        let ca_eq_ac = d.lemma(p.add_comm, &[c, a]);
        let cb_eq_bc = d.lemma(p.add_comm, &[c, b]);
        let lower_motive = d.eq_motive(ca, &|d, lower| d.le(lower, cb));
        let lower_shifted = d.transport(ca, lower_motive, shifted, ac, ca_eq_ac);
        let upper_motive = d.eq_motive(cb, &|d, upper| d.le(ac, upper));
        let body = d.transport(cb, upper_motive, lower_shifted, bc, cb_eq_bc);
        let conclusion = d.le(ac, bc);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // le_of_add_le_add_left : ∀ c a b, Le (c+a) (c+b) → Le a b
    d.theorem(p.le_of_add_le_add_left, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let ca = d.add(c, a);
        let cb = d.add(c, b);
        let hyp_ty = d.le(ca, cb);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let represented = d.lemma(p.le_dest, &[ca, cb, h]);
        let pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let cak = d.add(ca, k);
            let body = d.eq(cak, cb);
            d.lam_fv(k_fv, nat, body)
        };
        let conclusion = d.le(a, b);
        let represented_ty = {
            let one = d.level_one();
            let exists = d.kernel().const_(p.logic.exists_, vec![one]);
            d.apply(exists, &[nat, pred])
        };
        let motive = d
            .kernel()
            .lam(anon, represented_ty, conclusion, BinderInfo::Default);
        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let cak = d.add(ca, k);
            let e_fv = d.fresh_fvar();
            let e_ty = d.eq(cak, cb);
            let e = d.kernel().fvar(e_fv);
            let ak = d.add(a, k);
            let c_ak = d.add(c, ak);
            let assoc = d.lemma(p.add_assoc, &[c, a, k]);
            let assoc_rev = d.symm(cak, c_ak, assoc);
            let (_end, common_sum) = d.chain(c_ak, &[(cak, assoc_rev), (cb, e)]);
            let ak_eq_b = d.lemma(p.add_left_cancel, &[c, ak, b, common_sum]);
            let body = d.lemma(p.le_intro, &[a, b, k, ak_eq_b]);
            let with_e = d.lam_fv(e_fv, e_ty, body);
            d.lam_fv(k_fv, nat, with_e)
        };
        let one = d.level_one();
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(rec, &[nat, pred, motive, minor, represented]);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // le_of_add_le_add_right : ∀ c a b, Le (a+c) (b+c) → Le a b
    d.theorem(p.le_of_add_le_add_right, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let ac = d.add(a, c);
        let bc = d.add(b, c);
        let hyp_ty = d.le(ac, bc);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ca = d.add(c, a);
        let cb = d.add(c, b);
        let ac_eq_ca = d.lemma(p.add_comm, &[a, c]);
        let bc_eq_cb = d.lemma(p.add_comm, &[b, c]);
        let lower_motive = d.eq_motive(ac, &|d, lower| d.le(lower, bc));
        let common_lower = d.transport(ac, lower_motive, h, ca, ac_eq_ca);
        let upper_motive = d.eq_motive(bc, &|d, upper| d.le(ca, upper));
        let common = d.transport(bc, upper_motive, common_lower, cb, bc_eq_cb);
        let body = d.lemma(p.le_of_add_le_add_left, &[c, a, b, common]);
        let conclusion = d.le(a, b);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // mul_le_mul_left : ∀ c a b, Le a b → Le (mul c a) (mul c b)
    // Each derivation step appends one `c`; transitivity with `le_add_right`
    // preserves the fixed lower endpoint.
    d.theorem(p.mul_le_mul_left, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let hyp_ty = d.le(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ca = d.mul(c, a);
        let cb = d.mul(c, b);
        let conclusion = d.le(ca, cb);
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(a, x);
            let cx = d.mul(c, x);
            let body = d.le(ca, cx);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.const_app(p.le_refl, &[ca]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(a, x);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let cx = d.mul(c, x);
            let ih_ty = d.le(ca, cx);
            let cx_le_next = d.lemma(p.le_add_right, &[cx, c]);
            let next = d.add(cx, c);
            let body = d.lemma(p.le_trans, &[ca, cx, next, ih, cx_le_next]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let body = d.const_app(p.le_rec, &[a, motive, minor_refl, minor_step, b, h]);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // mul_succ_add_lt_of_le_of_lt : ∀ n m i j,
    //   Le i m → Lt j (succ n) → Lt (add (mul (succ n) i) j) (mul (succ n) (succ m))
    //
    // The "flatten a row-major (block, offset) index" bound. Route: `succ
    // (mul sn i + j) = mul sn i + succ j` (`add_succ`) `<= mul sn i + sn`
    // (`add_le_add_left` against `j < succ n`) `= mul sn (succ i)`
    // (`mul_succ`, reversed) `<= mul sn (succ m)` (`mul_le_mul_left` against
    // `succ i <= succ m`, from `le_succ_succ` on `i <= m`), then `le_trans`
    // closes the chain -- the conclusion `Lt (mul sn i + j) (mul sn sm)` is
    // exactly `Le (succ (mul sn i + j)) (mul sn sm)` by `Nat.lt`'s own
    // definition, so no further unfolding step is needed at the end.
    d.theorem(p.mul_succ_add_lt_of_le_of_lt, 4, &|d, v| {
        let (n, m, i, j) = (v[0], v[1], v[2], v[3]);
        let sn = d.succ(n);
        let sm = d.succ(m);
        let si = d.succ(i);
        let sj = d.succ(j);

        let hle_ty = d.le(i, m);
        let hle_fv = d.fresh_fvar();
        let hle = d.kernel().fvar(hle_fv);

        let hlt_ty = d.lt(j, sn);
        let hlt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(hlt_fv);

        let mul_sn_i = d.mul(sn, i);
        let global_idx = d.add(mul_sn_i, j);
        let succ_global_idx = d.succ(global_idx);
        let total = d.mul(sn, sm);
        let conclusion = d.lt(global_idx, total);

        let global_idx_sj = d.add(mul_sn_i, sj);
        // eq1 : Eq global_idx_sj succ_global_idx.
        let eq1 = d.lemma(p.add_succ, &[mul_sn_i, j]);

        let mul_sn_i_sn = d.add(mul_sn_i, sn);
        // step1 : Le global_idx_sj mul_sn_i_sn.
        let step1 = d.lemma(p.add_le_add_left, &[mul_sn_i, sj, sn, hlt]);

        // step1_at_succ : Le succ_global_idx mul_sn_i_sn -- rewriting
        // `step1` along `eq1` from `global_idx_sj` to `succ_global_idx`.
        let step1_at_succ = {
            let motive = d.eq_motive(global_idx_sj, &|d, x| d.le(x, mul_sn_i_sn));
            d.transport(global_idx_sj, motive, step1, succ_global_idx, eq1)
        };

        let mul_sn_si = d.mul(sn, si);
        // eq2 : Eq mul_sn_i_sn mul_sn_si.
        let eq2 = {
            let mul_succ_eq = d.lemma(p.mul_succ, &[sn, i]);
            d.symm(mul_sn_si, mul_sn_i_sn, mul_succ_eq)
        };

        // step1_final : Le succ_global_idx mul_sn_si.
        let step1_final = {
            let motive = d.eq_motive(mul_sn_i_sn, &|d, x| d.le(succ_global_idx, x));
            d.transport(mul_sn_i_sn, motive, step1_at_succ, mul_sn_si, eq2)
        };

        // step2 : Le mul_sn_si total.
        let step2 = {
            let h_succ = d.lemma(p.le_succ_succ, &[i, m, hle]);
            d.lemma(p.mul_le_mul_left, &[sn, si, sm, h_succ])
        };

        let proof_body = d.lemma(
            p.le_trans,
            &[succ_global_idx, mul_sn_si, total, step1_final, step2],
        );

        let stmt = {
            let inner = d.arrow(hlt_ty, conclusion);
            d.arrow(hle_ty, inner)
        };
        let proof = {
            let inner = d.lam_fv(hlt_fv, hlt_ty, proof_body);
            d.lam_fv(hle_fv, hle_ty, inner)
        };
        (stmt, proof)
    })?;

    // le_of_mul_le_mul_left_succ :
    //   ∀ c a b, Le ((succ c)*a) ((succ c)*b) → Le a b
    // Induct on both compared values. Successor/successor products expose a
    // common positive addend, which additive order reflection cancels.
    d.theorem(p.le_of_mul_le_mul_left_succ, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let factor = d.succ(c);
        let cancellation_at = |d: &mut NatDev<'_>, x: ExprId| {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let fx = d.mul(factor, x);
            let fy = d.mul(factor, y);
            let hyp = d.le(fx, fy);
            let conclusion = d.le(x, y);
            let body = d.arrow(hyp, conclusion);
            d.pi_fv(y_fv, nat, body)
        };
        let at_zero = |d: &mut NatDev<'_>| {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let zero = d.zero();
            let fy = d.mul(factor, y);
            let hyp_ty = d.le(zero, fy);
            let h_fv = d.fresh_fvar();
            let body = d.lemma(p.zero_le, &[y]);
            let with_h = d.lam_fv(h_fv, hyp_ty, body);
            d.lam_fv(y_fv, nat, with_h)
        };
        let step_x = |d: &mut NatDev<'_>, x: ExprId, ih: ExprId| {
            let sx = d.succ(x);
            let motive_y = |d: &mut NatDev<'_>, y: ExprId| {
                let fsx = d.mul(factor, sx);
                let fy = d.mul(factor, y);
                let hyp = d.le(fsx, fy);
                let conclusion = d.le(sx, y);
                d.arrow(hyp, conclusion)
            };
            let at_y_zero = |d: &mut NatDev<'_>| {
                let zero = d.zero();
                let fx = d.mul(factor, x);
                let positive_body = d.add(fx, c);
                let positive = d.succ(positive_body);
                let hyp_ty = d.le(positive, zero);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let impossible = d.lemma(p.not_succ_le_zero, &[positive_body, h]);
                let target = d.le(sx, zero);
                let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
                let level_zero = d.kernel().level_zero();
                let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                let body = d.apply(rec, &[motive, impossible]);
                d.lam_fv(h_fv, hyp_ty, body)
            };
            let step_y = |d: &mut NatDev<'_>, y: ExprId, _inner_ih: ExprId| {
                let sy = d.succ(y);
                let fx = d.mul(factor, x);
                let fy = d.mul(factor, y);
                let fsx = d.mul(factor, sx);
                let fsy = d.mul(factor, sy);
                let hyp_ty = d.le(fsx, fsy);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let left_common = d.add(factor, fx);
                let right_common = d.add(factor, fy);
                let left_comm = d.lemma(p.add_comm, &[fx, factor]);
                let right_comm = d.lemma(p.add_comm, &[fy, factor]);
                let lower_motive = d.eq_motive(fsx, &|d, lower| d.le(lower, fsy));
                let common_lower = d.transport(fsx, lower_motive, h, left_common, left_comm);
                let upper_motive = d.eq_motive(fsy, &|d, upper| d.le(left_common, upper));
                let common = d.transport(fsy, upper_motive, common_lower, right_common, right_comm);
                let smaller = d.lemma(p.le_of_add_le_add_left, &[factor, fx, fy, common]);
                let prior = d.apply(ih, &[y, smaller]);
                let body = d.lemma(p.le_succ_succ, &[x, y, prior]);
                d.lam_fv(h_fv, hyp_ty, body)
            };
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = d.induct(&motive_y, &at_y_zero, &step_y, y);
            d.lam_fv(y_fv, nat, body)
        };
        let all_b = d.induct(&cancellation_at, &at_zero, &step_x, a);
        let proof = d.apply(all_b, &[b]);
        let fa = d.mul(factor, a);
        let fb = d.mul(factor, b);
        let hyp = d.le(fa, fb);
        let conclusion = d.le(a, b);
        (d.arrow(hyp, conclusion), proof)
    })?;

    // le_of_mul_le_mul_left :
    //   ∀ c a b, Le one c → Le (c*a) (c*b) → Le a b
    // Expose c as one plus a witness, normalize that sum to a successor, and
    // reuse the structural successor-factor cancellation theorem above.
    d.theorem(p.le_of_mul_le_mul_left, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let positive_ty = d.le(one, c);
        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let ca = d.mul(c, a);
        let cb = d.mul(c, b);
        let scaled_ty = d.le(ca, cb);
        let scaled_fv = d.fresh_fvar();
        let scaled = d.kernel().fvar(scaled_fv);
        let conclusion = d.le(a, b);

        let represented = d.lemma(p.le_dest, &[one, c, positive]);
        let representation_pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sum = d.add(one, k);
            let body = d.eq(sum, c);
            d.lam_fv(k_fv, nat, body)
        };
        let level_one = d.level_one();
        let exists = d.kernel().const_(p.logic.exists_, vec![level_one]);
        let represented_ty = d.apply(exists, &[nat, representation_pred]);
        let motive = d
            .kernel()
            .lam(anon, represented_ty, conclusion, BinderInfo::Default);
        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sum = d.add(one, k);
            let e_fv = d.fresh_fvar();
            let e_ty = d.eq(sum, c);
            let e = d.kernel().fvar(e_fv);
            let successor = d.succ(k);

            let zero = d.zero();
            let successor_zero = d.succ(zero);
            let zero_sum = d.add(zero, k);
            let successor_sum = d.add(successor_zero, k);
            let successor_zero_sum = d.succ(zero_sum);
            let successor_k = d.succ(k);
            let h_succ_add = d.lemma(p.succ_add, &[zero, k]);
            let h_zero_add = d.lemma(p.zero_add, &[k]);
            let h_succ_zero_add = d.congr(zero_sum, k, h_zero_add, &|d, x| d.succ(x));
            let (_, sum_eq_successor) = d.chain(
                successor_sum,
                &[
                    (successor_zero_sum, h_succ_add),
                    (successor_k, h_succ_zero_add),
                ],
            );
            let successor_eq_sum = d.symm(sum, successor, sum_eq_successor);
            let (_, successor_eq_c) = d.chain(successor, &[(sum, successor_eq_sum), (c, e)]);
            let c_eq_successor = d.symm(successor, c, successor_eq_c);

            let successor_a = d.mul(successor, a);
            let successor_b = d.mul(successor, b);
            let ca_eq_successor_a = d.congr(c, successor, c_eq_successor, &|d, x| d.mul(x, a));
            let cb_eq_successor_b = d.congr(c, successor, c_eq_successor, &|d, x| d.mul(x, b));
            let lower_motive = d.eq_motive(ca, &|d, lower| d.le(lower, cb));
            let successor_lower =
                d.transport(ca, lower_motive, scaled, successor_a, ca_eq_successor_a);
            let upper_motive = d.eq_motive(cb, &|d, upper| d.le(successor_a, upper));
            let successor_scaled = d.transport(
                cb,
                upper_motive,
                successor_lower,
                successor_b,
                cb_eq_successor_b,
            );
            let body = d.lemma(p.le_of_mul_le_mul_left_succ, &[k, a, b, successor_scaled]);
            let with_e = d.lam_fv(e_fv, e_ty, body);
            d.lam_fv(k_fv, nat, with_e)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);
        let body = d.apply(rec, &[nat, representation_pred, motive, minor, represented]);
        let proof = {
            let with_scaled = d.lam_fv(scaled_fv, scaled_ty, body);
            d.lam_fv(positive_fv, positive_ty, with_scaled)
        };
        let stmt = {
            let with_scaled = d.arrow(scaled_ty, conclusion);
            d.arrow(positive_ty, with_scaled)
        };
        (stmt, proof)
    })?;

    // mul_left_cancel_of_pos :
    //   ∀ c a b, Le one c → Eq (c*a) (c*b) → Eq a b
    // Convert equality to bounds in both directions, reflect each through the
    // proof-positive factor, then apply order antisymmetry.
    d.theorem(p.mul_left_cancel_of_pos, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let positive_ty = d.le(one, c);
        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let ca = d.mul(c, a);
        let cb = d.mul(c, b);
        let equality_ty = d.eq(ca, cb);
        let equality_fv = d.fresh_fvar();
        let equality = d.kernel().fvar(equality_fv);

        let ca_le_ca = d.lemma(p.le_refl, &[ca]);
        let upper_motive = d.eq_motive(ca, &|d, upper| d.le(ca, upper));
        let ca_le_cb = d.transport(ca, upper_motive, ca_le_ca, cb, equality);
        let cb_eq_ca = d.symm(ca, cb, equality);
        let cb_le_cb = d.lemma(p.le_refl, &[cb]);
        let reverse_motive = d.eq_motive(cb, &|d, upper| d.le(cb, upper));
        let cb_le_ca = d.transport(cb, reverse_motive, cb_le_cb, ca, cb_eq_ca);
        let a_le_b = d.lemma(p.le_of_mul_le_mul_left, &[c, a, b, positive, ca_le_cb]);
        let b_le_a = d.lemma(p.le_of_mul_le_mul_left, &[c, b, a, positive, cb_le_ca]);
        let body = d.lemma(p.le_antisymm, &[a, b, a_le_b, b_le_a]);
        let conclusion = d.eq(a, b);
        let proof = {
            let with_equality = d.lam_fv(equality_fv, equality_ty, body);
            d.lam_fv(positive_fv, positive_ty, with_equality)
        };
        let stmt = {
            let with_equality = d.arrow(equality_ty, conclusion);
            d.arrow(positive_ty, with_equality)
        };
        (stmt, proof)
    })?;

    // sub_add_cancel : ∀ m n, Le m n → add (sub n m) m = n
    // Induct on the subtrahend. In the successor case, eliminate the bound
    // derivation so both `Le` and `sub` expose matching successor structure.
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let cancellation_at = |d: &mut NatDev<'_>, subtrahend: ExprId| {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let hyp = d.le(subtrahend, n);
            let difference = d.sub(n, subtrahend);
            let restored = d.add(difference, subtrahend);
            let conclusion = d.eq(restored, n);
            let implication = d.arrow(hyp, conclusion);
            let nat = d.nat_ty();
            d.pi_fv(n_fv, nat, implication)
        };
        let stmt = cancellation_at(d, m);
        let proof = d.induct(
            &cancellation_at,
            &|d| {
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let zero = d.zero();
                let hyp_ty = d.le(zero, n);
                let h_fv = d.fresh_fvar();
                let body = d.refl(n);
                let with_h = d.lam_fv(h_fv, hyp_ty, body);
                let nat = d.nat_ty();
                d.lam_fv(n_fv, nat, with_h)
            },
            &|d, j, ih| {
                let sj = d.succ(j);
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let hyp_ty = d.le(sj, n);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);

                let le_motive = {
                    let x_fv = d.fresh_fvar();
                    let x = d.kernel().fvar(x_fv);
                    let dom = d.le(sj, x);
                    let difference = d.sub(x, sj);
                    let restored = d.add(difference, sj);
                    let body = d.eq(restored, x);
                    let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
                    d.lam_fv(x_fv, nat, inner)
                };

                let minor_refl = {
                    let difference = d.sub(sj, sj);
                    let start = d.add(difference, sj);
                    let zero = d.zero();
                    let middle = d.add(zero, sj);
                    let h_sub = d.lemma(p.sub_self, &[sj]);
                    let h1 = d.congr(difference, zero, h_sub, &|d, x| d.add(x, sj));
                    let h2 = d.lemma(p.zero_add, &[sj]);
                    let (_end, proof) = d.chain(start, &[(middle, h1), (sj, h2)]);
                    proof
                };

                let minor_step = {
                    let x_fv = d.fresh_fvar();
                    let x = d.kernel().fvar(x_fv);
                    let hx_fv = d.fresh_fvar();
                    let hx_ty = d.le(sj, x);
                    let hx = d.kernel().fvar(hx_fv);
                    let rec_ih_fv = d.fresh_fvar();
                    let difference = d.sub(x, sj);
                    let rec_restored = d.add(difference, sj);
                    let rec_ih_ty = d.eq(rec_restored, x);

                    let sx = d.succ(x);
                    let successor_difference = d.sub(sx, sj);
                    let start = d.add(successor_difference, sj);
                    let prior_difference = d.sub(x, j);
                    let middle = d.add(prior_difference, sj);
                    let h_sub = d.lemma(p.succ_sub_succ, &[x, j]);
                    let h1 = d.congr(successor_difference, prior_difference, h_sub, &|d, t| {
                        d.add(t, sj)
                    });

                    let j_refl = d.const_app(p.le_refl, &[j]);
                    let j_le_sj = d.const_app(p.le_step, &[j, j, j_refl]);
                    let j_le_x = d.lemma(p.le_trans, &[j, sj, x, j_le_sj, hx]);
                    let prior_restored = d.add(prior_difference, j);
                    let restored = d.apply(ih, &[x, j_le_x]);
                    let h2 = d.congr(prior_restored, x, restored, &|d, t| d.succ(t));
                    let (_end, body) = d.chain(start, &[(middle, h1), (sx, h2)]);

                    let with_rec_ih = d.lam_fv(rec_ih_fv, rec_ih_ty, body);
                    let with_hx = d.lam_fv(hx_fv, hx_ty, with_rec_ih);
                    d.lam_fv(x_fv, nat, with_hx)
                };

                let body = d.const_app(p.le_rec, &[sj, le_motive, minor_refl, minor_step, n, h]);
                let with_h = d.lam_fv(h_fv, hyp_ty, body);
                d.lam_fv(n_fv, nat, with_h)
            },
            m,
        );
        let ty = d.pi_fv(m_fv, nat, stmt);
        let value = d.lam_fv(m_fv, nat, proof);
        d.declare_theorem(p.sub_add_cancel, ty, value)?;
    }

    // sub_eq_zero_of_le : ∀ a b, Le a b → sub a b = zero
    d.theorem(p.sub_eq_zero_of_le, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.zero();
        let hyp_ty = d.le(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(a, x);
            let difference = d.sub(a, x);
            let body = d.eq(difference, zero);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.lemma(p.sub_self, &[a]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(a, x);
            let ih_fv = d.fresh_fvar();
            let difference = d.sub(a, x);
            let ih_ty = d.eq(difference, zero);
            let ih = d.kernel().fvar(ih_fv);
            let body = d.congr(difference, zero, ih, &|d, value| d.pred(value));
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let body = d.const_app(p.le_rec, &[a, motive, minor_refl, minor_step, b, h]);
        let difference = d.sub(a, b);
        let conclusion = d.eq(difference, zero);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // sub_le_iff_le_add : ∀ x y z, Iff (Le (sub x y) z) (Le x (add z y))
    d.theorem(p.sub_le_iff_le_add, 3, &|d, v| {
        let (x, y, z) = (v[0], v[1], v[2]);
        let difference = d.sub(x, y);
        let sum = d.add(z, y);
        let lhs = d.le(difference, z);
        let rhs = d.le(x, sum);
        let total = d.lemma(p.le_total, &[y, x]);
        let y_le_x = d.le(y, x);
        let x_le_y = d.le(x, y);
        let total_ty = d.const_app(p.logic.or, &[y_le_x, x_le_y]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let motive = d.kernel().lam(anon, total_ty, rhs, BinderInfo::Default);
            let bounded_minor = {
                let hyx_fv = d.fresh_fvar();
                let hyx = d.kernel().fvar(hyx_fv);
                let restored = d.add(difference, y);
                let restored_eq_x = d.lemma(p.sub_add_cancel, &[y, x, hyx]);
                let shifted = d.lemma(p.add_le_add_right, &[y, difference, z, h]);
                let lower_motive = d.eq_motive(restored, &|d, lower| d.le(lower, sum));
                let body = d.transport(restored, lower_motive, shifted, x, restored_eq_x);
                d.lam_fv(hyx_fv, y_le_x, body)
            };
            let truncated_minor = {
                let hxy_fv = d.fresh_fvar();
                let hxy = d.kernel().fvar(hxy_fv);
                let y_plus_z = d.add(y, z);
                let y_le_y_plus_z = d.lemma(p.le_add_right, &[y, z]);
                let y_plus_z_eq_sum = d.lemma(p.add_comm, &[y, z]);
                let upper_motive = d.eq_motive(y_plus_z, &|d, upper| d.le(y, upper));
                let y_le_sum =
                    d.transport(y_plus_z, upper_motive, y_le_y_plus_z, sum, y_plus_z_eq_sum);
                let body = d.lemma(p.le_trans, &[x, y, sum, hxy, y_le_sum]);
                d.lam_fv(hxy_fv, x_le_y, body)
            };
            let rec = d.kernel().const_(p.logic.or_rec, vec![]);
            let body = d.apply(
                rec,
                &[
                    y_le_x,
                    x_le_y,
                    motive,
                    bounded_minor,
                    truncated_minor,
                    total,
                ],
            );
            d.lam_fv(h_fv, lhs, body)
        };

        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let motive = d.kernel().lam(anon, total_ty, lhs, BinderInfo::Default);
            let bounded_minor = {
                let hyx_fv = d.fresh_fvar();
                let hyx = d.kernel().fvar(hyx_fv);
                let restored = d.add(difference, y);
                let restored_eq_x = d.lemma(p.sub_add_cancel, &[y, x, hyx]);
                let x_eq_restored = d.symm(restored, x, restored_eq_x);
                let lower_motive = d.eq_motive(x, &|d, lower| d.le(lower, sum));
                let restored_le_sum = d.transport(x, lower_motive, h, restored, x_eq_restored);
                let body = d.lemma(
                    p.le_of_add_le_add_right,
                    &[y, difference, z, restored_le_sum],
                );
                d.lam_fv(hyx_fv, y_le_x, body)
            };
            let truncated_minor = {
                let hxy_fv = d.fresh_fvar();
                let hxy = d.kernel().fvar(hxy_fv);
                let zero = d.zero();
                let zero_le_z = d.lemma(p.zero_le, &[z]);
                let difference_eq_zero = d.lemma(p.sub_eq_zero_of_le, &[x, y, hxy]);
                let zero_eq_difference = d.symm(difference, zero, difference_eq_zero);
                let lower_motive = d.eq_motive(zero, &|d, lower| d.le(lower, z));
                let body = d.transport(
                    zero,
                    lower_motive,
                    zero_le_z,
                    difference,
                    zero_eq_difference,
                );
                d.lam_fv(hxy_fv, x_le_y, body)
            };
            let rec = d.kernel().const_(p.logic.or_rec, vec![]);
            let body = d.apply(
                rec,
                &[
                    y_le_x,
                    x_le_y,
                    motive,
                    bounded_minor,
                    truncated_minor,
                    total,
                ],
            );
            d.lam_fv(h_fv, rhs, body)
        };
        let stmt = d.const_app(p.logic.iff, &[lhs, rhs]);
        let proof = d.const_app(p.logic.iff_intro, &[lhs, rhs, mp, mpr]);
        (stmt, proof)
    })?;

    // mul_sub_left_distrib : ∀ b q a, Le a q → b*(q-a) = b*q-b*a
    // Rather than postulating monotonicity, construct the scaled difference,
    // prove it restores `b*q`, transport the corresponding bound, and cancel
    // the common right summand.
    d.theorem(p.mul_sub_left_distrib, 3, &|d, v| {
        let (b, q, a) = (v[0], v[1], v[2]);
        let hyp_ty = d.le(a, q);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let difference = d.sub(q, a);
        let restored = d.add(difference, a);
        let h_restore = d.lemma(p.sub_add_cancel, &[a, q, h]);
        let b_difference = d.mul(b, difference);
        let ba = d.mul(b, a);
        let bq = d.mul(b, q);
        let scaled_sum = d.mul(b, restored);
        let sum = d.add(b_difference, ba);
        let h_distribute = d.lemma(p.left_distrib, &[b, difference, a]);
        let h_distribute_rev = d.symm(scaled_sum, sum, h_distribute);
        let h_scaled_restore = d.congr(restored, q, h_restore, &|d, x| d.mul(b, x));
        let (_end, sum_eq_bq) = d.chain(
            sum,
            &[(scaled_sum, h_distribute_rev), (bq, h_scaled_restore)],
        );

        let reordered_sum = d.add(ba, b_difference);
        let ba_le_reordered = d.lemma(p.le_add_right, &[ba, b_difference]);
        let h_comm = d.lemma(p.add_comm, &[ba, b_difference]);
        let (_end, reordered_eq_bq) = d.chain(reordered_sum, &[(sum, h_comm), (bq, sum_eq_bq)]);
        let le_motive = d.eq_motive(reordered_sum, &|d, x| d.le(ba, x));
        let ba_le_bq = d.transport(
            reordered_sum,
            le_motive,
            ba_le_reordered,
            bq,
            reordered_eq_bq,
        );

        let scaled_difference = d.sub(bq, ba);
        let scaled_restored = d.add(scaled_difference, ba);
        let h_sub_restore = d.lemma(p.sub_add_cancel, &[ba, bq, ba_le_bq]);
        let h_sub_restore_rev = d.symm(scaled_restored, bq, h_sub_restore);
        let (_end, common_sum) = d.chain(
            sum,
            &[(bq, sum_eq_bq), (scaled_restored, h_sub_restore_rev)],
        );
        let body = d.lemma(
            p.add_right_cancel,
            &[b_difference, scaled_difference, ba, common_sum],
        );
        let conclusion = d.eq(b_difference, scaled_difference);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // The total Nat identity follows by totality. The bounded branch is the
    // theorem above; in the reverse-order branch both truncated differences
    // are zero, with multiplication monotonicity supplying the scaled bound.
    d.theorem(p.mul_sub_left_distrib_total, 3, &|d, v| {
        let (b, q, a) = (v[0], v[1], v[2]);
        let difference = d.sub(q, a);
        let lhs = d.mul(b, difference);
        let bq = d.mul(b, q);
        let ba = d.mul(b, a);
        let rhs = d.sub(bq, ba);
        let target = d.eq(lhs, rhs);
        let q_le_a = d.le(q, a);
        let a_le_q = d.le(a, q);
        let total_ty = d.const_app(p.logic.or, &[q_le_a, a_le_q]);
        let total = d.lemma(p.le_total, &[q, a]);
        let anon = d.anon_name();
        let motive = d.kernel().lam(anon, total_ty, target, BinderInfo::Default);
        let truncated_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let zero = d.zero();
            let difference_zero = d.lemma(p.sub_eq_zero_of_le, &[q, a, h]);
            let lhs_to_bzero = d.congr(difference, zero, difference_zero, &|d, x| d.mul(b, x));
            let bzero = d.mul(b, zero);
            let bzero_zero = d.lemma(p.mul_zero, &[b]);
            let lhs_zero = d.trans(lhs, bzero, zero, lhs_to_bzero, bzero_zero);
            let scaled = d.lemma(p.mul_le_mul_left, &[b, q, a, h]);
            let rhs_zero = d.lemma(p.sub_eq_zero_of_le, &[bq, ba, scaled]);
            let zero_rhs = d.symm(rhs, zero, rhs_zero);
            let body = d.trans(lhs, zero, rhs, lhs_zero, zero_rhs);
            d.lam_fv(h_fv, q_le_a, body)
        };
        let bounded_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = d.lemma(p.mul_sub_left_distrib, &[b, q, a, h]);
            d.lam_fv(h_fv, a_le_q, body)
        };
        let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
        let proof = d.apply(
            or_rec,
            &[
                q_le_a,
                a_le_q,
                motive,
                truncated_minor,
                bounded_minor,
                total,
            ],
        );
        (target, proof)
    })?;

    // add_sub_cancel_left : ∀ m n, (m+n)-m = n. Restore the subtrahend,
    // commute the original sum, then cancel the common right summand.
    d.theorem(p.add_sub_cancel_left, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let sum = d.add(m, n);
        let difference = d.sub(sum, m);
        let restored = d.add(difference, m);
        let m_le_sum = d.lemma(p.le_add_right, &[m, n]);
        let restore = d.lemma(p.sub_add_cancel, &[m, sum, m_le_sum]);
        let reordered = d.add(n, m);
        let commute = d.lemma(p.add_comm, &[m, n]);
        let (_, common_sum) = d.chain(restored, &[(sum, restore), (reordered, commute)]);
        let proof = d.lemma(p.add_right_cancel, &[difference, n, m, common_sum]);
        (d.eq(difference, n), proof)
    })?;

    // sub_sub_self : ∀ n k, Le k n → sub n (sub n k) = k
    //
    // No induction of its own. `sub_add_cancel` gives `add (sub n k) k = n`;
    // rewriting only the OUTER `n` of `sub n (sub n k)` along it turns the goal
    // into `sub (add (sub n k) k) (sub n k) = k`, which is
    // `add_sub_cancel_left` at `(sub n k, k)`. The `Le k n` hypothesis is
    // essential and not cosmetic: `Nat.sub` truncates, so the unbounded form is
    // false (`sub 3 (sub 3 5) = 3`).
    d.theorem(p.sub_sub_self, 2, &|d, v| {
        let (n, k) = (v[0], v[1]);
        let hyp_ty = d.le(k, n);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let diff = d.sub(n, k);
        let lhs = d.sub(n, diff);
        let stmt = d.eq(lhs, k);
        let full = d.arrow(hyp_ty, stmt);

        let restored = d.add(diff, k);
        let cancel = d.lemma(p.sub_add_cancel, &[k, n, h]); // add (sub n k) k = n
        let base = d.lemma(p.add_sub_cancel_left, &[diff, k]); // sub (add diff k) diff = k
        let moved = {
            let motive = d.eq_motive(restored, &|d, z| {
                let diff = d.sub(n, k);
                let inner = d.sub(z, diff);
                d.eq(inner, k)
            });
            d.transport(restored, motive, base, n, cancel)
        };
        (full, d.lam_fv(h_fv, hyp_ty, moved))
    })?;
    Ok(())
}
