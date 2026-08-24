//! `Int.prodRange : (Nat → Int) → Nat → Int` — the finite product missing
//! under Wilson's theorem and the permutation proof of Fermat's little
//! theorem: `prodRange f n = f 0 * f 1 * … * f (n-1)`.
//!
//! Mirrors [`NatPrelude::sum_range`](crate::nat_prelude::NatPrelude::sum_range)'s
//! own convention exactly (`nat_prelude/defs.rs::declare_finite_ranges`): the
//! bound is **exclusive**, the base case is the identity of the operation
//! (`Int.one`, where `sumRange` uses `Nat.zero`), and the recursive step
//! multiplies the fresh factor onto the **right** of the prior product
//! (`prodRange f (succ n) ≡ mul (prodRange f n) (f n)`, where `sumRange`
//! *adds* `f n` onto the right of the prior sum) — same shape as
//! [`super::defs::declare_pow`], which folds a single fixed factor `a` the
//! same way; here the factor varies with the index instead of staying fixed.
//!
//! `Int.prodRange` is a checked `Nat.rec` definition, not an axiom — the same
//! `Int`-valued, `Nat`-recursion pattern as `Int.pow`
//! (`defs.rs::declare_pow`), so it reuses `NatPrelude::rec` rather than
//! `Int.rec`.

use super::defs::POW_HEIGHT;
use super::ops::IntDev;
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::nat_prelude::NatOps;

/// Delta height for `Int.prodRange`, which calls `Int.mul`
/// (`DERIVED_HEIGHT`, 21) and closes over an arbitrary `Nat → Int` argument.
/// Strictly greater than `Int.pow`'s own height (`POW_HEIGHT`, 22) so the two
/// stay ordered even though neither calls the other.
const PROD_RANGE_HEIGHT: u16 = POW_HEIGHT + 1;

/// Admit `Int.prodRange : (Nat → Int) → Nat → Int` by structural recursion on
/// the `Nat` bound:
///
/// `prodRange f Nat.zero ≡ Int.one`,
/// `prodRange f (Nat.succ n) ≡ Int.mul (prodRange f n) (f n)`.
///
/// The motive is the constant family `fun _ => Int` (non-dependent), exactly
/// as [`super::defs::declare_pow`]'s `Nat.rec` application over the exponent —
/// the only difference is that the minor premise for `succ` here also applies
/// the closed-over `f` at the predecessor index, since the factor being
/// multiplied in varies with position instead of staying fixed.
///
/// # Errors
///
/// Returns the kernel's rejection if the generated definition does not
/// type-check or the name is already taken.
pub(super) fn declare_prod_range(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();

    let fn_ty = d.arrow(nat, int_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let motive = d.kernel().lam(anon, nat, int_ty, BinderInfo::Default);
    let minor_zero = d.ione();
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let fj = d.apply(f, &[j]);
        let body = d.imul(ih, fj);
        let inner = d.lam_fv(ih_fv, int_ty, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(f_fv, fn_ty, with_n)
    };
    let ty = {
        let over_n = d.arrow(nat, int_ty);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.prod_range,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(PROD_RANGE_HEIGHT),
    })
}

/// The defining equations of `Int.prodRange`: `prodRange_zero` and
/// `prodRange_succ`, each an `Eq.refl` at `Int` — `Int.prodRange` computes on
/// both minor premises, exactly as `Int.pow`'s own `pow_zero`/`pow_succ` do
/// (`defs.rs::declare_pow_equations`).
///
/// Both quantify over a `Nat → Int` function (`prodRange_succ` also over a
/// `Nat`), so neither can go through
/// [`IntDev::int_theorem`](super::ops::IntDev::int_theorem) (which quantifies
/// only over `Int`) — their `Pi`/`lam` chains are built by hand, as
/// `declare_pow_equations`'s are.
///
/// # Errors
///
/// Returns the kernel's rejection if a generated proof does not check.
pub(super) fn declare_prod_range_equations(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);

    // prodRange_zero : ∀ (f : Nat → Int), Eq Int (prodRange f zero) one.
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let zero = d.zero();
        let lhs = d.const_app(p.prod_range, &[f, zero]);
        let one = d.ione();
        let stmt = d.ieq(lhs, one);
        let proof = d.irefl(one);
        let ty = d.pi_fv(f_fv, fn_ty, stmt);
        let value = d.lam_fv(f_fv, fn_ty, proof);
        d.declare_theorem(p.prod_range_zero, ty, value)?;
    }

    // prodRange_succ :
    //   ∀ (f : Nat → Int) (n : Nat),
    //     Eq Int (prodRange f (succ n)) (mul (prodRange f n) (f n)).
    {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);

        let sn = d.succ(n);
        let lhs = d.const_app(p.prod_range, &[f, sn]);
        let prior = d.const_app(p.prod_range, &[f, n]);
        let fn_ = d.apply(f, &[n]);
        let rhs = d.imul(prior, fn_);
        let stmt = d.ieq(lhs, rhs);
        let proof = d.irefl(rhs);

        let ty = {
            let with_n = d.pi_fv(n_fv, nat, stmt);
            d.pi_fv(f_fv, fn_ty, with_n)
        };
        let value = {
            let with_n = d.lam_fv(n_fv, nat, proof);
            d.lam_fv(f_fv, fn_ty, with_n)
        };
        d.declare_theorem(p.prod_range_succ, ty, value)?;
    }
    Ok(())
}

/// `Int.prodRange_congr :
///   ∀ f g n, (∀ k, Eq Int (f k) (g k)) → Eq Int (prodRange f n) (prodRange g n)`
/// — pointwise-equal factors give equal products.
///
/// Induction on `n`, mirroring
/// [`declare_finite_sum_theorems`](crate::nat_prelude::algebra)'s
/// `sumRange_congr` exactly, with `Int.mul`/`Eq Int` in place of `Nat.add`/
/// `Eq Nat`: the base case is `Eq.refl one` (`prodRange _ zero` computes to
/// `one` regardless of the function), and the successor case rewrites the
/// prior product via the induction hypothesis, then the fresh factor via the
/// pointwise hypothesis at the predecessor index, and chains the two.
///
/// `NatOps::induct` still applies unchanged: its motive is `Prop`-valued
/// (`Eq.{1} Int … : Prop`), so only the *contents* of the proposition are
/// `Int`-typed, not the induction itself.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_prod_range_congr(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let eq = d.ieq(fk, gk);
        d.pi_fv(k_fv, nat, eq)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let lhs = d.const_app(p.prod_range, &[f, x]);
        let rhs = d.const_app(p.prod_range, &[g, x]);
        d.ieq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let one = d.ione();
            d.irefl(one)
        },
        &|d, j, ih| {
            let f_prior = d.const_app(p.prod_range, &[f, j]);
            let g_prior = d.const_app(p.prod_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let start = d.imul(f_prior, fj);
            let mid = d.imul(g_prior, fj);
            let h1 = d.icongr(f_prior, g_prior, ih, &|d, t| d.imul(t, fj));
            let end = d.imul(g_prior, gj);
            let pointwise_j = d.apply(h, &[j]);
            let h2 = d.icongr(fj, gj, pointwise_j, &|d, t| d.imul(g_prior, t));
            let (_, proof) = d.ichain(start, &[(mid, h1), (end, h2)]);
            proof
        },
        n,
    );

    let ty = {
        let with_h = d.pi_fv(h_fv, pointwise, stmt);
        let over_n = d.pi_fv(n_fv, nat, with_h);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, pointwise, proof);
        let over_n = d.lam_fv(n_fv, nat, with_h);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.prod_range_congr, ty, value)
}

/// `Int.modEq_prodRange :
///   ∀ n f g m, 0 < n → (∀ k, ModEq n (f k) (g k)) →
///     ModEq n (prodRange f m) (prodRange g m)`
/// — the headline result: a product reduces modulo `n` factor by factor.
///
/// Induction on `m`, using [`super::modeq::declare_modeq_mul`]'s
/// `Int.ModEq.mul` at each step, exactly mirroring
/// [`super::modeq::declare_modeq_pow`]'s induction on the exponent (which is
/// the special case `f = g = fun _ => a`/`fun _ => b` — a *constant* function
/// forced through the same recursion `Int.pow` uses). The base case is
/// `ModEq.refl n one` (`prodRange _ zero` computes to `one` on both sides
/// regardless of `f`/`g`); the successor case applies `ModEq.mul` to the
/// induction hypothesis (`ModEq n (prodRange f j) (prodRange g j)`) and the
/// pointwise hypothesis instantiated at the predecessor index
/// (`ModEq n (f j) (g j)`), which is exactly
/// `ModEq n (prodRange f j * f j) (prodRange g j * g j)`
/// `= ModEq n (prodRange f (succ j)) (prodRange g (succ j))` by
/// `prodRange_succ`'s defining equation (definitional, no rewrite needed).
///
/// Quantifies over `Int` (`n`), two `Nat → Int` functions (`f`, `g`), and a
/// `Nat` (`m`), so — like `modEq_pow` — it is declared by hand rather than
/// through [`IntDev::int_theorem`](super::ops::IntDev::int_theorem).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_prod_range(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let int_ty = d.int_ty();
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, int_ty);

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let zero = d.izero();
    let pos_ty = d.ilt(zero, n);
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let eq = super::modeq::imodeq(d, n, fk, gk);
        d.pi_fv(k_fv, nat, eq)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| {
        let pf = d.const_app(p.prod_range, &[f, x]);
        let pg = d.const_app(p.prod_range, &[g, x]);
        super::modeq::imodeq(d, n, pf, pg)
    };
    let conclusion_for_m = motive(d, m);

    let h_pos_fv = d.fresh_fvar();
    let h_pos = d.kernel().fvar(h_pos_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let proof_body = d.induct(
        &motive,
        &|d| {
            let one = d.ione();
            d.const_app(p.mod_eq_refl, &[n, one])
        },
        &|d, j, ih| {
            let pf_j = d.const_app(p.prod_range, &[f, j]);
            let pg_j = d.const_app(p.prod_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let pointwise_j = d.apply(h, &[j]);
            d.const_app(
                p.mod_eq_mul,
                &[n, pf_j, pg_j, fj, gj, h_pos, ih, pointwise_j],
            )
        },
        m,
    );

    let with_h = d.lam_fv(h_fv, pointwise, proof_body);
    let with_h_pos = d.lam_fv(h_pos_fv, pos_ty, with_h);

    let value = {
        let with_m = d.lam_fv(m_fv, nat, with_h_pos);
        let with_g = d.lam_fv(g_fv, fn_ty, with_m);
        let with_f = d.lam_fv(f_fv, fn_ty, with_g);
        d.lam_fv(n_fv, int_ty, with_f)
    };
    let ty = {
        let inner_arrow = d.arrow(pointwise, conclusion_for_m);
        let with_pos = d.arrow(pos_ty, inner_arrow);
        let with_m = d.pi_fv(m_fv, nat, with_pos);
        let with_g = d.pi_fv(g_fv, fn_ty, with_m);
        let with_f = d.pi_fv(f_fv, fn_ty, with_g);
        d.pi_fv(n_fv, int_ty, with_f)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mod_eq_prod_range,
        uparams: vec![],
        ty,
        value,
    })
}
