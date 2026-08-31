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
use super::ops::{IntDev, exists_elim};
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

/// `Int.prodRange_shiftFront :
///   ∀ f n, Eq Int (prodRange f (succ n))
///     (mul (f zero) (prodRange (fun k => f (succ k)) n))`
///
/// Peels the FRONT term off a finite product — `prodRange_succ` (the defining
/// equation) already peels the BACK term for free; this direction needs
/// induction, because the front term stays fixed while the bound moves.
///
/// Induction on `n`, mirroring `Nat.sumRange_shiftFront`'s own proof shape
/// (`nat_prelude/binomial.rs::declare_sum_range_shift_front`) exactly, with
/// `Int.mul`/`Int.mul_assoc` standing in for `Nat.add`/`Nat.add_assoc`. One
/// genuine difference from the `Nat` proof:
/// there, the base case closes with a single `zero_add` because `Nat.add`
/// reduces definitionally to its left argument when the right argument is
/// `zero`. `Int.mul` has no such definitional identity on a symbolic
/// argument (its recursor needs to match on the actual constructor of *both*
/// operands), so the base case here needs both `Int.one_mul` and
/// `Int.mul_one` chained together rather than one computation.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_prod_range_shift_front(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // `fun k => f (succ k)`, built fresh each time it is needed (the fvar it
    // binds must not escape).
    let shifted_of = |d: &mut IntDev<'_>, f: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let body = d.apply(f, &[sk]);
        d.lam_fv(k_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sx = d.succ(x);
        let lhs = d.const_app(p.prod_range, &[f, sx]);
        let zero = d.zero();
        let f0 = d.apply(f, &[zero]);
        let shifted_f = shifted_of(d, f);
        let pr = d.const_app(p.prod_range, &[shifted_f, x]);
        let rhs = d.imul(f0, pr);
        d.ieq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let p = d.int();
            let zero = d.zero();
            let f0 = d.apply(f, &[zero]);
            let one_i = d.ione();

            // LHS unfolds (prodRange_succ, prodRange_zero) to `mul one f0`.
            let mul_one_f0 = d.imul(one_i, f0);
            let step1 = d.const_app(p.one_mul, &[f0]); // one * f0 = f0

            // RHS unfolds (prodRange_zero of the shifted function) to
            // `mul f0 one`.
            let mul_f0_one = d.imul(f0, one_i);
            let step2 = d.const_app(p.mul_one, &[f0]); // f0 * one = f0
            let step2_rev = d.isymm(mul_f0_one, f0, step2);

            d.itrans(mul_one_f0, f0, mul_f0_one, step1, step2_rev)
        },
        &|d, j, ih| {
            let p = d.int();
            let sj = d.succ(j);
            let f_prior_succ = d.const_app(p.prod_range, &[f, sj]);
            let f_sj = d.apply(f, &[sj]);
            let start = d.imul(f_prior_succ, f_sj);

            let zero = d.zero();
            let f0 = d.apply(f, &[zero]);
            let shifted_f = shifted_of(d, f);
            let shifted_j = d.const_app(p.prod_range, &[shifted_f, j]);
            let mid1 = d.imul(f0, shifted_j);
            let h1 = d.icongr(f_prior_succ, mid1, ih, &|d, t| d.imul(t, f_sj));
            let after_ih = d.imul(mid1, f_sj);

            let inner = d.imul(shifted_j, f_sj);
            let end_ = d.imul(f0, inner);
            let h2 = d.const_app(p.mul_assoc, &[f0, shifted_j, f_sj]);

            let (_e, proof) = d.ichain(start, &[(after_ih, h1), (end_, h2)]);
            proof
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(f_fv, fn_ty, over_n)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty, over_n)
    };
    d.declare_theorem(p.prod_range_shift_front, ty, value)
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

/// `Not (Eq Nat a b)`, from `hlt : Lt a b`. Transport `hlt` along
/// `Eq Nat b a` (`Nat.symm` of an assumed `Eq Nat a b`) to reach `Lt a a`,
/// then close with `Nat.lt_irrefl`.
fn ne_of_lt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let eq_ab = d.eq(a, b);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let h_rev = d.symm(a, b, e);
    let motive = d.eq_motive(b, &|d, x| d.lt(a, x));
    let laa = d.transport(b, motive, hlt, a, h_rev);
    let irrefl = d.int().nat.lt_irrefl;
    let contra = d.const_app(irrefl, &[a, laa]);
    d.lam_fv(e_fv, eq_ab, contra)
}

/// `Not (Eq Nat b a)`, from `hlt : Lt a b` — [`ne_of_lt`] with the equality
/// flipped, for the argument order `InjectiveOn`/`prodRange_swap_adjacent`'s
/// agreement hypothesis actually wants (the varying index first).
fn ne_of_lt_symm(d: &mut IntDev<'_>, a: ExprId, b: ExprId, hlt: ExprId) -> ExprId {
    let ne_ab = ne_of_lt(d, a, b, hlt);
    let eq_ba = d.eq(b, a);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let flipped = d.symm(b, a, e);
    let contra = d.apply(ne_ab, &[flipped]);
    d.lam_fv(e_fv, eq_ba, contra)
}

/// `fun k => Lt k bound → Eq Int (f k) (g k)`.
fn bounded_pointwise_int(d: &mut IntDev<'_>, f: ExprId, g: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let hyp = d.lt(k, bound);
    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let eqn = d.ieq(fk, gk);
    let body = d.arrow(hyp, eqn);
    d.pi_fv(k_fv, nat, body)
}

/// `Int.prodRange_congr_lt :
///   ∀ f g n, (∀ k, Lt k n → Eq Int (f k) (g k)) →
///     Eq Int (prodRange f n) (prodRange g n)`
/// — [`declare_prod_range_congr`]'s pointwise hypothesis weakened to indices
/// below the bound, mirroring `Nat.sumRange_congr_lt`
/// (`nat_prelude/binomial.rs::declare_sum_range_congr_lt`) exactly, with
/// `Int.mul`/`Eq Int` in place of `Nat.add`/`Eq Nat`. Induction on `n`; the
/// successor step weakens the `Lt _ (succ j)` hypothesis to `Lt _ j` via
/// `Nat.le_succ` + `Nat.lt_of_lt_of_le` before applying the induction
/// hypothesis, exactly as the `Nat` original does.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_prod_range_congr_lt(d: &mut IntDev<'_>) -> Result<(), KernelError> {
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

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_pointwise_int(d, f, g, x);
        let lhs = d.const_app(p.prod_range, &[f, x]);
        let rhs = d.const_app(p.prod_range, &[g, x]);
        let eqn = d.ieq(lhs, rhs);
        d.arrow(hyp, eqn)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let zero = d.zero();
            let hyp_ty = bounded_pointwise_int(d, f, g, zero);
            let h_fv = d.fresh_fvar();
            let one_i = d.ione();
            let body = d.irefl(one_i);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_pointwise_int(d, f, g, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let h_lt_j = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let hk_ty = d.lt(k, j);
                let hk_fv = d.fresh_fvar();
                let hk = d.kernel().fvar(hk_fv);
                let le_succ_j = d.lemma(p.nat.le_succ, &[j]);
                let lifted = d.lemma(p.nat.lt_of_lt_of_le, &[k, j, sj, hk, le_succ_j]);
                let applied = d.apply(h, &[k, lifted]);
                let with_hk = d.lam_fv(hk_fv, hk_ty, applied);
                d.lam_fv(k_fv, nat, with_hk)
            };
            let sub1 = d.apply(ih, &[h_lt_j]);

            let lt_j_sj = d.lemma(p.nat.lt_succ_self, &[j]);
            let sub2 = d.apply(h, &[j, lt_j_sj]);

            let f_prior = d.const_app(p.prod_range, &[f, j]);
            let g_prior = d.const_app(p.prod_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let start = d.imul(f_prior, fj);
            let mid = d.imul(g_prior, fj);
            let h1 = d.icongr(f_prior, g_prior, sub1, &|d, t| d.imul(t, fj));
            let end = d.imul(g_prior, gj);
            let h2 = d.icongr(fj, gj, sub2, &|d, t| d.imul(g_prior, t));
            let (_e, body) = d.ichain(start, &[(mid, h1), (end, h2)]);

            d.lam_fv(h_fv, hyp_ty, body)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.prod_range_congr_lt, ty, value)
}

/// Proves `Eq Int (mul (mul a b) (mul x y)) (mul (mul a x) (mul b y))` — the
/// pure ring rearrangement [`declare_prod_range_mul`]'s successor step needs
/// to match the two ways of grouping four factors. Five steps, all
/// `mul_assoc`/`mul_comm`, mirroring [`super::wilson::diff_of_squares`]'s
/// nested-`icongr` idiom: `(a*b)*(x*y) = a*(b*(x*y)) = a*((b*x)*y) =
/// a*((x*b)*y) = a*(x*(b*y)) = (a*x)*(b*y)`.
fn mul_swap_inner(d: &mut IntDev<'_>, a: ExprId, b: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let p = d.int();
    let ab = d.imul(a, b);
    let xy = d.imul(x, y);
    let start = d.imul(ab, xy);

    // (a*b)*(x*y) = a*(b*(x*y))
    let bxy = d.imul(b, xy);
    let t1 = d.imul(a, bxy);
    let p1 = d.const_app(p.mul_assoc, &[a, b, xy]);

    // a*(b*(x*y)) = a*((b*x)*y)
    let bx = d.imul(b, x);
    let bx_y = d.imul(bx, y);
    let t2 = d.imul(a, bx_y);
    let assoc_bxy = d.const_app(p.mul_assoc, &[b, x, y]); // Eq (b*x)*y (b*(x*y))
    let assoc_bxy_rev = d.isymm(bx_y, bxy, assoc_bxy);
    let p2 = d.icongr(bxy, bx_y, assoc_bxy_rev, &|d, t| d.imul(a, t));

    // a*((b*x)*y) = a*((x*b)*y)
    let xb = d.imul(x, b);
    let xb_y = d.imul(xb, y);
    let t3 = d.imul(a, xb_y);
    let comm_bx = d.const_app(p.mul_comm, &[b, x]); // Eq (b*x) (x*b)
    let p3 = d.icongr(bx, xb, comm_bx, &|d, t| {
        let ty_ = d.imul(t, y);
        d.imul(a, ty_)
    });

    // a*((x*b)*y) = a*(x*(b*y))
    let by = d.imul(b, y);
    let x_by = d.imul(x, by);
    let t4 = d.imul(a, x_by);
    let assoc_xby = d.const_app(p.mul_assoc, &[x, b, y]); // Eq (x*b)*y (x*(b*y))
    let p4 = d.icongr(xb_y, x_by, assoc_xby, &|d, t| d.imul(a, t));

    // a*(x*(b*y)) = (a*x)*(b*y)
    let ax = d.imul(a, x);
    let end_ = d.imul(ax, by);
    let assoc_axby = d.const_app(p.mul_assoc, &[a, x, by]); // Eq (a*x)*(b*y) (a*(x*(b*y)))
    let assoc_axby_rev = d.isymm(end_, t4, assoc_axby);

    let (_e, proof) = d.ichain(
        start,
        &[
            (t1, p1),
            (t2, p2),
            (t3, p3),
            (t4, p4),
            (end_, assoc_axby_rev),
        ],
    );
    proof
}

/// `Int.prodRange_mul :
///   ∀ f g n, Eq Int (prodRange (fun k => mul (f k) (g k)) n)
///     (mul (prodRange f n) (prodRange g n))`
/// — a product of pointwise products is the product of the two products.
/// Induction on `n`: the base case is `mul_one` (both sides reduce to
/// `Int.one`, matching via `Int.mul_one one`); the successor step rewrites
/// the pointwise-product prior (`prodRange (fun k=>f k*g k) j`) through the
/// induction hypothesis and then regroups the four factors
/// `(Pf_j*Pg_j)*(f_j*g_j) = (Pf_j*f_j)*(Pg_j*g_j)` via [`mul_swap_inner`].
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_prod_range_mul(d: &mut IntDev<'_>) -> Result<(), KernelError> {
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

    // fg := fun k => mul (f k) (g k).
    let fg_lambda = |d: &mut IntDev<'_>| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let body = d.imul(fk, gk);
        d.lam_fv(k_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let fg = fg_lambda(d);
        let lhs = d.const_app(p.prod_range, &[fg, x]);
        let pf = d.const_app(p.prod_range, &[f, x]);
        let pg = d.const_app(p.prod_range, &[g, x]);
        let rhs = d.imul(pf, pg);
        d.ieq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let one_i = d.ione();
            let one_one = d.imul(one_i, one_i);
            let mul_one_pf = d.const_app(p.mul_one, &[one_i]); // Eq (one*one) one
            d.isymm(one_one, one_i, mul_one_pf)
        },
        &|d, j, ih| {
            // ih : Eq Int (prodRange fg j) (mul (prodRange f j) (prodRange g j))
            let pf_j = d.const_app(p.prod_range, &[f, j]);
            let pg_j = d.const_app(p.prod_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let fj_gj = d.imul(fj, gj);

            let pfg_j = {
                let fg = fg_lambda(d);
                d.const_app(p.prod_range, &[fg, j])
            };
            let start = d.imul(pfg_j, fj_gj);
            let pf_pg = d.imul(pf_j, pg_j);
            let mid = d.imul(pf_pg, fj_gj);
            let step1 = d.icongr(pfg_j, pf_pg, ih, &|d, t| d.imul(t, fj_gj));

            let end_ = mul_swap_inner(d, pf_j, pg_j, fj, gj);
            let (_e, proof) = d.ichain(start, &[(mid, step1)]);
            let pf_fj = d.imul(pf_j, fj);
            let pg_gj = d.imul(pg_j, gj);
            let final_target = d.imul(pf_fj, pg_gj);
            d.itrans(start, mid, final_target, proof, end_)
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(f_fv, fn_ty, over_g)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(f_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.prod_range_mul, ty, value)
}

/// `Int.modEq_prodRange_lt :
///   ∀ n f g m, 0 < n → (∀ k, Lt k m → ModEq n (f k) (g k)) →
///     ModEq n (prodRange f m) (prodRange g m)`
/// — [`declare_modeq_prod_range`]'s pointwise hypothesis weakened to indices
/// below the bound, mirroring [`declare_prod_range_congr_lt`]'s own
/// weakening of `declare_prod_range_congr` (`Eq Int` swapped for `ModEq n`,
/// `Int.ModEq.mul` in place of `icongr`). Needed because
/// [`super::wilson::declare_factorial_sq_modeq_one`]'s pointwise congruence
/// only holds for indices inside the factorial's own range — `Nat.inverseIndex`
/// composed with `Int.mul_inv_of_pow` needs `0 < a` and `a < p`, so the
/// unrestricted `declare_modeq_prod_range` cannot be fed it directly.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_modeq_prod_range_lt(d: &mut IntDev<'_>) -> Result<(), KernelError> {
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

    let bounded_pointwise = |d: &mut IntDev<'_>, bound: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hyp = d.lt(k, bound);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let eqn = super::modeq::imodeq(d, n, fk, gk);
        let body = d.arrow(hyp, eqn);
        d.pi_fv(k_fv, nat, body)
    };

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let hyp = bounded_pointwise(d, x);
        let pf = d.const_app(p.prod_range, &[f, x]);
        let pg = d.const_app(p.prod_range, &[g, x]);
        let concl = super::modeq::imodeq(d, n, pf, pg);
        d.arrow(hyp, concl)
    };
    let stmt_at_m = motive(d, m);

    let h_pos_fv = d.fresh_fvar();
    let h_pos = d.kernel().fvar(h_pos_fv);

    let proof_body = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let hyp_ty = bounded_pointwise(d, zero_n);
            let h_fv = d.fresh_fvar();
            let one_i = d.ione();
            let body = d.const_app(p.mod_eq_refl, &[n, one_i]);
            d.lam_fv(h_fv, hyp_ty, body)
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let hyp_ty = bounded_pointwise(d, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let h_lt_j = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let hk_ty = d.lt(k, j);
                let hk_fv = d.fresh_fvar();
                let hk = d.kernel().fvar(hk_fv);
                let le_succ_j = d.lemma(p.nat.le_succ, &[j]);
                let lifted = d.lemma(p.nat.lt_of_lt_of_le, &[k, j, sj, hk, le_succ_j]);
                let applied = d.apply(h, &[k, lifted]);
                let with_hk = d.lam_fv(hk_fv, hk_ty, applied);
                d.lam_fv(k_fv, nat, with_hk)
            };
            let sub1 = d.apply(ih, &[h_lt_j]);

            let lt_j_sj = d.lemma(p.nat.lt_succ_self, &[j]);
            let sub2 = d.apply(h, &[j, lt_j_sj]);

            let pf_j = d.const_app(p.prod_range, &[f, j]);
            let pg_j = d.const_app(p.prod_range, &[g, j]);
            let fj = d.apply(f, &[j]);
            let gj = d.apply(g, &[j]);
            let body = d.const_app(p.mod_eq_mul, &[n, pf_j, pg_j, fj, gj, h_pos, sub1, sub2]);

            d.lam_fv(h_fv, hyp_ty, body)
        },
        m,
    );

    let with_h_pos = d.lam_fv(h_pos_fv, pos_ty, proof_body);

    let value = {
        let with_m = d.lam_fv(m_fv, nat, with_h_pos);
        let with_g = d.lam_fv(g_fv, fn_ty, with_m);
        let with_f = d.lam_fv(f_fv, fn_ty, with_g);
        d.lam_fv(n_fv, int_ty, with_f)
    };
    let ty = {
        let inner = d.arrow(pos_ty, stmt_at_m);
        let with_m = d.pi_fv(m_fv, nat, inner);
        let with_g = d.pi_fv(g_fv, fn_ty, with_m);
        let with_f = d.pi_fv(f_fv, fn_ty, with_g);
        d.pi_fv(n_fv, int_ty, with_f)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mod_eq_prod_range_lt,
        uparams: vec![],
        ty,
        value,
    })
}

/// `fun (_ : Nat) => a` — the constant `Nat → Int` function `prodRange`
/// folds over in [`declare_prod_range_const_pow`].
fn const_int_fn(d: &mut IntDev<'_>, a: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    d.lam_fv(k_fv, nat, a)
}

/// `Int.prodRange_const_pow : ∀ a n, Eq Int (prodRange (fun _ => a) n) (pow a n)`
/// — a product of `n` copies of the same factor is that factor raised to the
/// `n`th power. Sized in ADR-0990 as the first missing piece of Gauss's
/// lemma's connecting-theorem assembly (`∏_{k=1}^m (a·k) = a^m · m!`, this
/// lemma supplying the `a^m` half once combined with `Int.prodRange_mul` and
/// `Int.factorial`'s own defeq unfold to `prodRange (fun k => ofNat (succ
/// k))`).
///
/// Induction on `n`: the base case is `Eq.refl one` (`prodRange _ zero` and
/// `pow a zero` both reduce to `Int.one` by δι alone, regardless of `a`); the
/// successor step is a single [`IntDev::icongr`] on the induction hypothesis
/// through `fun t => mul t a`, since `prodRange (const a) (succ j)` reduces
/// (via `prodRange_succ`) to `mul (prodRange (const a) j) a` and `pow a
/// (succ j)` reduces (via `pow_succ`) to the identical shape `mul (pow a j)
/// a` — no case split needed anywhere, unlike the sign-selected products
/// this lemma's sibling ([`super::euler_theorem::declare_prod_range_if_const_eq_pow_count`])
/// needs.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_prod_range_const_pow(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let p = d.int();
        let ca = const_int_fn(d, a);
        let lhs = d.const_app(p.prod_range, &[ca, x]);
        let rhs = d.ipow(a, x);
        d.ieq(lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let one_i = d.ione();
            d.irefl(one_i)
        },
        &|d, j, ih| {
            // ih : Eq Int (prodRange (const a) j) (pow a j).
            let ca = const_int_fn(d, a);
            let p = d.int();
            let pr_j = d.const_app(p.prod_range, &[ca, j]);
            let pow_a_j = d.ipow(a, j);
            d.icongr(pr_j, pow_a_j, ih, &|d, t| d.imul(t, a))
        },
        n,
    );

    let ty = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        d.pi_fv(a_fv, int_ty, with_n)
    };
    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(a_fv, int_ty, with_n)
    };
    d.declare_theorem(p.prod_range_const_pow, ty, value)
}

/// `Int.prodRange_swap_adjacent` — swapping `f`'s values at one adjacent pair
/// of indices `(i, succ i)` leaves the product unchanged, given `g` supplied
/// (not computed) with the two matching values and full agreement elsewhere.
///
/// # Why `g` is a parameter, not a computed swap function
///
/// The natural statement would build `g` internally
/// (`g k := if k = i then f (succ i) else if k = succ i then f i else f k`),
/// but computing that `Nat`-valued conditional needs `Nat.beq` case analysis
/// (this development's decidable-equality route — see
/// `nat_prelude/finite.rs`'s status note on the pigeonhole principle for the
/// same trade-off from the other side). Taking `g` and the two connecting
/// equations as hypotheses instead makes this lemma strictly more general
/// (any `g` satisfying the three hypotheses closes it, whether or not it was
/// built by a case split) and needs no decidable-equality machinery at all —
/// only the already-proved decidable *order* (`Nat.lt_of_lt_of_le`,
/// `Nat.le_succ`, `Nat.le_add_right`, `Nat.le_trans`, `Nat.lt_succ_self`) that
/// [`declare_prod_range_congr_lt`] already uses. It is also exactly the shape
/// `prodRange_permute`'s adjacent-transposition induction (`prod_range.rs`'s
/// future extension) will supply `g` as: a fully rearranged function it
/// already has in hand, not one this lemma needs to construct.
///
/// # Route
///
/// `Lt (succ i) n` is definitionally `Le (succ (succ i)) n`
/// (`Nat.lt x y := Nat.le (succ x) y`), so `Nat.le_dest` reads off a witness
/// `m` with `succ (succ i) + m = n`. Induction on `m` proves the *offset*
/// statement `Eq Int (prodRange f (succ (succ i) + m)) (prodRange g (…))`
/// directly (both `Nat.add _ (succ _)` and `Int.prodRange _ (succ _)` unfold
/// definitionally, so the successor step needs only [`declare_prod_range_congr_lt`]'s
/// four order lemmas — `succ (succ i) + m` always exceeds `succ i`, hence `i` —
/// to invoke the agreement hypothesis at the fresh factor's index, plus the
/// induction hypothesis and `Int.mul_assoc`/`Int.mul_comm` congruence, exactly
/// as [`declare_prod_range_congr_lt`]'s own step does); transporting along
/// `Nat.le_dest`'s witness equation then replaces `succ (succ i) + m` with the
/// original `n`. The base case (`m = 0`) is the one genuinely new piece of
/// algebra: both sides reduce (by the same two unfoldings) to
/// `(prodRange _ i * _ i) * _ (succ i)`, and matching them needs
/// [`declare_prod_range_congr_lt`] once (at bound `i`, using that `f`/`g` agree
/// on every index below `i`, since those are never `i` or `succ i`) plus the
/// rearrangement `(Q*a)*b = (Q*b)*a` from `Int.mul_assoc`/`Int.mul_comm`.
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_prod_range_swap_adjacent(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let si = d.succ(i);
    let hyp_range = d.lt(si, n);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let f_si = d.apply(f, &[si]);
    let g_si = d.apply(g, &[si]);
    let hyp_gi = d.ieq(gi, f_si);
    let hyp_gsi = d.ieq(g_si, fi);
    let hyp_agree = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let eq_ki = d.eq(k, i);
        let ne_ki = d.not(eq_ki);
        let eq_ksi = d.eq(k, si);
        let ne_ksi = d.not(eq_ksi);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let concl = d.ieq(fk, gk);
        let inner = d.arrow(ne_ksi, concl);
        let step = d.arrow(ne_ki, inner);
        d.pi_fv(k_fv, nat, step)
    };

    let lhs_final = d.const_app(p.prod_range, &[f, n]);
    let rhs_final = d.const_app(p.prod_range, &[g, n]);
    let conclusion = d.ieq(lhs_final, rhs_final);

    let stmt = {
        let with_agree = d.arrow(hyp_agree, conclusion);
        let with_gsi = d.arrow(hyp_gsi, with_agree);
        let with_gi = d.arrow(hyp_gi, with_gsi);
        d.arrow(hyp_range, with_gi)
    };

    let range_fv = d.fresh_fvar();
    let h_range = d.kernel().fvar(range_fv);
    let gi_fv = d.fresh_fvar();
    let h_gi = d.kernel().fvar(gi_fv);
    let gsi_fv = d.fresh_fvar();
    let h_gsi = d.kernel().fvar(gsi_fv);
    let agree_fv = d.fresh_fvar();
    let h_agree = d.kernel().fvar(agree_fv);

    let si2 = d.succ(si);
    let one = d.level_one();

    // pointwise_lt_i : ∀ k, Lt k i → Eq Int (f k) (g k), from `h_agree` plus
    // `k < i → k ≠ i` and `k < i → k ≠ succ i` (via `k < i < succ i`).
    let pointwise_lt_i = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, i);
        let ne_ki = ne_of_lt(d, k, i, hk);
        let le_i_si = d.lemma(p.nat.le_succ, &[i]);
        let lt_k_si = d.lemma(p.nat.lt_of_lt_of_le, &[k, i, si, hk, le_i_si]);
        let ne_ksi = ne_of_lt(d, k, si, lt_k_si);
        let body = d.apply(h_agree, &[k, ne_ki, ne_ksi]);
        let with_hk = d.lam_fv(hk_fv, hk_ty, body);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let p_f_i = d.const_app(p.prod_range, &[f, i]);
    let p_g_i = d.const_app(p.prod_range, &[g, i]);
    let base_eq1 = d.lemma(p.prod_range_congr_lt, &[f, g, i, pointwise_lt_i]);

    // Base-case algebra: (Pf_i * fi) * f_si = (Pg_i * gi) * g_si, closing
    // `motive zero` (defeq to `Eq Int (prodRange f (succ (succ i)))
    // (prodRange g (succ (succ i)))`) via `mul_assoc`/`mul_comm` and the three
    // connecting equalities.
    let base_proof = {
        let start = d.imul(p_f_i, fi);
        let start = d.imul(start, f_si);

        let a_times_b = d.imul(fi, f_si);
        let t1 = d.imul(p_f_i, a_times_b);
        let assoc1 = d.lemma(p.mul_assoc, &[p_f_i, fi, f_si]);

        let b_times_a = d.imul(f_si, fi);
        let t2 = d.imul(p_f_i, b_times_a);
        let mul_comm_ab = d.lemma(p.mul_comm, &[fi, f_si]);
        let step_comm = d.icongr(a_times_b, b_times_a, mul_comm_ab, &|d, t| d.imul(p_f_i, t));

        let pf_i_f_si = d.imul(p_f_i, f_si);
        let t3 = d.imul(pf_i_f_si, fi);
        let assoc2_raw = d.lemma(p.mul_assoc, &[p_f_i, f_si, fi]);
        let assoc2_rev = d.isymm(t3, t2, assoc2_raw);

        let pg_i_f_si = d.imul(p_g_i, f_si);
        let t4 = d.imul(pg_i_f_si, fi);
        let step_eq1 = d.icongr(p_f_i, p_g_i, base_eq1, &|d, t| {
            let inner = d.imul(t, f_si);
            d.imul(inner, fi)
        });

        let pg_i_gi = d.imul(p_g_i, gi);
        let t5 = d.imul(pg_i_gi, fi);
        let sym_gi = d.isymm(gi, f_si, h_gi);
        let step_gi = d.icongr(f_si, gi, sym_gi, &|d, t| {
            let inner = d.imul(p_g_i, t);
            d.imul(inner, fi)
        });

        let pg_i_gi2 = d.imul(p_g_i, gi);
        let t6 = d.imul(pg_i_gi2, g_si);
        let sym_gsi = d.isymm(g_si, fi, h_gsi);
        let step_gsi = d.icongr(fi, g_si, sym_gsi, &|d, t| {
            let inner = d.imul(p_g_i, gi);
            d.imul(inner, t)
        });

        let (_e, proof) = d.ichain(
            start,
            &[
                (t1, assoc1),
                (t2, step_comm),
                (t3, assoc2_rev),
                (t4, step_eq1),
                (t5, step_gi),
                (t6, step_gsi),
            ],
        );
        proof
    };

    // motive(m) := Eq Int (prodRange f (add si2 m)) (prodRange g (add si2 m)).
    let motive = |d: &mut IntDev<'_>, m: ExprId| -> ExprId {
        let xm = d.add(si2, m);
        let lhs = d.const_app(p.prod_range, &[f, xm]);
        let rhs = d.const_app(p.prod_range, &[g, xm]);
        d.ieq(lhs, rhs)
    };

    let claim = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
        d.induct(
            &motive,
            &|_d| base_proof,
            &|d, m, ih| {
                let xm = d.add(si2, m);

                let le_si_si2 = d.lemma(p.nat.le_succ, &[si]);
                let le_si2_xm = d.lemma(p.nat.le_add_right, &[si2, m]);
                let le_si_xm = d.lemma(p.nat.le_trans, &[si, si2, xm, le_si_si2, le_si2_xm]);
                let lt_i_si = d.lemma(p.nat.lt_succ_self, &[i]);
                let lt_i_xm = d.lemma(p.nat.lt_of_lt_of_le, &[i, si, xm, lt_i_si, le_si_xm]);

                let lt_si_si2 = d.lemma(p.nat.lt_succ_self, &[si]);
                let lt_si_xm = d.lemma(p.nat.lt_of_lt_of_le, &[si, si2, xm, lt_si_si2, le_si2_xm]);

                let ne_xm_i = ne_of_lt_symm(d, i, xm, lt_i_xm);
                let ne_xm_si = ne_of_lt_symm(d, si, xm, lt_si_xm);
                let fxm_eq_gxm = d.apply(h_agree, &[xm, ne_xm_i, ne_xm_si]);

                let f_prior = d.const_app(p.prod_range, &[f, xm]);
                let g_prior = d.const_app(p.prod_range, &[g, xm]);
                let fxm = d.apply(f, &[xm]);
                let gxm = d.apply(g, &[xm]);
                let start = d.imul(f_prior, fxm);
                let mid = d.imul(g_prior, fxm);
                let h1 = d.icongr(f_prior, g_prior, ih, &|d, t| d.imul(t, fxm));
                let end = d.imul(g_prior, gxm);
                let h2 = d.icongr(fxm, gxm, fxm_eq_gxm, &|d, t| d.imul(g_prior, t));
                let (_e, body) = d.ichain(start, &[(mid, h1), (end, h2)]);
                body
            },
            k,
        )
    };

    // Exists.rec over `Nat.le_dest si2 n h_range : Exists (fun k => si2+k=n)`.
    let existential = d.lemma(p.nat.le_dest, &[si2, n, h_range]);
    let pred = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sum = d.add(si2, k);
        let body = d.eq(sum, n);
        d.lam_fv(k_fv, nat, body)
    };
    let exists_ty = {
        let ex = d.kernel().const_(p.logic.exists_, vec![one]);
        d.apply(ex, &[nat, pred])
    };
    let anon = d.anon_name();
    let motive_outer = d
        .kernel()
        .lam(anon, exists_ty, conclusion, BinderInfo::Default);
    let minor = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let sum = d.add(si2, k);
        let e_ty = d.eq(sum, n);

        let claim_k = claim(d, k);
        // NOTE: the equality being eliminated (`e : Eq Nat sum n`) is a `Nat`
        // equality even though the motive's BODY talks about `Int` — so this
        // is `eq_motive`/`transport` (the generic `NatOps` pair, `Nat`
        // carrier), not `ieq_motive`/`itransport` (which fix the carrier to
        // `Int` and would reject `e` outright).
        let transport_motive = d.eq_motive(sum, &|d, x| {
            let lhs = d.const_app(p.prod_range, &[f, x]);
            let rhs = d.const_app(p.prod_range, &[g, x]);
            d.ieq(lhs, rhs)
        });
        let final_claim = d.transport(sum, transport_motive, claim_k, n, e);
        let with_e = d.lam_fv(e_fv, e_ty, final_claim);
        d.lam_fv(k_fv, nat, with_e)
    };
    let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    let proof_body = d.apply(exists_rec, &[nat, pred, motive_outer, minor, existential]);

    let value = {
        let with_agree = d.lam_fv(agree_fv, hyp_agree, proof_body);
        let with_gsi = d.lam_fv(gsi_fv, hyp_gsi, with_agree);
        let with_gi = d.lam_fv(gi_fv, hyp_gi, with_gsi);
        d.lam_fv(range_fv, hyp_range, with_gi)
    };

    // Close the outer quantifiers: ∀ (f g : Nat → Int) (i n : Nat), stmt.
    let full_stmt = {
        let with_n = d.pi_fv(n_fv, nat, stmt);
        let with_i = d.pi_fv(i_fv, nat, with_n);
        let with_g = d.pi_fv(g_fv, fn_ty, with_i);
        d.pi_fv(f_fv, fn_ty, with_g)
    };
    let full_value = {
        let with_n = d.lam_fv(n_fv, nat, value);
        let with_i = d.lam_fv(i_fv, nat, with_n);
        let with_g = d.lam_fv(g_fv, fn_ty, with_i);
        d.lam_fv(f_fv, fn_ty, with_g)
    };

    d.declare_theorem(p.prod_range_swap_adjacent, full_stmt, full_value)
}

// ---------------------------------------------------------------------------
// `Int.prodRange_swap` — the general transposition (any `i < j`, not just
// adjacent indices).
// ---------------------------------------------------------------------------
//
// `Int.prodRange_swap : ∀ f g i j n, Lt i j → Lt j n → Eq Int (g i) (f j) →
// Eq Int (g j) (f i) → (∀ k, Not (Eq Nat k i) → Not (Eq Nat k j) →
// Eq Int (f k) (g k)) → Eq Int (prodRange f n) (prodRange g n)` — stated the
// way `prodRange_swap_adjacent` is (`g` supplied by hypothesis, not computed),
// for the same reason: it keeps the CALLER free of decidable equality. This
// proof cannot avoid decidable equality itself, though — unlike
// `swap_adjacent`, whose caller always already holds the rearranged partner
// function, THIS theorem has to build one, for two indices that may be
// arbitrarily far apart. It does so with `point_swap` (below), an explicit
// `Nat.ble`-cascaded case-split (never `Nat.beq`) generalizing
// `nat_prelude/finite.rs`'s pigeonhole `compact` from one cut point to two.
//
// Route: extract `d` with `Nat.le_dest (succ i) j (Lt i j)`, so
// `j = add (succ i) d`, and induct on `d` (generalized over `f`, `g` — the
// recursive call needs a DIFFERENT pair, exactly as the pigeonhole's own
// induction generalizes over `f`). Base (`d = zero`): `j` is definitionally
// `succ i`, so the goal literally IS `prod_range_swap_adjacent`'s statement.
// Step (`d = succ d'`, `j' := add (succ i) d'`, so `j = succ j'`
// definitionally): conjugate through the identity
// `(j' j) ∘ (i j') ∘ (j' j) = (i j)` — `A := point_swap f j' j` (adjacent),
// `prod_range_swap_adjacent(f, A, j', n)`; `B := point_swap A i j'` (gap `d'`,
// the induction hypothesis's OWN canonical partner for `A`, supplied to it);
// `C := point_swap B j' j` (adjacent again),
// `prod_range_swap_adjacent(B, C, j', n)`. `C` and the caller's `g` then agree
// pointwise everywhere (six live regions relative to `i`, `j'`, `j`, worked
// out by [`swap_conjugation_agrees_with_g`]; a seventh, `j' < k < j`, is
// impossible since `j = succ j'` and closes by contradiction), so
// `Int.prodRange_congr` closes `prodRange C n = prodRange g n`.

/// `Bool.rec.{1}` selecting between two `Int` values — the `Int` counterpart
/// of `NatOps::bool_select_nat`, which is hardwired to `Nat`.
pub(super) fn bool_select_int(
    d: &mut IntDev<'_>,
    condition: ExprId,
    on_true: ExprId,
    on_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let int_ty = d.int_ty();
    let anon = d.anon_name();
    let motive = d.kernel().lam(anon, bool_ty, int_ty, BinderInfo::Default);
    let one = d.level_one();
    let bool_rec = d.int().logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![one]);
    d.apply(rec, &[motive, on_false, on_true, condition])
}

/// `heq : Eq Bool cond true ⊢ Eq Int (bool_select_int cond a b) a`.
pub(super) fn select_int_true(
    d: &mut IntDev<'_>,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
    let true_val = d.bool_true();
    let symm_hb = d.bool_symm(cond, true_val, heq);
    let motive = d.bool_eq_motive(true_val, &|d, value| {
        let sel = bool_select_int(d, value, a, b);
        d.ieq(sel, a)
    });
    let refl_case = d.irefl(a);
    d.bool_transport(true_val, motive, refl_case, cond, symm_hb)
}

/// `heq : Eq Bool cond false ⊢ Eq Int (bool_select_int cond a b) b`.
pub(super) fn select_int_false(
    d: &mut IntDev<'_>,
    cond: ExprId,
    a: ExprId,
    b: ExprId,
    heq: ExprId,
) -> ExprId {
    let false_val = d.bool_false();
    let symm_hb = d.bool_symm(cond, false_val, heq);
    let motive = d.bool_eq_motive(false_val, &|d, value| {
        let sel = bool_select_int(d, value, a, b);
        d.ieq(sel, b)
    });
    let refl_case = d.irefl(b);
    d.bool_transport(false_val, motive, refl_case, cond, symm_hb)
}

/// `h : Lt a b ⊢ Le a b` — weaken a strict order fact by one step
/// (`Nat.le_succ` + `Nat.le_trans`).
pub(super) fn nat_le_of_lt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let sa = d.succ(a);
    let le_a_sa = d.lemma(p.nat.le_succ, &[a]);
    d.lemma(p.nat.le_trans, &[a, sa, b, le_a_sa, h])
}

/// `h : Lt b a ⊢ Eq Bool (Nat.ble a b) false` — the "generalize the selector,
/// then instantiate at `bool_refl(condition)`" trick
/// `nat_prelude/finite.rs`'s `compact_eq_of_gt` uses, extracted generically:
/// `point_swap`'s nested selection needs this fact at every level, not once.
pub(super) fn ble_eq_false_of_lt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h_lt: ExprId) -> ExprId {
    let p = d.int();
    let cond = d.ble(a, b);
    let false_val = d.bool_false();
    let true_val = d.bool_true();
    let bool_ty = d.bool_ty();

    let branch_for = |d: &mut IntDev<'_>, selector: ExprId| -> ExprId {
        let eq_cond_sel = d.bool_eq(cond, selector);
        let concl = d.bool_eq(selector, false_val);
        d.arrow(eq_cond_sel, concl)
    };
    let false_minor = {
        let heq_fv = d.fresh_fvar();
        let heq_ty = d.bool_eq(cond, false_val);
        let body = d.bool_refl(false_val);
        d.lam_fv(heq_fv, heq_ty, body)
    };
    let true_minor = {
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let heq_ty = d.bool_eq(cond, true_val);
        let a_le_b = d.lemma(p.nat.le_of_ble_eq_true, &[a, b, heq]);
        let succ_b = d.succ(b);
        let succ_b_le_b = d.lemma(p.nat.le_trans, &[succ_b, a, b, h_lt, a_le_b]);
        let false_pf = d.lemma(p.nat.not_succ_le_self, &[b, succ_b_le_b]);
        let concl_ty = d.bool_eq(true_val, false_val);
        let body = d.absurd(concl_ty, false_pf);
        d.lam_fv(heq_fv, heq_ty, body)
    };
    let motive = {
        let sel_fv = d.fresh_fvar();
        let sel = d.kernel().fvar(sel_fv);
        let body = branch_for(d, sel);
        d.lam_fv(sel_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.int().logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![level_zero]);
    let selected = d.apply(rec, &[motive, false_minor, true_minor, cond]);
    let cond_refl = d.bool_refl(cond);
    d.apply(selected, &[cond_refl])
}

// --- `point_swap`: the concrete two-point swap `compact` never needed -----

/// `point_swap f p q`'s outermost (4th) layer: for `k > q`, `f k`; for
/// `k = q`, `f p` — the two cases [`ps_level3`] delegates to.
fn ps_level4(d: &mut IntDev<'_>, f: ExprId, p_idx: ExprId, q_idx: ExprId, k: ExprId) -> ExprId {
    let fp = d.apply(f, &[p_idx]);
    let fk = d.apply(f, &[k]);
    let le_k_q = d.ble(k, q_idx);
    bool_select_int(d, le_k_q, fp, fk)
}

/// `point_swap f p q`'s 3rd layer: for `p < k < q`, `f k`; else [`ps_level4`].
fn ps_level3(d: &mut IntDev<'_>, f: ExprId, p_idx: ExprId, q_idx: ExprId, k: ExprId) -> ExprId {
    let fk = d.apply(f, &[k]);
    let level4 = ps_level4(d, f, p_idx, q_idx, k);
    let sk = d.succ(k);
    let lt_k_q = d.ble(sk, q_idx);
    bool_select_int(d, lt_k_q, fk, level4)
}

/// `point_swap f p q`'s 2nd layer: for `k = p`, `f q`; else [`ps_level3`].
fn ps_level2(d: &mut IntDev<'_>, f: ExprId, p_idx: ExprId, q_idx: ExprId, k: ExprId) -> ExprId {
    let fq = d.apply(f, &[q_idx]);
    let level3 = ps_level3(d, f, p_idx, q_idx, k);
    let le_k_p = d.ble(k, p_idx);
    bool_select_int(d, le_k_p, fq, level3)
}

/// `point_swap f p q k` — the value at `k` of `f` with the values at `p` and
/// `q` (`p < q`, supplied by the caller) exchanged: `f q` at `p`, `f p` at
/// `q`, `f k` everywhere else. Four nested `Nat.ble` case-splits, never
/// `Nat.beq` — the same convention `nat_prelude/finite.rs`'s pigeonhole
/// `compact` uses, generalized from one cut point to two.
///
/// [`point_swap_eq_lt_p`], [`point_swap_eq_at_p`], [`point_swap_eq_between`],
/// [`point_swap_eq_at_q`], and [`point_swap_eq_gt_q`] are this function's five
/// correctness facts, one per region a `k` can fall in relative to `p < q`.
pub(super) fn point_swap(
    d: &mut IntDev<'_>,
    f: ExprId,
    p_idx: ExprId,
    q_idx: ExprId,
    k: ExprId,
) -> ExprId {
    let fk = d.apply(f, &[k]);
    let level2 = ps_level2(d, f, p_idx, q_idx, k);
    let sk = d.succ(k);
    let lt_k_p = d.ble(sk, p_idx);
    bool_select_int(d, lt_k_p, fk, level2)
}

/// `h : Lt k p ⊢ Eq Int (point_swap f p q k) (f k)`.
pub(super) fn point_swap_eq_lt_p(
    d: &mut IntDev<'_>,
    f: ExprId,
    p_idx: ExprId,
    q_idx: ExprId,
    k: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let fk = d.apply(f, &[k]);
    let level2 = ps_level2(d, f, p_idx, q_idx, k);
    let sk = d.succ(k);
    let lt_k_p = d.ble(sk, p_idx);
    let lt_true = d.lemma(p.nat.ble_eq_true_of_le, &[sk, p_idx, h]);
    select_int_true(d, lt_k_p, fk, level2, lt_true)
}

/// `Eq Int (point_swap f p q p) (f q)`.
pub(super) fn point_swap_eq_at_p(
    d: &mut IntDev<'_>,
    f: ExprId,
    p_idx: ExprId,
    q_idx: ExprId,
) -> ExprId {
    let p = d.int();
    let fk = d.apply(f, &[p_idx]);
    let fq = d.apply(f, &[q_idx]);
    let level2 = ps_level2(d, f, p_idx, q_idx, p_idx);
    let level3 = ps_level3(d, f, p_idx, q_idx, p_idx);
    let sp = d.succ(p_idx);
    let lt_k_p = d.ble(sp, p_idx);
    let lt_succ_self_p = d.lemma(p.nat.lt_succ_self, &[p_idx]);
    let lt_false = ble_eq_false_of_lt(d, sp, p_idx, lt_succ_self_p);
    let step1 = select_int_false(d, lt_k_p, fk, level2, lt_false);
    let le_k_p = d.ble(p_idx, p_idx);
    let le_refl_p = d.lemma(p.nat.le_refl, &[p_idx]);
    let le_true = d.lemma(p.nat.ble_eq_true_of_le, &[p_idx, p_idx, le_refl_p]);
    let step2 = select_int_true(d, le_k_p, fq, level3, le_true);
    let start = point_swap(d, f, p_idx, q_idx, p_idx);
    let (_, proof) = d.ichain(start, &[(level2, step1), (fq, step2)]);
    proof
}

/// `h1 : Lt p k, h2 : Lt k q ⊢ Eq Int (point_swap f p q k) (f k)`.
#[allow(clippy::too_many_arguments)]
pub(super) fn point_swap_eq_between(
    d: &mut IntDev<'_>,
    f: ExprId,
    p_idx: ExprId,
    q_idx: ExprId,
    k: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let p = d.int();
    let fk = d.apply(f, &[k]);
    let fq = d.apply(f, &[q_idx]);
    let level2 = ps_level2(d, f, p_idx, q_idx, k);
    let level3 = ps_level3(d, f, p_idx, q_idx, k);
    let level4 = ps_level4(d, f, p_idx, q_idx, k);
    let sk = d.succ(k);

    let le_succ_k = d.lemma(p.nat.le_succ, &[k]);
    let lt_p_sk = d.lemma(p.nat.lt_of_lt_of_le, &[p_idx, k, sk, h1, le_succ_k]);
    let lt_k_p = d.ble(sk, p_idx);
    let lt_k_p_false = ble_eq_false_of_lt(d, sk, p_idx, lt_p_sk);
    let step1 = select_int_false(d, lt_k_p, fk, level2, lt_k_p_false);

    let le_k_p = d.ble(k, p_idx);
    let le_k_p_false = ble_eq_false_of_lt(d, k, p_idx, h1);
    let step2 = select_int_false(d, le_k_p, fq, level3, le_k_p_false);

    let lt_k_q = d.ble(sk, q_idx);
    let lt_k_q_true = d.lemma(p.nat.ble_eq_true_of_le, &[sk, q_idx, h2]);
    let step3 = select_int_true(d, lt_k_q, fk, level4, lt_k_q_true);

    let start = point_swap(d, f, p_idx, q_idx, k);
    let (_, proof) = d.ichain(start, &[(level2, step1), (level3, step2), (fk, step3)]);
    proof
}

/// `h_pq : Lt p q ⊢ Eq Int (point_swap f p q q) (f p)`.
pub(super) fn point_swap_eq_at_q(
    d: &mut IntDev<'_>,
    f: ExprId,
    p_idx: ExprId,
    q_idx: ExprId,
    h_pq: ExprId,
) -> ExprId {
    let p = d.int();
    let fk = d.apply(f, &[q_idx]);
    let fp = d.apply(f, &[p_idx]);
    let level2 = ps_level2(d, f, p_idx, q_idx, q_idx);
    let level3 = ps_level3(d, f, p_idx, q_idx, q_idx);
    let level4 = ps_level4(d, f, p_idx, q_idx, q_idx);
    let sq = d.succ(q_idx);

    let le_succ_q = d.lemma(p.nat.le_succ, &[q_idx]);
    let lt_p_sq = d.lemma(p.nat.lt_of_lt_of_le, &[p_idx, q_idx, sq, h_pq, le_succ_q]);
    let lt_k_p = d.ble(sq, p_idx);
    let lt_k_p_false = ble_eq_false_of_lt(d, sq, p_idx, lt_p_sq);
    let step1 = select_int_false(d, lt_k_p, fk, level2, lt_k_p_false);

    let le_k_p = d.ble(q_idx, p_idx);
    let le_k_p_false = ble_eq_false_of_lt(d, q_idx, p_idx, h_pq);
    let step2 = select_int_false(d, le_k_p, fk, level3, le_k_p_false);

    let lt_succ_self_q = d.lemma(p.nat.lt_succ_self, &[q_idx]);
    let lt_k_q = d.ble(sq, q_idx);
    let lt_k_q_false = ble_eq_false_of_lt(d, sq, q_idx, lt_succ_self_q);
    let step3 = select_int_false(d, lt_k_q, fk, level4, lt_k_q_false);

    let le_refl_q = d.lemma(p.nat.le_refl, &[q_idx]);
    let le_k_q = d.ble(q_idx, q_idx);
    let le_k_q_true = d.lemma(p.nat.ble_eq_true_of_le, &[q_idx, q_idx, le_refl_q]);
    let step4 = select_int_true(d, le_k_q, fp, fk, le_k_q_true);

    let start = point_swap(d, f, p_idx, q_idx, q_idx);
    let (_, proof) = d.ichain(
        start,
        &[
            (level2, step1),
            (level3, step2),
            (level4, step3),
            (fp, step4),
        ],
    );
    proof
}

/// `h_pq : Lt p q, h : Lt q k ⊢ Eq Int (point_swap f p q k) (f k)`.
#[allow(clippy::too_many_arguments)]
pub(super) fn point_swap_eq_gt_q(
    d: &mut IntDev<'_>,
    f: ExprId,
    p_idx: ExprId,
    q_idx: ExprId,
    k: ExprId,
    h_pq: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let fk = d.apply(f, &[k]);
    let fq = d.apply(f, &[q_idx]);
    let fp = d.apply(f, &[p_idx]);
    let level2 = ps_level2(d, f, p_idx, q_idx, k);
    let level3 = ps_level3(d, f, p_idx, q_idx, k);
    let level4 = ps_level4(d, f, p_idx, q_idx, k);
    let sk = d.succ(k);

    let le_p_q = nat_le_of_lt(d, p_idx, q_idx, h_pq);
    let lt_p_k = d.lemma(p.nat.lt_of_le_of_lt, &[p_idx, q_idx, k, le_p_q, h]);

    let le_succ_k = d.lemma(p.nat.le_succ, &[k]);
    let lt_p_sk = d.lemma(p.nat.lt_of_lt_of_le, &[p_idx, k, sk, lt_p_k, le_succ_k]);
    let lt_k_p = d.ble(sk, p_idx);
    let lt_k_p_false = ble_eq_false_of_lt(d, sk, p_idx, lt_p_sk);
    let step1 = select_int_false(d, lt_k_p, fk, level2, lt_k_p_false);

    let le_k_p = d.ble(k, p_idx);
    let le_k_p_false = ble_eq_false_of_lt(d, k, p_idx, lt_p_k);
    let step2 = select_int_false(d, le_k_p, fq, level3, le_k_p_false);

    let lt_q_sk = d.lemma(p.nat.lt_of_lt_of_le, &[q_idx, k, sk, h, le_succ_k]);
    let lt_k_q = d.ble(sk, q_idx);
    let lt_k_q_false = ble_eq_false_of_lt(d, sk, q_idx, lt_q_sk);
    let step3 = select_int_false(d, lt_k_q, fk, level4, lt_k_q_false);

    let le_k_q = d.ble(k, q_idx);
    let le_k_q_false = ble_eq_false_of_lt(d, k, q_idx, h);
    let step4 = select_int_false(d, le_k_q, fp, fk, le_k_q_false);

    let start = point_swap(d, f, p_idx, q_idx, k);
    let (_, proof) = d.ichain(
        start,
        &[
            (level2, step1),
            (level3, step2),
            (level4, step3),
            (fk, step4),
        ],
    );
    proof
}

// --- order trichotomy, rebuilt for `IntDev` --------------------------------

/// `Or (Lt a b) (Or (Eq Nat a b) (Lt b a))`, via `Nat.le_total` +
/// `Nat.lt_or_eq_of_le` — the `IntDev` counterpart of
/// `nat_prelude/finite.rs`'s private `trichotomy` (typed over `NatDev`, so
/// not reusable here without a signature change to that file).
pub(super) fn nat_trichotomy(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let p = d.int();
    let lt_ab = d.lt(a, b);
    let eq_ab = d.eq(a, b);
    let lt_ba = d.lt(b, a);
    let inner = d.or(eq_ab, lt_ba);
    let target = d.or(lt_ab, inner);

    let total = d.lemma(p.nat.le_total, &[a, b]);
    let le_ab = d.le(a, b);
    let le_ba = d.le(b, a);

    let on_left = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
        let sub = d.lemma(p.nat.lt_or_eq_of_le, &[a, b, h]);
        let on1 = &|d: &mut IntDev<'_>, h2: ExprId| d.or_inl(lt_ab, inner, h2);
        let on2 = &|d: &mut IntDev<'_>, h2: ExprId| {
            let mid = d.or_inl(eq_ab, lt_ba, h2);
            d.or_inr(lt_ab, inner, mid)
        };
        d.or_elim(lt_ab, eq_ab, target, sub, on1, on2)
    };
    let on_right = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
        let sub = d.lemma(p.nat.lt_or_eq_of_le, &[b, a, h]);
        let eq_ba = d.eq(b, a);
        // `sub : Or (Lt b a) (Eq Nat b a)` — LEFT is `Lt b a`, RIGHT is
        // `Eq Nat b a` (`lt_or_eq_of_le`'s own disjunct order), so `on1` here
        // must handle `Lt b a` and `on2` must handle `Eq Nat b a`.
        let on1 = &|d: &mut IntDev<'_>, h2: ExprId| {
            let mid = d.or_inr(eq_ab, lt_ba, h2);
            d.or_inr(lt_ab, inner, mid)
        };
        let on2 = &|d: &mut IntDev<'_>, h2: ExprId| {
            let eq_ab_pf = d.symm(b, a, h2);
            let mid = d.or_inl(eq_ab, lt_ba, eq_ab_pf);
            d.or_inr(lt_ab, inner, mid)
        };
        d.or_elim(lt_ba, eq_ba, target, sub, on1, on2)
    };
    d.or_elim(le_ab, le_ba, target, total, on_left, on_right)
}

/// `tri : Or (Lt a b) (Or (Eq Nat a b) (Lt b a))`, `not_eq : Not (Eq Nat a b)`
/// `⊢ Or (Lt a b) (Lt b a)` — eliminate the middle case of [`nat_trichotomy`].
pub(super) fn nat_two_way(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    tri: ExprId,
    not_eq: ExprId,
) -> ExprId {
    let lt_ab = d.lt(a, b);
    let eq_ab = d.eq(a, b);
    let lt_ba = d.lt(b, a);
    let inner = d.or(eq_ab, lt_ba);
    let target = d.or(lt_ab, lt_ba);

    let on_left = &|d: &mut IntDev<'_>, h: ExprId| d.or_inl(lt_ab, lt_ba, h);
    let on_right = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
        let sub_left = &|d: &mut IntDev<'_>, h2: ExprId| {
            let false_pf = d.apply(not_eq, &[h2]);
            d.absurd(target, false_pf)
        };
        let sub_right = &|d: &mut IntDev<'_>, h2: ExprId| d.or_inr(lt_ab, lt_ba, h2);
        d.or_elim(eq_ab, lt_ba, target, h, sub_left, sub_right)
    };
    d.or_elim(lt_ab, inner, target, tri, on_left, on_right)
}

/// `Not (Eq Nat a b) ⊢ Or (Lt a b) (Lt b a)`.
pub(super) fn nat_lt_or_gt_of_ne(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    not_eq: ExprId,
) -> ExprId {
    let tri = nat_trichotomy(d, a, b);
    nat_two_way(d, a, b, tri, not_eq)
}

/// `ne_p : Not (Eq Nat k p), ne_q : Not (Eq Nat k q), h_pq : Lt p q
/// ⊢ Eq Int (f k) (point_swap f p q k)` — the "elsewhere" agreement
/// `prod_range_swap_adjacent`'s own `g`-hypothesis wants, proved here for the
/// CONCRETE `point_swap`-built partner rather than an arbitrarily supplied
/// one.
#[allow(clippy::too_many_arguments)]
pub(super) fn general_swap_agree(
    d: &mut IntDev<'_>,
    f: ExprId,
    p_idx: ExprId,
    q_idx: ExprId,
    k: ExprId,
    ne_p: ExprId,
    ne_q: ExprId,
    h_pq: ExprId,
) -> ExprId {
    let fk = d.apply(f, &[k]);
    let swapped = point_swap(d, f, p_idx, q_idx, k);
    let target = d.ieq(fk, swapped);
    let dis_p = nat_lt_or_gt_of_ne(d, k, p_idx, ne_p);
    let lt_kp = d.lt(k, p_idx);
    let lt_pk = d.lt(p_idx, k);

    let on_lt = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
        let eqp = point_swap_eq_lt_p(d, f, p_idx, q_idx, k, h);
        d.isymm(swapped, fk, eqp)
    };
    let on_gt = &|d: &mut IntDev<'_>, h1: ExprId| -> ExprId {
        let dis_q = nat_lt_or_gt_of_ne(d, k, q_idx, ne_q);
        let lt_kq = d.lt(k, q_idx);
        let lt_qk = d.lt(q_idx, k);
        let on_between = &|d: &mut IntDev<'_>, h2: ExprId| -> ExprId {
            let eqp = point_swap_eq_between(d, f, p_idx, q_idx, k, h1, h2);
            d.isymm(swapped, fk, eqp)
        };
        let on_gt_q = &|d: &mut IntDev<'_>, h2: ExprId| -> ExprId {
            let eqp = point_swap_eq_gt_q(d, f, p_idx, q_idx, k, h_pq, h2);
            d.isymm(swapped, fk, eqp)
        };
        d.or_elim(lt_kq, lt_qk, target, dis_q, on_between, on_gt_q)
    };
    d.or_elim(lt_kp, lt_pk, target, dis_p, on_lt, on_gt)
}

/// The four hypothesis types plus the conclusion of `prod_range_swap`'s
/// statement, parameterized by explicit `(f, g, i, j, n)` — shared between
/// [`swap_aux_motive`] (needs it at `j := add (succ i) d`) and
/// [`swap_aux_step`]'s final wrapping (needs it at `j := succ j'`).
fn swap_hyp_types(
    d: &mut IntDev<'_>,
    f: ExprId,
    g: ExprId,
    i: ExprId,
    j: ExprId,
    n: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId) {
    let p = d.int();
    let nat = d.nat_ty();
    let h_jn_ty = d.lt(j, n);
    let fj = d.apply(f, &[j]);
    let gi = d.apply(g, &[i]);
    let hyp_gi_ty = d.ieq(gi, fj);
    let fi = d.apply(f, &[i]);
    let gj = d.apply(g, &[j]);
    let hyp_gj_ty = d.ieq(gj, fi);
    let hyp_agree_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let eq_ne_ki = d.eq(k, i);
        let ne_ki = d.not(eq_ne_ki);
        let eq_ne_kj = d.eq(k, j);
        let ne_kj = d.not(eq_ne_kj);
        let fk = d.apply(f, &[k]);
        let gk = d.apply(g, &[k]);
        let concl = d.ieq(fk, gk);
        let inner = d.arrow(ne_kj, concl);
        let step_ = d.arrow(ne_ki, inner);
        d.pi_fv(k_fv, nat, step_)
    };
    let lhs = d.const_app(p.prod_range, &[f, n]);
    let rhs = d.const_app(p.prod_range, &[g, n]);
    let conclusion = d.ieq(lhs, rhs);
    (h_jn_ty, hyp_gi_ty, hyp_gj_ty, hyp_agree_ty, conclusion)
}

// --- the six live regions of `swap_conjugation_agrees_with_g` -------------

/// `k < i` (hence `k < j'`): `A k = f k`, `B k = A k`, `C k = B k` (all three
/// `point_swap`s land in their `lt_p` case), and `f k = g k` from `h_agree`.
#[allow(clippy::too_many_arguments)]
fn region_below_i(
    d: &mut IntDev<'_>,
    f: ExprId,
    a_fn: ExprId,
    b_fn: ExprId,
    c_fn: ExprId,
    g: ExprId,
    i: ExprId,
    j_prime: ExprId,
    j: ExprId,
    k: ExprId,
    le_i_jprime: ExprId,
    le_jprime_j: ExprId,
    h_agree: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let lt_k_jprime = d.lemma(p.nat.lt_of_lt_of_le, &[k, i, j_prime, h, le_i_jprime]);
    let lt_k_j = d.lemma(
        p.nat.lt_of_lt_of_le,
        &[k, j_prime, j, lt_k_jprime, le_jprime_j],
    );
    let a_fact = point_swap_eq_lt_p(d, f, j_prime, j, k, lt_k_jprime);
    let b_fact = point_swap_eq_lt_p(d, a_fn, i, j_prime, k, h);
    let c_fact = point_swap_eq_lt_p(d, b_fn, j_prime, j, k, lt_k_jprime);
    let ne_ki = ne_of_lt(d, k, i, h);
    let ne_kj = ne_of_lt(d, k, j, lt_k_j);
    chain_to_g_via_agree(
        d, f, g, a_fn, b_fn, c_fn, k, a_fact, b_fact, c_fact, h_agree, ne_ki, ne_kj,
    )
}

/// `i < k < j'`: `A k = f k`, `B k = A k` (`point_swap`'s `between` case on
/// `(i, j')`), `C k = B k`, and `f k = g k` from `h_agree`.
#[allow(clippy::too_many_arguments)]
fn region_between_i_jprime(
    d: &mut IntDev<'_>,
    f: ExprId,
    a_fn: ExprId,
    b_fn: ExprId,
    c_fn: ExprId,
    g: ExprId,
    i: ExprId,
    j_prime: ExprId,
    j: ExprId,
    k: ExprId,
    le_jprime_j: ExprId,
    h_agree: ExprId,
    h_i_k: ExprId,
    h_k_jprime: ExprId,
) -> ExprId {
    let p = d.int();
    let lt_k_j = d.lemma(
        p.nat.lt_of_lt_of_le,
        &[k, j_prime, j, h_k_jprime, le_jprime_j],
    );
    let a_fact = point_swap_eq_lt_p(d, f, j_prime, j, k, h_k_jprime);
    let b_fact = point_swap_eq_between(d, a_fn, i, j_prime, k, h_i_k, h_k_jprime);
    let c_fact = point_swap_eq_lt_p(d, b_fn, j_prime, j, k, h_k_jprime);
    let ne_ki = ne_of_lt_symm(d, i, k, h_i_k);
    let ne_kj = ne_of_lt(d, k, j, lt_k_j);
    chain_to_g_via_agree(
        d, f, g, a_fn, b_fn, c_fn, k, a_fact, b_fact, c_fact, h_agree, ne_ki, ne_kj,
    )
}

/// `k > j`: `A k = f k`, `B k = A k`, `C k = B k` (all three `gt_q` cases),
/// and `f k = g k` from `h_agree`.
#[allow(clippy::too_many_arguments)]
fn region_above_j(
    d: &mut IntDev<'_>,
    f: ExprId,
    a_fn: ExprId,
    b_fn: ExprId,
    c_fn: ExprId,
    g: ExprId,
    i: ExprId,
    j_prime: ExprId,
    j: ExprId,
    k: ExprId,
    h_i_lt_jprime: ExprId,
    h_jprime_lt_j: ExprId,
    h_agree: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let le_j_k = nat_le_of_lt(d, j, k, h);
    let lt_jprime_k = d.lemma(
        p.nat.lt_of_lt_of_le,
        &[j_prime, j, k, h_jprime_lt_j, le_j_k],
    );
    let le_jprime_k = nat_le_of_lt(d, j_prime, k, lt_jprime_k);
    let lt_i_k = d.lemma(
        p.nat.lt_of_lt_of_le,
        &[i, j_prime, k, h_i_lt_jprime, le_jprime_k],
    );
    let a_fact = point_swap_eq_gt_q(d, f, j_prime, j, k, h_jprime_lt_j, h);
    let b_fact = point_swap_eq_gt_q(d, a_fn, i, j_prime, k, h_i_lt_jprime, lt_jprime_k);
    let c_fact = point_swap_eq_gt_q(d, b_fn, j_prime, j, k, h_jprime_lt_j, h);
    let ne_ki = ne_of_lt_symm(d, i, k, lt_i_k);
    let ne_kj = ne_of_lt_symm(d, j, k, h);
    chain_to_g_via_agree(
        d, f, g, a_fn, b_fn, c_fn, k, a_fact, b_fact, c_fact, h_agree, ne_ki, ne_kj,
    )
}

/// Chain `c_fact : Eq Int (C k) (B k)`, `b_fact : Eq Int (B k) (A k)`,
/// `a_fact : Eq Int (A k) (f k)` into `Eq Int (C k) (f k)`, then close against
/// `g k` via `h_agree k ne_ki ne_kj : Eq Int (f k) (g k)`.
#[allow(clippy::too_many_arguments)]
fn chain_to_g_via_agree(
    d: &mut IntDev<'_>,
    f: ExprId,
    g: ExprId,
    a_fn: ExprId,
    b_fn: ExprId,
    c_fn: ExprId,
    k: ExprId,
    a_fact: ExprId,
    b_fact: ExprId,
    c_fact: ExprId,
    h_agree: ExprId,
    ne_ki: ExprId,
    ne_kj: ExprId,
) -> ExprId {
    let ck = d.apply(c_fn, &[k]);
    let bk = d.apply(b_fn, &[k]);
    let ak = d.apply(a_fn, &[k]);
    let fk = d.apply(f, &[k]);
    let gk = d.apply(g, &[k]);
    let step_cb = d.itrans(ck, bk, ak, c_fact, b_fact);
    let step_to_f = d.itrans(ck, ak, fk, step_cb, a_fact);
    let agree_k = d.apply(h_agree, &[k, ne_ki, ne_kj]);
    d.itrans(ck, fk, gk, step_to_f, agree_k)
}

// --- the three exact-index regions, and the impossible one -----------------

/// `Eq Int (C i) (g i)`: `C(i) = B(i) = A(j') = f(j) = g(i)`, the second step
/// via [`point_swap_eq_at_p`] applied twice (`B` at `i` lands on `A j'`, which
/// itself needs resolving through `A`'s own pair) and the last via `h_gi`.
fn c_agrees_with_g_at_i(
    d: &mut IntDev<'_>,
    f: ExprId,
    a_fn: ExprId,
    b_fn: ExprId,
    c_fn: ExprId,
    g: ExprId,
    i: ExprId,
    j_prime: ExprId,
    j: ExprId,
    h_i_lt_jprime: ExprId,
    h_gi: ExprId,
) -> ExprId {
    let b_fact = point_swap_eq_at_p(d, a_fn, i, j_prime);
    let a_fact_jprime = point_swap_eq_at_p(d, f, j_prime, j);
    let c_fact = point_swap_eq_lt_p(d, b_fn, j_prime, j, i, h_i_lt_jprime);

    let ci = d.apply(c_fn, &[i]);
    let bi = d.apply(b_fn, &[i]);
    let ajprime = d.apply(a_fn, &[j_prime]);
    let fj = d.apply(f, &[j]);
    let gi = d.apply(g, &[i]);

    let step1 = d.itrans(ci, bi, ajprime, c_fact, b_fact);
    let step2 = d.itrans(ci, ajprime, fj, step1, a_fact_jprime);
    let hgi_rev = d.isymm(gi, fj, h_gi);
    d.itrans(ci, fj, gi, step2, hgi_rev)
}

/// `Eq Int (C j') (g j')`: `C(j') = B(j) = A(j) = f(j') = g(j')`, the last
/// step via `h_agree` (`j'` is neither `i` nor `j`).
#[allow(clippy::too_many_arguments)]
fn c_agrees_with_g_at_jprime(
    d: &mut IntDev<'_>,
    f: ExprId,
    a_fn: ExprId,
    b_fn: ExprId,
    c_fn: ExprId,
    g: ExprId,
    i: ExprId,
    j_prime: ExprId,
    j: ExprId,
    h_i_lt_jprime: ExprId,
    h_jprime_lt_j: ExprId,
    h_agree: ExprId,
) -> ExprId {
    let c_fact = point_swap_eq_at_p(d, b_fn, j_prime, j);
    let b_fact = point_swap_eq_gt_q(d, a_fn, i, j_prime, j, h_i_lt_jprime, h_jprime_lt_j);
    let a_fact = point_swap_eq_at_q(d, f, j_prime, j, h_jprime_lt_j);

    let cjp = d.apply(c_fn, &[j_prime]);
    let bj = d.apply(b_fn, &[j]);
    let aj = d.apply(a_fn, &[j]);
    let fjp = d.apply(f, &[j_prime]);
    let gjp = d.apply(g, &[j_prime]);

    let step1 = d.itrans(cjp, bj, aj, c_fact, b_fact);
    let step2 = d.itrans(cjp, aj, fjp, step1, a_fact);
    let ne_jp_i = ne_of_lt_symm(d, i, j_prime, h_i_lt_jprime);
    let ne_jp_j = ne_of_lt(d, j_prime, j, h_jprime_lt_j);
    let agree_jp = d.apply(h_agree, &[j_prime, ne_jp_i, ne_jp_j]);
    d.itrans(cjp, fjp, gjp, step2, agree_jp)
}

/// `Eq Int (C j) (g j)`: `C(j) = B(j') = A(i) = f(i) = g(j)`, the last step
/// via `h_gj`.
#[allow(clippy::too_many_arguments)]
fn c_agrees_with_g_at_j(
    d: &mut IntDev<'_>,
    f: ExprId,
    a_fn: ExprId,
    b_fn: ExprId,
    c_fn: ExprId,
    g: ExprId,
    i: ExprId,
    j_prime: ExprId,
    j: ExprId,
    h_i_lt_jprime: ExprId,
    h_jprime_lt_j: ExprId,
    h_gj: ExprId,
) -> ExprId {
    let c_fact = point_swap_eq_at_q(d, b_fn, j_prime, j, h_jprime_lt_j);
    let b_fact = point_swap_eq_at_q(d, a_fn, i, j_prime, h_i_lt_jprime);
    let a_fact = point_swap_eq_lt_p(d, f, j_prime, j, i, h_i_lt_jprime);

    let cj = d.apply(c_fn, &[j]);
    let bjp = d.apply(b_fn, &[j_prime]);
    let ai = d.apply(a_fn, &[i]);
    let fi = d.apply(f, &[i]);
    let gj = d.apply(g, &[j]);

    let step1 = d.itrans(cj, bjp, ai, c_fact, b_fact);
    let step2 = d.itrans(cj, ai, fi, step1, a_fact);
    let hgj_rev = d.isymm(gj, fi, h_gj);
    d.itrans(cj, fi, gj, step2, hgj_rev)
}

/// `h1 : Lt j' k, h2 : Lt k j ⊢ target` for ANY `target` — the region
/// `j' < k < j` is impossible since `j = succ j'` (`Nat.le_of_lt_succ` +
/// `Nat.le_trans` + `Nat.not_succ_le_self`), so it closes by contradiction.
fn region_impossible(
    d: &mut IntDev<'_>,
    j_prime: ExprId,
    k: ExprId,
    target: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let p = d.int();
    // h2 : Lt k j, and j is literally `succ j_prime` at every call site, so
    // h2 : Le (succ k) (succ j_prime) up to that unfold — `le_of_lt_succ`
    // wants exactly `Lt k (succ j_prime)`, which `h2` already is.
    let k_le_jprime = d.lemma(p.nat.le_of_lt_succ, &[k, j_prime, h2]);
    let succ_jprime = d.succ(j_prime);
    let succ_jprime_le_jprime =
        d.lemma(p.nat.le_trans, &[succ_jprime, k, j_prime, h1, k_le_jprime]);
    let false_pf = d.lemma(p.nat.not_succ_le_self, &[j_prime, succ_jprime_le_jprime]);
    d.absurd(target, false_pf)
}

/// From `heq : Eq Nat k m` and `proof_at_m : Eq Int (C m) (g m)`, produce
/// `Eq Int (C k) (g k)` by transporting along `heq` (reversed).
fn transport_c_agrees(
    d: &mut IntDev<'_>,
    c_fn: ExprId,
    g: ExprId,
    k: ExprId,
    m: ExprId,
    heq: ExprId,
    proof_at_m: ExprId,
) -> ExprId {
    let rev = d.symm(k, m, heq);
    d.nat_rewrite(m, k, rev, proof_at_m, &|d, x| {
        let cx = d.apply(c_fn, &[x]);
        let gx = d.apply(g, &[x]);
        d.ieq(cx, gx)
    })
}

/// `Eq Int (C k) (g k)` for arbitrary `k`, where
/// `C := point_swap (point_swap (point_swap f j' j) i j') j' j` is
/// [`swap_aux_step`]'s conjugated transposition and `g` is the caller's own
/// partner for `f` at `(i, j)` (`j = succ j'`). Case-splits `k` against `i`,
/// then `j'`, then `j` (`nat_trichotomy`, nested); the six live regions each
/// unwind `C`'s three `point_swap` layers back to `f` and close against `g`
/// via `h_agree`/`h_gi`/`h_gj`; the seventh combination (`j' < k < j`) is
/// impossible since `j = succ j'` ([`region_impossible`]).
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn swap_conjugation_agrees_with_g(
    d: &mut IntDev<'_>,
    f: ExprId,
    a_fn: ExprId,
    b_fn: ExprId,
    c_fn: ExprId,
    g: ExprId,
    i: ExprId,
    j_prime: ExprId,
    j: ExprId,
    k: ExprId,
    h_i_lt_jprime: ExprId,
    h_jprime_lt_j: ExprId,
    h_gi: ExprId,
    h_gj: ExprId,
    h_agree: ExprId,
) -> ExprId {
    let ck = d.apply(c_fn, &[k]);
    let gk = d.apply(g, &[k]);
    let target = d.ieq(ck, gk);

    let le_i_jprime = nat_le_of_lt(d, i, j_prime, h_i_lt_jprime);
    let le_jprime_j = nat_le_of_lt(d, j_prime, j, h_jprime_lt_j);

    let tri_i = nat_trichotomy(d, k, i);
    let lt_ki = d.lt(k, i);
    let eq_ki = d.eq(k, i);
    let lt_ik = d.lt(i, k);
    let inner_i = d.or(eq_ki, lt_ik);

    let on_lt_ki = &|d: &mut IntDev<'_>, h: ExprId| -> ExprId {
        region_below_i(
            d,
            f,
            a_fn,
            b_fn,
            c_fn,
            g,
            i,
            j_prime,
            j,
            k,
            le_i_jprime,
            le_jprime_j,
            h_agree,
            h,
        )
    };
    let on_rest_i = &|d: &mut IntDev<'_>, h_inner: ExprId| -> ExprId {
        let on_eq_ki = &|d: &mut IntDev<'_>, heq: ExprId| -> ExprId {
            let proof_at_i = c_agrees_with_g_at_i(
                d,
                f,
                a_fn,
                b_fn,
                c_fn,
                g,
                i,
                j_prime,
                j,
                h_i_lt_jprime,
                h_gi,
            );
            transport_c_agrees(d, c_fn, g, k, i, heq, proof_at_i)
        };
        let on_lt_ik = &|d: &mut IntDev<'_>, h_i_k: ExprId| -> ExprId {
            let tri_jp = nat_trichotomy(d, k, j_prime);
            let lt_k_jp = d.lt(k, j_prime);
            let eq_k_jp = d.eq(k, j_prime);
            let lt_jp_k = d.lt(j_prime, k);
            let inner_jp = d.or(eq_k_jp, lt_jp_k);

            let on_lt_k_jp = &|d: &mut IntDev<'_>, h_k_jp: ExprId| -> ExprId {
                region_between_i_jprime(
                    d,
                    f,
                    a_fn,
                    b_fn,
                    c_fn,
                    g,
                    i,
                    j_prime,
                    j,
                    k,
                    le_jprime_j,
                    h_agree,
                    h_i_k,
                    h_k_jp,
                )
            };
            let on_rest_jp = &|d: &mut IntDev<'_>, h_inner2: ExprId| -> ExprId {
                let on_eq_k_jp = &|d: &mut IntDev<'_>, heq2: ExprId| -> ExprId {
                    let proof_at_jp = c_agrees_with_g_at_jprime(
                        d,
                        f,
                        a_fn,
                        b_fn,
                        c_fn,
                        g,
                        i,
                        j_prime,
                        j,
                        h_i_lt_jprime,
                        h_jprime_lt_j,
                        h_agree,
                    );
                    transport_c_agrees(d, c_fn, g, k, j_prime, heq2, proof_at_jp)
                };
                let on_lt_jp_k = &|d: &mut IntDev<'_>, h_jp_k: ExprId| -> ExprId {
                    let tri_j = nat_trichotomy(d, k, j);
                    let lt_kj = d.lt(k, j);
                    let eq_kj = d.eq(k, j);
                    let lt_jk = d.lt(j, k);
                    let inner_j = d.or(eq_kj, lt_jk);

                    let on_lt_kj = &|d: &mut IntDev<'_>, h_kj: ExprId| -> ExprId {
                        region_impossible(d, j_prime, k, target, h_jp_k, h_kj)
                    };
                    let on_rest_j = &|d: &mut IntDev<'_>, h_inner3: ExprId| -> ExprId {
                        let on_eq_kj = &|d: &mut IntDev<'_>, heq3: ExprId| -> ExprId {
                            let proof_at_j = c_agrees_with_g_at_j(
                                d,
                                f,
                                a_fn,
                                b_fn,
                                c_fn,
                                g,
                                i,
                                j_prime,
                                j,
                                h_i_lt_jprime,
                                h_jprime_lt_j,
                                h_gj,
                            );
                            transport_c_agrees(d, c_fn, g, k, j, heq3, proof_at_j)
                        };
                        let on_lt_jk = &|d: &mut IntDev<'_>, h_jk: ExprId| -> ExprId {
                            region_above_j(
                                d,
                                f,
                                a_fn,
                                b_fn,
                                c_fn,
                                g,
                                i,
                                j_prime,
                                j,
                                k,
                                h_i_lt_jprime,
                                h_jprime_lt_j,
                                h_agree,
                                h_jk,
                            )
                        };
                        d.or_elim(eq_kj, lt_jk, target, h_inner3, on_eq_kj, on_lt_jk)
                    };
                    d.or_elim(lt_kj, inner_j, target, tri_j, on_lt_kj, on_rest_j)
                };
                d.or_elim(eq_k_jp, lt_jp_k, target, h_inner2, on_eq_k_jp, on_lt_jp_k)
            };
            d.or_elim(lt_k_jp, inner_jp, target, tri_jp, on_lt_k_jp, on_rest_jp)
        };
        d.or_elim(eq_ki, lt_ik, target, h_inner, on_eq_ki, on_lt_ik)
    };
    d.or_elim(lt_ki, inner_i, target, tri_i, on_lt_ki, on_rest_i)
}

// --- the auxiliary induction, generalized over `f`, `g` at fixed `i`, `n` --

/// `motive(dd) := ∀ f g, Lt j n → Eq(g i)(f j) → Eq(g j)(f i) →
/// (∀k,¬k=i→¬k=j→Eq(f k)(g k)) → Eq(prodRange f n)(prodRange g n)`, where
/// `j := add (succ i) dd`. `i`, `n` are FIXED across the induction (the
/// recursive call reuses them, only `f`, `g` change); `dd` is what
/// [`declare_prod_range_swap`] inducts on.
fn swap_aux_motive(d: &mut IntDev<'_>, i: ExprId, n: ExprId, dd: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);
    let succ_i = d.succ(i);
    let j = d.add(succ_i, dd);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let (h_jn_ty, hyp_gi_ty, hyp_gj_ty, hyp_agree_ty, conclusion) =
        swap_hyp_types(d, f, g, i, j, n);
    let inner_stmt = {
        let w3 = d.arrow(hyp_agree_ty, conclusion);
        let w2 = d.arrow(hyp_gj_ty, w3);
        let w1 = d.arrow(hyp_gi_ty, w2);
        d.arrow(h_jn_ty, w1)
    };
    let with_g = d.pi_fv(g_fv, fn_ty, inner_stmt);
    d.pi_fv(f_fv, fn_ty, with_g)
}

/// `dd = zero`: `j` is definitionally `succ i`, so `swap_aux_motive(zero)` IS
/// `prod_range_swap_adjacent`'s statement (applied at `i`, `n`) up to the
/// kernel's own unfolding of `add i zero`.
fn swap_aux_base(d: &mut IntDev<'_>, i: ExprId, n: ExprId) -> ExprId {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);
    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let body = d.const_app(p.prod_range_swap_adjacent, &[f, g, i, n]);
    let with_g = d.lam_fv(g_fv, fn_ty, body);
    d.lam_fv(f_fv, fn_ty, with_g)
}

/// `dd = succ m`, `ih : swap_aux_motive(m)` ⊢ `swap_aux_motive(succ m)` — see
/// the module doc's "Route" paragraph above `declare_prod_range_swap` for the
/// conjugation this builds.
#[allow(clippy::too_many_lines)]
fn swap_aux_step(d: &mut IntDev<'_>, i: ExprId, n: ExprId, m: ExprId, ih: ExprId) -> ExprId {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);
    let succ_i = d.succ(i);
    let j_prime = d.add(succ_i, m);
    let j = d.succ(j_prime);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let jn_fv = d.fresh_fvar();
    let h_jn = d.kernel().fvar(jn_fv);
    let gi_fv = d.fresh_fvar();
    let h_gi = d.kernel().fvar(gi_fv);
    let gj_fv = d.fresh_fvar();
    let h_gj = d.kernel().fvar(gj_fv);
    let agree_fv = d.fresh_fvar();
    let h_agree = d.kernel().fvar(agree_fv);

    let lt_succ_i = d.lemma(p.nat.lt_succ_self, &[i]);
    let le_succ_i_jprime = d.lemma(p.nat.le_add_right, &[succ_i, m]);
    let h_i_lt_jprime = d.lemma(
        p.nat.lt_of_lt_of_le,
        &[i, succ_i, j_prime, lt_succ_i, le_succ_i_jprime],
    );
    let h_jprime_lt_j = d.lemma(p.nat.lt_succ_self, &[j_prime]);

    // --- A := point_swap f j' j ---
    let a_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = point_swap(d, f, j_prime, j, k);
        d.lam_fv(k_fv, nat, body)
    };
    let agree_f_a = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let nej_fv = d.fresh_fvar();
        let ne_j = d.kernel().fvar(nej_fv);
        let nesj_fv = d.fresh_fvar();
        let ne_sj = d.kernel().fvar(nesj_fv);
        let body = general_swap_agree(d, f, j_prime, j, k, ne_j, ne_sj, h_jprime_lt_j);
        let eq_ne_j_ty = d.eq(k, j_prime);
        let ne_j_ty = d.not(eq_ne_j_ty);
        let eq_ne_sj_ty = d.eq(k, j);
        let ne_sj_ty = d.not(eq_ne_sj_ty);
        let with_nesj = d.lam_fv(nesj_fv, ne_sj_ty, body);
        let with_nej = d.lam_fv(nej_fv, ne_j_ty, with_nesj);
        d.lam_fv(k_fv, nat, with_nej)
    };
    let a_at_jprime = point_swap_eq_at_p(d, f, j_prime, j);
    let a_at_j = point_swap_eq_at_q(d, f, j_prime, j, h_jprime_lt_j);
    let step1 = d.const_app(
        p.prod_range_swap_adjacent,
        &[f, a_fn, j_prime, n, h_jn, a_at_jprime, a_at_j, agree_f_a],
    );

    // --- B := point_swap A i j', the induction hypothesis's own partner ---
    let b_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = point_swap(d, a_fn, i, j_prime, k);
        d.lam_fv(k_fv, nat, body)
    };
    let b_at_i = point_swap_eq_at_p(d, a_fn, i, j_prime);
    let b_at_jprime = point_swap_eq_at_q(d, a_fn, i, j_prime, h_i_lt_jprime);
    let agree_a_b = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let nei_fv = d.fresh_fvar();
        let ne_i = d.kernel().fvar(nei_fv);
        let nej_fv = d.fresh_fvar();
        let ne_j = d.kernel().fvar(nej_fv);
        let body = general_swap_agree(d, a_fn, i, j_prime, k, ne_i, ne_j, h_i_lt_jprime);
        let eq_ne_i_ty = d.eq(k, i);
        let ne_i_ty = d.not(eq_ne_i_ty);
        let eq_ne_j_ty = d.eq(k, j_prime);
        let ne_j_ty = d.not(eq_ne_j_ty);
        let with_nej = d.lam_fv(nej_fv, ne_j_ty, body);
        let with_nei = d.lam_fv(nei_fv, ne_i_ty, with_nej);
        d.lam_fv(k_fv, nat, with_nei)
    };
    let le_j_n = nat_le_of_lt(d, j, n, h_jn);
    let h_jprime_n = d.lemma(
        p.nat.lt_of_lt_of_le,
        &[j_prime, j, n, h_jprime_lt_j, le_j_n],
    );
    let ih_at_ab = d.apply(ih, &[a_fn, b_fn]);
    let step2 = d.apply(ih_at_ab, &[h_jprime_n, b_at_i, b_at_jprime, agree_a_b]);

    // --- C := point_swap B j' j ---
    let c_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = point_swap(d, b_fn, j_prime, j, k);
        d.lam_fv(k_fv, nat, body)
    };
    let c_at_jprime = point_swap_eq_at_p(d, b_fn, j_prime, j);
    let c_at_j = point_swap_eq_at_q(d, b_fn, j_prime, j, h_jprime_lt_j);
    let agree_b_c = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let nej_fv = d.fresh_fvar();
        let ne_j = d.kernel().fvar(nej_fv);
        let nesj_fv = d.fresh_fvar();
        let ne_sj = d.kernel().fvar(nesj_fv);
        let body = general_swap_agree(d, b_fn, j_prime, j, k, ne_j, ne_sj, h_jprime_lt_j);
        let eq_ne_j_ty = d.eq(k, j_prime);
        let ne_j_ty = d.not(eq_ne_j_ty);
        let eq_ne_sj_ty = d.eq(k, j);
        let ne_sj_ty = d.not(eq_ne_sj_ty);
        let with_nesj = d.lam_fv(nesj_fv, ne_sj_ty, body);
        let with_nej = d.lam_fv(nej_fv, ne_j_ty, with_nesj);
        d.lam_fv(k_fv, nat, with_nej)
    };
    let step3 = d.const_app(
        p.prod_range_swap_adjacent,
        &[b_fn, c_fn, j_prime, n, h_jn, c_at_jprime, c_at_j, agree_b_c],
    );

    // --- prodRange C n = prodRange g n, via prod_range_congr ---
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = swap_conjugation_agrees_with_g(
            d,
            f,
            a_fn,
            b_fn,
            c_fn,
            g,
            i,
            j_prime,
            j,
            k,
            h_i_lt_jprime,
            h_jprime_lt_j,
            h_gi,
            h_gj,
            h_agree,
        );
        d.lam_fv(k_fv, nat, body)
    };
    let step4 = d.const_app(p.prod_range_congr, &[c_fn, g, n, pointwise]);

    let start = d.const_app(p.prod_range, &[f, n]);
    let a_range = d.const_app(p.prod_range, &[a_fn, n]);
    let b_range = d.const_app(p.prod_range, &[b_fn, n]);
    let c_range = d.const_app(p.prod_range, &[c_fn, n]);
    let (_, chained) = d.ichain(
        start,
        &[(a_range, step1), (b_range, step2), (c_range, step3)],
    );
    let g_range = d.const_app(p.prod_range, &[g, n]);
    let full = d.itrans(start, c_range, g_range, chained, step4);

    let (h_jn_ty, hyp_gi_ty, hyp_gj_ty, hyp_agree_ty, _concl) = swap_hyp_types(d, f, g, i, j, n);
    let with_agree = d.lam_fv(agree_fv, hyp_agree_ty, full);
    let with_gj = d.lam_fv(gj_fv, hyp_gj_ty, with_agree);
    let with_gi = d.lam_fv(gi_fv, hyp_gi_ty, with_gj);
    let with_jn = d.lam_fv(jn_fv, h_jn_ty, with_gi);
    let with_g = d.lam_fv(g_fv, fn_ty, with_jn);
    d.lam_fv(f_fv, fn_ty, with_g)
}

/// Declare `Int.prodRange_swap` — the general transposition. See the module
/// doc above for the route (`Nat.le_dest` + the aux induction generalized
/// over `f`, `g`).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
#[allow(clippy::too_many_lines)]
pub(super) fn declare_prod_range_swap(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty = d.arrow(nat, int_ty);
    let one = d.level_one();
    let anon = d.anon_name();

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let h_ij_ty = d.lt(i, j);
    let (h_jn_ty, hyp_gi_ty, hyp_gj_ty, hyp_agree_ty, conclusion) =
        swap_hyp_types(d, f, g, i, j, n);
    let stmt_inner = {
        let w5 = d.arrow(hyp_agree_ty, conclusion);
        let w4 = d.arrow(hyp_gj_ty, w5);
        let w3 = d.arrow(hyp_gi_ty, w4);
        let w2 = d.arrow(h_jn_ty, w3);
        d.arrow(h_ij_ty, w2)
    };

    let range_fv = d.fresh_fvar();
    let h_range = d.kernel().fvar(range_fv);
    let jn_fv = d.fresh_fvar();
    let h_jn = d.kernel().fvar(jn_fv);
    let gi_fv = d.fresh_fvar();
    let h_gi = d.kernel().fvar(gi_fv);
    let gj_fv = d.fresh_fvar();
    let h_gj = d.kernel().fvar(gj_fv);
    let agree_fv = d.fresh_fvar();
    let h_agree = d.kernel().fvar(agree_fv);

    let succ_i = d.succ(i);
    let existential = d.lemma(p.nat.le_dest, &[succ_i, j, h_range]);
    let pred = {
        let dd_fv = d.fresh_fvar();
        let dd = d.kernel().fvar(dd_fv);
        let sum = d.add(succ_i, dd);
        let body = d.eq(sum, j);
        d.lam_fv(dd_fv, nat, body)
    };
    let exists_ty = {
        let ex = d.kernel().const_(p.logic.exists_, vec![one]);
        d.apply(ex, &[nat, pred])
    };
    let motive_outer = d
        .kernel()
        .lam(anon, exists_ty, conclusion, BinderInfo::Default);
    let minor = {
        let dd_fv = d.fresh_fvar();
        let dd = d.kernel().fvar(dd_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let sum = d.add(succ_i, dd);
        let e_ty = d.eq(sum, j);

        let aux_proof_at_dd = d.induct(
            &|d, x| swap_aux_motive(d, i, n, x),
            &|d| swap_aux_base(d, i, n),
            &|d, mm, ih| swap_aux_step(d, i, n, mm, ih),
            dd,
        );
        let applied_fg = d.apply(aux_proof_at_dd, &[f, g]);

        let e_rev = d.symm(sum, j, e);
        let h_jn_sum = d.nat_rewrite(j, sum, e_rev, h_jn, &|d, x| d.lt(x, n));
        let gi = d.apply(g, &[i]);
        let h_gi_sum = d.nat_rewrite(j, sum, e_rev, h_gi, &|d, x| {
            let fx = d.apply(f, &[x]);
            d.ieq(gi, fx)
        });
        let fi = d.apply(f, &[i]);
        let h_gj_sum = d.nat_rewrite(j, sum, e_rev, h_gj, &|d, x| {
            let gx = d.apply(g, &[x]);
            d.ieq(gx, fi)
        });
        let h_agree_sum = d.nat_rewrite(j, sum, e_rev, h_agree, &|d, x| {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let eq_ne_ki = d.eq(k, i);
            let ne_ki = d.not(eq_ne_ki);
            let eq_ne_kx = d.eq(k, x);
            let ne_kx = d.not(eq_ne_kx);
            let fk = d.apply(f, &[k]);
            let gk = d.apply(g, &[k]);
            let concl = d.ieq(fk, gk);
            let inner = d.arrow(ne_kx, concl);
            let step_ = d.arrow(ne_ki, inner);
            d.pi_fv(k_fv, nat, step_)
        });

        let final_body = d.apply(applied_fg, &[h_jn_sum, h_gi_sum, h_gj_sum, h_agree_sum]);
        let with_e = d.lam_fv(e_fv, e_ty, final_body);
        d.lam_fv(dd_fv, nat, with_e)
    };
    let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    let proof_body = d.apply(exists_rec, &[nat, pred, motive_outer, minor, existential]);

    let value = {
        let with_agree = d.lam_fv(agree_fv, hyp_agree_ty, proof_body);
        let with_gj = d.lam_fv(gj_fv, hyp_gj_ty, with_agree);
        let with_gi = d.lam_fv(gi_fv, hyp_gi_ty, with_gj);
        let with_jn = d.lam_fv(jn_fv, h_jn_ty, with_gi);
        d.lam_fv(range_fv, h_ij_ty, with_jn)
    };
    let full_stmt = {
        let with_n = d.pi_fv(n_fv, nat, stmt_inner);
        let with_j = d.pi_fv(j_fv, nat, with_n);
        let with_i = d.pi_fv(i_fv, nat, with_j);
        let with_g = d.pi_fv(g_fv, fn_ty, with_i);
        d.pi_fv(f_fv, fn_ty, with_g)
    };
    let full_value = {
        let with_n = d.lam_fv(n_fv, nat, value);
        let with_j = d.lam_fv(j_fv, nat, with_n);
        let with_i = d.lam_fv(i_fv, nat, with_j);
        let with_g = d.lam_fv(g_fv, fn_ty, with_i);
        d.lam_fv(f_fv, fn_ty, with_g)
    };

    d.declare_theorem(p.prod_range_swap, full_stmt, full_value)
}

// ---------------------------------------------------------------------------
// `Int.prodRange_permute` — the general permutation, the assembly named in
// `wilson.rs`'s module doc: any `InjectiveOn`/`MapsInto` self-map of
// `{0,…,n-1}` rearranges `prodRange f n` without changing its value.
// ---------------------------------------------------------------------------
//
// `Int.prodRange_permute : ∀ f σ n, InjectiveOn σ n → MapsInto σ n →
// Eq Int (prodRange f n) (prodRange (fun k => f (σ k)) n)`.
//
// Induction on `n`, with `f` quantified OUTSIDE the `Nat.rec` and motive
// `∀ σ, InjectiveOn σ x → MapsInto σ x → prodRange f x = prodRange (f∘σ) x`
// — generalized over `σ`, NOT over `f` (copying the earlier chain's shape,
// generalizing over `f`, yields a motive that does not close: the recursive
// call here reuses the SAME `f` and only `σ` changes to the restricted `τ`).
//
// At `n+1`, `Nat.injective_on_imp_surjective_on` (the pigeonhole) gives
// `i0 < n+1` with `σ i0 = n`. [`permute_branch_fixed`] handles `i0 = n`
// (bound-weakening only, no restriction needed); [`permute_branch_swap`]
// handles `i0 < n` (`point_swap` on `f∘σ` at `(i0, n)`, plus
// `Nat.restrict_injective`/`Nat.restrict_maps_into`'s override
// `τ := point_override σ i0 (σ n)` feeding the induction hypothesis).

/// `fun k => f (g k)`.
fn compose(d: &mut IntDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let gk = d.apply(g, &[k]);
    let body = d.apply(f, &[gk]);
    d.lam_fv(k_fv, nat, body)
}

/// `h : Lt i n ⊢ Lt i (succ n)`.
fn lift_lt_succ(d: &mut IntDev<'_>, i: ExprId, n: ExprId, h: ExprId) -> ExprId {
    let p = d.int();
    let sn = d.succ(n);
    let le_n_sn = d.lemma(p.nat.le_succ, &[n]);
    d.lemma(p.nat.lt_of_lt_of_le, &[i, n, sn, h, le_n_sn])
}

// --- `point_override`, the `IntDev` counterpart of `nat_prelude/finite.rs`'s
// private `NatDev`-typed version, needed here because `prodRange_permute`'s
// restriction step is built over `IntDev`. Same order-based (never
// `Nat.beq`) single-point override.

/// `point_override σ i0 v k`'s inner layer: `σ k` when `i0 < k`, else `v`.
fn po_inner(d: &mut IntDev<'_>, sigma: ExprId, i0: ExprId, v: ExprId, k: ExprId) -> ExprId {
    let sk = d.apply(sigma, &[k]);
    let succ_i0 = d.succ(i0);
    let above_cond = d.ble(succ_i0, k);
    d.bool_select_nat(above_cond, sk, v)
}

/// `point_override σ i0 v k := if k < i0 then σ k else po_inner(σ, i0, v, k)`.
fn point_override(d: &mut IntDev<'_>, sigma: ExprId, i0: ExprId, v: ExprId, k: ExprId) -> ExprId {
    let sk = d.apply(sigma, &[k]);
    let inner = po_inner(d, sigma, i0, v, k);
    let succ_k = d.succ(k);
    let below_cond = d.ble(succ_k, i0);
    d.bool_select_nat(below_cond, sk, inner)
}

/// `heq : Eq Bool cond true ⊢ Eq Nat (bool_select_nat cond a b) a`.
fn select_nat_true(d: &mut IntDev<'_>, cond: ExprId, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let true_val = d.bool_true();
    let symm_hb = d.bool_symm(cond, true_val, heq);
    let motive = d.bool_eq_motive(true_val, &|d, value| {
        let sel = d.bool_select_nat(value, a, b);
        d.eq(sel, a)
    });
    let refl_case = d.refl(a);
    d.bool_transport(true_val, motive, refl_case, cond, symm_hb)
}

/// `heq : Eq Bool cond false ⊢ Eq Nat (bool_select_nat cond a b) b`.
fn select_nat_false(d: &mut IntDev<'_>, cond: ExprId, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let false_val = d.bool_false();
    let symm_hb = d.bool_symm(cond, false_val, heq);
    let motive = d.bool_eq_motive(false_val, &|d, value| {
        let sel = d.bool_select_nat(value, a, b);
        d.eq(sel, b)
    });
    let refl_case = d.refl(b);
    d.bool_transport(false_val, motive, refl_case, cond, symm_hb)
}

/// `h : Lt k i0 ⊢ Eq Nat (point_override σ i0 v k) (σ k)`.
fn override_eq_lt(
    d: &mut IntDev<'_>,
    sigma: ExprId,
    i0: ExprId,
    v: ExprId,
    k: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let sk = d.apply(sigma, &[k]);
    let inner = po_inner(d, sigma, i0, v, k);
    let succ_k = d.succ(k);
    let below_cond = d.ble(succ_k, i0);
    let below_true = d.lemma(p.nat.ble_eq_true_of_le, &[succ_k, i0, h]);
    select_nat_true(d, below_cond, sk, inner, below_true)
}

/// `h : Lt i0 k ⊢ Eq Nat (point_override σ i0 v k) (σ k)`.
fn override_eq_gt(
    d: &mut IntDev<'_>,
    sigma: ExprId,
    i0: ExprId,
    v: ExprId,
    k: ExprId,
    h: ExprId,
) -> ExprId {
    let p = d.int();
    let sk = d.apply(sigma, &[k]);
    let inner = po_inner(d, sigma, i0, v, k);
    let succ_k = d.succ(k);
    let below_cond = d.ble(succ_k, i0);

    let succ_i0 = d.succ(i0);
    let le_k_succ_k = d.lemma(p.nat.le_succ, &[k]);
    let lt_i0_succ_k = d.lemma(p.nat.le_trans, &[succ_i0, k, succ_k, h, le_k_succ_k]);
    let below_false = ble_eq_false_of_lt(d, succ_k, i0, lt_i0_succ_k);
    let step1 = select_nat_false(d, below_cond, sk, inner, below_false);

    let above_cond = d.ble(succ_i0, k);
    let above_true = d.lemma(p.nat.ble_eq_true_of_le, &[succ_i0, k, h]);
    let step2 = select_nat_true(d, above_cond, sk, v, above_true);

    let start = point_override(d, sigma, i0, v, k);
    d.trans(start, inner, sk, step1, step2)
}

/// `Eq Nat (point_override σ i0 v i0) v`.
fn override_eq_at(d: &mut IntDev<'_>, sigma: ExprId, i0: ExprId, v: ExprId) -> ExprId {
    let p = d.int();
    let si0 = d.apply(sigma, &[i0]);
    let inner = po_inner(d, sigma, i0, v, i0);
    let succ_i0 = d.succ(i0);
    let below_cond = d.ble(succ_i0, i0);

    let lt_i0_succ_i0 = d.lemma(p.nat.lt_succ_self, &[i0]);
    let below_false = ble_eq_false_of_lt(d, succ_i0, i0, lt_i0_succ_i0);
    let step1 = select_nat_false(d, below_cond, si0, inner, below_false);

    let above_cond = d.ble(succ_i0, i0);
    let step2 = select_nat_false(d, above_cond, si0, v, below_false);

    let start = point_override(d, sigma, i0, v, i0);
    d.trans(start, inner, v, step1, step2)
}

/// `motive(x) := ∀ σ, InjectiveOn σ x → MapsInto σ x →
///   Eq Int (prodRange f x) (prodRange (f ∘ σ) x)` — `f` fixed (captured from
/// the enclosing scope), generalized over `σ`.
fn permute_motive(d: &mut IntDev<'_>, f: ExprId, x: ExprId) -> ExprId {
    let p = d.int();
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);

    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let inj_ty = d.const_app(p.nat.injective_on, &[sigma, x]);
    let maps_ty = d.const_app(p.nat.maps_into, &[sigma, x]);

    let f_comp_sigma = compose(d, f, sigma);
    let lhs = d.const_app(p.prod_range, &[f, x]);
    let rhs = d.const_app(p.prod_range, &[f_comp_sigma, x]);
    let concl = d.ieq(lhs, rhs);

    let inner = d.arrow(maps_ty, concl);
    let with_inj = d.arrow(inj_ty, inner);
    d.pi_fv(sigma_fv, fn_ty, with_inj)
}

/// `motive(zero)`: both sides reduce to `Int.one` regardless of `σ`.
fn permute_base(d: &mut IntDev<'_>, f: ExprId) -> ExprId {
    let _ = f;
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let zero = d.zero();
    let p = d.int();

    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let inj_ty = d.const_app(p.nat.injective_on, &[sigma, zero]);
    let maps_ty = d.const_app(p.nat.maps_into, &[sigma, zero]);

    let one = d.ione();
    let body = d.irefl(one);
    let inj_fv = d.fresh_fvar();
    let maps_fv = d.fresh_fvar();
    let with_maps = d.lam_fv(maps_fv, maps_ty, body);
    let with_inj = d.lam_fv(inj_fv, inj_ty, with_maps);
    d.lam_fv(sigma_fv, fn_ty, with_inj)
}

/// Branch `i0 = n` of [`permute_step`]: no restriction is needed at all —
/// `σ i0 = n` and `i0 = n` combine to `σ n = n`, so `InjectiveOn σ n` is pure
/// bound-weakening from `InjectiveOn σ (succ n)`, and `MapsInto σ n` follows
/// from `MapsInto σ (succ n)` plus `σ i ≠ n` for `i < n` (else injectivity at
/// `(i, n)`, using `σ n = n`, would force `i = n`).
#[allow(clippy::too_many_arguments)]
fn permute_branch_fixed(
    d: &mut IntDev<'_>,
    f: ExprId,
    n: ExprId,
    sigma: ExprId,
    inj_sigma: ExprId,
    maps_sigma: ExprId,
    i0: ExprId,
    heq: ExprId,
    sigma_i0_eq_n: ExprId,
    ih: ExprId,
) -> ExprId {
    let p = d.int();
    let nat = d.nat_ty();

    let sigma_n_eq_n = d.nat_rewrite(i0, n, heq, sigma_i0_eq_n, &|d, x| {
        let sx = d.apply(sigma, &[x]);
        d.eq(sx, n)
    });
    let sigma_n = d.apply(sigma, &[n]);
    let n_eq_sigma_n = d.symm(sigma_n, n, sigma_n_eq_n);

    // InjectiveOn σ n : pure bound-weakening.
    let inj_n = {
        let i_fv = d.fresh_fvar();
        let ivar = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let jvar = d.kernel().fvar(j_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hj_fv = d.fresh_fvar();
        let hj = d.kernel().fvar(hj_fv);
        let heq2_fv = d.fresh_fvar();
        let heq2 = d.kernel().fvar(heq2_fv);
        let si = d.apply(sigma, &[ivar]);
        let sj = d.apply(sigma, &[jvar]);
        let heq2_ty = d.eq(si, sj);
        let i_lt_sn = lift_lt_succ(d, ivar, n, hi);
        let j_lt_sn = lift_lt_succ(d, jvar, n, hj);
        let result = d.apply(inj_sigma, &[ivar, jvar, i_lt_sn, j_lt_sn, heq2]);
        let with_heq2 = d.lam_fv(heq2_fv, heq2_ty, result);
        let hj_ty = d.lt(jvar, n);
        let with_hj = d.lam_fv(hj_fv, hj_ty, with_heq2);
        let hi_ty = d.lt(ivar, n);
        let with_hi = d.lam_fv(hi_fv, hi_ty, with_hj);
        let with_j = d.lam_fv(j_fv, nat, with_hi);
        d.lam_fv(i_fv, nat, with_j)
    };

    // MapsInto σ n.
    let maps_n = {
        let i_fv = d.fresh_fvar();
        let ivar = d.kernel().fvar(i_fv);
        let hi_fv = d.fresh_fvar();
        let hi = d.kernel().fvar(hi_fv);
        let hi_ty = d.lt(ivar, n);
        let i_lt_sn = lift_lt_succ(d, ivar, n, hi);
        let si = d.apply(sigma, &[ivar]);
        let si_lt_sn = d.apply(maps_sigma, &[ivar, i_lt_sn]);
        let si_le_n = d.lemma(p.nat.le_of_lt_succ, &[si, n, si_lt_sn]);

        let si_ne_n = {
            let e_fv = d.fresh_fvar();
            let e = d.kernel().fvar(e_fv);
            let eq_sin_ty = d.eq(si, n);
            let si_eq_sigma_n = d.trans(si, n, sigma_n, e, n_eq_sigma_n);
            let n_lt_sn = d.lemma(p.nat.lt_succ_self, &[n]);
            let i_eq_n = d.apply(inj_sigma, &[ivar, n, i_lt_sn, n_lt_sn, si_eq_sigma_n]);
            let motive = d.eq_motive(ivar, &|d, x| d.lt(x, n));
            let n_lt_n = d.transport(ivar, motive, hi, n, i_eq_n);
            let false_pf = d.lemma(p.nat.lt_irrefl, &[n, n_lt_n]);
            d.lam_fv(e_fv, eq_sin_ty, false_pf)
        };
        let si_lt_n = {
            let disj = d.lemma(p.nat.lt_or_eq_of_le, &[si, n, si_le_n]);
            let lt_sin = d.lt(si, n);
            let eq_sin = d.eq(si, n);
            let target = d.lt(si, n);
            d.or_elim(lt_sin, eq_sin, target, disj, &|_d, hh| hh, &|d, hh| {
                let false_pf = d.apply(si_ne_n, &[hh]);
                d.absurd(target, false_pf)
            })
        };
        let with_hi = d.lam_fv(hi_fv, hi_ty, si_lt_n);
        d.lam_fv(i_fv, nat, with_hi)
    };

    let ih_result = d.apply(ih, &[sigma, inj_n, maps_n]);

    let f_comp_sigma = compose(d, f, sigma);
    let f_prior = d.const_app(p.prod_range, &[f, n]);
    let g_prior = d.const_app(p.prod_range, &[f_comp_sigma, n]);
    let fn_ = d.apply(f, &[n]);
    let f_sigma_n = d.apply(f, &[sigma_n]);

    let start = d.imul(f_prior, fn_);
    let mid = d.imul(g_prior, fn_);
    let h1 = d.icongr(f_prior, g_prior, ih_result, &|d, t| d.imul(t, fn_));
    let end_ = d.imul(g_prior, f_sigma_n);
    let fn_eq_fsigman = d.nat_eq_to_int(n, sigma_n, n_eq_sigma_n, &|d, x| d.apply(f, &[x]));
    let h2 = d.icongr(fn_, f_sigma_n, fn_eq_fsigman, &|d, t| d.imul(g_prior, t));
    let (_e, proof) = d.ichain(start, &[(mid, h1), (end_, h2)]);
    proof
}

/// Branch `i0 < n` of [`permute_step`]: apply `point_swap` to `g := f ∘ σ` at
/// `(i0, n)`, moving `g i0 = f (σ i0) = f n` onto the top slot; the remaining
/// product over `[0, n)` is then reindexed through `Nat.restrict_injective`/
/// `Nat.restrict_maps_into`'s override `τ := point_override σ i0 (σ n)`,
/// closing with the induction hypothesis applied to `τ` (see `wilson.rs`'s
/// module doc: this is an override, not a downward reindex — `i0 < n` already
/// puts `i0` inside the smaller domain).
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn permute_branch_swap(
    d: &mut IntDev<'_>,
    f: ExprId,
    n: ExprId,
    sigma: ExprId,
    inj_sigma: ExprId,
    maps_sigma: ExprId,
    i0: ExprId,
    h_i0_lt_n: ExprId,
    sigma_i0_eq_n: ExprId,
    ih: ExprId,
) -> ExprId {
    let _ = inj_sigma;
    let _ = maps_sigma;
    let p = d.int();
    let nat = d.nat_ty();
    let sn = d.succ(n);
    let g = compose(d, f, sigma);

    // h := point_swap g i0 n.
    let h_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = point_swap(d, g, i0, n, k);
        d.lam_fv(k_fv, nat, body)
    };
    let at_p_fact = point_swap_eq_at_p(d, g, i0, n);
    let at_q_fact = point_swap_eq_at_q(d, g, i0, n, h_i0_lt_n);

    let agree_g_h = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let nei0_fv = d.fresh_fvar();
        let ne_i0 = d.kernel().fvar(nei0_fv);
        let nen_fv = d.fresh_fvar();
        let ne_n = d.kernel().fvar(nen_fv);
        let body = general_swap_agree(d, g, i0, n, k, ne_i0, ne_n, h_i0_lt_n);
        let eq_ne_n_ty = d.eq(k, n);
        let ne_n_ty = d.not(eq_ne_n_ty);
        let eq_ne_i0_ty = d.eq(k, i0);
        let ne_i0_ty = d.not(eq_ne_i0_ty);
        let with_nen = d.lam_fv(nen_fv, ne_n_ty, body);
        let with_nei0 = d.lam_fv(nei0_fv, ne_i0_ty, with_nen);
        d.lam_fv(k_fv, nat, with_nei0)
    };

    let n_lt_sn = d.lemma(p.nat.lt_succ_self, &[n]);
    let swap_result = d.const_app(
        p.prod_range_swap,
        &[
            g, h_fn, i0, n, sn, h_i0_lt_n, n_lt_sn, at_p_fact, at_q_fact, agree_g_h,
        ],
    );

    // h n = g i0 = f (σ i0) = f n.
    let h_n = d.apply(h_fn, &[n]);
    let g_i0 = d.apply(g, &[i0]);
    let f_n = d.apply(f, &[n]);
    let sigma_i0 = d.apply(sigma, &[i0]);
    let fsi0_eq_fn = d.nat_eq_to_int(sigma_i0, n, sigma_i0_eq_n, &|d, x| d.apply(f, &[x]));
    let h_n_eq_f_n = d.itrans(h_n, g_i0, f_n, at_q_fact, fsi0_eq_fn);

    let h_range_n = d.const_app(p.prod_range, &[h_fn, n]);
    let mid2 = d.imul(h_range_n, f_n);
    let step_hn = d.icongr(h_n, f_n, h_n_eq_f_n, &|d, t| d.imul(h_range_n, t));
    let prod_range_g_sn = d.const_app(p.prod_range, &[g, sn]);
    let start2 = d.imul(h_range_n, h_n);
    let combined = d.itrans(prod_range_g_sn, start2, mid2, swap_result, step_hn);

    // τ := point_override σ i0 (σ n).
    let sigma_n = d.apply(sigma, &[n]);
    let tau_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = point_override(d, sigma, i0, sigma_n, k);
        d.lam_fv(k_fv, nat, body)
    };
    let inj_tau_n = d.const_app(
        p.nat.restrict_injective,
        &[sigma, i0, n, inj_sigma, h_i0_lt_n],
    );
    let maps_tau_n = d.const_app(
        p.nat.restrict_maps_into,
        &[
            sigma,
            i0,
            n,
            inj_sigma,
            maps_sigma,
            h_i0_lt_n,
            sigma_i0_eq_n,
        ],
    );
    let ih_result = d.apply(ih, &[tau_fn, inj_tau_n, maps_tau_n]);

    let f_comp_tau = compose(d, f, tau_fn);
    let prod_range_ftau_n = d.const_app(p.prod_range, &[f_comp_tau, n]);
    let prod_range_f_n = d.const_app(p.prod_range, &[f, n]);

    // pointwise_h_tau : ∀ k, Lt k n → Eq Int (h k) ((f∘τ) k).
    let pointwise_h_tau = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let hk_fv = d.fresh_fvar();
        let hk = d.kernel().fvar(hk_fv);
        let hk_ty = d.lt(k, n);

        let h_k = d.apply(h_fn, &[k]);
        let ftau_k = d.apply(f_comp_tau, &[k]);
        let target = d.ieq(h_k, ftau_k);

        let lt_k_i0 = d.lt(k, i0);
        let eq_k_i0 = d.eq(k, i0);
        let lt_i0_k = d.lt(i0, k);
        let inner_or = d.or(eq_k_i0, lt_i0_k);
        let tri = nat_trichotomy(d, k, i0);

        let on_lt = &|d: &mut IntDev<'_>, h_k_lt_i0: ExprId| -> ExprId {
            let hk_eq_gk = point_swap_eq_lt_p(d, g, i0, n, k, h_k_lt_i0);
            let tau_k_eq_sigma_k = override_eq_lt(d, sigma, i0, sigma_n, k, h_k_lt_i0);
            let tau_k = d.apply(tau_fn, &[k]);
            let sigma_k = d.apply(sigma, &[k]);
            let f_tauk_eq_f_sigmak =
                d.nat_eq_to_int(tau_k, sigma_k, tau_k_eq_sigma_k, &|d, x| d.apply(f, &[x]));
            let f_tau_k_pt = d.apply(f, &[tau_k]);
            let f_sigma_k_pt = d.apply(f, &[sigma_k]);
            let f_sigmak_eq_f_tauk = d.isymm(f_tau_k_pt, f_sigma_k_pt, f_tauk_eq_f_sigmak);
            let g_k = d.apply(g, &[k]);
            d.itrans(h_k, g_k, ftau_k, hk_eq_gk, f_sigmak_eq_f_tauk)
        };
        let on_eq = &|d: &mut IntDev<'_>, heq: ExprId| -> ExprId {
            let tau_i0_eq_sigma_n = override_eq_at(d, sigma, i0, sigma_n);
            let tau_i0 = d.apply(tau_fn, &[i0]);
            let f_tau_i0_eq_f_sigma_n =
                d.nat_eq_to_int(tau_i0, sigma_n, tau_i0_eq_sigma_n, &|d, x| d.apply(f, &[x]));
            let f_tau_i0_pt = d.apply(f, &[tau_i0]);
            let f_sigma_n_pt = d.apply(f, &[sigma_n]);
            let f_sigman_eq_ftaui0 = d.isymm(f_tau_i0_pt, f_sigma_n_pt, f_tau_i0_eq_f_sigma_n);
            let g_n = d.apply(g, &[n]);
            let h_i0 = d.apply(h_fn, &[i0]);
            let ftau_i0 = d.apply(f_comp_tau, &[i0]);
            let proof_at_i0 = d.itrans(h_i0, g_n, ftau_i0, at_p_fact, f_sigman_eq_ftaui0);
            let heq_rev = d.symm(k, i0, heq);
            let motive = d.eq_motive(i0, &|d, x| {
                let hx = d.apply(h_fn, &[x]);
                let ftaux = d.apply(f_comp_tau, &[x]);
                d.ieq(hx, ftaux)
            });
            d.transport(i0, motive, proof_at_i0, k, heq_rev)
        };
        let on_gt = &|d: &mut IntDev<'_>, h_i0_lt_k: ExprId| -> ExprId {
            let hk_eq_gk = point_swap_eq_between(d, g, i0, n, k, h_i0_lt_k, hk);
            let tau_k_eq_sigma_k = override_eq_gt(d, sigma, i0, sigma_n, k, h_i0_lt_k);
            let tau_k = d.apply(tau_fn, &[k]);
            let sigma_k = d.apply(sigma, &[k]);
            let f_tauk_eq_f_sigmak =
                d.nat_eq_to_int(tau_k, sigma_k, tau_k_eq_sigma_k, &|d, x| d.apply(f, &[x]));
            let f_tau_k_pt = d.apply(f, &[tau_k]);
            let f_sigma_k_pt = d.apply(f, &[sigma_k]);
            let f_sigmak_eq_f_tauk = d.isymm(f_tau_k_pt, f_sigma_k_pt, f_tauk_eq_f_sigmak);
            let g_k = d.apply(g, &[k]);
            d.itrans(h_k, g_k, ftau_k, hk_eq_gk, f_sigmak_eq_f_tauk)
        };

        let body = d.or_elim(lt_k_i0, inner_or, target, tri, on_lt, &|d, h_inner| {
            d.or_elim(eq_k_i0, lt_i0_k, target, h_inner, on_eq, on_gt)
        });

        let with_hk = d.lam_fv(hk_fv, hk_ty, body);
        d.lam_fv(k_fv, nat, with_hk)
    };

    let cong_h_tau = d.const_app(
        p.prod_range_congr_lt,
        &[h_fn, f_comp_tau, n, pointwise_h_tau],
    );
    let ih_result_rev = d.isymm(prod_range_f_n, prod_range_ftau_n, ih_result);
    let h_range_eq_f_range = d.itrans(
        h_range_n,
        prod_range_ftau_n,
        prod_range_f_n,
        cong_h_tau,
        ih_result_rev,
    );
    let f_n_range_times_fn = d.imul(prod_range_f_n, f_n);
    let step_final = d.icongr(h_range_n, prod_range_f_n, h_range_eq_f_range, &|d, t| {
        d.imul(t, f_n)
    });
    let whole = d.itrans(
        prod_range_g_sn,
        mid2,
        f_n_range_times_fn,
        combined,
        step_final,
    );
    d.isymm(prod_range_g_sn, f_n_range_times_fn, whole)
}

/// The successor step of `Int.prodRange_permute`'s induction: given
/// `ih : permute_motive(f, n)`, produce a proof of `permute_motive(f, succ n)`.
/// The pigeonhole (`Nat.injective_on_imp_surjective_on`) locates `i0 < succ n`
/// with `σ i0 = n`; [`permute_branch_fixed`] handles `i0 = n`,
/// [`permute_branch_swap`] handles `i0 < n`.
fn permute_step(d: &mut IntDev<'_>, f: ExprId, n: ExprId, ih: ExprId) -> ExprId {
    let p = d.int();
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let sn = d.succ(n);

    let sigma_fv = d.fresh_fvar();
    let sigma = d.kernel().fvar(sigma_fv);
    let inj_ty = d.const_app(p.nat.injective_on, &[sigma, sn]);
    let inj_fv = d.fresh_fvar();
    let inj_sigma = d.kernel().fvar(inj_fv);
    let maps_ty = d.const_app(p.nat.maps_into, &[sigma, sn]);
    let maps_fv = d.fresh_fvar();
    let maps_sigma = d.kernel().fvar(maps_fv);

    let f_comp_sigma = compose(d, f, sigma);
    let lhs = d.const_app(p.prod_range, &[f, sn]);
    let rhs = d.const_app(p.prod_range, &[f_comp_sigma, sn]);
    let target = d.ieq(lhs, rhs);

    // Pigeonhole: SurjectiveOn σ (succ n), applied at n.
    let surj = d.const_app(
        p.nat.injective_on_imp_surjective_on,
        &[sn, sigma, inj_sigma, maps_sigma],
    );
    let n_lt_sn = d.lemma(p.nat.lt_succ_self, &[n]);
    let ex = d.apply(surj, &[n, n_lt_sn]);

    let predicate = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let bound = d.lt(i, sn);
        let si = d.apply(sigma, &[i]);
        let eqn = d.eq(si, n);
        let body = d.and(bound, eqn);
        d.lam_fv(i_fv, nat, body)
    };

    let minor = {
        let i0_fv = d.fresh_fvar();
        let i0 = d.kernel().fvar(i0_fv);
        let hand_fv = d.fresh_fvar();
        let hand = d.kernel().fvar(hand_fv);
        let bound_ty = d.lt(i0, sn);
        let si0 = d.apply(sigma, &[i0]);
        let eqn_ty = d.eq(si0, n);
        let hand_ty = d.and(bound_ty, eqn_ty);
        let h_i0_lt_sn = d.and_left(bound_ty, eqn_ty, hand);
        let sigma_i0_eq_n = d.and_right(bound_ty, eqn_ty, hand);

        let le_i0_n = d.lemma(p.nat.le_of_lt_succ, &[i0, n, h_i0_lt_sn]);
        let disj = d.lemma(p.nat.lt_or_eq_of_le, &[i0, n, le_i0_n]);
        let lt_i0_n = d.lt(i0, n);
        let eq_i0_n = d.eq(i0, n);

        let on_lt = &|d: &mut IntDev<'_>, h_i0_lt_n: ExprId| -> ExprId {
            permute_branch_swap(
                d,
                f,
                n,
                sigma,
                inj_sigma,
                maps_sigma,
                i0,
                h_i0_lt_n,
                sigma_i0_eq_n,
                ih,
            )
        };
        let on_eq = &|d: &mut IntDev<'_>, heq: ExprId| -> ExprId {
            permute_branch_fixed(
                d,
                f,
                n,
                sigma,
                inj_sigma,
                maps_sigma,
                i0,
                heq,
                sigma_i0_eq_n,
                ih,
            )
        };
        let body = d.or_elim(lt_i0_n, eq_i0_n, target, disj, on_lt, on_eq);
        let with_hand = d.lam_fv(hand_fv, hand_ty, body);
        d.lam_fv(i0_fv, nat, with_hand)
    };

    let final_for_sigma = exists_elim(d, predicate, target, ex, minor);

    let with_maps = d.lam_fv(maps_fv, maps_ty, final_for_sigma);
    let with_inj = d.lam_fv(inj_fv, inj_ty, with_maps);
    d.lam_fv(sigma_fv, fn_ty, with_inj)
}

/// Declare `Int.prodRange_permute` — the assembly `wilson.rs`'s module doc
/// names as the last step toward Wilson's theorem's permutation argument.
/// Induction on `n`, with `f` quantified OUTSIDE the recursion and the
/// motive generalized over `σ` (see the module doc above [`permute_step`]).
///
/// # Errors
///
/// Returns the trusted gate's rejection if the constructed term does not
/// check.
pub(super) fn declare_prod_range_permute(d: &mut IntDev<'_>) -> Result<(), KernelError> {
    let p = d.int();
    let nat = d.nat_ty();
    let int_ty = d.int_ty();
    let fn_ty_int = d.arrow(nat, int_ty);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let stmt_at_n = permute_motive(d, f, n);
    let proof = d.induct(
        &|d, x| permute_motive(d, f, x),
        &|d| permute_base(d, f),
        &|d, m, ih| permute_step(d, f, m, ih),
        n,
    );

    let value = {
        let with_n = d.lam_fv(n_fv, nat, proof);
        d.lam_fv(f_fv, fn_ty_int, with_n)
    };
    let full_stmt = {
        let with_n = d.pi_fv(n_fv, nat, stmt_at_n);
        d.pi_fv(f_fv, fn_ty_int, with_n)
    };

    d.declare_theorem(p.prod_range_permute, full_stmt, value)
}
