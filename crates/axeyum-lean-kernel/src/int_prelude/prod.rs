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
