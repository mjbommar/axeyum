//! `Rat.polyEval` — evaluating a polynomial at a point, over `ℚ`.
//!
//! # The representation
//!
//! This kernel has no `List` and no tuple type (`Rat.det2` takes four
//! separate arguments for exactly this reason), so a polynomial is a
//! **coefficient function** `Nat → Rat` together with an explicit degree
//! bound `n`, the same shape [`super::sum::RatPrelude::sum_range`] already
//! takes a function and a bound: `polyEval c n x := sumRange (fun i => c i *
//! x^i) n`.
//!
//! # `Rat.pow`
//!
//! `ℚ` had no `pow` before this file. It is admitted here by structural
//! recursion on the natural exponent, mirroring `Int.pow`
//! (`int_prelude/defs.rs::declare_pow`) exactly: `pow a zero ≡ one`,
//! `pow a (succ j) ≡ mul (pow a j) a` — the new factor on the RIGHT, the same
//! convention `Complex.pow` uses and `Int.pow`/`Nat.pow` both use.
//!
//! # What is proved
//!
//! - `polyEval_zero`/`polyEval_succ`: the defining equations, both closed by
//!   `Eq.refl` alone — `polyEval` is a plain (non-recursive) `Definition`
//!   wrapping `sumRange`, so it unfolds (`δ`) to `sumRange`'s own `Nat.rec`
//!   application and the usual `ι`/`β` steps finish it, exactly as
//!   [`super::sum::declare_sum_range_equations`]'s own two equations do.
//! - `polyEval_add`: evaluation is additive, via `Rat.right_distrib`
//!   pointwise (`Rat.sumRange_congr`) then `Rat.sumRange_add`.
//! - `polyEval_smul`: a scalar distributes through evaluation, via
//!   `Rat.mul_assoc` pointwise then `Rat.mul_sumRange` (symm'd — that lemma
//!   runs the other direction).
//!
//! - `pow_add`/`pow_sub_add`: the exponent law and the **antidiagonal cell
//!   collapse** `i ≤ k → x^k = x^(k−i) · x^i`, which is what a polynomial
//!   product needs at every point of the antidiagonal `i + j = k`.
//!
//! # Where `polyEval_mul` stands
//!
//! Still not here — but this section has now been wrong twice in opposite
//! directions, so it states what is CHECKED and what is not.
//!
//! Checked and available:
//!
//! - the `ℚ` reindexing machinery ([`super::diagonal`]:
//!   `Rat.sumRange_split`, `Rat.sumRange_diagonal`,
//!   `Rat.sumRange_rect_eq_diag_add_corner`);
//! - a PRODUCT of two `sumRange`s carried all the way to
//!   `(antidiagonal triangle) + corner`
//!   ([`super::diagonal::declare_sum_range_mul_eq_diag_add_corner`]), with
//!   the rectangle steps ([`super::diagonal::declare_sum_range_mul`],
//!   [`super::diagonal::declare_sum_range_mul_double`]) general in TWO
//!   independent bounds;
//! - the cell collapse [`declare_pow_sub_add`], so the antidiagonal summand
//!   `(a i · x^i) · (b (k−i) · x^(k−i))` can become `(a i · b (k−i)) · x^k`.
//!
//! What remains is therefore neither reindexing nor `pow` arithmetic. It is
//! (1) a four-factor commutative-ring rearrangement of that cell, done under
//! `sumRange_congr_lt` because the collapse needs `i ≤ k` and only the
//! RESTRICTED congruence carries a bound hypothesis; and (2) a decision about
//! the statement, because **the corner does not simplify to a `polyEval`**.
//! `polyEval a n x · polyEval b n x` equals `polyEval (conv a b) n x` plus a
//! corner term that is not itself a polynomial evaluation, so the honest
//! `polyEval_mul` is a three-term identity, not the two-term one its name
//! suggests. See [`super::diagonal`]'s module doc for why the corner is
//! real (the naive identity is refuted at `n = 2`) and
//! `sum_range_mul_eq_diag_add_corner_computes_and_the_naive_identity_is_false`
//! for the concrete instance where the corner is 66 of 91.

use super::RatPrelude;
use super::ops::{
    nat_eq_to_rat, radd, rat_ty, rchain, rcongr, req, rmul, rone, rpoly_eval, rpow, rrefl,
    rsum_range, rsymm, rzero,
};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.pow`: above `Rat.one`/`Rat.mul` (both far below —
/// `Rat.mul` is carried by `int_prelude`, `Rat.one` at `rat_prelude::defs`'s
/// `LEAF_HEIGHT` = 30) and above every other height declared so far in this
/// prelude (`PairwiseUncorrelated` at `rat_prelude::probability`'s
/// `PAIRWISE_UNCORRELATED_HEIGHT` = 41).
const POW_HEIGHT: u16 = 42;
/// Height for `Rat.polyEval`, which calls `Rat.pow` (42) and `Rat.sumRange`
/// (`rat_prelude::sum`'s `SUM_HEIGHT` = 34) — above both.
const POLY_EVAL_HEIGHT: u16 = 43;

/// Declare `Rat.pow` and everything this file proves about it and
/// `Rat.polyEval`.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_polynomial(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_pow(d, p)?;
    declare_pow_equations(d, p)?;
    declare_pow_add(d, p)?;
    declare_pow_sub_add(d, p)?;
    declare_poly_eval(d, p)?;
    declare_poly_eval_equations(d, p)?;
    declare_poly_eval_add(d, p)?;
    declare_poly_eval_smul(d, p)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// `Rat.pow`.
// ---------------------------------------------------------------------------

/// `Rat.pow : Rat → Nat → Rat`, structural `Nat.rec` on the exponent:
/// `pow a zero ≡ Rat.one`, `pow a (succ j) ≡ Rat.mul (pow a j) a` — mirroring
/// `Int.pow` (`int_prelude/defs.rs::declare_pow`) exactly.
fn declare_pow(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one_level = d.level_one();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let minor_zero = rone(d, p);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let body = rmul(d, ih, a);
        let inner = d.lam_fv(ih_fv, carrier, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let body = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(a_fv, carrier, with_n)
    };
    let ty = {
        let inner = d.arrow(nat, carrier);
        d.arrow(carrier, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.pow,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(POW_HEIGHT),
    })
}

/// `Rat.pow_zero`/`Rat.pow_succ`: the defining equations, each closed by
/// `Eq.refl` alone — `Rat.pow`'s `Nat.rec` application `ι`-reduces on both
/// minor premises, exactly `Int.pow`'s own `pow_zero`/`pow_succ`
/// (`int_prelude/defs.rs::declare_pow_equations`).
fn declare_pow_equations(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();

    // pow_zero : ∀ a, Eq Rat (pow a zero) one.
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let zero = d.zero();
        let lhs = rpow(d, p, a, zero);
        let one = rone(d, p);
        let stmt_inner = req(d, lhs, one);
        let proof_inner = rrefl(d, one);
        let ty = d.pi_fv(a_fv, carrier, stmt_inner);
        let value = d.lam_fv(a_fv, carrier, proof_inner);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.pow_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // pow_succ : ∀ a m, Eq Rat (pow a (succ m)) (mul (pow a m) a).
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);

        let sm = d.succ(m);
        let lhs = rpow(d, p, a, sm);
        let pm = rpow(d, p, a, m);
        let rhs = rmul(d, pm, a);
        let stmt_inner = req(d, lhs, rhs);
        let proof_inner = rrefl(d, rhs);

        let ty = {
            let inner = d.pi_fv(m_fv, nat, stmt_inner);
            d.pi_fv(a_fv, carrier, inner)
        };
        let value = {
            let inner = d.lam_fv(m_fv, nat, proof_inner);
            d.lam_fv(a_fv, carrier, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.pow_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Rat.pow_add : ∀ a (m n : Nat), pow a (Nat.add m n) = mul (pow a m) (pow a n)`.
///
/// Induction on `n`, `a` and `m` fixed — the `Rat` port of `Int.pow_add`
/// (`int_prelude/algebra.rs::declare_pow_add`) step for step, which is the
/// right blueprint because [`declare_pow`] mirrors `Int.pow` exactly (`pow a
/// zero ≡ one`, `pow a (succ j) ≡ mul (pow a j) a`, new factor on the RIGHT).
/// `Nat`, `Int`, `Complex` and `CReal` all already carry this lemma; `ℚ` was
/// the hole.
///
/// The exponent arithmetic is entirely definitional and needs no `Nat` lemma:
/// `Nat.add` recurses on its RIGHT argument, so `add m zero ≡ m` and
/// `add m (succ j) ≡ succ (add m j)` both compute with `m` symbolic. That is
/// why `n` is the induction variable and `m` is held fixed — inducting on `m`
/// instead would leave `add zero n` stuck and drag in `Nat.zero_add`.
///
/// Only the base case is a genuine `Rat` law rather than reduction: `pow a
/// zero` is defeq to `Rat.one`, but `Rat.mul` renormalises, so
/// `mul (pow a m) one = pow a m` is [`RatPrelude::mul_one`](super::RatPrelude::mul_one)
/// and not `Eq.refl` — the same place `Rat.mul_sumRange`'s base case needs
/// `Rat.mul_zero` where `Nat`'s needed nothing.
fn declare_pow_add(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sum = d.add(m, x);
        let lhs = rpow(d, p, a, sum);
        let pow_m = rpow(d, p, a, m);
        let pow_x = rpow(d, p, a, x);
        let rhs = rmul(d, pow_m, pow_x);
        req(d, lhs, rhs)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            // `pow a (add m zero)` computes to `pow a m`; the goal is
            // `pow a m = mul (pow a m) (pow a zero)`, and `pow a zero` is
            // defeq to `one`, so a literal `one` closes it via `mul_one`
            // reversed.
            let pow_m = rpow(d, p, a, m);
            let one = rone(d, p);
            let product = rmul(d, pow_m, one);
            let h = d.lemma(p.mul_one, &[pow_m]);
            rsymm(d, product, pow_m, h)
        },
        &|d, j, ih| {
            // `pow a (add m (succ j))` computes to `mul (pow a (add m j)) a`.
            let pow_m = rpow(d, p, a, m);
            let pow_j = rpow(d, p, a, j);
            let sum_mj = d.add(m, j);
            let pow_sum = rpow(d, p, a, sum_mj);
            let start = rmul(d, pow_sum, a);

            let ih_applied = rmul(d, pow_m, pow_j);
            let after_ih = rmul(d, ih_applied, a);
            let h_ih = rcongr(d, pow_sum, ih_applied, ih, &|d, t| rmul(d, t, a));

            let inner = rmul(d, pow_j, a);
            let associated = rmul(d, pow_m, inner);
            let h_assoc = d.lemma(p.mul_assoc, &[pow_m, pow_j, a]);

            let succ_j = d.succ(j);
            let pow_succ_j = rpow(d, p, a, succ_j);
            let end = rmul(d, pow_m, pow_succ_j);
            let h_pow = d.lemma(p.pow_succ, &[a, j]);
            let h_pow_rev = rsymm(d, pow_succ_j, inner, h_pow);
            let h_end = rcongr(d, inner, pow_succ_j, h_pow_rev, &|d, t| rmul(d, pow_m, t));

            let (_e, proof) = rchain(
                d,
                start,
                &[(after_ih, h_ih), (associated, h_assoc), (end, h_end)],
            );
            proof
        },
        n,
    );

    let ty = {
        let over_n = d.pi_fv(n_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, nat, over_n);
        d.pi_fv(a_fv, carrier, over_m)
    };
    let value = {
        let over_n = d.lam_fv(n_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, nat, over_n);
        d.lam_fv(a_fv, carrier, over_m)
    };
    d.declare_theorem(p.pow_add, ty, value)
}

/// `Rat.pow_sub_add : ∀ x i k, Nat.le i k →`
/// `pow x k = mul (pow x (Nat.sub k i)) (pow x i)`.
///
/// **The antidiagonal cell collapse**, and the reason [`declare_pow_add`] was
/// worth landing. On the antidiagonal `i + j = k` the rectangle machinery
/// hands you the cell at `j = k − i`, so a polynomial product's summand is
/// `(a i · x^i) · (b (k−i) · x^(k−i))` and turning it into
/// `(a i · b (k−i)) · x^k` needs exactly this: the two powers recombine into
/// `x^k` **provided `i ≤ k`**, which on the antidiagonal is free (`i` ranges
/// over `[0, k]`).
///
/// The hypothesis is not decoration. `Nat.sub` TRUNCATES, so without `i ≤ k`
/// the identity is false — at `i = 3`, `k = 1`, `x = 2` it would claim
/// `2 = 2^1 = 2^(1−3) · 2^3 = 2^0 · 8 = 8`.
///
/// No induction: `Nat.sub_add_cancel` gives the INDEX equation
/// `(k − i) + i = k`, [`super::ops::nat_eq_to_rat`] lifts it through
/// `fun e => pow x e` to a VALUE equation, and [`declare_pow_add`] splits the
/// left side. Two rewrites and a `symm` — the same `np` for index facts /
/// local prelude for value facts split `super::diagonal` documents.
fn declare_pow_sub_add(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let np = d.prelude();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let hyp_ty = d.le(i, k);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let sub_ki = d.sub(k, i);
    let pow_k = rpow(d, p, x, k);
    let pow_sub = rpow(d, p, x, sub_ki);
    let pow_i = rpow(d, p, x, i);
    let rhs = rmul(d, pow_sub, pow_i);
    let stmt = req(d, pow_k, rhs);

    // INDEX level: (k − i) + i = k, from `Nat.sub_add_cancel i k h`.
    let h_idx = d.lemma(np.sub_add_cancel, &[i, k, h]);
    let restored = d.add(sub_ki, i);
    // VALUE level: pow x ((k−i)+i) = pow x k.
    let h_lift = nat_eq_to_rat(d, restored, k, h_idx, &|d, e| rpow(d, p, x, e));
    let pow_restored = rpow(d, p, x, restored);
    // pow x k = pow x ((k−i)+i).
    let h_back = rsymm(d, pow_restored, pow_k, h_lift);
    // pow x ((k−i)+i) = pow x (k−i) * pow x i.
    let h_split = d.lemma(p.pow_add, &[x, sub_ki, i]);

    let (_e, proof) = rchain(d, pow_k, &[(pow_restored, h_back), (rhs, h_split)]);

    let ty = {
        let over_h = d.pi_fv(h_fv, hyp_ty, stmt);
        let over_k = d.pi_fv(k_fv, nat, over_h);
        let over_i = d.pi_fv(i_fv, nat, over_k);
        d.pi_fv(x_fv, carrier, over_i)
    };
    let value = {
        let over_h = d.lam_fv(h_fv, hyp_ty, proof);
        let over_k = d.lam_fv(k_fv, nat, over_h);
        let over_i = d.lam_fv(i_fv, nat, over_k);
        d.lam_fv(x_fv, carrier, over_i)
    };
    d.declare_theorem(p.pow_sub_add, ty, value)
}

// ---------------------------------------------------------------------------
// `Rat.polyEval` and its algebra.
// ---------------------------------------------------------------------------

/// `fun i => mul (c i) (pow x i)` — one polynomial's summand function, the
/// argument [`RatPrelude::sum_range`] evaluates.
fn poly_summand(d: &mut IntDev<'_>, p: RatPrelude, c: ExprId, x: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let ci = d.apply(c, &[i]);
    let xi = rpow(d, p, x, i);
    let body = rmul(d, ci, xi);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => add (f i) (g i)` — matches `sumRange_add`'s own internal
/// combined-function shape exactly (`sum.rs`'s own `combined_fn`), reused
/// here both for coefficient functions and for summand functions since both
/// are `Nat → Rat`.
fn combined(d: &mut IntDev<'_>, f: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let gi = d.apply(g, &[i]);
    let body = radd(d, fi, gi);
    d.lam_fv(i_fv, nat, body)
}

/// `fun i => mul a (f i)` — matches `mul_sumRange`'s own internal scaled
/// function shape exactly (`sum.rs`'s own `scaled_fn`), reused here both for
/// coefficient functions and for summand functions.
fn scaled(d: &mut IntDev<'_>, a: ExprId, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let fi = d.apply(f, &[i]);
    let body = rmul(d, a, fi);
    d.lam_fv(i_fv, nat, body)
}

/// `Rat.polyEval : (Nat → Rat) → Nat → Rat → Rat`,
/// `polyEval c n x := sumRange (fun i => c i * x^i) n` — a plain (not
/// recursive) definition, unlike `Rat.sumRange`/`Rat.pow` themselves.
fn declare_poly_eval(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let summand = poly_summand(d, p, c, x);
    let body = rsum_range(d, p, summand, n);

    let value = {
        let with_x = d.lam_fv(x_fv, carrier, body);
        let with_n = d.lam_fv(n_fv, nat, with_x);
        d.lam_fv(c_fv, fn_ty, with_n)
    };
    let ty = {
        let over_x = d.arrow(carrier, carrier);
        let over_n = d.arrow(nat, over_x);
        d.arrow(fn_ty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.poly_eval,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(POLY_EVAL_HEIGHT),
    })
}

/// `Rat.polyEval_zero`/`Rat.polyEval_succ`: the defining equations, each
/// closed by `Eq.refl` alone. `polyEval c n x` `δ`-unfolds to `sumRange (fun
/// i => c i * x^i) n`, which then `ι`/`β`-reduces exactly as
/// [`super::sum::declare_sum_range_equations`]'s own two equations do — no
/// lemma from `sum.rs` is invoked, the unfolding chain does the whole job.
fn declare_poly_eval_equations(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    // polyEval_zero : ∀ c x, Eq Rat (polyEval c zero x) zero.
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);

        let zero_n = d.zero();
        let lhs = rpoly_eval(d, p, c, zero_n, x);
        let zero_r = rzero(d, p);
        let stmt_inner = req(d, lhs, zero_r);
        let proof_inner = rrefl(d, zero_r);

        let ty = {
            let inner = d.pi_fv(x_fv, carrier, stmt_inner);
            d.pi_fv(c_fv, fn_ty, inner)
        };
        let value = {
            let inner = d.lam_fv(x_fv, carrier, proof_inner);
            d.lam_fv(c_fv, fn_ty, inner)
        };
        d.declare_theorem(p.poly_eval_zero, ty, value)?;
    }

    // polyEval_succ : ∀ c n x,
    //   Eq Rat (polyEval c (succ n) x) (add (polyEval c n x) (mul (c n) (pow x n))).
    {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);

        let sn = d.succ(n);
        let lhs = rpoly_eval(d, p, c, sn, x);
        let prior = rpoly_eval(d, p, c, n, x);
        let cn = d.apply(c, &[n]);
        let xn = rpow(d, p, x, n);
        let term_n = rmul(d, cn, xn);
        let rhs = radd(d, prior, term_n);
        let stmt_inner = req(d, lhs, rhs);
        let proof_inner = rrefl(d, rhs);

        let ty = {
            let over_x = d.pi_fv(x_fv, carrier, stmt_inner);
            let over_n = d.pi_fv(n_fv, nat, over_x);
            d.pi_fv(c_fv, fn_ty, over_n)
        };
        let value = {
            let over_x = d.lam_fv(x_fv, carrier, proof_inner);
            let over_n = d.lam_fv(n_fv, nat, over_x);
            d.lam_fv(c_fv, fn_ty, over_n)
        };
        d.declare_theorem(p.poly_eval_succ, ty, value)?;
    }
    Ok(())
}

/// `Rat.polyEval_add : ∀ c g n x,`
/// `polyEval (fun i => c i + g i) n x = polyEval c n x + polyEval g n x` —
/// evaluation is additive.
///
/// Route: pointwise `Rat.right_distrib` at each summand (`(c i + g i) * x^i
/// = c i * x^i + g i * x^i`) lifted to the sums via `Rat.sumRange_congr`,
/// then `Rat.sumRange_add` splits the combined sum.
fn declare_poly_eval_add(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let combined_c = combined(d, c, g);
    let summand_combined = poly_summand(d, p, combined_c, x);
    let summand_c = poly_summand(d, p, c, x);
    let summand_g = poly_summand(d, p, g, x);
    let combined_summands = combined(d, summand_c, summand_g);

    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ci = d.apply(c, &[i]);
        let gi = d.apply(g, &[i]);
        let xi = rpow(d, p, x, i);
        let body = d.lemma(p.right_distrib, &[ci, gi, xi]);
        d.lam_fv(i_fv, nat, body)
    };

    let h1 = d.lemma(
        p.sum_range_congr,
        &[summand_combined, combined_summands, n, pointwise],
    );
    let h2 = d.lemma(p.sum_range_add, &[summand_c, summand_g, n]);

    let start = rsum_range(d, p, summand_combined, n);
    let mid = rsum_range(d, p, combined_summands, n);
    let sum_c = rsum_range(d, p, summand_c, n);
    let sum_g = rsum_range(d, p, summand_g, n);
    let final_rhs = radd(d, sum_c, sum_g);

    let (_e, proof) = rchain(d, start, &[(mid, h1), (final_rhs, h2)]);

    let lhs_stmt = rpoly_eval(d, p, combined_c, n, x);
    let eval_c = rpoly_eval(d, p, c, n, x);
    let eval_g = rpoly_eval(d, p, g, n, x);
    let rhs_stmt = radd(d, eval_c, eval_g);
    let stmt = req(d, lhs_stmt, rhs_stmt);

    let ty = {
        let over_x = d.pi_fv(x_fv, carrier, stmt);
        let over_n = d.pi_fv(n_fv, nat, over_x);
        let over_g = d.pi_fv(g_fv, fn_ty, over_n);
        d.pi_fv(c_fv, fn_ty, over_g)
    };
    let value = {
        let over_x = d.lam_fv(x_fv, carrier, proof);
        let over_n = d.lam_fv(n_fv, nat, over_x);
        let over_g = d.lam_fv(g_fv, fn_ty, over_n);
        d.lam_fv(c_fv, fn_ty, over_g)
    };
    d.declare_theorem(p.poly_eval_add, ty, value)
}

/// `Rat.polyEval_smul : ∀ a c n x,`
/// `polyEval (fun i => a * c i) n x = a * polyEval c n x` — a scalar
/// distributes through evaluation.
///
/// Route: pointwise `Rat.mul_assoc` at each summand (`(a * c i) * x^i = a *
/// (c i * x^i)`) lifted to the sums via `Rat.sumRange_congr`, then
/// `Rat.mul_sumRange` symm'd (that lemma runs `a * sumRange f n = sumRange
/// (a*f) n`, the opposite direction from what is needed here).
fn declare_poly_eval_smul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let carrier = rat_ty(d);
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, carrier);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let scaled_c = scaled(d, a, c);
    let summand_scaled = poly_summand(d, p, scaled_c, x);
    let summand_c = poly_summand(d, p, c, x);
    let scaled_summand = scaled(d, a, summand_c);

    let pointwise = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let ci = d.apply(c, &[i]);
        let xi = rpow(d, p, x, i);
        let body = d.lemma(p.mul_assoc, &[a, ci, xi]);
        d.lam_fv(i_fv, nat, body)
    };

    let h1 = d.lemma(
        p.sum_range_congr,
        &[summand_scaled, scaled_summand, n, pointwise],
    );
    let h2 = d.lemma(p.mul_sum_range, &[a, summand_c, n]);
    // h2 : Eq Rat (mul a (sumRange summand_c n)) (sumRange scaled_summand n)
    let sum_summand_c = rsum_range(d, p, summand_c, n);
    let sum_scaled_summand = rsum_range(d, p, scaled_summand, n);
    let mul_a_sum = rmul(d, a, sum_summand_c);
    let h2_symm = rsymm(d, mul_a_sum, sum_scaled_summand, h2);

    let start = rsum_range(d, p, summand_scaled, n);
    let mid = sum_scaled_summand;
    let final_rhs = mul_a_sum;

    let (_e, proof) = rchain(d, start, &[(mid, h1), (final_rhs, h2_symm)]);

    let lhs_stmt = rpoly_eval(d, p, scaled_c, n, x);
    let eval_c = rpoly_eval(d, p, c, n, x);
    let rhs_stmt = rmul(d, a, eval_c);
    let stmt = req(d, lhs_stmt, rhs_stmt);

    let ty = {
        let over_x = d.pi_fv(x_fv, carrier, stmt);
        let over_n = d.pi_fv(n_fv, nat, over_x);
        let over_c = d.pi_fv(c_fv, fn_ty, over_n);
        d.pi_fv(a_fv, carrier, over_c)
    };
    let value = {
        let over_x = d.lam_fv(x_fv, carrier, proof);
        let over_n = d.lam_fv(n_fv, nat, over_x);
        let over_c = d.lam_fv(c_fv, fn_ty, over_n);
        d.lam_fv(a_fv, carrier, over_c)
    };
    d.declare_theorem(p.poly_eval_smul, ty, value)
}
