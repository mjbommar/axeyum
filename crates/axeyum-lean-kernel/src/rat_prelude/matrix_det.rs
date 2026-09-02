//! **`Rat.det`** — the determinant at *general* `n`, by cofactor expansion
//! along the first row.
//!
//! [`super::matrix`] has `Rat.det2` and `Rat.det3` at fixed dimension, and
//! [`super::matrix_n`] has `Rat.matMul` at symbolic dimension. This file is
//! the missing piece named as linear algebra's keystone in
//! `docs/curriculum/DEPTH-PROPOSAL-number-theory-and-linear-algebra.md`: a
//! determinant that takes the dimension as an argument.
//!
//! ## The encoding
//!
//! A matrix is a function `Nat → Nat → Rat` plus an explicit bound, exactly as
//! in [`super::matrix_n`] — this kernel has no `List`, `Finset`, `Prod` or
//! vector type, so a finite family is a function plus a bound and nothing else.
//!
//! **Scoped, 2026-08-31 (ADR-1310).** The clause after the dash reads as a law
//! and is an inventory: `Nat.Pair` (2026-08-29) and `Nat.Primrec` (2026-08-31)
//! were both added by ordinary `Kernel::add_inductive` calls, and an inductive
//! contributes **zero** rows to `Kernel::axiom_footprint`. The encoding here is
//! still the right one — `Nat.Fin` already exists and has zero non-test
//! consumers, so the development has declined an indexed finite type once
//! already — but "and nothing else" overstates it. In particular a finite
//! family does not need a type at all: it needs a FOLD, and `Int.sumMaps`
//! (`int_prelude/sum_maps.rs`) folds over an entire FUNCTION SPACE by `Nat.rec`
//! with a higher-order motive, which is the same device `Rat.det` uses below.
//! See the "what actually blocks multiplicativity" section of ADR-1310 before
//! quoting either this paragraph or ADR-1135's three-route wall.
//! The determinant is then
//!
//! ```text
//! det A 0        = 1
//! det A (succ m) = sumRange (fun j => altSign j * (A 0 j * det (matMinor A 0 j) m)) (succ m)
//! ```
//!
//! The recursion is a `Nat.rec` **whose motive is a function type**,
//! `fun _ : Nat => (Nat → Nat → Rat) → Rat`, because the recursive call is at a
//! *different matrix* (the minor) rather than at the same one. That is the only
//! structural subtlety in the definition; everything else is ordinary index
//! arithmetic.
//!
//! ### The minor is an index shift, not a data structure
//!
//! [`RatPrelude::mat_skip`](super::RatPrelude::mat_skip) is
//! `matSkip p x := if p ≤ x then x+1 else x`, the order-preserving injection
//! `[0,n) → [0,n+1)` that misses `p`, built from `Nat.ble` and
//! [`NatOps::bool_select_nat`]. Then
//! `matMinor A i j r c := A (matSkip i r) (matSkip j c)` deletes row `i` and
//! column `j` with no copying and no container.
//!
//! ### The sign is a `Nat.rec`, deliberately
//!
//! `altSign j = (-1)^j` is defined by `altSign 0 = 1`,
//! `altSign (succ j) = neg (altSign j)`, so **both defining equations are
//! `Eq.refl`**. Defining it as `if j % 2 = 0 then 1 else -1` would have made
//! `altSign_succ` a parity induction for no gain, and would have formed a
//! `Nat.mod` at every summand — this kernel's numerals are unary, so a formed
//! magnitude is a real cost (see the `Nat` numeral entry in `CLAUDE.md`).
//! Every value `altSign` forms is `1` or an iterated `neg` of it, magnitude 1.
//!
//! ## What is proved, and what is only defined
//!
//! **The trusted gate cannot tell you a `Definition` is wrong** — it
//! type-checks a stated type and `(Nat → Nat → Rat) → Nat → Rat` is that type
//! whatever the function returns. So the correctness evidence here is
//! *agreement* and *evaluation*, both admitted as theorems:
//!
//! - [`RatPrelude::det_eq_det2`](super::RatPrelude::det_eq_det2) and
//!   [`RatPrelude::det_eq_det3`](super::RatPrelude::det_eq_det3) — `det A 2`
//!   and `det A 3` equal `Rat.det2`/`Rat.det3` on the entries, **symbolically**
//!   in a universally quantified matrix. This is the strongest check available:
//!   `det3`'s six signed products were written independently, years of this
//!   prelude's history apart from this file, and a transposed index or a sign
//!   error in the cofactor recursion cannot survive it.
//! - [`RatPrelude::det_one`](super::RatPrelude::det_one) — `det A 1 = A 0 0`.
//! - Concrete evaluations at a **non-symmetric** 3×3, a **singular** 3×3, and
//!   a 4×4, each closed by `Eq.refl` against an independently computed value.
//!   Each was chosen so that a plausible mutation of the recursion changes the
//!   answer, and each declaration's doc records which mutation it separates and
//!   which it does not — a `0` that stays `0` under a sign flip is not evidence
//!   about the sign.
//!
//! Nothing here proves multiplicativity, `det Aᵀ = det A`, expansion along a
//! *general* row, or `det matId n = 1` at symbolic `n`. Those need an induction
//! over the minor structure and are honestly out of scope for this file; the
//! definition and its agreement with the fixed-dimension determinants is what
//! landed.
//!
//! ## Every statement is pointwise where it touches a matrix
//!
//! `funext` is absent from this kernel (positive control of the same kind,
//! present: `congrFun'`), so no statement below is an `Eq` between two
//! `Nat → Nat → Rat` values. `det` returns a scalar, so this costs nothing
//! here — but it is why `matMinor` is exposed as a five-argument *applied*
//! form rather than as a matrix-valued equation.

use super::RatPrelude;
use super::matrix::{det2_zero_of_ad_eq_bc, rdet2, rdet3};
use super::ops::{
    nat_eq_to_rat, nat_rewrite_prop, radd, rat_theorem, rat_ty, rchain, rcongr, req, rmul, rneg,
    rone, rrefl, rsum_range, rsymm, rtrans, rzero,
};
use super::probability::{bool_select_rat, select_rat_false, select_rat_true};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::{BinderInfo, ExprId};
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.matSkip` and `Rat.altSign`: above every height this
/// prelude declares today (the highest is `MAT_INV2_HEIGHT` = 48), following
/// the "outranks everything it unfolds to" convention `super::defs` sets.
const SKIP_HEIGHT: u16 = 49;

/// Delta height for `Rat.matMinor`: one above [`SKIP_HEIGHT`], which it calls.
const MINOR_HEIGHT: u16 = 50;

/// Delta height for `Rat.unskip`, alongside [`SKIP_HEIGHT`]: it calls only
/// `Nat.pred` and `Nat.rec`, never `Rat.matSkip`, so it does not outrank it.
const UNSKIP_HEIGHT: u16 = 49;

/// Delta height for `Rat.det`: above [`MINOR_HEIGHT`], `Rat.altSign` and
/// `Rat.sumRange`, all of which it unfolds to.
const DET_HEIGHT: u16 = 51;

/// Admit `Rat.det` and everything this file proves about it.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_matrix_det(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_mat_skip(d, p)?;
    declare_mat_minor(d, p)?;
    declare_alt_sign(d, p)?;
    declare_alt_sign_equations(d, p)?;
    declare_det(d, p)?;
    declare_det_equations(d, p)?;
    declare_det_one(d, p)?;
    declare_det_eq_det2(d, p)?;
    declare_det_eq_det3(d, p)?;
    declare_mat_minor_eval_example(d, p)?;
    declare_det_eval_example(d, p)?;
    declare_det_eval_singular(d, p)?;
    declare_det_eval_example4(d, p)?;
    declare_sum_range_head_of_tail_zero(d, p)?;
    declare_det_congr(d, p)?;
    declare_mat_minor_mat_id(d, p)?;
    declare_det_mat_id(d, p)?;
    declare_mat_skip_zero(d, p)?;
    declare_mat_skip_succ_succ(d, p)?;
    declare_mat_skip_comm(d, p)?;
    declare_mat_minor_col_comm(d, p)?;
    declare_det_minor_col_comm(d, p)?;
    declare_sum_range_peel_head(d, p)?;
    declare_sum_range_mat_skip(d, p)?;
    declare_unskip(d, p)?;
    declare_unskip_equations(d, p)?;
    declare_unskip_mat_skip(d, p)?;
    declare_beq_mat_skip(d, p)?;
    declare_alt_sign_succ_add(d, p)?;
    declare_ble_flip_of_false(d, p)?;
    declare_unskip_bounds(d, p)?;
    declare_double_minor_comm(d, p)?;
    declare_mul_perm4(d, p)?;
    declare_laplace_summand(d, p)?;
    declare_laplace_summand_row_zero(d, p)?;
    declare_laplace_summand_row_i(d, p)?;
    declare_laplace_summand_diag(d, p)?;
    declare_det_row_expansion(d, p)?;
    declare_mat_minor_row_col_comm(d, p)?;
    declare_det_minor_row_col_comm(d, p)?;
    declare_det_col_expansion(d, p)?;
    declare_mat_minor_transpose(d, p)?;
    declare_det_transpose(d, p)?;
    declare_det_alternating(d, p)?;
    declare_det_row_swap(d, p)?;
    declare_det_row_replaced(d, p)?;
    declare_det_row_zero(d, p)?;
    declare_det_row_smul(d, p)?;
    declare_det_row_multilinear(d, p)?;
    declare_det_mat_mul_2(d, p)
}

// --- shared term builders --------------------------------------------------

/// `Nat → Nat → Rat`, the matrix type (a local copy of `matrix_n`'s private
/// `mat_ty`).
pub(super) fn mat_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let row = d.arrow(nat, carrier);
    d.arrow(nat, row)
}

/// `Rat.matSkip p x`.
pub(super) fn rmat_skip(d: &mut IntDev<'_>, p: RatPrelude, at: ExprId, x: ExprId) -> ExprId {
    d.const_app(p.mat_skip, &[at, x])
}

/// `Rat.matMinor A i j r c`.
fn rmat_minor(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    i: ExprId,
    j: ExprId,
    r: ExprId,
    c: ExprId,
) -> ExprId {
    d.const_app(p.mat_minor, &[a, i, j, r, c])
}

/// `Rat.matMinor A i j`, partially applied — itself a `Nat → Nat → Rat`.
pub(super) fn rmat_minor_of(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    i: ExprId,
    j: ExprId,
) -> ExprId {
    d.const_app(p.mat_minor, &[a, i, j])
}

/// `Rat.altSign j`.
pub(super) fn ralt_sign(d: &mut IntDev<'_>, p: RatPrelude, j: ExprId) -> ExprId {
    d.const_app(p.alt_sign, &[j])
}

/// `Rat.det A n`.
pub(super) fn rdet(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.det, &[a, n])
}

/// `Eq Rat (Rat.mul Rat.one x) x` — this prelude has no `one_mul`, so it is
/// `mul_comm` followed by `mul_one` every time (`super::RatPrelude`'s own
/// note at `mul_one` says the same).
pub(super) fn one_mul_pf(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    let one = rone(d, p);
    let one_x = rmul(d, one, x);
    let x_one = rmul(d, x, one);
    let comm = d.lemma(p.mul_comm, &[one, x]);
    let unit = d.lemma(p.mul_one, &[x]);
    rtrans(d, one_x, x_one, x, comm, unit)
}

/// `Eq Rat (Rat.mul (Rat.neg Rat.one) x) (Rat.neg x)`.
fn neg_one_mul_pf(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    let one = rone(d, p);
    let neg_one = rneg(d, one);
    let lhs = rmul(d, neg_one, x);
    let one_x = rmul(d, one, x);
    let neg_one_x = rneg(d, one_x);
    let neg_x = rneg(d, x);
    // neg_mul : (-a) * b = -(a * b)
    let pull = d.lemma(p.neg_mul, &[one, x]);
    let inner = one_mul_pf(d, p, x);
    let under_neg = rcongr(d, one_x, x, inner, &|d, t| rneg(d, t));
    rtrans(d, lhs, neg_one_x, neg_x, pull, under_neg)
}

/// `Eq Rat (Rat.add Rat.zero (Rat.mul Rat.one (Rat.mul x Rat.one))) x` — the
/// shape `det _ 1` unfolds to, with `x` the single surviving entry.
fn det1_shape_pf(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> (ExprId, ExprId) {
    let zero = rzero(d, p);
    let one = rone(d, p);
    let x_one = rmul(d, x, one);
    let start = {
        let inner = rmul(d, one, x_one);
        radd(d, zero, inner)
    };

    // add zero (mul one (mul x one))  ->  add zero (mul x one)
    let s1 = {
        let pf = one_mul_pf(d, p, x_one);
        let from = rmul(d, one, x_one);
        rcongr(d, from, x_one, pf, &|d, t| radd(d, zero, t))
    };
    let mid1 = radd(d, zero, x_one);

    // add zero (mul x one)  ->  add zero x
    let s2 = {
        let pf = d.lemma(p.mul_one, &[x]);
        rcongr(d, x_one, x, pf, &|d, t| radd(d, zero, t))
    };
    let mid2 = radd(d, zero, x);

    // add zero x -> x
    let s3 = d.lemma(p.zero_add, &[x]);

    let (result, proof) = rchain(d, start, &[(mid1, s1), (mid2, s2), (x, s3)]);
    (result, proof)
}

// --- the definitions -------------------------------------------------------

/// Admit `Rat.matSkip : Nat → Nat → Nat`,
/// `matSkip p x := if Nat.ble p x then Nat.succ x else x`.
///
/// The order-preserving injection `[0, n) → [0, n+1)` whose image misses `p`.
/// `Nat.ble p x` is `p ≤ x`, so the branch taken at `x = p` is `succ x` and
/// index `p` itself is never produced.
fn declare_mat_skip(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let at_fv = d.fresh_fvar();
    let at = d.kernel().fvar(at_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let cond = NatOps::ble(d, at, x);
    let shifted = d.succ(x);
    let body = NatOps::bool_select_nat(d, cond, shifted, x);

    let value = {
        let with_x = d.lam_fv(x_fv, nat, body);
        d.lam_fv(at_fv, nat, with_x)
    };
    let ty = {
        let inner = d.arrow(nat, nat);
        d.arrow(nat, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mat_skip,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SKIP_HEIGHT),
    })
}

/// Admit `Rat.matMinor : (Nat → Nat → Rat) → Nat → Nat → Nat → Nat → Rat`,
/// `matMinor A i j r c := A (matSkip i r) (matSkip j c)` — the submatrix with
/// row `i` and column `j` deleted, as an index reindex.
fn declare_mat_minor(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let row = rmat_skip(d, p, i, r);
    let col = rmat_skip(d, p, j, c);
    let body = d.apply(a, &[row, col]);

    let value = {
        let with_c = d.lam_fv(c_fv, nat, body);
        let with_r = d.lam_fv(r_fv, nat, with_c);
        let with_j = d.lam_fv(j_fv, nat, with_r);
        let with_i = d.lam_fv(i_fv, nat, with_j);
        d.lam_fv(a_fv, mty, with_i)
    };
    let ty = {
        let mut t = carrier;
        for _ in 0..4 {
            t = d.arrow(nat, t);
        }
        d.arrow(mty, t)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mat_minor,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MINOR_HEIGHT),
    })
}

/// Admit `Rat.altSign : Nat → Rat`, `(-1)^j` by `Nat.rec`.
fn declare_alt_sign(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let anon = d.anon_name();
    let one_level = d.level_one();

    let motive = d.kernel().lam(anon, nat, carrier, BinderInfo::Default);
    let minor_zero = rone(d, p);
    let minor_succ = {
        let j_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let body = rneg(d, ih);
        let inner = d.lam_fv(ih_fv, carrier, body);
        d.lam_fv(j_fv, nat, inner)
    };
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let applied = d.apply(rec, &[motive, minor_zero, minor_succ, j]);
    let value = d.lam_fv(j_fv, nat, applied);
    let ty = d.arrow(nat, carrier);

    d.kernel().add_declaration(Declaration::Definition {
        name: p.alt_sign,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SKIP_HEIGHT),
    })
}

/// `Rat.altSign_zero` and `Rat.altSign_succ`: the defining equations, each
/// closed by `Eq.refl` alone since `altSign`'s `Nat.rec` ι-reduces on both
/// minor premises.
fn declare_alt_sign_equations(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.alt_sign_zero, 0, &|d, _v| {
        let zero_n = d.zero();
        let lhs = ralt_sign(d, p, zero_n);
        let one = rone(d, p);
        let stmt = req(d, lhs, one);
        let proof = super::ops::rrefl(d, one);
        (stmt, proof)
    })?;

    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let sj = d.succ(j);
    let lhs = ralt_sign(d, p, sj);
    let prior = ralt_sign(d, p, j);
    let rhs = rneg(d, prior);
    let stmt = req(d, lhs, rhs);
    let proof = super::ops::rrefl(d, rhs);
    let ty = d.pi_fv(j_fv, nat, stmt);
    let value = d.lam_fv(j_fv, nat, proof);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.alt_sign_succ,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `Rat.det : (Nat → Nat → Rat) → Nat → Rat` by cofactor expansion
/// along the first row.
///
/// The `Nat.rec` motive is `fun _ : Nat => (Nat → Nat → Rat) → Rat` — a
/// *function* type, because the recursive call is at the minor rather than at
/// the same matrix. The bound `n` is the recursion variable and the matrix is
/// applied afterwards.
fn declare_det(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let mty = mat_ty(d);
    let anon = d.anon_name();
    let one_level = d.level_one();

    let motive_body = d.arrow(mty, carrier);
    let motive = d.kernel().lam(anon, nat, motive_body, BinderInfo::Default);

    // `fun _ : (Nat → Nat → Rat) => Rat.one`
    let minor_zero = {
        let one = rone(d, p);
        d.kernel().lam(anon, mty, one, BinderInfo::Default)
    };

    // `fun (m : Nat) (ih : (Nat → Nat → Rat) → Rat) (B : Nat → Nat → Rat) =>
    //    sumRange (fun j => altSign j * (B 0 j * ih (matMinor B 0 j))) (succ m)`
    let minor_succ = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);

        let summand = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let zero_n = d.zero();
            let entry = d.apply(b, &[zero_n, j]);
            let sub = rmat_minor_of(d, p, b, zero_n, j);
            let rec_call = d.apply(ih, &[sub]);
            let product = rmul(d, entry, rec_call);
            let sign = ralt_sign(d, p, j);
            let body = rmul(d, sign, product);
            d.lam_fv(j_fv, nat, body)
        };
        let sm = d.succ(m);
        let sum = rsum_range(d, p, summand, sm);

        let with_b = d.lam_fv(b_fv, mty, sum);
        let with_ih = d.lam_fv(ih_fv, motive_body, with_b);
        d.lam_fv(m_fv, nat, with_ih)
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let rec_name = d.prelude().rec;
    let rec = d.kernel().const_(rec_name, vec![one_level]);
    let recursed = d.apply(rec, &[motive, minor_zero, minor_succ, n]);
    let body = d.apply(recursed, &[a]);

    let value = {
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(a_fv, mty, with_n)
    };
    let ty = {
        let over_n = d.arrow(nat, carrier);
        d.arrow(mty, over_n)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.det,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(DET_HEIGHT),
    })
}

/// `Rat.det_zero` and `Rat.det_succ`: the defining equations, both `Eq.refl`.
fn declare_det_equations(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    // det_zero : ∀ A, det A 0 = 1.
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let zero_n = d.zero();
        let lhs = rdet(d, p, a, zero_n);
        let one = rone(d, p);
        let stmt = req(d, lhs, one);
        let proof = super::ops::rrefl(d, one);
        let ty = d.pi_fv(a_fv, mty, stmt);
        let value = d.lam_fv(a_fv, mty, proof);
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.det_zero,
            uparams: vec![],
            ty,
            value,
        })?;
    }

    // det_succ : ∀ A m, det A (succ m)
    //   = sumRange (fun j => altSign j * (A 0 j * det (matMinor A 0 j) m)) (succ m).
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let sm = d.succ(m);
        let lhs = rdet(d, p, a, sm);

        let summand = {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let zero_n = d.zero();
            let entry = d.apply(a, &[zero_n, j]);
            let sub = rmat_minor_of(d, p, a, zero_n, j);
            let rec_call = rdet(d, p, sub, m);
            let product = rmul(d, entry, rec_call);
            let sign = ralt_sign(d, p, j);
            let body = rmul(d, sign, product);
            d.lam_fv(j_fv, nat, body)
        };
        let rhs = rsum_range(d, p, summand, sm);
        let stmt = req(d, lhs, rhs);
        let proof = super::ops::rrefl(d, rhs);
        let ty = {
            let inner = d.pi_fv(m_fv, nat, stmt);
            d.pi_fv(a_fv, mty, inner)
        };
        let value = {
            let inner = d.lam_fv(m_fv, nat, proof);
            d.lam_fv(a_fv, mty, inner)
        };
        d.kernel().add_declaration(Declaration::Theorem {
            name: p.det_succ,
            uparams: vec![],
            ty,
            value,
        })?;
    }
    Ok(())
}

/// `Rat.det_one : ∀ A, det A 1 = A 0 0`.
fn declare_det_one(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let mty = mat_ty(d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let one_n = d.num(1);
    let zero_n = d.zero();

    let lhs = rdet(d, p, a, one_n);
    let a00 = d.apply(a, &[zero_n, zero_n]);
    let stmt = req(d, lhs, a00);
    let (_, proof) = det1_shape_pf(d, p, a00);

    let ty = d.pi_fv(a_fv, mty, stmt);
    let value = d.lam_fv(a_fv, mty, proof);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.det_one,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.det_eq_det2 : ∀ A, det A 2 = det2 (A 0 0) (A 0 1) (A 1 0) (A 1 1)`.
///
/// The single most valuable check on the cofactor recursion: `Rat.det2` was
/// written independently of this file, so a transposed index or an inverted
/// sign cannot survive.
fn declare_det_eq_det2(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let mty = mat_ty(d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let i0 = d.zero();
    let i1 = d.num(1);
    let i2 = d.num(2);

    let a00 = d.apply(a, &[i0, i0]);
    let a01 = d.apply(a, &[i0, i1]);
    let a10 = d.apply(a, &[i1, i0]);
    let a11 = d.apply(a, &[i1, i1]);

    let lhs = rdet(d, p, a, i2);
    let rhs = rdet2(d, p, a00, a01, a10, a11);
    let stmt = req(d, lhs, rhs);

    let zero = rzero(d, p);
    let one = rone(d, p);
    let neg_one = rneg(d, one);

    // The unfolded LHS, built by hand: sumRange f 2 = add (add zero (f 0)) (f 1),
    // with `det (matMinor A 0 j) 1` written in its own unfolded shape.
    let (d0_start, d0_pf) = det1_shape_pf(d, p, a11);
    debug_assert_eq!(d0_start, a11);
    let (d1_start, d1_pf) = det1_shape_pf(d, p, a10);
    debug_assert_eq!(d1_start, a10);

    let inner0 = {
        let x_one = rmul(d, a11, one);
        let m = rmul(d, one, x_one);
        radd(d, zero, m)
    };
    let inner1 = {
        let x_one = rmul(d, a10, one);
        let m = rmul(d, one, x_one);
        radd(d, zero, m)
    };

    let term0 = |d: &mut IntDev<'_>, inner: ExprId| {
        let prod = rmul(d, a00, inner);
        rmul(d, one, prod)
    };
    let term1 = |d: &mut IntDev<'_>, inner: ExprId| {
        let prod = rmul(d, a01, inner);
        rmul(d, neg_one, prod)
    };

    let t0_raw = term0(d, inner0);
    let t1_raw = term1(d, inner1);
    let start = {
        let head = radd(d, zero, t0_raw);
        radd(d, head, t1_raw)
    };

    // 1. det (matMinor A 0 0) 1  ->  A 1 1
    let s1 = rcongr(d, inner0, a11, d0_pf, &|d, t| {
        let left = term0(d, t);
        let head = radd(d, zero, left);
        radd(d, head, t1_raw)
    });
    let t0_mid = term0(d, a11);
    let mid1 = {
        let head = radd(d, zero, t0_mid);
        radd(d, head, t1_raw)
    };

    // 2. det (matMinor A 0 1) 1  ->  A 1 0
    let s2 = rcongr(d, inner1, a10, d1_pf, &|d, t| {
        let right = term1(d, t);
        let head = radd(d, zero, t0_mid);
        radd(d, head, right)
    });
    let t1_mid = term1(d, a10);
    let mid2 = {
        let head = radd(d, zero, t0_mid);
        radd(d, head, t1_mid)
    };

    // 3. mul one (mul a00 a11)  ->  mul a00 a11
    let prod0 = rmul(d, a00, a11);
    let s3 = {
        let pf = one_mul_pf(d, p, prod0);
        rcongr(d, t0_mid, prod0, pf, &|d, t| {
            let head = radd(d, zero, t);
            radd(d, head, t1_mid)
        })
    };
    let mid3 = {
        let head = radd(d, zero, prod0);
        radd(d, head, t1_mid)
    };

    // 4. add zero (mul a00 a11)  ->  mul a00 a11
    let s4 = {
        let pf = d.lemma(p.zero_add, &[prod0]);
        let from = radd(d, zero, prod0);
        rcongr(d, from, prod0, pf, &|d, t| radd(d, t, t1_mid))
    };
    let mid4 = radd(d, prod0, t1_mid);

    // 5. mul (neg one) (mul a01 a10)  ->  neg (mul a01 a10)
    let prod1 = rmul(d, a01, a10);
    let neg_prod1 = rneg(d, prod1);
    let s5 = {
        let pf = neg_one_mul_pf(d, p, prod1);
        rcongr(d, t1_mid, neg_prod1, pf, &|d, t| radd(d, prod0, t))
    };
    let mid5 = radd(d, prod0, neg_prod1);

    let (_, proof) = rchain(
        d,
        start,
        &[(mid1, s1), (mid2, s2), (mid3, s3), (mid4, s4), (mid5, s5)],
    );

    let ty = d.pi_fv(a_fv, mty, stmt);
    let value = d.lam_fv(a_fv, mty, proof);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.det_eq_det2,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.det_eq_det3 : ∀ A, det A 3 = det3 (A 0 0) … (A 2 2)`.
///
/// Built on [`declare_det_eq_det2`] applied at each of the three minors, so
/// the only new content is the outer three-term alternating sum — in
/// particular `altSign 2 = neg (neg 1)`, which needs `neg_neg` and is where a
/// sign convention that drifts after the first two columns would show.
fn declare_det_eq_det3(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let mty = mat_ty(d);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);

    let i0 = d.zero();
    let i1 = d.num(1);
    let i2 = d.num(2);
    let i3 = d.num(3);

    let e = |d: &mut IntDev<'_>, r: ExprId, c: ExprId| d.apply(a, &[r, c]);
    let a00 = e(d, i0, i0);
    let a01 = e(d, i0, i1);
    let a02 = e(d, i0, i2);
    let a10 = e(d, i1, i0);
    let a11 = e(d, i1, i1);
    let a12 = e(d, i1, i2);
    let a20 = e(d, i2, i0);
    let a21 = e(d, i2, i1);
    let a22 = e(d, i2, i2);

    let lhs = rdet(d, p, a, i3);
    let rhs = rdet3(d, p, a00, a01, a02, a10, a11, a12, a20, a21, a22);
    let stmt = req(d, lhs, rhs);

    let zero = rzero(d, p);
    let one = rone(d, p);
    let neg_one = rneg(d, one);
    let neg_neg_one = rneg(d, neg_one);

    // The three minors, and `det (minor) 2` rewritten by `det_eq_det2`.
    let m0 = rmat_minor_of(d, p, a, i0, i0);
    let m1 = rmat_minor_of(d, p, a, i0, i1);
    let m2 = rmat_minor_of(d, p, a, i0, i2);
    let inner0 = rdet(d, p, m0, i2);
    let inner1 = rdet(d, p, m1, i2);
    let inner2 = rdet(d, p, m2, i2);
    // The reduced right-hand sides: `matMinor A 0 j r c` at literal indices is
    // definitionally `A (skip 0 r) (skip j c)`, so these are what
    // `det_eq_det2`'s conclusion is defeq to.
    let x0 = rdet2(d, p, a11, a12, a21, a22);
    let x1 = rdet2(d, p, a10, a12, a20, a22);
    let x2 = rdet2(d, p, a10, a11, a20, a21);
    let pf0 = d.lemma(p.det_eq_det2, &[m0]);
    let pf1 = d.lemma(p.det_eq_det2, &[m1]);
    let pf2 = d.lemma(p.det_eq_det2, &[m2]);

    // Summand builders, parameterised on the inner determinant and on the sign.
    let build = |d: &mut IntDev<'_>, sign: ExprId, entry: ExprId, inner: ExprId| {
        let prod = rmul(d, entry, inner);
        rmul(d, sign, prod)
    };

    let u0_raw = build(d, one, a00, inner0);
    let u1_raw = build(d, neg_one, a01, inner1);
    let u2_raw = build(d, neg_neg_one, a02, inner2);
    let start = {
        let h1 = radd(d, zero, u0_raw);
        let h2 = radd(d, h1, u1_raw);
        radd(d, h2, u2_raw)
    };

    // 1. det (matMinor A 0 0) 2 -> det2 (A 1 1) (A 1 2) (A 2 1) (A 2 2)
    let s1 = rcongr(d, inner0, x0, pf0, &|d, t| {
        let u0 = build(d, one, a00, t);
        let h1 = radd(d, zero, u0);
        let h2 = radd(d, h1, u1_raw);
        radd(d, h2, u2_raw)
    });
    let u0_mid = build(d, one, a00, x0);
    let mid1 = {
        let h1 = radd(d, zero, u0_mid);
        let h2 = radd(d, h1, u1_raw);
        radd(d, h2, u2_raw)
    };

    // 2. det (matMinor A 0 1) 2 -> det2 (A 1 0) (A 1 2) (A 2 0) (A 2 2)
    let s2 = rcongr(d, inner1, x1, pf1, &|d, t| {
        let u1 = build(d, neg_one, a01, t);
        let h1 = radd(d, zero, u0_mid);
        let h2 = radd(d, h1, u1);
        radd(d, h2, u2_raw)
    });
    let u1_mid = build(d, neg_one, a01, x1);
    let mid2 = {
        let h1 = radd(d, zero, u0_mid);
        let h2 = radd(d, h1, u1_mid);
        radd(d, h2, u2_raw)
    };

    // 3. det (matMinor A 0 2) 2 -> det2 (A 1 0) (A 1 1) (A 2 0) (A 2 1)
    let s3 = rcongr(d, inner2, x2, pf2, &|d, t| {
        let u2 = build(d, neg_neg_one, a02, t);
        let h1 = radd(d, zero, u0_mid);
        let h2 = radd(d, h1, u1_mid);
        radd(d, h2, u2)
    });
    let u2_mid = build(d, neg_neg_one, a02, x2);
    let mid3 = {
        let h1 = radd(d, zero, u0_mid);
        let h2 = radd(d, h1, u1_mid);
        radd(d, h2, u2_mid)
    };

    // 4. mul one (mul a00 x0) -> mul a00 x0
    let prod0 = rmul(d, a00, x0);
    let s4 = {
        let pf = one_mul_pf(d, p, prod0);
        rcongr(d, u0_mid, prod0, pf, &|d, t| {
            let h1 = radd(d, zero, t);
            let h2 = radd(d, h1, u1_mid);
            radd(d, h2, u2_mid)
        })
    };
    let mid4 = {
        let h1 = radd(d, zero, prod0);
        let h2 = radd(d, h1, u1_mid);
        radd(d, h2, u2_mid)
    };

    // 5. add zero (mul a00 x0) -> mul a00 x0
    let s5 = {
        let pf = d.lemma(p.zero_add, &[prod0]);
        let from = radd(d, zero, prod0);
        rcongr(d, from, prod0, pf, &|d, t| {
            let h2 = radd(d, t, u1_mid);
            radd(d, h2, u2_mid)
        })
    };
    let mid5 = {
        let h2 = radd(d, prod0, u1_mid);
        radd(d, h2, u2_mid)
    };

    // 6. mul (neg one) (mul a01 x1) -> neg (mul a01 x1)
    let prod1 = rmul(d, a01, x1);
    let neg_prod1 = rneg(d, prod1);
    let s6 = {
        let pf = neg_one_mul_pf(d, p, prod1);
        rcongr(d, u1_mid, neg_prod1, pf, &|d, t| {
            let h2 = radd(d, prod0, t);
            radd(d, h2, u2_mid)
        })
    };
    let mid6 = {
        let h2 = radd(d, prod0, neg_prod1);
        radd(d, h2, u2_mid)
    };
    let head = radd(d, prod0, neg_prod1);

    // 7. neg (neg one) -> one, under the third summand
    let s7 = {
        let pf = d.lemma(p.neg_neg, &[one]);
        rcongr(d, neg_neg_one, one, pf, &|d, t| {
            let u2 = build(d, t, a02, x2);
            radd(d, head, u2)
        })
    };
    let u2_one = build(d, one, a02, x2);
    let mid7 = radd(d, head, u2_one);

    // 8. mul one (mul a02 x2) -> mul a02 x2
    let prod2 = rmul(d, a02, x2);
    let s8 = {
        let pf = one_mul_pf(d, p, prod2);
        rcongr(d, u2_one, prod2, pf, &|d, t| radd(d, head, t))
    };
    let mid8 = radd(d, head, prod2);

    let (_, proof) = rchain(
        d,
        start,
        &[
            (mid1, s1),
            (mid2, s2),
            (mid3, s3),
            (mid4, s4),
            (mid5, s5),
            (mid6, s6),
            (mid7, s7),
            (mid8, s8),
        ],
    );

    let ty = d.pi_fv(a_fv, mty, stmt);
    let value = d.lam_fv(a_fv, mty, proof);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.det_eq_det3,
        uparams: vec![],
        ty,
        value,
    })
}

// --- concrete evaluation ---------------------------------------------------

/// The `Int` numeral `n` — a local copy of `super::matrix::int_numeral`
/// (private there), as `super::matrix_transpose` also keeps.
fn int_numeral(d: &mut IntDev<'_>, n: i64) -> ExprId {
    if n >= 0 {
        let nat = d.num(u32::try_from(n).expect("non-negative"));
        d.of_nat(nat)
    } else {
        let nat = d.num(u32::try_from(-n - 1).expect("negative"));
        d.neg_succ(nat)
    }
}

/// `Rat.ofInt n` for a small integer `n`.
pub(super) fn rq(d: &mut IntDev<'_>, p: RatPrelude, n: i64) -> ExprId {
    let z = int_numeral(d, n);
    d.const_app(p.of_int, &[z])
}

/// A closed `Nat → Nat → Rat` for a concrete `k × k` matrix given in row-major
/// order, built by nested `Nat.beq` selection exactly as
/// `super::matrix_transpose::const2x2` does.
///
/// Out-of-range indices fall into the last row/column; every use below stays
/// inside the bound, and the determinant never reads outside it.
pub(super) fn const_matrix(d: &mut IntDev<'_>, p: RatPrelude, k: usize, rows: &[i64]) -> ExprId {
    assert_eq!(rows.len(), k * k, "row-major entries must fill the square");
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    // Each row is a `Nat.beq j c`-chain over the columns; the whole matrix is a
    // `Nat.beq i r`-chain over those rows.
    let mut row_terms: Vec<ExprId> = Vec::with_capacity(k);
    for r in 0..k {
        let mut term = rq(d, p, rows[r * k + (k - 1)]);
        for c in (0..k - 1).rev() {
            let entry = rq(d, p, rows[r * k + c]);
            let idx = d.num(u32::try_from(c).expect("small"));
            let cond = NatOps::beq(d, j, idx);
            term = bool_select_rat(d, cond, entry, term);
        }
        row_terms.push(term);
    }
    let mut body = row_terms[k - 1];
    for r in (0..k - 1).rev() {
        let idx = d.num(u32::try_from(r).expect("small"));
        let cond = NatOps::beq(d, i, idx);
        body = bool_select_rat(d, cond, row_terms[r], body);
    }

    let with_j = d.lam_fv(j_fv, nat, body);
    d.lam_fv(i_fv, nat, with_j)
}

/// `Rat.matMinor_eval_example : matMinor A 0 1 1 0 = ofInt 7`, where
///
/// ```text
/// A = [[1, 2, 3],
///      [4, 5, 6],
///      [7, 8, 9]]
/// ```
///
/// Deleting row 0 and column 1 leaves `[[4, 6], [7, 9]]`, whose `(1, 0)` entry
/// is `A 2 0 = 7`. The matrix is deliberately **non-symmetric**, so a
/// transposed index would give `3` (`A 0 2`) and a shift applied to the wrong
/// axis would give `8` (`A 2 1`) — three distinct answers for the three
/// mistakes, which is the point of pinning this entry rather than a diagonal
/// one.
fn declare_mat_minor_eval_example(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.mat_minor_eval_example, 0, &|d, _v| {
        let m = const_matrix(d, p, 3, &[1, 2, 3, 4, 5, 6, 7, 8, 9]);
        let i0 = d.zero();
        let i1 = d.num(1);
        let lhs = rmat_minor(d, p, m, i0, i1, i1, i0);
        let expected = rq(d, p, 7);
        let stmt = req(d, lhs, expected);
        let proof = super::ops::rrefl(d, expected);
        (stmt, proof)
    })
}

/// `Rat.det_eval_example : det A 3 = ofInt 13`, where
///
/// ```text
/// A = [[1, 2, 0],
///      [0, 1, 3],
///      [2, 0, 1]]
/// ```
///
/// Computed independently: `1·(1·1 − 3·0) − 2·(0·1 − 3·2) + 0·(0·0 − 1·2)`
/// `= 1 + 12 + 0 = 13`.
///
/// Chosen to DISCRIMINATE, not merely to evaluate. Under the recursion with
/// the alternating sign inverted the same matrix gives **−13**; under a
/// recursion that deletes row `j` instead of row `0` it gives **−4**. Largest
/// magnitude formed anywhere in the evaluation is 13, which matters because
/// this kernel's numerals are unary and the binary-literal fast path never
/// fires.
fn declare_det_eval_example(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.det_eval_example, 0, &|d, _v| {
        let m = const_matrix(d, p, 3, &[1, 2, 0, 0, 1, 3, 2, 0, 1]);
        let n = d.num(3);
        let lhs = rdet(d, p, m, n);
        let expected = rq(d, p, 13);
        let stmt = req(d, lhs, expected);
        let proof = super::ops::rrefl(d, expected);
        (stmt, proof)
    })
}

/// `Rat.det_eval_singular : det A 3 = 0`, where
///
/// ```text
/// A = [[1, 2, 1],
///      [2, 1, 3],
///      [3, 3, 4]]
/// ```
///
/// Row 2 is row 0 + row 1, so the determinant is `0`. Non-symmetric, with no
/// zero entry anywhere, and largest magnitude formed is 9.
///
/// Its honest limit, stated because a control that cannot fail is worse than
/// none: inverting the alternating sign leaves this at `0` as well (a
/// singular matrix stays singular), so this case discriminates a *row/column
/// deletion* bug — it gives **−6** under deletion of row `j` — and not a sign
/// bug. The sign is discriminated by
/// [`RatPrelude::det_eval_example`](super::RatPrelude::det_eval_example) and,
/// symbolically, by
/// [`RatPrelude::det_eq_det2`](super::RatPrelude::det_eq_det2).
fn declare_det_eval_singular(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.det_eval_singular, 0, &|d, _v| {
        let m = const_matrix(d, p, 3, &[1, 2, 1, 2, 1, 3, 3, 3, 4]);
        let n = d.num(3);
        let lhs = rdet(d, p, m, n);
        let expected = rzero(d, p);
        let stmt = req(d, lhs, expected);
        let proof = super::ops::rrefl(d, expected);
        (stmt, proof)
    })
}

/// `Rat.det_eval_example4 : det A 4 = ofInt 2`, where
///
/// ```text
/// A = [[2, 0, 1, 1],
///      [1, 3, 0, 2],
///      [0, 1, 2, 0],
///      [1, 1, 1, 1]]
/// ```
///
/// The first dimension the fixed-dimension determinants cannot reach at all,
/// so it exercises the recursion one level past anything `det2`/`det3` can
/// confirm. Under a recursion deleting row `j` instead of row `0` it gives
/// **18**. Largest magnitude formed is 8: entries are kept small deliberately,
/// since this kernel's numerals are unary and cost is superlinear in the
/// largest magnitude *formed*.
fn declare_det_eval_example4(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.det_eval_example4, 0, &|d, _v| {
        let m = const_matrix(d, p, 4, &[2, 0, 1, 1, 1, 3, 0, 2, 0, 1, 2, 0, 1, 1, 1, 1]);
        let n = d.num(4);
        let lhs = rdet(d, p, m, n);
        let expected = rq(d, p, 2);
        let stmt = req(d, lhs, expected);
        let proof = super::ops::rrefl(d, expected);
        (stmt, proof)
    })
}

// --- the determinant laws (`Rat.det_congr`, `Rat.det_matId`) ---------------

/// `Rat.matId`, a bare constant (a local copy of `matrix_n`'s private
/// `rmat_id`; the identity matrix carries no dimension argument).
pub(super) fn rmat_id(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    d.kernel().const_(p.mat_id, vec![])
}

/// `∀ r c, Eq Rat (A r c) (B r c)` — the pointwise agreement of two matrices,
/// which is the ONLY way to say "these are the same matrix" in a kernel
/// without `funext`.
fn pointwise_ty(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let ar = d.apply(a, &[r, c]);
    let br = d.apply(b, &[r, c]);
    let eq = req(d, ar, br);
    let inner = d.pi_fv(c_fv, nat, eq);
    d.pi_fv(r_fv, nat, inner)
}

/// Admit `Rat.sumRange_head_of_tail_zero : ∀ f n, (∀ k, f (succ k) = 0) →
/// sumRange f (succ n) = f 0`.
///
/// `Rat.sumRange` peels from the RIGHT (`sumRange f (succ n) ≡ sumRange f n +
/// f n`), so there is no equation that hands you the *first* summand. This
/// supplies it for the one shape that needs it: a sum whose entire tail
/// vanishes. Direct induction on `n`, mirroring
/// [`super::sum::declare_sum_range_congr`]'s successor step
/// (`rcongr`/`rchain` under `Rat.add`), with `Rat.zero_add` closing the base
/// and `Rat.add_zero` the step.
///
/// It lives here rather than in [`super::sum`] for the same reason
/// `Rat.sumRange_delta` lives in [`super::matrix_n`]: the shape is the one the
/// cofactor expansion needs, and nothing else in this prelude sums a function
/// supported at a single index.
fn declare_sum_range_head_of_tail_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // tail : ∀ k, Eq Rat (f (succ k)) zero
    let tail_ty = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let sk = d.succ(k);
        let fsk = d.apply(f, &[sk]);
        let zero_r = rzero(d, p);
        let eq = req(d, fsk, zero_r);
        d.pi_fv(k_fv, nat, eq)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero_n = d.zero();
    let head = d.apply(f, &[zero_n]);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sx = d.succ(x);
        let lhs = rsum_range(d, p, f, sx);
        req(d, lhs, head)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        // `sumRange f (succ 0) ≡ add (sumRange f 0) (f 0) ≡ add zero (f 0)`.
        &|d| d.lemma(p.zero_add, &[head]),
        &|d, j, ih| {
            // `sumRange f (succ (succ j)) ≡ add (sumRange f (succ j)) (f (succ j))`.
            let sj = d.succ(j);
            let prior = rsum_range(d, p, f, sj);
            let fsj = d.apply(f, &[sj]);
            let start = radd(d, prior, fsj);

            let s1 = rcongr(d, prior, head, ih, &|d, t| radd(d, t, fsj));
            let mid1 = radd(d, head, fsj);

            let zero_r = rzero(d, p);
            let h_at = d.apply(h, &[j]);
            let s2 = rcongr(d, fsj, zero_r, h_at, &|d, t| radd(d, head, t));
            let mid2 = radd(d, head, zero_r);

            let s3 = d.lemma(p.add_zero, &[head]);
            let (_end, proof) = rchain(d, start, &[(mid1, s1), (mid2, s2), (head, s3)]);
            proof
        },
        n,
    );

    let ty = {
        let with_h = d.pi_fv(h_fv, tail_ty, stmt);
        let over_n = d.pi_fv(n_fv, nat, with_h);
        d.pi_fv(f_fv, fn_ty, over_n)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, tail_ty, proof);
        let over_n = d.lam_fv(n_fv, nat, with_h);
        d.lam_fv(f_fv, fn_ty, over_n)
    };
    d.declare_theorem(p.sum_range_head_of_tail_zero, ty, value)
}

/// Admit `Rat.det_congr : ∀ n A B, (∀ r c, A r c = B r c) → det A n = det B n`
/// — the determinant respects *pointwise* equality of matrices.
///
/// **This is the lemma the absence of `funext` forces, and it is what unblocks
/// every law over the general-`n` determinant.** `Rat.det`'s recursive call is
/// at the MINOR, so any induction over the dimension arrives at a matrix that
/// is only *pointwise* the one the induction hypothesis is about — for
/// `Rat.matId` the minor `matMinor matId 0 0` is the identity at every index
/// pair and is not the same term. With `funext` one would rewrite the matrix
/// argument and be done; without it, `det` needs its own congruence, proved
/// once here.
///
/// The dimension is quantified OUTERMOST and the two matrices live under the
/// `Nat.rec` motive `fun n => ∀ A B, (∀ r c, A r c = B r c) → det A n = det B
/// n`, deliberately: the induction hypothesis has to be applicable at a
/// DIFFERENT pair of matrices (the two minors), which it cannot be if `A` and
/// `B` are fixed outside the induction.
///
/// The successor step is then `Rat.sumRange_congr` on the two cofactor sums,
/// whose per-index obligation splits into the entry (`h 0 c`) and the minor
/// determinant (the induction hypothesis at `matMinor A 0 c` / `matMinor B 0
/// c`, with `fun r c' => h (matSkip 0 r) (matSkip c c')` as its pointwise
/// premise — well-typed because `matMinor` δβ-reduces to exactly that
/// application).
fn declare_det_congr(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let mty = mat_ty(d);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let hyp = pointwise_ty(d, a, b);
        let lhs = rdet(d, p, a, x);
        let rhs = rdet(d, p, b, x);
        let eq = req(d, lhs, rhs);
        // The conclusion does not mention the hypothesis's variable, so the
        // non-dependent `arrow` is correct here.
        let with_h = d.arrow(hyp, eq);
        let over_b = d.pi_fv(b_fv, mty, with_h);
        d.pi_fv(a_fv, mty, over_b)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        // `det A 0 ≡ one ≡ det B 0`.
        &|d| {
            let mty = mat_ty(d);
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let hyp = pointwise_ty(d, a, b);
            let h_fv = d.fresh_fvar();
            let one = rone(d, p);
            let refl = rrefl(d, one);
            let with_h = d.lam_fv(h_fv, hyp, refl);
            let over_b = d.lam_fv(b_fv, mty, with_h);
            d.lam_fv(a_fv, mty, over_b)
        },
        &|d, j, ih| {
            let nat = d.nat_ty();
            let mty = mat_ty(d);
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let hyp = pointwise_ty(d, a, b);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let zero_n = d.zero();

            // `fun c => altSign c * (M 0 c * det (matMinor M 0 c) j)`, the
            // cofactor summand `det_succ` unfolds to.
            let summand = |d: &mut IntDev<'_>, m: ExprId| -> ExprId {
                let nat = d.nat_ty();
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let zero_n = d.zero();
                let entry = d.apply(m, &[zero_n, c]);
                let sub = rmat_minor_of(d, p, m, zero_n, c);
                let rec_call = rdet(d, p, sub, j);
                let product = rmul(d, entry, rec_call);
                let sign = ralt_sign(d, p, c);
                let body = rmul(d, sign, product);
                d.lam_fv(c_fv, nat, body)
            };
            let f_a = summand(d, a);
            let f_b = summand(d, b);

            // `∀ c, f_A c = f_B c`, the premise `sumRange_congr` wants.
            let pointwise = {
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let entry_a = d.apply(a, &[zero_n, c]);
                let entry_b = d.apply(b, &[zero_n, c]);
                let sub_a = rmat_minor_of(d, p, a, zero_n, c);
                let sub_b = rmat_minor_of(d, p, b, zero_n, c);
                let det_a = rdet(d, p, sub_a, j);
                let det_b = rdet(d, p, sub_b, j);
                let sign = ralt_sign(d, p, c);

                // `fun r c' => h (matSkip 0 r) (matSkip c c')` inhabits
                // `∀ r c', matMinor A 0 c r c' = matMinor B 0 c r c'`.
                let minor_pointwise = {
                    let r_fv = d.fresh_fvar();
                    let r = d.kernel().fvar(r_fv);
                    let cc_fv = d.fresh_fvar();
                    let cc = d.kernel().fvar(cc_fv);
                    let row = rmat_skip(d, p, zero_n, r);
                    let col = rmat_skip(d, p, c, cc);
                    let body = d.apply(h, &[row, col]);
                    let inner = d.lam_fv(cc_fv, nat, body);
                    d.lam_fv(r_fv, nat, inner)
                };
                let h_det = d.apply(ih, &[sub_a, sub_b, minor_pointwise]);
                let h_entry = d.apply(h, &[zero_n, c]);

                let start = {
                    let product = rmul(d, entry_a, det_a);
                    rmul(d, sign, product)
                };
                let s1 = rcongr(d, entry_a, entry_b, h_entry, &|d, t| {
                    let product = rmul(d, t, det_a);
                    rmul(d, sign, product)
                });
                let mid = {
                    let product = rmul(d, entry_b, det_a);
                    rmul(d, sign, product)
                };
                let s2 = rcongr(d, det_a, det_b, h_det, &|d, t| {
                    let product = rmul(d, entry_b, t);
                    rmul(d, sign, product)
                });
                let end = {
                    let product = rmul(d, entry_b, det_b);
                    rmul(d, sign, product)
                };
                let (_e, body) = rchain(d, start, &[(mid, s1), (end, s2)]);
                d.lam_fv(c_fv, nat, body)
            };

            let sj = d.succ(j);
            let sum_pf = d.lemma(p.sum_range_congr, &[f_a, f_b, sj, pointwise]);

            let with_h = d.lam_fv(h_fv, hyp, sum_pf);
            let over_b = d.lam_fv(b_fv, mty, with_h);
            d.lam_fv(a_fv, mty, over_b)
        },
        n,
    );

    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.det_congr, ty, value)
}

/// Admit `Rat.matMinor_matId : ∀ r c, matMinor matId 0 0 r c = matId r c` —
/// the identity's leading minor is the identity, POINTWISE.
///
/// `Eq.refl`, and the three reductions that make it so are worth naming
/// because each is a place an off-by-one would show up:
///
/// - `Nat.ble zero r ≡ true` (the `ble` zero row is the constant `true`
///   function, no inner recursion), so `matSkip 0 r ≡ succ r`;
/// - `Nat.beq (succ r) (succ c) ≡ Nat.beq r c` (`beq`'s outer recursion is on
///   the first argument, its inner on the second, and both fire);
/// - `matId` is `bool_select_rat (beq i j) one zero`, a `Bool.rec`, so the two
///   sides are the *same* `bool_select_rat` term.
///
/// This is the statement that cannot be phrased as a matrix equation: it is
/// exactly "`matMinor matId 0 0` and `matId` are the same function", which
/// without `funext` is only ever available at an index pair.
fn declare_mat_minor_mat_id(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mat_id = rmat_id(d, p);
    let zero_n = d.zero();

    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let lhs = rmat_minor(d, p, mat_id, zero_n, zero_n, r, c);
    let rhs = d.apply(mat_id, &[r, c]);
    let stmt = req(d, lhs, rhs);
    let proof = rrefl(d, rhs);

    let ty = {
        let inner = d.pi_fv(c_fv, nat, stmt);
        d.pi_fv(r_fv, nat, inner)
    };
    let value = {
        let inner = d.lam_fv(c_fv, nat, proof);
        d.lam_fv(r_fv, nat, inner)
    };
    d.declare_theorem(p.mat_minor_mat_id, ty, value)
}

/// Admit `Rat.det_matId : ∀ n, det matId n = 1` — the determinant of the
/// identity at a **symbolic** dimension, the first of the four laws
/// `matrix_det`'s module doc left open.
///
/// Induction on `n`. The base is `Eq.refl` (`det _ 0 ≡ 1`). The step is the
/// whole content, and it is three moves:
///
/// 1. **Kill the tail.** `matId 0 (succ k) ≡ Rat.zero` definitionally
///    (`beq 0 (succ k) ≡ false` and `matId` is a `Bool.rec`), so every
///    summand past the first is `sign * (0 * _)`, which `Rat.mul_comm` and
///    `Rat.mul_zero` take to `0`. That discharges
///    [`declare_sum_range_head_of_tail_zero`]'s premise and collapses the
///    cofactor sum to its `j = 0` term.
/// 2. **Recognise the minor.** The surviving term is
///    `altSign 0 * (matId 0 0 * det (matMinor matId 0 0) n)`, and
///    `altSign 0 ≡ matId 0 0 ≡ Rat.one`, so only the minor determinant is
///    left. [`declare_det_congr`] carries it to `det matId n` along
///    [`declare_mat_minor_mat_id`] — **this is the step that needs `funext`
///    and does not have it**, and the reason `det_congr` had to exist first.
/// 3. **Apply the induction hypothesis**, then `1 * (1 * 1) = 1` by
///    `Rat.mul_one` twice.
///
/// Every magnitude formed is `0` or `1`; nothing here builds a numeral.
fn declare_det_mat_id(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let mat_id = rmat_id(d, p);
        let lhs = rdet(d, p, mat_id, x);
        let one = rone(d, p);
        req(d, lhs, one)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let one = rone(d, p);
            rrefl(d, one)
        },
        &|d, j, ih| {
            let nat = d.nat_ty();
            let mat_id = rmat_id(d, p);
            let zero_n = d.zero();
            let one = rone(d, p);
            let zero_r = rzero(d, p);

            // `f := fun c => altSign c * (matId 0 c * det (matMinor matId 0 c) j)`.
            let f = {
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let entry = d.apply(mat_id, &[zero_n, c]);
                let sub = rmat_minor_of(d, p, mat_id, zero_n, c);
                let rec_call = rdet(d, p, sub, j);
                let product = rmul(d, entry, rec_call);
                let sign = ralt_sign(d, p, c);
                let body = rmul(d, sign, product);
                d.lam_fv(c_fv, nat, body)
            };

            // `∀ k, f (succ k) = 0`, built at `Rat.zero` directly since
            // `matId 0 (succ k) ≡ Rat.zero`.
            let tail = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sk = d.succ(k);
                let sign = ralt_sign(d, p, sk);
                let sub = rmat_minor_of(d, p, mat_id, zero_n, sk);
                let minor_det = rdet(d, p, sub, j);

                let zero_x = rmul(d, zero_r, minor_det);
                let x_zero = rmul(d, minor_det, zero_r);
                let comm = d.lemma(p.mul_comm, &[zero_r, minor_det]);
                let annihilate = d.lemma(p.mul_zero, &[minor_det]);
                let inner = rtrans(d, zero_x, x_zero, zero_r, comm, annihilate);

                let start = rmul(d, sign, zero_x);
                let s1 = rcongr(d, zero_x, zero_r, inner, &|d, t| rmul(d, sign, t));
                let mid = rmul(d, sign, zero_r);
                let s2 = d.lemma(p.mul_zero, &[sign]);
                let (_e, body) = rchain(d, start, &[(mid, s1), (zero_r, s2)]);
                d.lam_fv(k_fv, nat, body)
            };

            let head_pf = d.lemma(p.sum_range_head_of_tail_zero, &[f, j, tail]);

            // `f 0`, with `altSign 0` and `matId 0 0` written as the `Rat.one`
            // they definitionally are.
            let sub_zero = rmat_minor_of(d, p, mat_id, zero_n, zero_n);
            let minor_det = rdet(d, p, sub_zero, j);
            let head = {
                let product = rmul(d, one, minor_det);
                rmul(d, one, product)
            };

            let id_det = rdet(d, p, mat_id, j);
            let minor_is_id = d.const_app(p.mat_minor_mat_id, &[]);
            let recognise = d.lemma(p.det_congr, &[j, sub_zero, mat_id, minor_is_id]);

            let s1 = rcongr(d, minor_det, id_det, recognise, &|d, t| {
                let product = rmul(d, one, t);
                rmul(d, one, product)
            });
            let mid1 = {
                let product = rmul(d, one, id_det);
                rmul(d, one, product)
            };
            let s2 = rcongr(d, id_det, one, ih, &|d, t| {
                let product = rmul(d, one, t);
                rmul(d, one, product)
            });
            let one_one = rmul(d, one, one);
            let mid2 = rmul(d, one, one_one);
            let collapse = d.lemma(p.mul_one, &[one]);
            let s3 = rcongr(d, one_one, one, collapse, &|d, t| rmul(d, one, t));
            let s4 = d.lemma(p.mul_one, &[one]);
            let (_e, tidy) = rchain(d, head, &[(mid1, s1), (mid2, s2), (one_one, s3), (one, s4)]);

            let sj = d.succ(j);
            let sum_lhs = rsum_range(d, p, f, sj);
            rtrans(d, sum_lhs, head, one, head_pf, tidy)
        },
        n,
    );

    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.det_mat_id, ty, value)
}

// --- the index layer of Laplace expansion (ADR-1155) -----------------------

/// `Bool.rec.{0}` as a two-branch case split at `Prop`: from `motive true` and
/// `motive false`, a proof of `motive b` for a symbolic `b : Bool`.
///
/// The kernel's defeq checker does not decide a `Bool.rec` on a symbolic
/// scrutinee, so every `Nat.ble`-guarded index identity in this file needs
/// this — `nat_prelude`'s own copies are `pub(super)` there and not reachable
/// from `rat_prelude`.
pub(super) fn bool_cases(
    d: &mut IntDev<'_>,
    scrutinee: ExprId,
    motive: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    at_true: &dyn Fn(&mut IntDev<'_>) -> ExprId,
    at_false: &dyn Fn(&mut IntDev<'_>) -> ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let motive_lam = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let body = motive(d, c);
        d.lam_fv(c_fv, bool_ty, body)
    };
    let case_true = at_true(d);
    let case_false = at_false(d);
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.prelude().logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![level_zero]);
    d.apply(rec, &[motive_lam, case_false, case_true, scrutinee])
}

/// Admit `Rat.matSkip_zero : ∀ x, matSkip 0 x = succ x`.
///
/// `Eq.refl`. `Nat.ble`'s zero row is the constant `true` function with no
/// inner recursion (`nat_prelude::ble`), so `ble zero x` iota-reduces to
/// `true` for a *symbolic* `x` and the `Bool.rec` inside `matSkip` fires.
/// This is the one `matSkip` equation that needs no case split, and it is why
/// deleting row 0 is definitionally a shift by one.
fn declare_mat_skip_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let zero_n = d.zero();
    let lhs = rmat_skip(d, p, zero_n, x);
    let rhs = d.succ(x);
    let stmt = NatOps::eq(d, lhs, rhs);
    let proof = NatOps::refl(d, rhs);
    let ty = d.pi_fv(x_fv, nat, stmt);
    let value = d.lam_fv(x_fv, nat, proof);
    d.declare_theorem(p.mat_skip_zero, ty, value)
}

/// Admit `Rat.matSkip_succ_succ : ∀ q x, matSkip (succ q) (succ x) =
/// succ (matSkip q x)`.
///
/// **Not** `Eq.refl`, and the reason is the shape of the guard rather than the
/// arithmetic. `Nat.ble (succ q) (succ x)` *does* iota-reduce to
/// `Nat.ble q x`, so both sides are `Bool.rec` applications on the same
/// symbolic scrutinee — but the left has `succ` inside its two branches and
/// the right has it outside, and the kernel does not push a constructor
/// through a stuck recursor. A two-branch [`bool_cases`] closes it: at `true`
/// both sides are `succ (succ x)` and at `false` both are `succ x`.
fn declare_mat_skip_succ_succ(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);

    let sq = d.succ(q);
    let sx = d.succ(x);
    let lhs = rmat_skip(d, p, sq, sx);
    let inner = rmat_skip(d, p, q, x);
    let rhs = d.succ(inner);
    let stmt = NatOps::eq(d, lhs, rhs);

    let ssx = d.succ(sx);
    let cond = d.ble(q, x);
    let motive = |d: &mut IntDev<'_>, c: ExprId| -> ExprId {
        let left = d.bool_select_nat(c, ssx, sx);
        let right_inner = d.bool_select_nat(c, sx, x);
        let right = d.succ(right_inner);
        NatOps::eq(d, left, right)
    };
    let proof = bool_cases(d, cond, &motive, &|d| NatOps::refl(d, ssx), &|d| {
        NatOps::refl(d, sx)
    });

    let ty = {
        let inner = d.pi_fv(x_fv, nat, stmt);
        d.pi_fv(q_fv, nat, inner)
    };
    let value = {
        let inner = d.lam_fv(x_fv, nat, proof);
        d.lam_fv(q_fv, nat, inner)
    };
    d.declare_theorem(p.mat_skip_succ_succ, ty, value)
}

/// `∀ x, matSkip a (matSkip b x) = matSkip (succ b) (matSkip a x)`, the body
/// of [`declare_mat_skip_comm`]'s statement at a given `a`, `b`.
fn skip_comm_body(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let inner_b = rmat_skip(d, p, b, x);
    let lhs = rmat_skip(d, p, a, inner_b);
    let inner_a = rmat_skip(d, p, a, x);
    let sb = d.succ(b);
    let rhs = rmat_skip(d, p, sb, inner_a);
    let eq = NatOps::eq(d, lhs, rhs);
    d.pi_fv(x_fv, nat, eq)
}

/// `Eq Bool (Nat.ble a b) true`, [`declare_mat_skip_comm`]'s hypothesis.
pub(super) fn ble_true_ty(d: &mut IntDev<'_>, a: ExprId, b: ExprId) -> ExprId {
    let lhs = d.ble(a, b);
    let true_ = d.bool_true();
    d.bool_eq(lhs, true_)
}

/// Admit `Rat.matSkip_comm : ∀ a b, Nat.ble a b = true → ∀ x,
/// matSkip a (matSkip b x) = matSkip (succ b) (matSkip a x)`.
///
/// **The index content of Laplace expansion.** Deleting index `b` and then
/// index `a` from `[0, n)` reaches the same injection as deleting `a` and then
/// the shifted `succ b`, provided `a ≤ b`.
///
/// The hypothesis is not decoration: at `a = 1`, `b = 0`, `x = 0` the two
/// sides are `2` and `0`. It is carried as the BOOLEAN `Nat.ble a b = true`
/// rather than `Nat.le a b` because the successor step has to invert it, and
/// `ble` inverts by iota-reduction alone — `ble (succ a') zero ≡ false` makes
/// the `b = 0` case a [`NatOps::false_true_elim`], and
/// `ble (succ a') (succ b') ≡ ble a' b'` hands the induction hypothesis its
/// own premise with no bridging lemma. With `Nat.le` both steps would need
/// inversion lemmas.
///
/// Induction on `a` with `b`, the hypothesis, and `x` all under the motive —
/// the same "quantify the moving arguments inside" shape
/// [`declare_det_congr`] needs, and for the same reason: the induction
/// hypothesis is applied at a *different* pair `(a', b')`.
///
/// - `a = 0`: `matSkip 0 y ≡ succ y`, so the goal is exactly
///   [`declare_mat_skip_succ_succ`] read backwards. No hypothesis is used.
/// - `a = succ a'`, `b = 0`: the premise is `false = true`.
/// - `a = succ a'`, `b = succ b'`, `x = 0`: both sides reduce to `0`, since
///   `ble (succ _) zero ≡ false` collapses every `matSkip (succ _) 0`.
/// - `a = succ a'`, `b = succ b'`, `x = succ x'`: five rewrites, four of them
///   [`declare_mat_skip_succ_succ`] peeling a `succ` off each nested shift,
///   with the induction hypothesis at `(a', b', x')` in the middle.
fn declare_mat_skip_comm(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let motive = |d: &mut IntDev<'_>, a: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let hyp = ble_true_ty(d, a, b);
        let concl = skip_comm_body(d, p, a, b);
        let arr = d.arrow(hyp, concl);
        d.pi_fv(b_fv, nat, arr)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let nat = d.nat_ty();
        let zero_n = d.zero();
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let hyp = ble_true_ty(d, zero_n, b);
        let h_fv = d.fresh_fvar();
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        // Goal: `matSkip 0 (matSkip b x) = matSkip (succ b) (matSkip 0 x)`,
        // definitionally `succ (matSkip b x) = matSkip (succ b) (succ x)`.
        let sx = d.succ(x);
        let sb = d.succ(b);
        let shifted = rmat_skip(d, p, sb, sx);
        let inner = rmat_skip(d, p, b, x);
        let peeled = d.succ(inner);
        let mss = d.lemma(p.mat_skip_succ_succ, &[b, x]);
        let pf = NatOps::symm(d, shifted, peeled, mss);
        let over_x = d.lam_fv(x_fv, nat, pf);
        let over_h = d.lam_fv(h_fv, hyp, over_x);
        d.lam_fv(b_fv, nat, over_h)
    };

    let step = |d: &mut IntDev<'_>, ap: ExprId, ih: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let sap = d.succ(ap);

        let motive_b = |d: &mut IntDev<'_>, b: ExprId| -> ExprId {
            let hyp = ble_true_ty(d, sap, b);
            let concl = skip_comm_body(d, p, sap, b);
            d.arrow(hyp, concl)
        };

        let b_at_zero = |d: &mut IntDev<'_>| -> ExprId {
            let zero_n = d.zero();
            let hyp = ble_true_ty(d, sap, zero_n);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let target = skip_comm_body(d, p, sap, zero_n);
            let pf = d.false_true_elim(target, h);
            d.lam_fv(h_fv, hyp, pf)
        };

        let b_at_succ = |d: &mut IntDev<'_>, bp: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let sbp = d.succ(bp);
            let ssbp = d.succ(sbp);
            let hyp = ble_true_ty(d, sap, sbp);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            // `h : ble (succ a') (succ b') = true` is definitionally
            // `ble a' b' = true`, which is exactly what `ih` wants at `b'`.
            let ih_at = d.apply(ih, &[bp, h]);

            let motive_x = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
                let inner_b = rmat_skip(d, p, sbp, x);
                let lhs = rmat_skip(d, p, sap, inner_b);
                let inner_a = rmat_skip(d, p, sap, x);
                let rhs = rmat_skip(d, p, ssbp, inner_a);
                NatOps::eq(d, lhs, rhs)
            };

            let x_at_zero = |d: &mut IntDev<'_>| -> ExprId {
                // `matSkip (succ _) 0 ≡ 0`, so both sides are `0`.
                let zero_n = d.zero();
                NatOps::refl(d, zero_n)
            };

            let x_at_succ = |d: &mut IntDev<'_>, xp: ExprId| -> ExprId {
                let sxp = d.succ(xp);
                let skip_bp = rmat_skip(d, p, bp, xp);
                let skip_ap = rmat_skip(d, p, ap, xp);

                let start = {
                    let inner = rmat_skip(d, p, sbp, sxp);
                    rmat_skip(d, p, sap, inner)
                };

                // 1. `matSkip (succ b') (succ x')  ->  succ (matSkip b' x')`
                let s1 = {
                    let from = rmat_skip(d, p, sbp, sxp);
                    let to = d.succ(skip_bp);
                    let pf = d.lemma(p.mat_skip_succ_succ, &[bp, xp]);
                    NatOps::congr(d, from, to, pf, &|d, t| rmat_skip(d, p, sap, t))
                };
                let mid1 = {
                    let peeled = d.succ(skip_bp);
                    rmat_skip(d, p, sap, peeled)
                };

                // 2. `matSkip (succ a') (succ y)  ->  succ (matSkip a' y)`
                let nested = rmat_skip(d, p, ap, skip_bp);
                let mid2 = d.succ(nested);
                let s2 = d.lemma(p.mat_skip_succ_succ, &[ap, skip_bp]);

                // 3. the induction hypothesis, under `succ`
                let swapped = rmat_skip(d, p, sbp, skip_ap);
                let mid3 = d.succ(swapped);
                let s3 = {
                    let pf = d.apply(ih_at, &[xp]);
                    NatOps::congr(d, nested, swapped, pf, &|d, t| d.succ(t))
                };

                // 4. `succ (matSkip (succ b') y)  ->  matSkip (succ (succ b')) (succ y)`
                let peeled_a = d.succ(skip_ap);
                let mid4 = rmat_skip(d, p, ssbp, peeled_a);
                let s4 = {
                    let pf = d.lemma(p.mat_skip_succ_succ, &[sbp, skip_ap]);
                    NatOps::symm(d, mid4, mid3, pf)
                };

                // 5. `succ (matSkip a' x')  ->  matSkip (succ a') (succ x')`
                let from5 = rmat_skip(d, p, sap, sxp);
                let s5 = {
                    let pf = d.lemma(p.mat_skip_succ_succ, &[ap, xp]);
                    let back = NatOps::symm(d, from5, peeled_a, pf);
                    NatOps::congr(d, peeled_a, from5, back, &|d, t| rmat_skip(d, p, ssbp, t))
                };
                let end = rmat_skip(d, p, ssbp, from5);

                let (_e, proof) = NatOps::chain(
                    d,
                    start,
                    &[(mid1, s1), (mid2, s2), (mid3, s3), (mid4, s4), (end, s5)],
                );
                proof
            };

            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let per_x = d.induct(&motive_x, &x_at_zero, &|d, xp, _ih| x_at_succ(d, xp), x);
            let over_x = d.lam_fv(x_fv, nat, per_x);
            d.lam_fv(h_fv, hyp, over_x)
        };

        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let per_b = d.induct(&motive_b, &b_at_zero, &|d, bp, _ih| b_at_succ(d, bp), b);
        d.lam_fv(b_fv, nat, per_b)
    };

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let stmt = motive(d, a);
    let proof = d.induct(&motive, &base, &step, a);
    let ty = d.pi_fv(a_fv, nat, stmt);
    let value = d.lam_fv(a_fv, nat, proof);
    d.declare_theorem(p.mat_skip_comm, ty, value)
}

/// Admit `Rat.matMinor_col_comm : ∀ A i j a b, Nat.ble a b = true → ∀ r c,
/// matMinor (matMinor A i a) j b r c = matMinor (matMinor A i (succ b)) j a r c`.
///
/// [`declare_mat_skip_comm`] lifted from indices to entries, POINTWISE — the
/// only form available, since `funext` is absent (ADR-1135).
///
/// The row indices `i`, `j` are the SAME on both sides, deliberately. A
/// cofactor expansion of a cofactor expansion deletes row `0` and then row `0`
/// of the minor, so the row half of the double deletion is already identical
/// term-for-term and only the columns need exchanging. The fully general
/// double-minor exchange would move the rows too (`(0,0)` becomes `(1,0)`),
/// which is a *different* matrix and not what Laplace needs.
fn declare_mat_minor_col_comm(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let mat = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let hyp = ble_true_ty(d, u, v);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let sv = d.succ(v);
    let left_outer = rmat_minor_of(d, p, mat, i, u);
    let lhs = rmat_minor(d, p, left_outer, j, v, r, c);
    let right_outer = rmat_minor_of(d, p, mat, i, sv);
    let rhs = rmat_minor(d, p, right_outer, j, u, r, c);
    let stmt = req(d, lhs, rhs);

    // Both sides delta-beta-reduce to `A (matSkip i (matSkip j r)) <column>`,
    // and only the column differs.
    let row_index = {
        let inner = rmat_skip(d, p, j, r);
        rmat_skip(d, p, i, inner)
    };
    let left_col = {
        let inner = rmat_skip(d, p, v, c);
        rmat_skip(d, p, u, inner)
    };
    let right_col = {
        let inner = rmat_skip(d, p, u, c);
        rmat_skip(d, p, sv, inner)
    };
    let comm = d.lemma(p.mat_skip_comm, &[u, v, h]);
    let comm_at = d.apply(comm, &[c]);
    let proof = nat_eq_to_rat(d, left_col, right_col, comm_at, &|d, t| {
        d.apply(mat, &[row_index, t])
    });

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_r = d.pi_fv(r_fv, nat, over_c);
        let with_h = d.pi_fv(h_fv, hyp, over_r);
        let over_v = d.pi_fv(v_fv, nat, with_h);
        let over_u = d.pi_fv(u_fv, nat, over_v);
        let over_j = d.pi_fv(j_fv, nat, over_u);
        let over_i = d.pi_fv(i_fv, nat, over_j);
        d.pi_fv(a_fv, mty, over_i)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_r = d.lam_fv(r_fv, nat, over_c);
        let with_h = d.lam_fv(h_fv, hyp, over_r);
        let over_v = d.lam_fv(v_fv, nat, with_h);
        let over_u = d.lam_fv(u_fv, nat, over_v);
        let over_j = d.lam_fv(j_fv, nat, over_u);
        let over_i = d.lam_fv(i_fv, nat, over_j);
        d.lam_fv(a_fv, mty, over_i)
    };
    d.declare_theorem(p.mat_minor_col_comm, ty, value)
}

/// Admit `Rat.det_minor_col_comm : ∀ m A i j a b, Nat.ble a b = true →
/// det (matMinor (matMinor A i a) j b) m =
/// det (matMinor (matMinor A i (succ b)) j a) m`.
///
/// [`declare_mat_minor_col_comm`] carried to the determinant by
/// [`declare_det_congr`] — the only route, because the two doubly-deleted
/// matrices agree at every index pair and are not the same term, and this
/// kernel has no `funext`.
///
/// This is the step a Laplace expansion needs at the *bottom* of its double
/// sum: for a pair of distinct columns `{x, y}`, the two orders of deletion
/// produce the two determinants whose alternating signs then have to cancel.
fn declare_det_minor_col_comm(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let a_fv = d.fresh_fvar();
    let mat = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let u_fv = d.fresh_fvar();
    let u = d.kernel().fvar(u_fv);
    let v_fv = d.fresh_fvar();
    let v = d.kernel().fvar(v_fv);
    let hyp = ble_true_ty(d, u, v);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let sv = d.succ(v);
    let left = {
        let outer = rmat_minor_of(d, p, mat, i, u);
        rmat_minor_of(d, p, outer, j, v)
    };
    let right = {
        let outer = rmat_minor_of(d, p, mat, i, sv);
        rmat_minor_of(d, p, outer, j, u)
    };
    let lhs = rdet(d, p, left, m);
    let rhs = rdet(d, p, right, m);
    let stmt = req(d, lhs, rhs);

    let pointwise = d.const_app(p.mat_minor_col_comm, &[mat, i, j, u, v, h]);
    let proof = d.lemma(p.det_congr, &[m, left, right, pointwise]);

    let ty = {
        let with_h = d.pi_fv(h_fv, hyp, stmt);
        let over_v = d.pi_fv(v_fv, nat, with_h);
        let over_u = d.pi_fv(u_fv, nat, over_v);
        let over_j = d.pi_fv(j_fv, nat, over_u);
        let over_i = d.pi_fv(i_fv, nat, over_j);
        let over_a = d.pi_fv(a_fv, mty, over_i);
        d.pi_fv(m_fv, nat, over_a)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp, proof);
        let over_v = d.lam_fv(v_fv, nat, with_h);
        let over_u = d.lam_fv(u_fv, nat, over_v);
        let over_j = d.lam_fv(j_fv, nat, over_u);
        let over_i = d.lam_fv(i_fv, nat, over_j);
        let over_a = d.lam_fv(a_fv, mty, over_i);
        d.lam_fv(m_fv, nat, over_a)
    };
    d.declare_theorem(p.det_minor_col_comm, ty, value)
}

/// `fun k => f (succ k)`, the tail reindexing
/// [`declare_sum_range_peel_head`] introduces.
fn shift_fn(d: &mut IntDev<'_>, f: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let sk = d.succ(k);
    let body = d.apply(f, &[sk]);
    d.lam_fv(k_fv, nat, body)
}

/// `fun k => f (matSkip j k)`, the summand of a sum over the range with index
/// `j` deleted.
fn skip_fn(d: &mut IntDev<'_>, p: RatPrelude, f: ExprId, j: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let idx = rmat_skip(d, p, j, k);
    let body = d.apply(f, &[idx]);
    d.lam_fv(k_fv, nat, body)
}

/// Admit `Rat.sumRange_peel_head : ∀ f n, sumRange f (succ n) =
/// add (f 0) (sumRange (fun k => f (succ k)) n)`.
///
/// `Rat.sumRange` peels from the RIGHT (`sumRange f (succ n) ≡
/// sumRange f n + f n`), so nothing in this prelude hands you the FIRST
/// summand — [`declare_sum_range_head_of_tail_zero`] had to be written for
/// exactly that reason, and it only reaches the special case where everything
/// past index `0` vanishes. This is the general form, and every left-side
/// reindexing needs it.
///
/// Induction on `n` with `f` fixed: the base is `add_comm` on
/// `zero + f 0` against `f 0 + zero`, and the step is the induction hypothesis
/// under `add _ (f (succ j))` followed by one `add_assoc`. The right-hand
/// side's own `sumRange` peel is definitional, which is why the step needs no
/// third move.
fn declare_sum_range_peel_head(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let zero_n = d.zero();
    let head = d.apply(f, &[zero_n]);
    let tail_fn = shift_fn(d, f);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sx = d.succ(x);
        let lhs = rsum_range(d, p, f, sx);
        let tail = rsum_range(d, p, tail_fn, x);
        let rhs = radd(d, head, tail);
        req(d, lhs, rhs)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        // `sumRange f 1 ≡ zero + f 0` and `f 0 + sumRange _ 0 ≡ f 0 + zero`.
        &|d| {
            let zero_r = rzero(d, p);
            d.lemma(p.add_comm, &[zero_r, head])
        },
        &|d, j, ih| {
            let sj = d.succ(j);
            let prior = rsum_range(d, p, f, sj);
            let fsj = d.apply(f, &[sj]);
            let start = radd(d, prior, fsj);

            let tail_j = rsum_range(d, p, tail_fn, j);
            let peeled = radd(d, head, tail_j);
            let s1 = rcongr(d, prior, peeled, ih, &|d, t| radd(d, t, fsj));
            let mid1 = radd(d, peeled, fsj);

            let s2 = d.lemma(p.add_assoc, &[head, tail_j, fsj]);
            let end = {
                let inner = radd(d, tail_j, fsj);
                radd(d, head, inner)
            };

            let (_e, proof) = rchain(d, start, &[(mid1, s1), (end, s2)]);
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
    d.declare_theorem(p.sum_range_peel_head, ty, value)
}

/// Admit `Rat.sumRange_matSkip : ∀ n f j, Nat.ble j n = true →
/// add (sumRange (fun k => f (matSkip j k)) n) (f j) = sumRange f (succ n)`.
///
/// **The range half of a Laplace expansion.** `matSkip j` is the
/// order-preserving bijection `[0, n) → [0, n+1) \ {j}`, so summing `f` along
/// it and adding `f j` back recovers the whole sum. It is what turns a
/// cofactor sum — which runs over a range ONE SHORT, reindexed by `matSkip` —
/// into a sum over the full range, and a double cofactor expansion whose two
/// sums both run over the full range is a plain rectangle, reachable by
/// [`RatPrelude::sum_range_swap`] with no triangle decomposition and no
/// `Nat.sub`.
///
/// The dimension is quantified OUTERMOST and **`f` is quantified under the
/// motive**, which is what makes the induction go through: the successor step
/// at `j = succ j'` applies the induction hypothesis at the SHIFTED function
/// `fun k => f (succ k)`, not at `f`. This is the same shape
/// [`declare_det_congr`] needs and for the same reason — an induction
/// hypothesis that cannot move to a different argument is useless here.
///
/// The hypothesis is the BOOLEAN `Nat.ble j n = true` for the reason
/// [`declare_mat_skip_comm`] gives: the case `j = succ j'`, `n = succ m`
/// reduces it to `ble j' m = true` by iota alone, and the case `n = 0`,
/// `j = succ j'` reduces it to `false = true`. Choosing `Nat.le` would put an
/// inversion lemma in both places.
///
/// The step, at `n = succ m`:
///
/// - `j = 0`: `matSkip 0 k ≡ succ k`, so the reindexed sum is *definitionally*
///   the shifted sum and the goal is [`declare_sum_range_peel_head`] after one
///   `add_comm`. No induction hypothesis is used.
/// - `j = succ j'`: peel the head off the reindexed sum
///   (`matSkip (succ j') 0 ≡ 0`, so that head is `f 0` definitionally), move
///   the tail across [`declare_mat_skip_succ_succ`] with
///   [`RatPrelude::sum_range_congr`], and the remainder is the induction
///   hypothesis at `(fun k => f (succ k), j')` under one `add_assoc`.
fn declare_sum_range_mat_skip(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let carrier = rat_ty(d);
        let fn_ty = d.arrow(nat, carrier);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let hyp = ble_true_ty(d, j, x);
        let reindexed = skip_fn(d, p, f, j);
        let partial = rsum_range(d, p, reindexed, x);
        let fj = d.apply(f, &[j]);
        let lhs = radd(d, partial, fj);
        let sx = d.succ(x);
        let rhs = rsum_range(d, p, f, sx);
        let eq = req(d, lhs, rhs);
        let with_h = d.arrow(hyp, eq);
        let over_j = d.pi_fv(j_fv, nat, with_h);
        d.pi_fv(f_fv, fn_ty, over_j)
    };
    let stmt = motive(d, n);

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let nat = d.nat_ty();
        let carrier = rat_ty(d);
        let fn_ty = d.arrow(nat, carrier);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);

        let motive_j = |d: &mut IntDev<'_>, j: ExprId| -> ExprId {
            let zero_n = d.zero();
            let hyp = ble_true_ty(d, j, zero_n);
            let reindexed = skip_fn(d, p, f, j);
            let partial = rsum_range(d, p, reindexed, zero_n);
            let fj = d.apply(f, &[j]);
            let lhs = radd(d, partial, fj);
            let one_n = d.succ(zero_n);
            let rhs = rsum_range(d, p, f, one_n);
            let eq = req(d, lhs, rhs);
            d.arrow(hyp, eq)
        };

        let j_at_zero = |d: &mut IntDev<'_>| -> ExprId {
            // `sumRange _ 0 ≡ zero` on both sides, and `j` is `0`, so the two
            // sides are the same term.
            let zero_n = d.zero();
            let hyp = ble_true_ty(d, zero_n, zero_n);
            let h_fv = d.fresh_fvar();
            let zero_r = rzero(d, p);
            let f0 = d.apply(f, &[zero_n]);
            let shape = radd(d, zero_r, f0);
            let pf = rrefl(d, shape);
            d.lam_fv(h_fv, hyp, pf)
        };

        let j_at_succ = |d: &mut IntDev<'_>, jp: ExprId| -> ExprId {
            // `ble (succ j') zero ≡ false`, so the premise is `false = true`.
            let zero_n = d.zero();
            let sjp = d.succ(jp);
            let hyp = ble_true_ty(d, sjp, zero_n);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let reindexed = skip_fn(d, p, f, sjp);
            let partial = rsum_range(d, p, reindexed, zero_n);
            let fj = d.apply(f, &[sjp]);
            let lhs = radd(d, partial, fj);
            let one_n = d.succ(zero_n);
            let rhs = rsum_range(d, p, f, one_n);
            let target = req(d, lhs, rhs);
            let pf = d.false_true_elim(target, h);
            d.lam_fv(h_fv, hyp, pf)
        };

        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let per_j = d.induct(&motive_j, &j_at_zero, &|d, jp, _ih| j_at_succ(d, jp), j);
        let over_j = d.lam_fv(j_fv, nat, per_j);
        d.lam_fv(f_fv, fn_ty, over_j)
    };

    let step = |d: &mut IntDev<'_>, m: ExprId, ih: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let carrier = rat_ty(d);
        let fn_ty = d.arrow(nat, carrier);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let sm = d.succ(m);
        let ssm = d.succ(sm);
        let zero_n = d.zero();
        let head = d.apply(f, &[zero_n]);
        let tail_fn = shift_fn(d, f);

        let motive_j = |d: &mut IntDev<'_>, j: ExprId| -> ExprId {
            let hyp = ble_true_ty(d, j, sm);
            let reindexed = skip_fn(d, p, f, j);
            let partial = rsum_range(d, p, reindexed, sm);
            let fj = d.apply(f, &[j]);
            let lhs = radd(d, partial, fj);
            let rhs = rsum_range(d, p, f, ssm);
            let eq = req(d, lhs, rhs);
            d.arrow(hyp, eq)
        };

        let j_at_zero = |d: &mut IntDev<'_>| -> ExprId {
            let zero_n = d.zero();
            let hyp = ble_true_ty(d, zero_n, sm);
            let h_fv = d.fresh_fvar();

            // `fun k => f (matSkip 0 k)` is definitionally `fun k => f (succ k)`.
            let reindexed = skip_fn(d, p, f, zero_n);
            let partial = rsum_range(d, p, reindexed, sm);
            let start = radd(d, partial, head);
            let s1 = d.lemma(p.add_comm, &[partial, head]);
            let mid1 = radd(d, head, partial);

            let shifted_sum = rsum_range(d, p, tail_fn, sm);
            let peeled = radd(d, head, shifted_sum);
            let full = rsum_range(d, p, f, ssm);
            let peel = d.lemma(p.sum_range_peel_head, &[f, sm]);
            let s2 = super::ops::rsymm(d, full, peeled, peel);

            let (_e, pf) = rchain(d, start, &[(mid1, s1), (full, s2)]);
            d.lam_fv(h_fv, hyp, pf)
        };

        let j_at_succ = |d: &mut IntDev<'_>, jp: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let sjp = d.succ(jp);
            let hyp = ble_true_ty(d, sjp, sm);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let reindexed = skip_fn(d, p, f, sjp);
            let partial = rsum_range(d, p, reindexed, sm);
            let fj = d.apply(f, &[sjp]);
            let start = radd(d, partial, fj);

            // 1. peel the head off the reindexed sum; `matSkip (succ j') 0 ≡ 0`
            //    so that head is `f 0` definitionally.
            let zero_n = d.zero();
            let phi_head = d.apply(reindexed, &[zero_n]);
            let phi_tail_fn = shift_fn(d, reindexed);
            let phi_tail = rsum_range(d, p, phi_tail_fn, m);
            let peeled = radd(d, phi_head, phi_tail);
            let peel = d.lemma(p.sum_range_peel_head, &[reindexed, m]);
            let s1 = rcongr(d, partial, peeled, peel, &|d, t| radd(d, t, fj));
            let mid1 = radd(d, peeled, fj);

            // 2. `f (matSkip (succ j') (succ k)) = (fun i => f (succ i)) (matSkip j' k)`
            //    at every `k`, by `matSkip_succ_succ`.
            let inner_fn = skip_fn(d, p, tail_fn, jp);
            let inner_sum = rsum_range(d, p, inner_fn, m);
            let pointwise = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sk = d.succ(k);
                let from = rmat_skip(d, p, sjp, sk);
                let skipped = rmat_skip(d, p, jp, k);
                let to = d.succ(skipped);
                let mss = d.lemma(p.mat_skip_succ_succ, &[jp, k]);
                let body = nat_eq_to_rat(d, from, to, mss, &|d, t| d.apply(f, &[t]));
                d.lam_fv(k_fv, nat, body)
            };
            let congr_sum = d.lemma(p.sum_range_congr, &[phi_tail_fn, inner_fn, m, pointwise]);
            let s2 = rcongr(d, phi_tail, inner_sum, congr_sum, &|d, t| {
                let inner = radd(d, phi_head, t);
                radd(d, inner, fj)
            });
            let mid2 = {
                let inner = radd(d, phi_head, inner_sum);
                radd(d, inner, fj)
            };

            // 3. reassociate so the induction hypothesis's own left-hand side
            //    appears as a subterm.
            let s3 = d.lemma(p.add_assoc, &[phi_head, inner_sum, fj]);
            let ih_lhs = radd(d, inner_sum, fj);
            let mid3 = radd(d, phi_head, ih_lhs);

            // 4. the induction hypothesis, at the SHIFTED function.
            let ih_at = d.apply(ih, &[tail_fn, jp, h]);
            let shifted_full = rsum_range(d, p, tail_fn, sm);
            let s4 = rcongr(d, ih_lhs, shifted_full, ih_at, &|d, t| radd(d, phi_head, t));
            let mid4 = radd(d, phi_head, shifted_full);

            // 5. `f 0 + sumRange (fun k => f (succ k)) (succ m) = sumRange f (succ (succ m))`.
            let peeled_full = radd(d, head, shifted_full);
            let full = rsum_range(d, p, f, ssm);
            let peel_f = d.lemma(p.sum_range_peel_head, &[f, sm]);
            let s5 = super::ops::rsymm(d, full, peeled_full, peel_f);

            let (_e, pf) = rchain(
                d,
                start,
                &[(mid1, s1), (mid2, s2), (mid3, s3), (mid4, s4), (full, s5)],
            );
            d.lam_fv(h_fv, hyp, pf)
        };

        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let per_j = d.induct(&motive_j, &j_at_zero, &|d, jp, _ih| j_at_succ(d, jp), j);
        let over_j = d.lam_fv(j_fv, nat, per_j);
        d.lam_fv(f_fv, fn_ty, over_j)
    };

    let proof = d.induct(&motive, &base, &step, n);
    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.sum_range_mat_skip, ty, value)
}

// --- the summand layer of Laplace expansion (ADR-1185) ---------------------
//
// ADR-1155 landed the index layer (`matSkip_*`) and the range layer
// (`sumRange_*`) and named what remains: a summand defined on the WHOLE
// square, with a `Nat.beq` diagonal guard, so that both cofactor
// parametrisations of a double expansion hit the same function and the double
// sum becomes a plain rectangle. This section is that summand's index layer.

/// `Rat.unskip p q`.
fn runskip(d: &mut IntDev<'_>, p: RatPrelude, at: ExprId, q: ExprId) -> ExprId {
    d.const_app(p.unskip, &[at, q])
}

/// From `h : Eq Nat a b`, derive `Eq Bool (f a) (f b)`.
///
/// The `Bool`-valued companion of
/// [`nat_eq_to_rat`](super::ops::nat_eq_to_rat), needed because the summand's
/// guard is `Nat.beq` — a `Bool`, not a `Rat` — and rewriting a `Nat` index
/// underneath it has to land in `Eq Bool`.
fn nat_eq_to_bool(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = NatOps::eq_motive(d, a, &|d, x| {
        let fx = f(d, x);
        d.bool_eq(fa, fx)
    });
    let refl_case = d.bool_refl(fa);
    NatOps::transport(d, a, motive, refl_case, b, h)
}

/// Admit `Rat.unskip : Nat → Nat → Nat`, the left inverse of
/// [`declare_mat_skip`].
///
/// ```text
/// unskip zero        q        ≡ Nat.pred q
/// unskip (succ p)    zero     ≡ zero
/// unskip (succ p) (succ q)    ≡ succ (unskip p q)
/// ```
///
/// A double `Nat.rec`, the construction `Nat.ble` and `Nat.beq` both use, so
/// **all three rows hold by ι-reduction alone**.
///
/// The closed form ADR-1155 names — `if Nat.ble (succ p) q then pred q else q`
/// — computes the same function (checked at all 64 pairs below 8 in
/// `docs/research/09-decisions/adr-1185-laplace-summand-checks.py`) and is the
/// wrong shape to reason with. `unskip p (matSkip p c)` leaves TWO stuck
/// `Nat.ble` guards, and a `Bool.rec` split on the inner one does not reach
/// the outer: reducing `ble (succ p) (succ c)` re-creates `ble p c`, the very
/// scrutinee the split had abstracted away. With the recursive form the same
/// lemma is a two-level induction with no case split at all.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_unskip(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let one = d.level_one();
    let rec_name = d.prelude().rec;
    let nat_to_nat = d.arrow(nat, nat);
    let nat_motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);

    // `unskip zero` is `Nat.pred`, with no inner recursion.
    let zero_minor = {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let body = d.pred(y);
        d.lam_fv(y_fv, nat, body)
    };

    // `unskip (succ x)`: zero at zero, `succ` of the row below at `succ y`.
    let succ_minor = {
        let x_fv = d.fresh_fvar();
        let ih_fv = d.fresh_fvar();
        let ih = d.kernel().fvar(ih_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let step = {
            let predecessor_fv = d.fresh_fvar();
            let predecessor = d.kernel().fvar(predecessor_fv);
            let unused_ih_fv = d.fresh_fvar();
            let inner = d.apply(ih, &[predecessor]);
            let body = d.succ(inner);
            let with_ih = d.lam_fv(unused_ih_fv, nat, body);
            d.lam_fv(predecessor_fv, nat, with_ih)
        };
        let zero_n = d.zero();
        let rec = d.kernel().const_(rec_name, vec![one]);
        let body = d.apply(rec, &[nat_motive, zero_n, step, y]);
        let with_y = d.lam_fv(y_fv, nat, body);
        let with_ih = d.lam_fv(ih_fv, nat_to_nat, with_y);
        d.lam_fv(x_fv, nat, with_ih)
    };

    let outer_motive = d.kernel().lam(anon, nat, nat_to_nat, BinderInfo::Default);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let y_fv = d.fresh_fvar();
    let y = d.kernel().fvar(y_fv);
    let rec = d.kernel().const_(rec_name, vec![one]);
    let row = d.apply(rec, &[outer_motive, zero_minor, succ_minor, x]);
    let body = d.apply(row, &[y]);
    let value = {
        let with_y = d.lam_fv(y_fv, nat, body);
        d.lam_fv(x_fv, nat, with_y)
    };
    let ty = {
        let inner = d.arrow(nat, nat);
        d.arrow(nat, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.unskip,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(UNSKIP_HEIGHT),
    })
}

/// `Rat.unskip_zero`, `Rat.unskip_succ_zero` and `Rat.unskip_succ_succ`: the
/// three defining equations, each `Eq.refl`.
///
/// Published rather than left implicit because **the trusted gate cannot tell
/// you a `Definition` is wrong** — `Nat → Nat → Nat` is that type whatever the
/// function returns — so a reader has no way to see which recursion was
/// declared except by reading these back. The evaluation evidence proper is
/// `rat_prelude_tests::the_laplace_summand_index_layer_computes`, which pins
/// concrete values.
fn declare_unskip_equations(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    // unskip_zero : ∀ q, unskip 0 q = Nat.pred q
    {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let zero_n = d.zero();
        let lhs = runskip(d, p, zero_n, q);
        let rhs = d.pred(q);
        let stmt = NatOps::eq(d, lhs, rhs);
        let proof = NatOps::refl(d, rhs);
        let ty = d.pi_fv(q_fv, nat, stmt);
        let value = d.lam_fv(q_fv, nat, proof);
        d.declare_theorem(p.unskip_zero, ty, value)?;
    }

    // unskip_succ_zero : ∀ x, unskip (succ x) 0 = 0
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let sx = d.succ(x);
        let zero_n = d.zero();
        let lhs = runskip(d, p, sx, zero_n);
        let stmt = NatOps::eq(d, lhs, zero_n);
        let proof = NatOps::refl(d, zero_n);
        let ty = d.pi_fv(x_fv, nat, stmt);
        let value = d.lam_fv(x_fv, nat, proof);
        d.declare_theorem(p.unskip_succ_zero, ty, value)?;
    }

    // unskip_succ_succ : ∀ x y, unskip (succ x) (succ y) = succ (unskip x y)
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let sx = d.succ(x);
        let sy = d.succ(y);
        let lhs = runskip(d, p, sx, sy);
        let inner = runskip(d, p, x, y);
        let rhs = d.succ(inner);
        let stmt = NatOps::eq(d, lhs, rhs);
        let proof = NatOps::refl(d, rhs);
        let ty = {
            let over_y = d.pi_fv(y_fv, nat, stmt);
            d.pi_fv(x_fv, nat, over_y)
        };
        let value = {
            let over_y = d.lam_fv(y_fv, nat, proof);
            d.lam_fv(x_fv, nat, over_y)
        };
        d.declare_theorem(p.unskip_succ_succ, ty, value)?;
    }
    Ok(())
}

/// Admit `Rat.unskip_matSkip : ∀ p k, unskip p (matSkip p k) = k`.
///
/// **Unconditional** — no `Nat.ble` premise, unlike every other lemma in this
/// cluster. `matSkip p` never produces `p`, so its whole image lies where
/// `unskip p` inverts it, and the two branches of the guard are covered by the
/// two branches of the recursion rather than by a case split.
///
/// Induction on `p` with `k` under the motive, then a case split on `k`:
///
/// - `p = 0`: `matSkip 0 k ≡ succ k` and `unskip 0 (succ k) ≡ pred (succ k) ≡ k`
///   — both steps ι, so this is `Eq.refl`.
/// - `p = succ p'`, `k = 0`: `matSkip (succ p') 0 ≡ 0` (since
///   `ble (succ p') zero ≡ false`) and `unskip (succ p') 0 ≡ 0` — `Eq.refl`.
/// - `p = succ p'`, `k = succ k'`: one [`declare_mat_skip_succ_succ`] to peel
///   the shift, after which `unskip (succ p') (succ _)` ι-reduces to
///   `succ (unskip p' _)` and the induction hypothesis finishes it under
///   `succ`.
fn declare_unskip_mat_skip(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let motive = |d: &mut IntDev<'_>, at: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let skipped = rmat_skip(d, p, at, k);
        let lhs = runskip(d, p, at, skipped);
        let eq = NatOps::eq(d, lhs, k);
        d.pi_fv(k_fv, nat, eq)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let nat = d.nat_ty();
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let pf = NatOps::refl(d, k);
        d.lam_fv(k_fv, nat, pf)
    };

    let step = |d: &mut IntDev<'_>, pp: ExprId, ih: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let spp = d.succ(pp);

        let motive_k = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
            let skipped = rmat_skip(d, p, spp, k);
            let lhs = runskip(d, p, spp, skipped);
            NatOps::eq(d, lhs, k)
        };

        let k_at_zero = |d: &mut IntDev<'_>| -> ExprId {
            let zero_n = d.zero();
            NatOps::refl(d, zero_n)
        };

        let k_at_succ = |d: &mut IntDev<'_>, kp: ExprId| -> ExprId {
            let skp = d.succ(kp);
            let inner = rmat_skip(d, p, pp, kp);
            let start = {
                let sk = rmat_skip(d, p, spp, skp);
                runskip(d, p, spp, sk)
            };

            // 1. `matSkip (succ p') (succ k')  ->  succ (matSkip p' k')`,
            //    under `unskip (succ p') _`; the result then ι-reduces to
            //    `succ (unskip p' (matSkip p' k'))`.
            let s1 = {
                let from = rmat_skip(d, p, spp, skp);
                let to = d.succ(inner);
                let pf = d.lemma(p.mat_skip_succ_succ, &[pp, kp]);
                NatOps::congr(d, from, to, pf, &|d, t| runskip(d, p, spp, t))
            };
            let peeled = runskip(d, p, pp, inner);
            let mid1 = d.succ(peeled);

            // 2. the induction hypothesis at `k'`, under `succ`.
            let s2 = {
                let pf = d.apply(ih, &[kp]);
                NatOps::congr(d, peeled, kp, pf, &|d, t| d.succ(t))
            };

            let (_e, proof) = NatOps::chain(d, start, &[(mid1, s1), (skp, s2)]);
            proof
        };

        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let per_k = d.induct(&motive_k, &k_at_zero, &|d, kp, _ih| k_at_succ(d, kp), k);
        d.lam_fv(k_fv, nat, per_k)
    };

    let p_fv = d.fresh_fvar();
    let at = d.kernel().fvar(p_fv);
    let stmt = motive(d, at);
    let proof = d.induct(&motive, &base, &step, at);
    let ty = d.pi_fv(p_fv, nat, stmt);
    let value = d.lam_fv(p_fv, nat, proof);
    d.declare_theorem(p.unskip_mat_skip, ty, value)
}

/// Admit `Rat.beq_matSkip : ∀ j k, Nat.beq j (matSkip j k) = false` and
/// `Rat.beq_matSkip_left : ∀ j k, Nat.beq (matSkip j k) j = false`.
///
/// `matSkip j` is the injection whose image MISSES `j`; these are that fact in
/// the `Bool` form the summand's diagonal guard is written in. Both are the
/// same two-level induction as [`declare_unskip_mat_skip`], with `Nat.beq`'s
/// three ι-rows (`beq zero (succ _) ≡ false`, `beq (succ _) zero ≡ false`,
/// `beq (succ x) (succ y) ≡ beq x y`) doing the work `Nat.pred` did there.
///
/// Stated in BOTH argument orders rather than derived one from the other: this
/// prelude has no `Nat.beq` commutativity, and the two cofactor
/// parametrisations reach the guard from opposite sides — the row-`0`
/// expansion has the skipped index on the right, the row-`i` expansion has it
/// on the left.
fn declare_beq_mat_skip(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    // beq_matSkip : ∀ j k, beq j (matSkip j k) = false
    {
        let motive = |d: &mut IntDev<'_>, j: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let skipped = rmat_skip(d, p, j, k);
            let lhs = d.beq(j, skipped);
            let false_ = d.bool_false();
            let eq = d.bool_eq(lhs, false_);
            d.pi_fv(k_fv, nat, eq)
        };

        let base = |d: &mut IntDev<'_>| -> ExprId {
            // `beq 0 (matSkip 0 k) ≡ beq 0 (succ k) ≡ false`.
            let nat = d.nat_ty();
            let k_fv = d.fresh_fvar();
            let false_ = d.bool_false();
            let pf = d.bool_refl(false_);
            d.lam_fv(k_fv, nat, pf)
        };

        let step = |d: &mut IntDev<'_>, jp: ExprId, ih: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let sjp = d.succ(jp);

            let motive_k = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let skipped = rmat_skip(d, p, sjp, k);
                let lhs = d.beq(sjp, skipped);
                let false_ = d.bool_false();
                d.bool_eq(lhs, false_)
            };
            let k_at_zero = |d: &mut IntDev<'_>| -> ExprId {
                // `matSkip (succ j') 0 ≡ 0` and `beq (succ j') 0 ≡ false`.
                let false_ = d.bool_false();
                d.bool_refl(false_)
            };
            let k_at_succ = |d: &mut IntDev<'_>, kp: ExprId| -> ExprId {
                let skp = d.succ(kp);
                let inner = rmat_skip(d, p, jp, kp);
                let start = {
                    let sk = rmat_skip(d, p, sjp, skp);
                    d.beq(sjp, sk)
                };
                let s1 = {
                    let from = rmat_skip(d, p, sjp, skp);
                    let to = d.succ(inner);
                    let pf = d.lemma(p.mat_skip_succ_succ, &[jp, kp]);
                    nat_eq_to_bool(d, from, to, pf, &|d, t| d.beq(sjp, t))
                };
                // `beq (succ j') (succ _) ≡ beq j' _`, which is what `ih` has.
                let mid1 = d.beq(jp, inner);
                let s2 = d.apply(ih, &[kp]);
                let false_ = d.bool_false();
                d.bool_trans(start, mid1, false_, s1, s2)
            };

            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let per_k = d.induct(&motive_k, &k_at_zero, &|d, kp, _ih| k_at_succ(d, kp), k);
            d.lam_fv(k_fv, nat, per_k)
        };

        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let stmt = motive(d, j);
        let proof = d.induct(&motive, &base, &step, j);
        let ty = d.pi_fv(j_fv, nat, stmt);
        let value = d.lam_fv(j_fv, nat, proof);
        d.declare_theorem(p.beq_mat_skip, ty, value)?;
    }

    // beq_matSkip_left : ∀ j k, beq (matSkip j k) j = false
    {
        let motive = |d: &mut IntDev<'_>, j: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let skipped = rmat_skip(d, p, j, k);
            let lhs = d.beq(skipped, j);
            let false_ = d.bool_false();
            let eq = d.bool_eq(lhs, false_);
            d.pi_fv(k_fv, nat, eq)
        };

        let base = |d: &mut IntDev<'_>| -> ExprId {
            // `beq (succ k) 0 ≡ false`.
            let nat = d.nat_ty();
            let k_fv = d.fresh_fvar();
            let false_ = d.bool_false();
            let pf = d.bool_refl(false_);
            d.lam_fv(k_fv, nat, pf)
        };

        let step = |d: &mut IntDev<'_>, jp: ExprId, ih: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let sjp = d.succ(jp);

            let motive_k = |d: &mut IntDev<'_>, k: ExprId| -> ExprId {
                let skipped = rmat_skip(d, p, sjp, k);
                let lhs = d.beq(skipped, sjp);
                let false_ = d.bool_false();
                d.bool_eq(lhs, false_)
            };
            let k_at_zero = |d: &mut IntDev<'_>| -> ExprId {
                // `matSkip (succ j') 0 ≡ 0` and `beq 0 (succ j') ≡ false`.
                let false_ = d.bool_false();
                d.bool_refl(false_)
            };
            let k_at_succ = |d: &mut IntDev<'_>, kp: ExprId| -> ExprId {
                let skp = d.succ(kp);
                let inner = rmat_skip(d, p, jp, kp);
                let start = {
                    let sk = rmat_skip(d, p, sjp, skp);
                    d.beq(sk, sjp)
                };
                let s1 = {
                    let from = rmat_skip(d, p, sjp, skp);
                    let to = d.succ(inner);
                    let pf = d.lemma(p.mat_skip_succ_succ, &[jp, kp]);
                    nat_eq_to_bool(d, from, to, pf, &|d, t| d.beq(t, sjp))
                };
                let mid1 = d.beq(inner, jp);
                let s2 = d.apply(ih, &[kp]);
                let false_ = d.bool_false();
                d.bool_trans(start, mid1, false_, s1, s2)
            };

            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let per_k = d.induct(&motive_k, &k_at_zero, &|d, kp, _ih| k_at_succ(d, kp), k);
            d.lam_fv(k_fv, nat, per_k)
        };

        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let stmt = motive(d, j);
        let proof = d.induct(&motive, &base, &step, j);
        let ty = d.pi_fv(j_fv, nat, stmt);
        let value = d.lam_fv(j_fv, nat, proof);
        d.declare_theorem(p.beq_mat_skip_left, ty, value)?;
    }

    Ok(())
}

/// Admit `Rat.altSign_succ_add : ∀ n k, altSign (Nat.add (succ n) k) =
/// neg (altSign (Nat.add n k))`.
///
/// The parity step the summand's sign needs. `Rat.altSign_succ` is `Eq.refl`
/// and gives the `succ` on the OUTSIDE; `Nat.add` recurses on its RIGHT
/// argument, so `add n (succ k)` ι-reduces and `add (succ n) k` is stuck. One
/// `Nat.succ_add` bridges them, and the `neg` then appears definitionally.
fn declare_alt_sign_succ_add(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let sn = d.succ(n);
    let shifted = d.add(sn, k);
    let plain = d.add(n, k);
    let lhs = ralt_sign(d, p, shifted);
    let rhs = {
        let inner = ralt_sign(d, p, plain);
        rneg(d, inner)
    };
    let stmt = req(d, lhs, rhs);

    let succ_add = {
        let name = d.prelude().succ_add;
        d.const_app(name, &[n, k])
    };
    let peeled = d.succ(plain);
    let proof = nat_eq_to_rat(d, shifted, peeled, succ_add, &|d, t| ralt_sign(d, p, t));

    let ty = {
        let over_k = d.pi_fv(k_fv, nat, stmt);
        d.pi_fv(n_fv, nat, over_k)
    };
    let value = {
        let over_k = d.lam_fv(k_fv, nat, proof);
        d.lam_fv(n_fv, nat, over_k)
    };
    d.declare_theorem(p.alt_sign_succ_add, ty, value)
}

/// `heq : Eq Bool cond true ⊢ Eq Nat (bool_select_nat cond a b) a`.
///
/// A local copy of the `Nat` analogue of
/// [`select_rat_true`](super::probability::select_rat_true);
/// `nat_prelude::finite`'s is `pub(super)` there and `int_prelude`'s two are
/// private, so `int_prelude/wilson.rs` and `int_prelude/prod.rs` each keep
/// their own as well.
fn select_nat_true(d: &mut IntDev<'_>, cond: ExprId, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let true_value = d.bool_true();
    let flipped = d.bool_symm(cond, true_value, heq);
    let motive = d.bool_eq_motive(true_value, &|d, value| {
        let selected = d.bool_select_nat(value, a, b);
        NatOps::eq(d, selected, a)
    });
    let refl_case = NatOps::refl(d, a);
    d.bool_transport(true_value, motive, refl_case, cond, flipped)
}

/// `heq : Eq Bool cond false ⊢ Eq Nat (bool_select_nat cond a b) b`.
fn select_nat_false(d: &mut IntDev<'_>, cond: ExprId, a: ExprId, b: ExprId, heq: ExprId) -> ExprId {
    let false_value = d.bool_false();
    let flipped = d.bool_symm(cond, false_value, heq);
    let motive = d.bool_eq_motive(false_value, &|d, value| {
        let selected = d.bool_select_nat(value, a, b);
        NatOps::eq(d, selected, b)
    });
    let refl_case = NatOps::refl(d, b);
    d.bool_transport(false_value, motive, refl_case, cond, flipped)
}

/// A `Bool` case split that KEEPS the equation: given proofs of
/// `Eq Bool cond true → target` and `Eq Bool cond false → target`, produce
/// `target`.
///
/// [`bool_cases`] is the other device and it is not interchangeable with this
/// one. That one abstracts the scrutinee out of the goal and replaces it by
/// each constructor, which works when every occurrence is *syntactically* the
/// scrutinee. It does not work when reduction RE-CREATES the scrutinee — the
/// reason [`declare_unskip`] is a double `Nat.rec` rather than the closed
/// `Nat.ble` form. This device leaves the goal alone and hands each branch the
/// hypothesis instead, which is what the summand identification needs: the two
/// branches differ in which `Rat.matSkip_comm` orientation applies, not in the
/// shape of the goal.
pub(super) fn bool_cases_eq(
    d: &mut IntDev<'_>,
    cond: ExprId,
    target: ExprId,
    at_true: ExprId,
    at_false: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let motive = {
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let equation = d.bool_eq(cond, b);
        let body = d.arrow(equation, target);
        d.lam_fv(b_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.prelude().logic.bool_rec;
    let rec = d.kernel().const_(bool_rec, vec![level_zero]);
    let dispatched = d.apply(rec, &[motive, at_false, at_true, cond]);
    let reflexive = d.bool_refl(cond);
    d.apply(dispatched, &[reflexive])
}

/// Admit `Rat.ble_flip_of_false : ∀ x y, Nat.ble (succ x) y = false →
/// Nat.ble y x = true`.
///
/// The one `Nat.ble` inversion this development needs and `nat_prelude/ble.rs`
/// does not carry: it has the two positive bridges to `Nat.le` and the negated
/// `Prop` form, but nothing turning a `= false` into the *other* comparison's
/// `= true`, which is the shape a `Bool.rec` branch hands you.
///
/// Induction on `x` with `y` under the motive, case-splitting on `y` in each
/// arm. Every case is ι: `ble (succ _) zero ≡ false`, `ble zero _ ≡ true`, and
/// `ble (succ a) (succ b) ≡ ble a b`, so the two impossible corners are a
/// [`NatOps::false_true_elim`] after one `bool_symm` and the live corner is the
/// induction hypothesis verbatim.
fn declare_ble_flip_of_false(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let sx = d.succ(x);
        let hyp = {
            let lhs = d.ble(sx, y);
            let false_ = d.bool_false();
            d.bool_eq(lhs, false_)
        };
        let concl = {
            let lhs = d.ble(y, x);
            let true_ = d.bool_true();
            d.bool_eq(lhs, true_)
        };
        let arr = d.arrow(hyp, concl);
        d.pi_fv(y_fv, nat, arr)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let nat = d.nat_ty();
        let zero_n = d.zero();
        let one_n = d.succ(zero_n);

        let motive_y = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
            let hyp = {
                let lhs = d.ble(one_n, y);
                let false_ = d.bool_false();
                d.bool_eq(lhs, false_)
            };
            let concl = {
                let lhs = d.ble(y, zero_n);
                let true_ = d.bool_true();
                d.bool_eq(lhs, true_)
            };
            d.arrow(hyp, concl)
        };

        let y_at_zero = |d: &mut IntDev<'_>| -> ExprId {
            // `ble 0 0 ≡ true`; the hypothesis is not used.
            let zero_n = d.zero();
            let one_n = d.succ(zero_n);
            let hyp = {
                let lhs = d.ble(one_n, zero_n);
                let false_ = d.bool_false();
                d.bool_eq(lhs, false_)
            };
            let h_fv = d.fresh_fvar();
            let true_ = d.bool_true();
            let pf = d.bool_refl(true_);
            d.lam_fv(h_fv, hyp, pf)
        };

        let y_at_succ = |d: &mut IntDev<'_>, yp: ExprId| -> ExprId {
            // `ble 1 (succ y') ≡ ble 0 y' ≡ true`, so the premise is
            // `true = false`.
            let zero_n = d.zero();
            let one_n = d.succ(zero_n);
            let syp = d.succ(yp);
            let hyp = {
                let lhs = d.ble(one_n, syp);
                let false_ = d.bool_false();
                d.bool_eq(lhs, false_)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let true_ = d.bool_true();
            let false_ = d.bool_false();
            let flipped = d.bool_symm(true_, false_, h);
            let target = {
                let lhs = d.ble(syp, zero_n);
                d.bool_eq(lhs, true_)
            };
            let pf = d.false_true_elim(target, flipped);
            d.lam_fv(h_fv, hyp, pf)
        };

        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let per_y = d.induct(&motive_y, &y_at_zero, &|d, yp, _ih| y_at_succ(d, yp), y);
        d.lam_fv(y_fv, nat, per_y)
    };

    let step = |d: &mut IntDev<'_>, xp: ExprId, ih: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let sxp = d.succ(xp);
        let ssxp = d.succ(sxp);

        let motive_y = |d: &mut IntDev<'_>, y: ExprId| -> ExprId {
            let hyp = {
                let lhs = d.ble(ssxp, y);
                let false_ = d.bool_false();
                d.bool_eq(lhs, false_)
            };
            let concl = {
                let lhs = d.ble(y, sxp);
                let true_ = d.bool_true();
                d.bool_eq(lhs, true_)
            };
            d.arrow(hyp, concl)
        };

        let y_at_zero = |d: &mut IntDev<'_>| -> ExprId {
            // `ble 0 (succ x') ≡ true`.
            let zero_n = d.zero();
            let hyp = {
                let lhs = d.ble(ssxp, zero_n);
                let false_ = d.bool_false();
                d.bool_eq(lhs, false_)
            };
            let h_fv = d.fresh_fvar();
            let true_ = d.bool_true();
            let pf = d.bool_refl(true_);
            d.lam_fv(h_fv, hyp, pf)
        };

        let y_at_succ = |d: &mut IntDev<'_>, yp: ExprId| -> ExprId {
            // The premise ι-reduces to `ble (succ x') y' = false` and the goal
            // to `ble y' x' = true`, which is the induction hypothesis at `y'`.
            let syp = d.succ(yp);
            let hyp = {
                let lhs = d.ble(ssxp, syp);
                let false_ = d.bool_false();
                d.bool_eq(lhs, false_)
            };
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let pf = d.apply(ih, &[yp, h]);
            d.lam_fv(h_fv, hyp, pf)
        };

        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let per_y = d.induct(&motive_y, &y_at_zero, &|d, yp, _ih| y_at_succ(d, yp), y);
        d.lam_fv(y_fv, nat, per_y)
    };

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let stmt = motive(d, x);
    let proof = d.induct(&motive, &base, &step, x);
    let ty = d.pi_fv(x_fv, nat, stmt);
    let value = d.lam_fv(x_fv, nat, proof);
    d.declare_theorem(p.ble_flip_of_false, ty, value)
}

/// Admit `Rat.unskip_le : ∀ p q, Nat.ble q p = true → unskip p q = q` and
/// `Rat.unskip_gt : ∀ p q, Nat.ble p q = true → unskip p (succ q) = q`.
///
/// The two halves of what `unskip` does, split by which side of the deleted
/// index `q` falls on. Both are the same two-level induction as
/// [`declare_unskip_mat_skip`] and every case is ι.
///
/// `unskip_gt` is stated at `succ q` rather than as
/// `Nat.ble (succ p) q = true → unskip p q = Nat.pred q`, which is the form
/// the closed definition suggests. The `pred` form's successor step ends at
/// `succ (Nat.pred q') = q'` and needs `q' > 0` — a further inversion — where
/// this form's successor step IS the induction hypothesis.
fn declare_unskip_bounds(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    // unskip_le : ∀ p q, ble q p = true → unskip p q = q
    {
        let motive = |d: &mut IntDev<'_>, at: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let hyp = ble_true_ty(d, q, at);
            let lhs = runskip(d, p, at, q);
            let concl = NatOps::eq(d, lhs, q);
            let arr = d.arrow(hyp, concl);
            d.pi_fv(q_fv, nat, arr)
        };

        let base = |d: &mut IntDev<'_>| -> ExprId {
            let nat = d.nat_ty();
            let zero_n = d.zero();

            let motive_q = |d: &mut IntDev<'_>, q: ExprId| -> ExprId {
                let zero_n = d.zero();
                let hyp = ble_true_ty(d, q, zero_n);
                let lhs = runskip(d, p, zero_n, q);
                let concl = NatOps::eq(d, lhs, q);
                d.arrow(hyp, concl)
            };
            let q_at_zero = |d: &mut IntDev<'_>| -> ExprId {
                // `unskip 0 0 ≡ Nat.pred 0 ≡ 0`.
                let zero_n = d.zero();
                let hyp = ble_true_ty(d, zero_n, zero_n);
                let h_fv = d.fresh_fvar();
                let pf = NatOps::refl(d, zero_n);
                d.lam_fv(h_fv, hyp, pf)
            };
            let q_at_succ = |d: &mut IntDev<'_>, qp: ExprId| -> ExprId {
                // `ble (succ q') zero ≡ false`.
                let zero_n = d.zero();
                let sqp = d.succ(qp);
                let hyp = ble_true_ty(d, sqp, zero_n);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let lhs = runskip(d, p, zero_n, sqp);
                let target = NatOps::eq(d, lhs, sqp);
                let pf = d.false_true_elim(target, h);
                d.lam_fv(h_fv, hyp, pf)
            };
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let per_q = d.induct(&motive_q, &q_at_zero, &|d, qp, _ih| q_at_succ(d, qp), q);
            let _ = zero_n;
            d.lam_fv(q_fv, nat, per_q)
        };

        let step = |d: &mut IntDev<'_>, pp: ExprId, ih: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let spp = d.succ(pp);

            let motive_q = |d: &mut IntDev<'_>, q: ExprId| -> ExprId {
                let hyp = ble_true_ty(d, q, spp);
                let lhs = runskip(d, p, spp, q);
                let concl = NatOps::eq(d, lhs, q);
                d.arrow(hyp, concl)
            };
            let q_at_zero = |d: &mut IntDev<'_>| -> ExprId {
                // `unskip (succ p') 0 ≡ 0`.
                let zero_n = d.zero();
                let hyp = ble_true_ty(d, zero_n, spp);
                let h_fv = d.fresh_fvar();
                let pf = NatOps::refl(d, zero_n);
                d.lam_fv(h_fv, hyp, pf)
            };
            let q_at_succ = |d: &mut IntDev<'_>, qp: ExprId| -> ExprId {
                let sqp = d.succ(qp);
                let hyp = ble_true_ty(d, sqp, spp);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                // `ble (succ q') (succ p') ≡ ble q' p'`, the hypothesis `ih`
                // wants; the goal ι-reduces to `succ (unskip p' q') = succ q'`.
                let inner = runskip(d, p, pp, qp);
                let ih_at = d.apply(ih, &[qp, h]);
                let pf = NatOps::congr(d, inner, qp, ih_at, &|d, t| d.succ(t));
                d.lam_fv(h_fv, hyp, pf)
            };
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let per_q = d.induct(&motive_q, &q_at_zero, &|d, qp, _ih| q_at_succ(d, qp), q);
            d.lam_fv(q_fv, nat, per_q)
        };

        let p_fv = d.fresh_fvar();
        let at = d.kernel().fvar(p_fv);
        let stmt = motive(d, at);
        let proof = d.induct(&motive, &base, &step, at);
        let ty = d.pi_fv(p_fv, nat, stmt);
        let value = d.lam_fv(p_fv, nat, proof);
        d.declare_theorem(p.unskip_le, ty, value)?;
    }

    // unskip_gt : ∀ p q, ble p q = true → unskip p (succ q) = q
    {
        let motive = |d: &mut IntDev<'_>, at: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let hyp = ble_true_ty(d, at, q);
            let sq = d.succ(q);
            let lhs = runskip(d, p, at, sq);
            let concl = NatOps::eq(d, lhs, q);
            let arr = d.arrow(hyp, concl);
            d.pi_fv(q_fv, nat, arr)
        };

        let base = |d: &mut IntDev<'_>| -> ExprId {
            // `unskip 0 (succ q) ≡ Nat.pred (succ q) ≡ q`, hypothesis unused.
            let nat = d.nat_ty();
            let zero_n = d.zero();
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let hyp = ble_true_ty(d, zero_n, q);
            let h_fv = d.fresh_fvar();
            let pf = NatOps::refl(d, q);
            let with_h = d.lam_fv(h_fv, hyp, pf);
            d.lam_fv(q_fv, nat, with_h)
        };

        let step = |d: &mut IntDev<'_>, pp: ExprId, ih: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let spp = d.succ(pp);

            let motive_q = |d: &mut IntDev<'_>, q: ExprId| -> ExprId {
                let hyp = ble_true_ty(d, spp, q);
                let sq = d.succ(q);
                let lhs = runskip(d, p, spp, sq);
                let concl = NatOps::eq(d, lhs, q);
                d.arrow(hyp, concl)
            };
            let q_at_zero = |d: &mut IntDev<'_>| -> ExprId {
                // `ble (succ p') zero ≡ false`.
                let zero_n = d.zero();
                let hyp = ble_true_ty(d, spp, zero_n);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let one_n = d.succ(zero_n);
                let lhs = runskip(d, p, spp, one_n);
                let target = NatOps::eq(d, lhs, zero_n);
                let pf = d.false_true_elim(target, h);
                d.lam_fv(h_fv, hyp, pf)
            };
            let q_at_succ = |d: &mut IntDev<'_>, qp: ExprId| -> ExprId {
                let sqp = d.succ(qp);
                let hyp = ble_true_ty(d, spp, sqp);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                // Goal ι-reduces to `succ (unskip p' (succ q')) = succ q'`.
                let ssqp = d.succ(sqp);
                let _ = ssqp;
                let inner = {
                    let arg = d.succ(qp);
                    runskip(d, p, pp, arg)
                };
                let ih_at = d.apply(ih, &[qp, h]);
                let pf = NatOps::congr(d, inner, qp, ih_at, &|d, t| d.succ(t));
                d.lam_fv(h_fv, hyp, pf)
            };
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let per_q = d.induct(&motive_q, &q_at_zero, &|d, qp, _ih| q_at_succ(d, qp), q);
            d.lam_fv(q_fv, nat, per_q)
        };

        let p_fv = d.fresh_fvar();
        let at = d.kernel().fvar(p_fv);
        let stmt = motive(d, at);
        let proof = d.induct(&motive, &base, &step, at);
        let ty = d.pi_fv(p_fv, nat, stmt);
        let value = d.lam_fv(p_fv, nat, proof);
        d.declare_theorem(p.unskip_gt, ty, value)?;
    }

    let _ = nat;
    Ok(())
}

/// Admit the two DOUBLE minor exchanges, pointwise and at `det`.
///
/// [`declare_mat_minor_col_comm`] keeps the row indices fixed, which is what a
/// double expansion along ONE row needs. Relating the row-`0` expansion to the
/// row-`succ i` expansion moves the rows too — `(0, i)` on one side becomes
/// `(succ i, 0)` on the other — so these are separate statements and neither
/// follows from that one.
///
/// The row half is [`declare_mat_skip_comm`] at `a = 0`, whose premise
/// `Nat.ble 0 i = true` is `Eq.refl` since `ble zero _ ≡ true`. The column half
/// is the same lemma at `(a, b)`, in the `_lo` orientation as stated and in the
/// `_hi` orientation reversed — which is the whole difference between the two,
/// and why the summand identification needs a case split on `Nat.ble q k` and
/// nothing weaker.
fn declare_double_minor_comm(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    // The two pointwise statements share everything but their column terms.
    let mut pointwise = |name, hi: bool| -> Result<(), KernelError> {
        let a_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(a_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let hyp = ble_true_ty(d, u, v);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);

        let zero_n = d.zero();
        let si = d.succ(i);
        let sv = d.succ(v);

        let (lhs, rhs) = if hi {
            let left = {
                let outer = rmat_minor_of(d, p, mat, zero_n, sv);
                rmat_minor(d, p, outer, i, u, r, c)
            };
            let right = {
                let outer = rmat_minor_of(d, p, mat, si, u);
                rmat_minor(d, p, outer, zero_n, v, r, c)
            };
            (left, right)
        } else {
            let left = {
                let outer = rmat_minor_of(d, p, mat, zero_n, u);
                rmat_minor(d, p, outer, i, v, r, c)
            };
            let right = {
                let outer = rmat_minor_of(d, p, mat, si, sv);
                rmat_minor(d, p, outer, zero_n, u, r, c)
            };
            (left, right)
        };
        let stmt = req(d, lhs, rhs);

        // Both sides δβ-reduce to `A <row> <column>`; the row halves are
        // identical up to `matSkip_comm` at `a = 0` and only the columns differ.
        let row_from = {
            let inner = rmat_skip(d, p, i, r);
            rmat_skip(d, p, zero_n, inner)
        };
        let row_to = {
            let inner = rmat_skip(d, p, zero_n, r);
            rmat_skip(d, p, si, inner)
        };
        let (col_from, col_to) = if hi {
            let from = {
                let inner = rmat_skip(d, p, u, c);
                rmat_skip(d, p, sv, inner)
            };
            let to = {
                let inner = rmat_skip(d, p, v, c);
                rmat_skip(d, p, u, inner)
            };
            (from, to)
        } else {
            let from = {
                let inner = rmat_skip(d, p, v, c);
                rmat_skip(d, p, u, inner)
            };
            let to = {
                let inner = rmat_skip(d, p, u, c);
                rmat_skip(d, p, sv, inner)
            };
            (from, to)
        };

        let start = d.apply(mat, &[row_from, col_from]);
        let mid = d.apply(mat, &[row_to, col_from]);
        let end = d.apply(mat, &[row_to, col_to]);

        let row_step = {
            let true_ = d.bool_true();
            let h_zero = d.bool_refl(true_);
            let comm = d.lemma(p.mat_skip_comm, &[zero_n, i, h_zero]);
            let comm_at = d.apply(comm, &[r]);
            nat_eq_to_rat(d, row_from, row_to, comm_at, &|d, t| {
                d.apply(mat, &[t, col_from])
            })
        };
        let col_step = {
            // `matSkip_comm u v h c : matSkip u (matSkip v c) =
            //  matSkip (succ v) (matSkip u c)`; the `_lo` orientation reads it
            // forwards and the `_hi` one backwards.
            let comm = d.lemma(p.mat_skip_comm, &[u, v, h]);
            let comm_at = d.apply(comm, &[c]);
            let low = {
                let inner = rmat_skip(d, p, v, c);
                rmat_skip(d, p, u, inner)
            };
            let high = {
                let inner = rmat_skip(d, p, u, c);
                rmat_skip(d, p, sv, inner)
            };
            let forward = nat_eq_to_rat(d, low, high, comm_at, &|d, t| d.apply(mat, &[row_to, t]));
            let at_low = d.apply(mat, &[row_to, low]);
            let at_high = d.apply(mat, &[row_to, high]);
            if hi {
                super::ops::rsymm(d, at_low, at_high, forward)
            } else {
                forward
            }
        };

        let (_e, proof) = rchain(d, start, &[(mid, row_step), (end, col_step)]);

        let ty = {
            let over_c = d.pi_fv(c_fv, nat, stmt);
            let over_r = d.pi_fv(r_fv, nat, over_c);
            let with_h = d.pi_fv(h_fv, hyp, over_r);
            let over_v = d.pi_fv(v_fv, nat, with_h);
            let over_u = d.pi_fv(u_fv, nat, over_v);
            let over_i = d.pi_fv(i_fv, nat, over_u);
            d.pi_fv(a_fv, mty, over_i)
        };
        let value = {
            let over_c = d.lam_fv(c_fv, nat, proof);
            let over_r = d.lam_fv(r_fv, nat, over_c);
            let with_h = d.lam_fv(h_fv, hyp, over_r);
            let over_v = d.lam_fv(v_fv, nat, with_h);
            let over_u = d.lam_fv(u_fv, nat, over_v);
            let over_i = d.lam_fv(i_fv, nat, over_u);
            d.lam_fv(a_fv, mty, over_i)
        };
        d.declare_theorem(name, ty, value)
    };
    pointwise(p.mat_minor_double_comm_lo, false)?;
    pointwise(p.mat_minor_double_comm_hi, true)?;

    // The `det` lifts, each one `det_congr` applied to the pointwise identity.
    let mut at_det = |name, pointwise_name, hi: bool| -> Result<(), KernelError> {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let a_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(a_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let u_fv = d.fresh_fvar();
        let u = d.kernel().fvar(u_fv);
        let v_fv = d.fresh_fvar();
        let v = d.kernel().fvar(v_fv);
        let hyp = ble_true_ty(d, u, v);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let zero_n = d.zero();
        let si = d.succ(i);
        let sv = d.succ(v);
        let (left, right) = if hi {
            let l = {
                let outer = rmat_minor_of(d, p, mat, zero_n, sv);
                rmat_minor_of(d, p, outer, i, u)
            };
            let r = {
                let outer = rmat_minor_of(d, p, mat, si, u);
                rmat_minor_of(d, p, outer, zero_n, v)
            };
            (l, r)
        } else {
            let l = {
                let outer = rmat_minor_of(d, p, mat, zero_n, u);
                rmat_minor_of(d, p, outer, i, v)
            };
            let r = {
                let outer = rmat_minor_of(d, p, mat, si, sv);
                rmat_minor_of(d, p, outer, zero_n, u)
            };
            (l, r)
        };
        let lhs = rdet(d, p, left, m);
        let rhs = rdet(d, p, right, m);
        let stmt = req(d, lhs, rhs);

        let pw = d.const_app(pointwise_name, &[mat, i, u, v, h]);
        let proof = d.lemma(p.det_congr, &[m, left, right, pw]);

        let ty = {
            let with_h = d.pi_fv(h_fv, hyp, stmt);
            let over_v = d.pi_fv(v_fv, nat, with_h);
            let over_u = d.pi_fv(u_fv, nat, over_v);
            let over_i = d.pi_fv(i_fv, nat, over_u);
            let over_a = d.pi_fv(a_fv, mty, over_i);
            d.pi_fv(m_fv, nat, over_a)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, hyp, proof);
            let over_v = d.lam_fv(v_fv, nat, with_h);
            let over_u = d.lam_fv(u_fv, nat, over_v);
            let over_i = d.lam_fv(i_fv, nat, over_u);
            let over_a = d.lam_fv(a_fv, mty, over_i);
            d.lam_fv(m_fv, nat, over_a)
        };
        d.declare_theorem(name, ty, value)
    };
    at_det(p.det_double_comm_lo, p.mat_minor_double_comm_lo, false)?;
    at_det(p.det_double_comm_hi, p.mat_minor_double_comm_hi, true)
}

/// Admit `Rat.mul_perm4 : ∀ x a y b d,
/// x * (a * (y * (b * d))) = y * (b * (x * (a * d)))`.
///
/// The one product permutation the summand identification needs, and it is
/// needed on both sides of a `Rat.neg`: the two cofactor parametrisations
/// order the same five factors — two signs, two entries, one determinant —
/// differently, and the sign difference between them is a single `neg` that
/// [`super::ops`]'s `neg_mul` moves outside first. Six steps of
/// `mul_assoc`/`mul_comm`; this prelude has no `mul_left_comm`.
fn declare_mul_perm4(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.mul_perm4, 5, &|d, v| {
        let (x, a, y, b, dd) = (v[0], v[1], v[2], v[3], v[4]);

        let bd = rmul(d, b, dd);
        let ybd = rmul(d, y, bd);
        let xa = rmul(d, x, a);
        let ad = rmul(d, a, dd);

        let start = {
            let inner = rmul(d, a, ybd);
            rmul(d, x, inner)
        };
        let target = {
            let inner = rmul(d, x, ad);
            let outer = rmul(d, b, inner);
            rmul(d, y, outer)
        };
        let stmt = req(d, start, target);

        // 1. `x * (a * P) -> (x * a) * P`
        let m1 = rmul(d, xa, ybd);
        let s1 = {
            let pf = d.lemma(p.mul_assoc, &[x, a, ybd]);
            super::ops::rsymm(d, m1, start, pf)
        };
        // 2. commute the two halves
        let m2 = rmul(d, ybd, xa);
        let s2 = d.lemma(p.mul_comm, &[xa, ybd]);
        // 3. `(y * Q) * R -> y * (Q * R)`
        let bdxa = rmul(d, bd, xa);
        let m3 = rmul(d, y, bdxa);
        let s3 = d.lemma(p.mul_assoc, &[y, bd, xa]);
        // 4. inside: `(b * d) * (x * a) -> b * (d * (x * a))`
        let dxa = rmul(d, dd, xa);
        let m4 = {
            let inner = rmul(d, b, dxa);
            rmul(d, y, inner)
        };
        let s4 = {
            let pf = d.lemma(p.mul_assoc, &[b, dd, xa]);
            let b_dxa = rmul(d, b, dxa);
            rcongr(d, bdxa, b_dxa, pf, &|d, t| rmul(d, y, t))
        };
        // 5. inside: `d * (x * a) -> (x * a) * d`
        let xad = rmul(d, xa, dd);
        let m5 = {
            let inner = rmul(d, b, xad);
            rmul(d, y, inner)
        };
        let s5 = {
            let pf = d.lemma(p.mul_comm, &[dd, xa]);
            rcongr(d, dxa, xad, pf, &|d, t| {
                let inner = rmul(d, b, t);
                rmul(d, y, inner)
            })
        };
        // 6. inside: `(x * a) * d -> x * (a * d)`
        let s6 = {
            let pf = d.lemma(p.mul_assoc, &[x, a, dd]);
            let xad_target = rmul(d, x, ad);
            rcongr(d, xad, xad_target, pf, &|d, t| {
                let inner = rmul(d, b, t);
                rmul(d, y, inner)
            })
        };

        let (_e, proof) = rchain(
            d,
            start,
            &[
                (m1, s1),
                (m2, s2),
                (m3, s3),
                (m4, s4),
                (m5, s5),
                (target, s6),
            ],
        );
        (stmt, proof)
    })
}

/// Delta height for `Rat.laplaceSummand`: above [`DET_HEIGHT`],
/// [`UNSKIP_HEIGHT`] and `Rat.altSign`, all of which it unfolds to.
const SUMMAND_HEIGHT: u16 = 52;

/// `Rat.laplaceSummand A i m p q`.
#[allow(clippy::too_many_arguments)]
fn rsummand(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    i: ExprId,
    m: ExprId,
    col0: ExprId,
    coli: ExprId,
) -> ExprId {
    d.const_app(p.laplace_summand, &[mat, i, m, col0, coli])
}

/// The summand's non-diagonal branch, with the INNER column supplied
/// explicitly rather than computed as `unskip col0 coli`.
///
/// Every step of both identifications rewrites that inner column and nothing
/// else, so taking it as a parameter is what lets one `nat_eq_to_rat` move
/// both of its occurrences — the `Rat.altSign` index and the inner
/// `Rat.matMinor` — at once.
#[allow(clippy::too_many_arguments)]
fn summand_body_at(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    i: ExprId,
    m: ExprId,
    col0: ExprId,
    coli: ExprId,
    inner: ExprId,
) -> ExprId {
    let zero_n = d.zero();
    let si = d.succ(i);
    let entry_top = d.apply(mat, &[zero_n, col0]);
    let entry_row = d.apply(mat, &[si, coli]);
    let sign_col = ralt_sign(d, p, col0);
    let index = d.add(inner, i);
    let sign_inner = ralt_sign(d, p, index);
    let minor = {
        let outer = rmat_minor_of(d, p, mat, zero_n, col0);
        rmat_minor_of(d, p, outer, i, inner)
    };
    let sub = rdet(d, p, minor, m);
    let t1 = rmul(d, entry_row, sub);
    let t2 = rmul(d, sign_inner, t1);
    let t3 = rmul(d, entry_top, t2);
    rmul(d, sign_col, t3)
}

/// Admit `Rat.laplaceSummand`, the Laplace double-expansion summand, defined
/// on the WHOLE square.
///
/// ```text
/// laplaceSummand A i m p q :=
///   if Nat.beq p q then 0
///   else altSign p * (A 0 p * (altSign (unskip p q + i)
///          * (A (succ i) q * det (matMinor (matMinor A 0 p) i (unskip p q)) m)))
/// ```
///
/// `p` is the column the row-`0` expansion takes; `q` is the column the
/// row-`succ i` expansion takes. **Neither cofactor sum defines a value on the
/// diagonal** — each runs over a range one short — and `0` there is exactly
/// what lets [`declare_sum_range_mat_skip`] fill both ranges out to the full
/// square, after which the double sum is a plain rectangle and
/// `Rat.sumRange_swap` is the entire reindexing step (ADR-1155).
///
/// The `if` is a `Bool.rec` through `Rat.bool_select_rat`, the same device
/// `Rat.matId` uses.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
fn declare_laplace_summand(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let mat = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let p_fv = d.fresh_fvar();
    let col0 = d.kernel().fvar(p_fv);
    let q_fv = d.fresh_fvar();
    let coli = d.kernel().fvar(q_fv);

    let inner = runskip(d, p, col0, coli);
    let body = summand_body_at(d, p, mat, i, m, col0, coli, inner);
    let guard = d.beq(col0, coli);
    let zero_r = rzero(d, p);
    let selected = bool_select_rat(d, guard, zero_r, body);

    let value = {
        let over_q = d.lam_fv(q_fv, nat, selected);
        let over_p = d.lam_fv(p_fv, nat, over_q);
        let over_m = d.lam_fv(m_fv, nat, over_p);
        let over_i = d.lam_fv(i_fv, nat, over_m);
        d.lam_fv(a_fv, mty, over_i)
    };
    let ty = {
        let over_q = d.arrow(nat, carrier);
        let over_p = d.arrow(nat, over_q);
        let over_m = d.arrow(nat, over_p);
        let over_i = d.arrow(nat, over_m);
        d.arrow(mty, over_i)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.laplace_summand,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(SUMMAND_HEIGHT),
    })
}

/// Admit `Rat.laplaceSummand_rowZero : ∀ A i m p k,
/// laplaceSummand A i m p (matSkip p k) = altSign p * (A 0 p *
/// (altSign (k + i) * (A (succ i) (matSkip p k) *
/// det (matMinor (matMinor A 0 p) i k) m)))`.
///
/// The summand agrees with the row-`0`-then-row-`i` parametrisation's own
/// summand. **Two rewrites and no case split**: [`declare_beq_mat_skip`] shows
/// the guard is false along the reindexing — `matSkip p` misses `p` — and
/// [`declare_unskip_mat_skip`] recovers the inner column, in one step for both
/// of its occurrences.
fn declare_laplace_summand_row_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let mat = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let p_fv = d.fresh_fvar();
    let col0 = d.kernel().fvar(p_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    let coli = rmat_skip(d, p, col0, k);
    let start = rsummand(d, p, mat, i, m, col0, coli);
    let target = summand_body_at(d, p, mat, i, m, col0, coli, k);
    let stmt = req(d, start, target);

    // 1. the guard: `Nat.beq p (matSkip p k) = false`.
    let inner = runskip(d, p, col0, coli);
    let mid = summand_body_at(d, p, mat, i, m, col0, coli, inner);
    let s1 = {
        let guard = d.beq(col0, coli);
        let zero_r = rzero(d, p);
        let hguard = d.const_app(p.beq_mat_skip, &[col0, k]);
        select_rat_false(d, guard, zero_r, mid, hguard)
    };

    // 2. the inner column: `unskip p (matSkip p k) = k`, in both places.
    let s2 = {
        let pf = d.const_app(p.unskip_mat_skip, &[col0, k]);
        nat_eq_to_rat(d, inner, k, pf, &|d, t| {
            summand_body_at(d, p, mat, i, m, col0, coli, t)
        })
    };

    let (_e, proof) = rchain(d, start, &[(mid, s1), (target, s2)]);

    let ty = {
        let over_k = d.pi_fv(k_fv, nat, stmt);
        let over_p = d.pi_fv(p_fv, nat, over_k);
        let over_m = d.pi_fv(m_fv, nat, over_p);
        let over_i = d.pi_fv(i_fv, nat, over_m);
        d.pi_fv(a_fv, mty, over_i)
    };
    let value = {
        let over_k = d.lam_fv(k_fv, nat, proof);
        let over_p = d.lam_fv(p_fv, nat, over_k);
        let over_m = d.lam_fv(m_fv, nat, over_p);
        let over_i = d.lam_fv(i_fv, nat, over_m);
        d.lam_fv(a_fv, mty, over_i)
    };
    d.declare_theorem(p.laplace_summand_row_zero, ty, value)
}

/// Admit `Rat.laplaceSummand_rowI : ∀ A i m q k,
/// laplaceSummand A i m (matSkip q k) q = altSign (q + succ i) *
/// (A (succ i) q * (altSign k * (A 0 (matSkip q k) *
/// det (matMinor (matMinor A (succ i) q) 0 k) m)))`.
///
/// **The bulk of ADR-1155's named remainder.** The summand agrees with the
/// row-`succ i`-then-row-`0` parametrisation too — which is the whole content
/// of general-row expansion, since the two sums then differ only by the order
/// of summation.
///
/// Unlike [`declare_laplace_summand_row_zero`] this needs a case split on
/// `Nat.ble q k`, and the split is not cosmetic: it decides
///
/// - what `matSkip q k` is (`succ k` or `k`), hence which `Rat.altSign`
///   carries the extra `Rat.neg`;
/// - what `unskip (matSkip q k) q` is (`q` by [`declare_unskip_bounds`]'s
///   `unskip_le`, or `Nat.pred q` by its `unskip_gt`);
/// - and WHICH orientation of the double minor exchange applies —
///   `det_double_comm_hi` in one order and `det_double_comm_lo` in the other.
///
/// It is [`bool_cases_eq`] rather than [`bool_cases`]: the goal keeps its
/// `Rat.matSkip` and each branch is handed the hypothesis, because the two
/// branches take different lemmas rather than reducing one term two ways.
///
/// The `= false` branch case-splits again on `q`, since `Nat.pred q` is only
/// `q''` once `q` is exposed as `succ q''`. That second case costs nothing:
/// `Nat.ble zero k ≡ true`, so `q = 0` makes the branch hypothesis
/// `true = false`.
///
/// The final algebra is the same on both sides — five factors permuted by
/// [`declare_mul_perm4`] — with the branches differing only in where the
/// `Rat.neg` sits: outside on the `true` side (`Rat.neg_mul`), and absorbed by
/// [`declare_alt_sign_succ_add`] plus `Rat.neg_neg` on the `false` side.
fn declare_laplace_summand_row_i(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let mat = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let q_fv = d.fresh_fvar();
    let coli = d.kernel().fvar(q_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);

    // The statement, as a function of whatever `matSkip q k` turns out to be.
    // Both sides mention it, so ONE rewrite moves the whole goal.
    let goal_at = |d: &mut IntDev<'_>, col0: ExprId, q: ExprId| -> ExprId {
        let zero_n = d.zero();
        let si = d.succ(i);
        let lhs = rsummand(d, p, mat, i, m, col0, q);
        let entry_top = d.apply(mat, &[zero_n, col0]);
        let entry_row = d.apply(mat, &[si, q]);
        let sign_k = ralt_sign(d, p, k);
        let sign_q = {
            let index = d.add(q, si);
            ralt_sign(d, p, index)
        };
        let sub = {
            let outer = rmat_minor_of(d, p, mat, si, q);
            let minor = rmat_minor_of(d, p, outer, zero_n, k);
            rdet(d, p, minor, m)
        };
        let t1 = rmul(d, entry_top, sub);
        let t2 = rmul(d, sign_k, t1);
        let t3 = rmul(d, entry_row, t2);
        let rhs = rmul(d, sign_q, t3);
        req(d, lhs, rhs)
    };

    let skipped = rmat_skip(d, p, coli, k);
    let stmt = goal_at(d, skipped, coli);

    // --- the `Nat.ble q k = true` branch: `matSkip q k` is `succ k` ---------
    let at_true = {
        let cond = d.ble(coli, k);
        let true_ = d.bool_true();
        let hyp = d.bool_eq(cond, true_);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let sk = d.succ(k);
        let hsel = {
            let cond = d.ble(coli, k);
            select_nat_true(d, cond, sk, k, h)
        };

        // The goal with `succ k` in place of `matSkip q k`.
        let start = rsummand(d, p, mat, i, m, sk, coli);

        // 1. the guard, transported off `beq_matSkip_left`.
        let hguard = {
            let from = d.beq(skipped, coli);
            let to = d.beq(sk, coli);
            let moved = nat_eq_to_bool(d, skipped, sk, hsel, &|d, t| d.beq(t, coli));
            let flipped = d.bool_symm(from, to, moved);
            let base = d.const_app(p.beq_mat_skip_left, &[coli, k]);
            let false_ = d.bool_false();
            d.bool_trans(to, from, false_, flipped, base)
        };
        let inner = runskip(d, p, sk, coli);
        let mid1 = summand_body_at(d, p, mat, i, m, sk, coli, inner);
        let s1 = {
            let guard = d.beq(sk, coli);
            let zero_r = rzero(d, p);
            select_rat_false(d, guard, zero_r, mid1, hguard)
        };

        // 2. `unskip (succ k) q = q`, since `q ≤ k < succ k`.
        let mid2 = summand_body_at(d, p, mat, i, m, sk, coli, coli);
        let s2 = {
            let ble_succ = d.prelude().ble_succ_eq_true;
            let hble = d.const_app(ble_succ, &[coli, k, h]);
            let pf = d.const_app(p.unskip_le, &[sk, coli, hble]);
            nat_eq_to_rat(d, inner, coli, pf, &|d, t| {
                summand_body_at(d, p, mat, i, m, sk, coli, t)
            })
        };

        // 3. the double minor, in the `_hi` orientation.
        let zero_n = d.zero();
        let si = d.succ(i);
        let det_from = {
            let outer = rmat_minor_of(d, p, mat, zero_n, sk);
            let minor = rmat_minor_of(d, p, outer, i, coli);
            rdet(d, p, minor, m)
        };
        let det_to = {
            let outer = rmat_minor_of(d, p, mat, si, coli);
            let minor = rmat_minor_of(d, p, outer, zero_n, k);
            rdet(d, p, minor, m)
        };
        let sign_sk = ralt_sign(d, p, sk);
        let sign_k = ralt_sign(d, p, k);
        let entry_top = d.apply(mat, &[zero_n, sk]);
        let entry_row = d.apply(mat, &[si, coli]);
        let sign_qi = {
            let index = d.add(coli, i);
            ralt_sign(d, p, index)
        };
        let rebuild = |d: &mut IntDev<'_>, sub: ExprId| -> ExprId {
            let t1 = rmul(d, entry_row, sub);
            let t2 = rmul(d, sign_qi, t1);
            let t3 = rmul(d, entry_top, t2);
            rmul(d, sign_sk, t3)
        };
        let mid3 = rebuild(d, det_to);
        let s3 = {
            let pf = d.const_app(p.det_double_comm_hi, &[m, mat, i, coli, k, h]);
            rcongr(d, det_from, det_to, pf, &|d, t| {
                let t1 = rmul(d, entry_row, t);
                let t2 = rmul(d, sign_qi, t1);
                let t3 = rmul(d, entry_top, t2);
                rmul(d, sign_sk, t3)
            })
        };

        // 4. the algebra: `neg x * (a * (y * (b * D)))` against
        //    `neg y * (b * (x * (a * D)))`, one `mul_perm4` under one `neg`.
        let bundle = {
            let t1 = rmul(d, entry_row, det_to);
            rmul(d, sign_qi, t1)
        };
        let inner_prod = rmul(d, entry_top, bundle);
        let signed_prod = rmul(d, sign_k, inner_prod);
        let negged_left = rneg(d, signed_prod);
        let s4 = d.lemma(p.neg_mul, &[sign_k, inner_prod]);

        let tail = {
            let t1 = rmul(d, entry_top, det_to);
            let t2 = rmul(d, sign_k, t1);
            rmul(d, entry_row, t2)
        };
        let permuted = rmul(d, sign_qi, tail);
        let negged_right = rneg(d, permuted);
        let s5 = {
            let pf = d.lemma(
                p.mul_perm4,
                &[sign_k, entry_top, sign_qi, entry_row, det_to],
            );
            rcongr(d, signed_prod, permuted, pf, &|d, t| rneg(d, t))
        };

        let final_term = {
            let index = d.add(coli, si);
            let sign_q = ralt_sign(d, p, index);
            rmul(d, sign_q, tail)
        };
        let s6 = {
            let pf = d.lemma(p.neg_mul, &[sign_qi, tail]);
            super::ops::rsymm(d, final_term, negged_right, pf)
        };

        let (_e, at_succ_k) = rchain(
            d,
            start,
            &[
                (mid1, s1),
                (mid2, s2),
                (mid3, s3),
                (negged_left, s4),
                (negged_right, s5),
                (final_term, s6),
            ],
        );

        // Transport the whole goal back along `succ k = matSkip q k`.
        let flipped = NatOps::symm(d, skipped, sk, hsel);
        let moved = nat_rewrite_prop(d, sk, skipped, flipped, at_succ_k, &|d, t| {
            goal_at(d, t, coli)
        });
        d.lam_fv(h_fv, hyp, moved)
    };

    // --- the `Nat.ble q k = false` branch: `matSkip q k` is `k` -------------
    let at_false = {
        let cond = d.ble(coli, k);
        let false_ = d.bool_false();
        let hyp = d.bool_eq(cond, false_);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        // `Nat.pred q` is only `q''` once `q` is exposed as `succ q''`, so the
        // hypothesis has to travel under a case split on `q`.
        let motive_q = |d: &mut IntDev<'_>, q: ExprId| -> ExprId {
            let cond = d.ble(q, k);
            let false_ = d.bool_false();
            let hyp = d.bool_eq(cond, false_);
            let sq = rmat_skip(d, p, q, k);
            let concl = goal_at(d, sq, q);
            d.arrow(hyp, concl)
        };

        let q_at_zero = |d: &mut IntDev<'_>| -> ExprId {
            // `Nat.ble zero k ≡ true`, so the hypothesis is `true = false`.
            let zero_n = d.zero();
            let cond = d.ble(zero_n, k);
            let false_ = d.bool_false();
            let hyp = d.bool_eq(cond, false_);
            let hz_fv = d.fresh_fvar();
            let hz = d.kernel().fvar(hz_fv);
            let true_ = d.bool_true();
            let flipped = d.bool_symm(true_, false_, hz);
            let target = {
                let sq = rmat_skip(d, p, zero_n, k);
                goal_at(d, sq, zero_n)
            };
            let pf = d.false_true_elim(target, flipped);
            d.lam_fv(hz_fv, hyp, pf)
        };

        let q_at_succ = |d: &mut IntDev<'_>, qp: ExprId| -> ExprId {
            let sqp = d.succ(qp);
            let cond = d.ble(sqp, k);
            let false_ = d.bool_false();
            let hyp = d.bool_eq(cond, false_);
            let hs_fv = d.fresh_fvar();
            let hs = d.kernel().fvar(hs_fv);

            let skipped_q = rmat_skip(d, p, sqp, k);
            let hsel = {
                let cond = d.ble(sqp, k);
                let sk = d.succ(k);
                select_nat_false(d, cond, sk, k, hs)
            };
            // `ble k q'' = true`, the premise both `unskip_gt` and the `_lo`
            // double-minor exchange need.
            let hkq = d.const_app(p.ble_flip_of_false, &[qp, k, hs]);

            let start = rsummand(d, p, mat, i, m, k, sqp);

            // 1. the guard.
            let hguard = {
                let from = d.beq(skipped_q, sqp);
                let to = d.beq(k, sqp);
                let moved = nat_eq_to_bool(d, skipped_q, k, hsel, &|d, t| d.beq(t, sqp));
                let flipped = d.bool_symm(from, to, moved);
                let base = d.const_app(p.beq_mat_skip_left, &[sqp, k]);
                let false_ = d.bool_false();
                d.bool_trans(to, from, false_, flipped, base)
            };
            let inner = runskip(d, p, k, sqp);
            let mid1 = summand_body_at(d, p, mat, i, m, k, sqp, inner);
            let s1 = {
                let guard = d.beq(k, sqp);
                let zero_r = rzero(d, p);
                select_rat_false(d, guard, zero_r, mid1, hguard)
            };

            // 2. `unskip k (succ q'') = q''`, since `k ≤ q''`.
            let mid2 = summand_body_at(d, p, mat, i, m, k, sqp, qp);
            let s2 = {
                let pf = d.const_app(p.unskip_gt, &[k, qp, hkq]);
                nat_eq_to_rat(d, inner, qp, pf, &|d, t| {
                    summand_body_at(d, p, mat, i, m, k, sqp, t)
                })
            };

            // 3. the double minor, in the `_lo` orientation.
            let zero_n = d.zero();
            let si = d.succ(i);
            let det_from = {
                let outer = rmat_minor_of(d, p, mat, zero_n, k);
                let minor = rmat_minor_of(d, p, outer, i, qp);
                rdet(d, p, minor, m)
            };
            let det_to = {
                let outer = rmat_minor_of(d, p, mat, si, sqp);
                let minor = rmat_minor_of(d, p, outer, zero_n, k);
                rdet(d, p, minor, m)
            };
            let sign_k = ralt_sign(d, p, k);
            let entry_top = d.apply(mat, &[zero_n, k]);
            let entry_row = d.apply(mat, &[si, sqp]);
            let sign_qi = {
                let index = d.add(qp, i);
                ralt_sign(d, p, index)
            };
            let mid3 = {
                let t1 = rmul(d, entry_row, det_to);
                let t2 = rmul(d, sign_qi, t1);
                let t3 = rmul(d, entry_top, t2);
                rmul(d, sign_k, t3)
            };
            let s3 = {
                let pf = d.const_app(p.det_double_comm_lo, &[m, mat, i, k, qp, hkq]);
                rcongr(d, det_from, det_to, pf, &|d, t| {
                    let t1 = rmul(d, entry_row, t);
                    let t2 = rmul(d, sign_qi, t1);
                    let t3 = rmul(d, entry_top, t2);
                    rmul(d, sign_k, t3)
                })
            };

            // 4. the permutation; no `neg` on this side.
            let permuted = {
                let t1 = rmul(d, entry_top, det_to);
                let t2 = rmul(d, sign_k, t1);
                let t3 = rmul(d, entry_row, t2);
                rmul(d, sign_qi, t3)
            };
            let s4 = d.lemma(
                p.mul_perm4,
                &[sign_k, entry_top, sign_qi, entry_row, det_to],
            );

            // 5. `altSign (succ q'' + succ i) = altSign (q'' + i)`, which is
            //    `altSign_succ_add` under a `neg` followed by `neg_neg`.
            let sign_q = {
                let index = d.add(sqp, si);
                ralt_sign(d, p, index)
            };
            let hsign = {
                let shifted = {
                    let index = d.add(sqp, i);
                    ralt_sign(d, p, index)
                };
                let negged = rneg(d, sign_qi);
                let step = d.const_app(p.alt_sign_succ_add, &[qp, i]);
                let under_neg = rcongr(d, shifted, negged, step, &|d, t| rneg(d, t));
                let double_neg = rneg(d, negged);
                let collapse = d.lemma(p.neg_neg, &[sign_qi]);
                let (_e, pf) = rchain(d, sign_q, &[(double_neg, under_neg), (sign_qi, collapse)]);
                pf
            };
            let tail = {
                let t1 = rmul(d, entry_top, det_to);
                let t2 = rmul(d, sign_k, t1);
                rmul(d, entry_row, t2)
            };
            let final_term = rmul(d, sign_q, tail);
            let s5 = {
                let flipped = super::ops::rsymm(d, sign_q, sign_qi, hsign);
                rcongr(d, sign_qi, sign_q, flipped, &|d, t| rmul(d, t, tail))
            };

            let (_e, at_k) = rchain(
                d,
                start,
                &[
                    (mid1, s1),
                    (mid2, s2),
                    (mid3, s3),
                    (permuted, s4),
                    (final_term, s5),
                ],
            );

            let flipped = NatOps::symm(d, skipped_q, k, hsel);
            let moved =
                nat_rewrite_prop(d, k, skipped_q, flipped, at_k, &|d, t| goal_at(d, t, sqp));
            d.lam_fv(hs_fv, hyp, moved)
        };

        let per_q = d.induct(&motive_q, &q_at_zero, &|d, qp, _ih| q_at_succ(d, qp), coli);
        let applied = d.apply(per_q, &[h]);
        d.lam_fv(h_fv, hyp, applied)
    };

    let cond = d.ble(coli, k);
    let proof = bool_cases_eq(d, cond, stmt, at_true, at_false);

    let ty = {
        let over_k = d.pi_fv(k_fv, nat, stmt);
        let over_q = d.pi_fv(q_fv, nat, over_k);
        let over_m = d.pi_fv(m_fv, nat, over_q);
        let over_i = d.pi_fv(i_fv, nat, over_m);
        d.pi_fv(a_fv, mty, over_i)
    };
    let value = {
        let over_k = d.lam_fv(k_fv, nat, proof);
        let over_q = d.lam_fv(q_fv, nat, over_k);
        let over_m = d.lam_fv(m_fv, nat, over_q);
        let over_i = d.lam_fv(i_fv, nat, over_m);
        d.lam_fv(a_fv, mty, over_i)
    };
    d.declare_theorem(p.laplace_summand_row_i, ty, value)
}

/// Admit `Rat.laplaceSummand_diag : ∀ A i m p, laplaceSummand A i m p p = 0`.
///
/// The diagonal branch, one `Nat.beq_refl` away. It is what makes both
/// cofactor ranges fillable to the full square for free: adding the value at
/// the missing index adds `0`.
fn declare_laplace_summand_diag(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let mat = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let p_fv = d.fresh_fvar();
    let col = d.kernel().fvar(p_fv);

    let lhs = rsummand(d, p, mat, i, m, col, col);
    let zero_r = rzero(d, p);
    let stmt = req(d, lhs, zero_r);

    let inner = runskip(d, p, col, col);
    let body = summand_body_at(d, p, mat, i, m, col, col, inner);
    let guard = d.beq(col, col);
    let hguard = {
        let name = d.prelude().beq_refl;
        d.const_app(name, &[col])
    };
    let proof = select_rat_true(d, guard, zero_r, body, hguard);

    let ty = {
        let over_p = d.pi_fv(p_fv, nat, stmt);
        let over_m = d.pi_fv(m_fv, nat, over_p);
        let over_i = d.pi_fv(i_fv, nat, over_m);
        d.pi_fv(a_fv, mty, over_i)
    };
    let value = {
        let over_p = d.lam_fv(p_fv, nat, proof);
        let over_m = d.lam_fv(m_fv, nat, over_p);
        let over_i = d.lam_fv(i_fv, nat, over_m);
        d.lam_fv(a_fv, mty, over_i)
    };
    d.declare_theorem(p.laplace_summand_diag, ty, value)
}

/// `fun q => laplaceSummand A i m p q` — the summand's row at a fixed first
/// column, the function the row-`0` expansion's inner sum runs over.
fn summand_row_fn(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    i: ExprId,
    m: ExprId,
    col0: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let body = rsummand(d, p, mat, i, m, col0, q);
    d.lam_fv(q_fv, nat, body)
}

/// `fun p => laplaceSummand A i m p q` — the summand's COLUMN at a fixed
/// second index, the function the row-`i` expansion's inner sum runs over.
fn summand_col_fn(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    i: ExprId,
    m: ExprId,
    coli: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let p_fv = d.fresh_fvar();
    let col0 = d.kernel().fvar(p_fv);
    let body = rsummand(d, p, mat, i, m, col0, coli);
    d.lam_fv(p_fv, nat, body)
}

/// `fun q => altSign (q + i) * (A i q * det (matMinor A i q) m)` — the
/// summand of a cofactor expansion along row `i`.
pub(super) fn row_expansion_fn(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    i: ExprId,
    m: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let index = d.add(q, i);
    let sign = ralt_sign(d, p, index);
    let entry = d.apply(mat, &[i, q]);
    let minor = rmat_minor_of(d, p, mat, i, q);
    let sub = rdet(d, p, minor, m);
    let product = rmul(d, entry, sub);
    let body = rmul(d, sign, product);
    d.lam_fv(q_fv, nat, body)
}

/// From `hlt : Nat.Lt x (succ n)`, derive `Nat.ble x n = true`.
///
/// `Nat.Lt a b` is `Nat.Le (succ a) b`, so this is `le_of_succ_le_succ`
/// followed by `ble_eq_true_of_le` — the bridge from the bound
/// `Rat.sumRange_congr_lt` supplies to the premise
/// [`declare_sum_range_mat_skip`] wants.
fn ble_of_lt_succ(d: &mut IntDev<'_>, x: ExprId, n: ExprId, hlt: ExprId) -> ExprId {
    let le_of_succ = d.prelude().le_of_succ_le_succ;
    let le = d.const_app(le_of_succ, &[x, n, hlt]);
    let ble_of_le = d.prelude().ble_eq_true_of_le;
    d.const_app(ble_of_le, &[x, n, le])
}

/// `sumRange (fun k => f (matSkip j k)) n = sumRange f (succ n)`, given
/// `hble : Nat.ble j n = true` and `hdiag : f j = 0`.
///
/// [`declare_sum_range_mat_skip`] with the value at the missing index added
/// back — and it is `0`, so `Rat.add_zero` absorbs it. This is the step that
/// turns a cofactor sum over a range ONE SHORT into a sum over the full range,
/// on both sides, which is what makes the double sum a plain rectangle.
fn fill_range(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    f: ExprId,
    n: ExprId,
    j: ExprId,
    hble: ExprId,
    hdiag: ExprId,
) -> (ExprId, ExprId, ExprId) {
    let reindexed = skip_fn(d, p, f, j);
    let start = rsum_range(d, p, reindexed, n);
    let zero_r = rzero(d, p);

    let mid1 = radd(d, start, zero_r);
    let s1 = {
        let pf = d.lemma(p.add_zero, &[start]);
        super::ops::rsymm(d, mid1, start, pf)
    };
    let fj = d.apply(f, &[j]);
    let mid2 = radd(d, start, fj);
    let s2 = {
        let flipped = super::ops::rsymm(d, fj, zero_r, hdiag);
        rcongr(d, zero_r, fj, flipped, &|d, t| radd(d, start, t))
    };
    let sn = d.succ(n);
    let end = rsum_range(d, p, f, sn);
    let s3 = d.lemma(p.sum_range_mat_skip, &[n, f, j, hble]);

    let (_e, proof) = rchain(d, start, &[(mid1, s1), (mid2, s2), (end, s3)]);
    (start, end, proof)
}

/// Admit `Rat.det_row_expansion : ∀ m A i, Nat.ble i m = true →
/// det A (succ m) = sumRange (fun q => altSign (q + i) *
/// (A i q * det (matMinor A i q) m)) (succ m)` — **cofactor expansion along a
/// GENERAL row**.
///
/// The second of the four laws ADR-1120 named over [`declare_det`], and the
/// one ADR-1135 declined to size. `Rat.det_succ` is the `i = 0` case
/// definitionally, since `Nat.add` recurses on its right argument and
/// `add q 0 ≡ q`.
///
/// **One induction on the dimension, whose step splits on the row**, and no
/// row-swap ladder anywhere. The classical proof proves the row-`1` case and
/// walks a general row to the top by adjacent transpositions, each negating
/// the determinant, which costs row antisymmetry. ADR-1155 measured that none
/// of that is needed: the double sums obtained by expanding along row `0` then
/// each minor's row `i-1`, and along row `i` then each minor's row `0`, are
/// indexed by the SAME ordered pairs of distinct columns and agree TERMWISE,
/// for every `i` at once. So they are the two orders of summation of ONE
/// function on the square — [`declare_laplace_summand`] — and the reindexing
/// is `Rat.sumRange_swap`.
///
/// The step, at `m = succ m'` and `i = succ i'`:
///
/// 1. `det_succ` opens the outer expansion along row `0`.
/// 2. Under `Rat.sumRange_congr_lt`, the induction hypothesis expands each
///    minor along ITS row `i'`, two `Rat.mul_sumRange` pulls take the
///    cofactor's coefficients inside, and
///    [`declare_laplace_summand_row_zero`] identifies the result as the
///    summand along `matSkip p`.
/// 3. [`fill_range`] fills that inner range out to the whole square.
/// 4. `Rat.sumRange_swap` — the ENTIRE reindexing step.
/// 5. The same three moves on the other side, with
///    [`declare_laplace_summand_row_i`] and `det_succ` swapping roles.
///
/// The bound is `sumRange_congr_lt` rather than `sumRange_congr` because the
/// summand identity needs `Nat.ble p m' = true`, which only holds below the
/// bound; [`ble_of_lt_succ`] is the bridge.
fn declare_det_row_expansion(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let motive = |d: &mut IntDev<'_>, m: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let mty = mat_ty(d);
        let a_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(a_fv);
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hyp = ble_true_ty(d, i, m);
        let sm = d.succ(m);
        let lhs = rdet(d, p, mat, sm);
        let summand = row_expansion_fn(d, p, mat, i, m);
        let rhs = rsum_range(d, p, summand, sm);
        let eq = req(d, lhs, rhs);
        let arr = d.arrow(hyp, eq);
        let over_i = d.pi_fv(i_fv, nat, arr);
        d.pi_fv(a_fv, mty, over_i)
    };

    // At `i = 0` the goal IS `det_succ`: `Nat.add q 0 ≡ q`, so the two
    // statements are the same term.
    let at_row_zero =
        |d: &mut IntDev<'_>, mat: ExprId, m: ExprId| -> ExprId { d.lemma(p.det_succ, &[mat, m]) };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let nat = d.nat_ty();
        let mty = mat_ty(d);
        let a_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(a_fv);

        let motive_i = |d: &mut IntDev<'_>, i: ExprId| -> ExprId {
            let zero_n = d.zero();
            let hyp = ble_true_ty(d, i, zero_n);
            let one_n = d.succ(zero_n);
            let lhs = rdet(d, p, mat, one_n);
            let summand = row_expansion_fn(d, p, mat, i, zero_n);
            let rhs = rsum_range(d, p, summand, one_n);
            let eq = req(d, lhs, rhs);
            d.arrow(hyp, eq)
        };
        let i_at_zero = |d: &mut IntDev<'_>| -> ExprId {
            let zero_n = d.zero();
            let hyp = ble_true_ty(d, zero_n, zero_n);
            let h_fv = d.fresh_fvar();
            let pf = at_row_zero(d, mat, zero_n);
            d.lam_fv(h_fv, hyp, pf)
        };
        let i_at_succ = |d: &mut IntDev<'_>, ip: ExprId| -> ExprId {
            // `ble (succ i') zero ≡ false`.
            let zero_n = d.zero();
            let sip = d.succ(ip);
            let hyp = ble_true_ty(d, sip, zero_n);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let one_n = d.succ(zero_n);
            let lhs = rdet(d, p, mat, one_n);
            let summand = row_expansion_fn(d, p, mat, sip, zero_n);
            let rhs = rsum_range(d, p, summand, one_n);
            let target = req(d, lhs, rhs);
            let pf = d.false_true_elim(target, h);
            d.lam_fv(h_fv, hyp, pf)
        };
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let per_i = d.induct(&motive_i, &i_at_zero, &|d, ip, _ih| i_at_succ(d, ip), i);
        let over_i = d.lam_fv(i_fv, nat, per_i);
        d.lam_fv(a_fv, mty, over_i)
    };

    let step = |d: &mut IntDev<'_>, mp: ExprId, ih: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let mty = mat_ty(d);
        let a_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(a_fv);
        let smp = d.succ(mp);

        let motive_i = |d: &mut IntDev<'_>, i: ExprId| -> ExprId {
            let hyp = ble_true_ty(d, i, smp);
            let ssmp = d.succ(smp);
            let lhs = rdet(d, p, mat, ssmp);
            let summand = row_expansion_fn(d, p, mat, i, smp);
            let rhs = rsum_range(d, p, summand, ssmp);
            let eq = req(d, lhs, rhs);
            d.arrow(hyp, eq)
        };

        let i_at_zero = |d: &mut IntDev<'_>| -> ExprId {
            let zero_n = d.zero();
            let hyp = ble_true_ty(d, zero_n, smp);
            let h_fv = d.fresh_fvar();
            let pf = at_row_zero(d, mat, smp);
            d.lam_fv(h_fv, hyp, pf)
        };

        let i_at_succ = |d: &mut IntDev<'_>, ip: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let sip = d.succ(ip);
            let n1 = d.succ(mp);
            let n2 = d.succ(n1);
            let zero_n = d.zero();
            let hyp = ble_true_ty(d, sip, n1);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            // --- the row-0 side ---------------------------------------------
            let outer_fn = {
                // `fun p => altSign p * (A 0 p * det (matMinor A 0 p) n1)`,
                // `det_succ`'s own summand at `m := n1`.
                let q_fv = d.fresh_fvar();
                let col = d.kernel().fvar(q_fv);
                let sign = ralt_sign(d, p, col);
                let entry = d.apply(mat, &[zero_n, col]);
                let minor = rmat_minor_of(d, p, mat, zero_n, col);
                let sub = rdet(d, p, minor, n1);
                let product = rmul(d, entry, sub);
                let body = rmul(d, sign, product);
                d.lam_fv(q_fv, nat, body)
            };
            let filled_rows = {
                let q_fv = d.fresh_fvar();
                let col = d.kernel().fvar(q_fv);
                let row = summand_row_fn(d, p, mat, ip, mp, col);
                let body = rsum_range(d, p, row, n2);
                d.lam_fv(q_fv, nat, body)
            };

            let pointwise_rows = {
                let q_fv = d.fresh_fvar();
                let col = d.kernel().fvar(q_fv);
                let lt_ty = d.lt(col, n2);
                let hl_fv = d.fresh_fvar();
                let hl = d.kernel().fvar(hl_fv);
                let hble = ble_of_lt_succ(d, col, n1, hl);

                let sign = ralt_sign(d, p, col);
                let entry = d.apply(mat, &[zero_n, col]);
                let minor = rmat_minor_of(d, p, mat, zero_n, col);
                let sub = rdet(d, p, minor, n1);
                let start = {
                    let product = rmul(d, entry, sub);
                    rmul(d, sign, product)
                };

                // 1. the induction hypothesis expands the minor along ITS row `i'`.
                let inner_summand = row_expansion_fn(d, p, minor, ip, mp);
                let inner_sum = rsum_range(d, p, inner_summand, n1);
                let mid1 = {
                    let product = rmul(d, entry, inner_sum);
                    rmul(d, sign, product)
                };
                let s1 = {
                    let pf = d.apply(ih, &[minor, ip, h]);
                    rcongr(d, sub, inner_sum, pf, &|d, t| {
                        let product = rmul(d, entry, t);
                        rmul(d, sign, product)
                    })
                };

                // 2. two `mul_sumRange` pulls take the coefficients inside.
                let scaled_fn = {
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);
                    let at_c = d.apply(inner_summand, &[c]);
                    let body = rmul(d, entry, at_c);
                    d.lam_fv(c_fv, nat, body)
                };
                let scaled_sum = rsum_range(d, p, scaled_fn, n1);
                let mid2 = rmul(d, sign, scaled_sum);
                let s2 = {
                    let pf = d.lemma(p.mul_sum_range, &[entry, inner_summand, n1]);
                    let from = rmul(d, entry, inner_sum);
                    rcongr(d, from, scaled_sum, pf, &|d, t| rmul(d, sign, t))
                };
                let signed_fn = {
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);
                    let at_c = d.apply(scaled_fn, &[c]);
                    let body = rmul(d, sign, at_c);
                    d.lam_fv(c_fv, nat, body)
                };
                let mid3 = rsum_range(d, p, signed_fn, n1);
                let s3 = d.lemma(p.mul_sum_range, &[sign, scaled_fn, n1]);

                // 3. that summand IS the Laplace summand along `matSkip p`.
                let row = summand_row_fn(d, p, mat, ip, mp, col);
                let reindexed = skip_fn(d, p, row, col);
                let mid4 = rsum_range(d, p, reindexed, n1);
                let s4 = {
                    let pointwise = {
                        let c_fv = d.fresh_fvar();
                        let c = d.kernel().fvar(c_fv);
                        let skipped = rmat_skip(d, p, col, c);
                        let lhs = rsummand(d, p, mat, ip, mp, col, skipped);
                        let rhs = summand_body_at(d, p, mat, ip, mp, col, skipped, c);
                        let base = d.const_app(p.laplace_summand_row_zero, &[mat, ip, mp, col, c]);
                        let flipped = super::ops::rsymm(d, lhs, rhs, base);
                        d.lam_fv(c_fv, nat, flipped)
                    };
                    d.lemma(p.sum_range_congr, &[signed_fn, reindexed, n1, pointwise])
                };

                // 4. fill the inner range out to the whole square.
                let hdiag = d.const_app(p.laplace_summand_diag, &[mat, ip, mp, col]);
                let (_from, end, s5) = fill_range(d, p, row, n1, col, hble, hdiag);

                let (_e, pf) = rchain(
                    d,
                    start,
                    &[(mid1, s1), (mid2, s2), (mid3, s3), (mid4, s4), (end, s5)],
                );
                let with_h = d.lam_fv(hl_fv, lt_ty, pf);
                d.lam_fv(q_fv, nat, with_h)
            };

            // --- the row-`succ i'` side --------------------------------------
            let target_fn = row_expansion_fn(d, p, mat, sip, n1);
            let filled_cols = {
                let q_fv = d.fresh_fvar();
                let col = d.kernel().fvar(q_fv);
                let column = summand_col_fn(d, p, mat, ip, mp, col);
                let body = rsum_range(d, p, column, n2);
                d.lam_fv(q_fv, nat, body)
            };

            let pointwise_cols = {
                let q_fv = d.fresh_fvar();
                let col = d.kernel().fvar(q_fv);
                let lt_ty = d.lt(col, n2);
                let hl_fv = d.fresh_fvar();
                let hl = d.kernel().fvar(hl_fv);
                let hble = ble_of_lt_succ(d, col, n1, hl);

                let index = d.add(col, sip);
                let sign = ralt_sign(d, p, index);
                let entry = d.apply(mat, &[sip, col]);
                let minor = rmat_minor_of(d, p, mat, sip, col);
                let sub = rdet(d, p, minor, n1);
                let start = {
                    let product = rmul(d, entry, sub);
                    rmul(d, sign, product)
                };

                // 1. `det_succ` expands the minor along ITS row `0`.
                let inner_summand = {
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);
                    let inner_sign = ralt_sign(d, p, c);
                    let inner_entry = d.apply(minor, &[zero_n, c]);
                    let inner_minor = rmat_minor_of(d, p, minor, zero_n, c);
                    let inner_sub = rdet(d, p, inner_minor, mp);
                    let product = rmul(d, inner_entry, inner_sub);
                    let body = rmul(d, inner_sign, product);
                    d.lam_fv(c_fv, nat, body)
                };
                let inner_sum = rsum_range(d, p, inner_summand, n1);
                let mid1 = {
                    let product = rmul(d, entry, inner_sum);
                    rmul(d, sign, product)
                };
                let s1 = {
                    let pf = d.lemma(p.det_succ, &[minor, mp]);
                    rcongr(d, sub, inner_sum, pf, &|d, t| {
                        let product = rmul(d, entry, t);
                        rmul(d, sign, product)
                    })
                };

                // 2. the same two `mul_sumRange` pulls.
                let scaled_fn = {
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);
                    let at_c = d.apply(inner_summand, &[c]);
                    let body = rmul(d, entry, at_c);
                    d.lam_fv(c_fv, nat, body)
                };
                let scaled_sum = rsum_range(d, p, scaled_fn, n1);
                let mid2 = rmul(d, sign, scaled_sum);
                let s2 = {
                    let pf = d.lemma(p.mul_sum_range, &[entry, inner_summand, n1]);
                    let from = rmul(d, entry, inner_sum);
                    rcongr(d, from, scaled_sum, pf, &|d, t| rmul(d, sign, t))
                };
                let signed_fn = {
                    let c_fv = d.fresh_fvar();
                    let c = d.kernel().fvar(c_fv);
                    let at_c = d.apply(scaled_fn, &[c]);
                    let body = rmul(d, sign, at_c);
                    d.lam_fv(c_fv, nat, body)
                };
                let mid3 = rsum_range(d, p, signed_fn, n1);
                let s3 = d.lemma(p.mul_sum_range, &[sign, scaled_fn, n1]);

                // 3. that summand IS the Laplace summand along `matSkip q`.
                let column = summand_col_fn(d, p, mat, ip, mp, col);
                let reindexed = skip_fn(d, p, column, col);
                let mid4 = rsum_range(d, p, reindexed, n1);
                let s4 = {
                    let pointwise = {
                        let c_fv = d.fresh_fvar();
                        let c = d.kernel().fvar(c_fv);
                        let skipped = rmat_skip(d, p, col, c);
                        let lhs = rsummand(d, p, mat, ip, mp, skipped, col);
                        let rhs = {
                            let entry_top = d.apply(mat, &[zero_n, skipped]);
                            let inner_minor = {
                                let outer = rmat_minor_of(d, p, mat, sip, col);
                                rmat_minor_of(d, p, outer, zero_n, c)
                            };
                            let inner_sub = rdet(d, p, inner_minor, mp);
                            let sign_c = ralt_sign(d, p, c);
                            let t1 = rmul(d, entry_top, inner_sub);
                            let t2 = rmul(d, sign_c, t1);
                            let t3 = rmul(d, entry, t2);
                            rmul(d, sign, t3)
                        };
                        let base = d.const_app(p.laplace_summand_row_i, &[mat, ip, mp, col, c]);
                        let flipped = super::ops::rsymm(d, lhs, rhs, base);
                        d.lam_fv(c_fv, nat, flipped)
                    };
                    d.lemma(p.sum_range_congr, &[signed_fn, reindexed, n1, pointwise])
                };

                // 4. fill this inner range out too.
                let hdiag = d.const_app(p.laplace_summand_diag, &[mat, ip, mp, col]);
                let (_from, end, s5) = fill_range(d, p, column, n1, col, hble, hdiag);

                let (_e, pf) = rchain(
                    d,
                    start,
                    &[(mid1, s1), (mid2, s2), (mid3, s3), (mid4, s4), (end, s5)],
                );
                let with_h = d.lam_fv(hl_fv, lt_ty, pf);
                d.lam_fv(q_fv, nat, with_h)
            };

            // --- the two orders of summation --------------------------------
            let start = rdet(d, p, mat, n2);
            let l1 = rsum_range(d, p, outer_fn, n2);
            let s1 = d.lemma(p.det_succ, &[mat, n1]);

            let l2 = rsum_range(d, p, filled_rows, n2);
            let s2 = d.lemma(
                p.sum_range_congr_lt,
                &[outer_fn, filled_rows, n2, pointwise_rows],
            );

            let l3 = rsum_range(d, p, filled_cols, n2);
            let s3 = {
                let square = {
                    let p_fv = d.fresh_fvar();
                    let col0 = d.kernel().fvar(p_fv);
                    let row = summand_row_fn(d, p, mat, ip, mp, col0);
                    d.lam_fv(p_fv, nat, row)
                };
                d.lemma(p.sum_range_swap, &[square, n2, n2])
            };

            let target = rsum_range(d, p, target_fn, n2);
            let s4 = {
                let pf = d.lemma(
                    p.sum_range_congr_lt,
                    &[target_fn, filled_cols, n2, pointwise_cols],
                );
                super::ops::rsymm(d, target, l3, pf)
            };

            let (_e, pf) = rchain(d, start, &[(l1, s1), (l2, s2), (l3, s3), (target, s4)]);
            d.lam_fv(h_fv, hyp, pf)
        };

        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let per_i = d.induct(&motive_i, &i_at_zero, &|d, ip, _ih| i_at_succ(d, ip), i);
        let over_i = d.lam_fv(i_fv, nat, per_i);
        d.lam_fv(a_fv, mty, over_i)
    };

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let stmt = motive(d, m);
    let proof = d.induct(&motive, &base, &step, m);
    let ty = d.pi_fv(m_fv, nat, stmt);
    let value = d.lam_fv(m_fv, nat, proof);
    let _ = mty;
    d.declare_theorem(p.det_row_expansion, ty, value)
}

// --- transpose invariance (ADR-1210) ---------------------------------------

/// `fun c => altSign c * (M 0 c * det (matMinor M 0 c) m)` — the summand
/// `Rat.det_succ` unfolds `det M (succ m)` to, expansion along the FIRST ROW.
pub(super) fn row_zero_expansion_fn(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    m: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let zero_n = d.zero();
    let c_fv = d.fresh_fvar();
    let col = d.kernel().fvar(c_fv);
    let sign = ralt_sign(d, p, col);
    let entry = d.apply(mat, &[zero_n, col]);
    let minor = rmat_minor_of(d, p, mat, zero_n, col);
    let sub = rdet(d, p, minor, m);
    let product = rmul(d, entry, sub);
    let body = rmul(d, sign, product);
    d.lam_fv(c_fv, nat, body)
}

/// `fun r => altSign r * (M r 0 * det (matMinor M r 0) m)` — expansion along
/// the FIRST COLUMN, the summand [`declare_det_col_expansion`] proves equal to
/// `det M (succ m)`.
pub(super) fn col_zero_expansion_fn(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    m: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let zero_n = d.zero();
    let r_fv = d.fresh_fvar();
    let row = d.kernel().fvar(r_fv);
    let sign = ralt_sign(d, p, row);
    let entry = d.apply(mat, &[row, zero_n]);
    let minor = rmat_minor_of(d, p, mat, row, zero_n);
    let sub = rdet(d, p, minor, m);
    let product = rmul(d, entry, sub);
    let body = rmul(d, sign, product);
    d.lam_fv(r_fv, nat, body)
}

/// `Rat.matTranspose A`, partially applied — itself a `Nat → Nat → Rat`.
fn rmat_transpose_of(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId) -> ExprId {
    d.const_app(p.mat_transpose, &[a])
}

/// The `(c, p)` term of the ROW-`0`-then-COLUMN-`0` double expansion, exactly
/// as [`declare_det_col_expansion`]'s left-hand chain builds it: the outer
/// cofactor at column `succ c`, then the induction hypothesis expanding that
/// minor along ITS first column at row `p`.
fn l_term_body(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    m: ExprId,
    c: ExprId,
    row: ExprId,
) -> ExprId {
    let zero_n = d.zero();
    let sc = d.succ(c);
    let sign = ralt_sign(d, p, sc);
    let entry = d.apply(mat, &[zero_n, sc]);
    let minor = rmat_minor_of(d, p, mat, zero_n, sc);
    let inner = col_zero_expansion_fn(d, p, minor, m);
    let at_row = d.apply(inner, &[row]);
    let scaled = rmul(d, entry, at_row);
    rmul(d, sign, scaled)
}

/// The `(p, c)` term of the COLUMN-`0`-then-ROW-`0` double expansion — the
/// same square, summed in the other order.
fn r_term_body(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    m: ExprId,
    row: ExprId,
    c: ExprId,
) -> ExprId {
    let zero_n = d.zero();
    let sr = d.succ(row);
    let sign = ralt_sign(d, p, sr);
    let entry = d.apply(mat, &[sr, zero_n]);
    let minor = rmat_minor_of(d, p, mat, sr, zero_n);
    let inner = row_zero_expansion_fn(d, p, minor, m);
    let at_c = d.apply(inner, &[c]);
    let scaled = rmul(d, entry, at_c);
    rmul(d, sign, scaled)
}

/// Admit `Rat.matMinor_row_col_comm : ∀ A p q r c,
/// matMinor (matMinor A 0 (succ q)) p 0 r c =
/// matMinor (matMinor A (succ p) 0) 0 q r c` — POINTWISE, and
/// **unconditionally**.
///
/// The double-minor identification the column expansion needs, and the place
/// this route is genuinely cheaper than ADR-1185's. There, both expansions ran
/// along ROWS, so the two column deletions had to be ordered against each
/// other and [`declare_mat_skip_comm`]'s `Nat.ble a b = true` hypothesis was
/// unavoidable. Here one expansion deletes a row and the other a column, the
/// two exchanges happen on DIFFERENT axes, and neither constrains the other:
/// the whole content is [`declare_mat_skip_succ_succ`] once per axis, with no
/// hypothesis and no case split.
///
/// Both sides delta-beta-iota-reduce to an application of `A`, using
/// `Nat.ble zero x ≡ true` (so `matSkip 0 x ≡ succ x`) on each side.
fn declare_mat_minor_row_col_comm(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let mat = d.kernel().fvar(a_fv);
    let p_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(p_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let zero_n = d.zero();
    let sq = d.succ(q);
    let spp = d.succ(pp);

    let left_outer = rmat_minor_of(d, p, mat, zero_n, sq);
    let lhs = rmat_minor(d, p, left_outer, pp, zero_n, r, c);
    let right_outer = rmat_minor_of(d, p, mat, spp, zero_n);
    let rhs = rmat_minor(d, p, right_outer, zero_n, q, r, c);
    let stmt = req(d, lhs, rhs);

    // `matSkip 0 (matSkip p r) ≡ succ (matSkip p r)`, and likewise on the
    // column axis, so the two reduced sides differ in exactly two indices.
    let row_left = {
        let inner = rmat_skip(d, p, pp, r);
        d.succ(inner)
    };
    let row_right = {
        let sr = d.succ(r);
        rmat_skip(d, p, spp, sr)
    };
    let col_left = {
        let sc = d.succ(c);
        rmat_skip(d, p, sq, sc)
    };
    let col_right = {
        let inner = rmat_skip(d, p, q, c);
        d.succ(inner)
    };

    let start = d.apply(mat, &[row_left, col_left]);
    let mid = d.apply(mat, &[row_left, col_right]);
    let end = d.apply(mat, &[row_right, col_right]);

    let s1 = {
        let h = d.lemma(p.mat_skip_succ_succ, &[q, c]);
        nat_eq_to_rat(d, col_left, col_right, h, &|d, t| {
            d.apply(mat, &[row_left, t])
        })
    };
    let s2 = {
        let h = d.lemma(p.mat_skip_succ_succ, &[pp, r]);
        let flipped = d.symm(row_right, row_left, h);
        nat_eq_to_rat(d, row_left, row_right, flipped, &|d, t| {
            d.apply(mat, &[t, col_right])
        })
    };
    let (_e, proof) = rchain(d, start, &[(mid, s1), (end, s2)]);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_r = d.pi_fv(r_fv, nat, over_c);
        let over_q = d.pi_fv(q_fv, nat, over_r);
        let over_p = d.pi_fv(p_fv, nat, over_q);
        d.pi_fv(a_fv, mty, over_p)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_r = d.lam_fv(r_fv, nat, over_c);
        let over_q = d.lam_fv(q_fv, nat, over_r);
        let over_p = d.lam_fv(p_fv, nat, over_q);
        d.lam_fv(a_fv, mty, over_p)
    };
    d.declare_theorem(p.mat_minor_row_col_comm, ty, value)
}

/// Admit `Rat.det_minor_row_col_comm : ∀ m A p q,
/// det (matMinor (matMinor A 0 (succ q)) p 0) m =
/// det (matMinor (matMinor A (succ p) 0) 0 q) m`.
///
/// [`declare_mat_minor_row_col_comm`] carried through [`declare_det_congr`] —
/// the only route a pointwise matrix identity has to a `det` in a kernel with
/// no `funext`, exactly as [`declare_det_minor_col_comm`] does for the
/// same-axis exchange.
fn declare_det_minor_row_col_comm(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let a_fv = d.fresh_fvar();
    let mat = d.kernel().fvar(a_fv);
    let p_fv = d.fresh_fvar();
    let pp = d.kernel().fvar(p_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let zero_n = d.zero();
    let sq = d.succ(q);
    let spp = d.succ(pp);

    let left = {
        let outer = rmat_minor_of(d, p, mat, zero_n, sq);
        rmat_minor_of(d, p, outer, pp, zero_n)
    };
    let right = {
        let outer = rmat_minor_of(d, p, mat, spp, zero_n);
        rmat_minor_of(d, p, outer, zero_n, q)
    };
    let lhs = rdet(d, p, left, m);
    let rhs = rdet(d, p, right, m);
    let stmt = req(d, lhs, rhs);

    let pointwise = d.const_app(p.mat_minor_row_col_comm, &[mat, pp, q]);
    let proof = d.lemma(p.det_congr, &[m, left, right, pointwise]);

    let ty = {
        let over_q = d.pi_fv(q_fv, nat, stmt);
        let over_p = d.pi_fv(p_fv, nat, over_q);
        let over_a = d.pi_fv(a_fv, mty, over_p);
        d.pi_fv(m_fv, nat, over_a)
    };
    let value = {
        let over_q = d.lam_fv(q_fv, nat, proof);
        let over_p = d.lam_fv(p_fv, nat, over_q);
        let over_a = d.lam_fv(a_fv, mty, over_p);
        d.lam_fv(m_fv, nat, over_a)
    };
    d.declare_theorem(p.det_minor_row_col_comm, ty, value)
}

/// `l_term_body c p = r_term_body p c` — the termwise agreement of the two
/// double expansions, at every `(c, p)` and with no bound at all.
///
/// Eight moves: [`declare_det_minor_row_col_comm`] exchanges the double minor,
/// `Rat.mul_perm4` moves the two cofactor coefficients past each other, and the
/// remaining six carry the single `Rat.neg` from `altSign (succ c)` over to
/// `altSign (succ p)` through `neg_mul`/`mul_neg`. The two `altSign_succ`
/// rewrites are written out rather than left to `Eq.refl`, so a change in
/// `Rat.altSign`'s shape would fail here loudly instead of silently.
fn l_eq_r_term(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    m: ExprId,
    c: ExprId,
    row: ExprId,
) -> ExprId {
    let zero_n = d.zero();
    let sc = d.succ(c);
    let srow = d.succ(row);

    let sign_c = ralt_sign(d, p, sc);
    let sign_row = ralt_sign(d, p, row);
    let sign_srow = ralt_sign(d, p, srow);
    let sign_cc = ralt_sign(d, p, c);
    let neg_sign_cc = rneg(d, sign_cc);
    let neg_sign_row = rneg(d, sign_row);

    let entry_top = d.apply(mat, &[zero_n, sc]);
    let minor_l = rmat_minor_of(d, p, mat, zero_n, sc);
    let entry_left = d.apply(minor_l, &[row, zero_n]);
    let double_l = rmat_minor_of(d, p, minor_l, row, zero_n);
    let det_l = rdet(d, p, double_l, m);

    let minor_r = rmat_minor_of(d, p, mat, srow, zero_n);
    let double_r = rmat_minor_of(d, p, minor_r, zero_n, c);
    let det_r = rdet(d, p, double_r, m);

    let start = {
        let inner = rmul(d, entry_left, det_l);
        let signed = rmul(d, sign_row, inner);
        let scaled = rmul(d, entry_top, signed);
        rmul(d, sign_c, scaled)
    };

    // 1. the two double minors are the same submatrix.
    let t1 = {
        let inner = rmul(d, entry_left, det_r);
        let signed = rmul(d, sign_row, inner);
        let scaled = rmul(d, entry_top, signed);
        rmul(d, sign_c, scaled)
    };
    let s1 = {
        let h = d.const_app(p.det_minor_row_col_comm, &[m, mat, row, c]);
        rcongr(d, det_l, det_r, h, &|d, t| {
            let inner = rmul(d, entry_left, t);
            let signed = rmul(d, sign_row, inner);
            let scaled = rmul(d, entry_top, signed);
            rmul(d, sign_c, scaled)
        })
    };

    // 2. `x*(a*(y*(b*d))) = y*(b*(x*(a*d)))` swaps the two cofactor
    //    coefficients, which is the whole reindexing at the term level.
    let w = rmul(d, entry_top, det_r);
    let t2 = {
        let inner = rmul(d, sign_c, w);
        let outer = rmul(d, entry_left, inner);
        rmul(d, sign_row, outer)
    };
    let s2 = d.lemma(
        p.mul_perm4,
        &[sign_c, entry_top, sign_row, entry_left, det_r],
    );

    // 3. `altSign (succ c) = neg (altSign c)`.
    let t3 = {
        let inner = rmul(d, neg_sign_cc, w);
        let outer = rmul(d, entry_left, inner);
        rmul(d, sign_row, outer)
    };
    let s3 = {
        let h = d.lemma(p.alt_sign_succ, &[c]);
        rcongr(d, sign_c, neg_sign_cc, h, &|d, t| {
            let inner = rmul(d, t, w);
            let outer = rmul(d, entry_left, inner);
            rmul(d, sign_row, outer)
        })
    };

    // 4-7. carry the `neg` out to the front and back down onto `altSign p`.
    let z = rmul(d, sign_cc, w);
    let neg_z = rneg(d, z);
    let t4 = {
        let outer = rmul(d, entry_left, neg_z);
        rmul(d, sign_row, outer)
    };
    let s4 = {
        let h = d.lemma(p.neg_mul, &[sign_cc, w]);
        let from = rmul(d, neg_sign_cc, w);
        rcongr(d, from, neg_z, h, &|d, t| {
            let outer = rmul(d, entry_left, t);
            rmul(d, sign_row, outer)
        })
    };

    let ez = rmul(d, entry_left, z);
    let neg_ez = rneg(d, ez);
    let t5 = rmul(d, sign_row, neg_ez);
    let s5 = {
        let h = d.lemma(p.mul_neg, &[entry_left, z]);
        let from = rmul(d, entry_left, neg_z);
        rcongr(d, from, neg_ez, h, &|d, t| rmul(d, sign_row, t))
    };

    let pez = rmul(d, sign_row, ez);
    let t6 = rneg(d, pez);
    let s6 = d.lemma(p.mul_neg, &[sign_row, ez]);

    let t7 = rmul(d, neg_sign_row, ez);
    let s7 = {
        let h = d.lemma(p.neg_mul, &[sign_row, ez]);
        super::ops::rsymm(d, t7, t6, h)
    };

    // 8. `neg (altSign p) = altSign (succ p)`.
    let end = r_term_body(d, p, mat, m, row, c);
    let s8 = {
        let h = d.lemma(p.alt_sign_succ, &[row]);
        let flipped = super::ops::rsymm(d, sign_srow, neg_sign_row, h);
        rcongr(d, neg_sign_row, sign_srow, flipped, &|d, t| rmul(d, t, ez))
    };

    let (_e, proof) = rchain(
        d,
        start,
        &[
            (t1, s1),
            (t2, s2),
            (t3, s3),
            (t4, s4),
            (t5, s5),
            (t6, s6),
            (t7, s7),
            (end, s8),
        ],
    );
    proof
}

/// Admit `Rat.det_col_expansion : ∀ m A, det A (succ m) =
/// sumRange (fun p => altSign p * (A p 0 * det (matMinor A p 0) m)) (succ m)` —
/// **cofactor expansion along the first COLUMN**.
///
/// The crux of transpose invariance, and it does NOT come from
/// [`declare_det_row_expansion`]. Each column summand is precisely the `c = 0`
/// slice of the row-`p` expansion, so the row law constrains each summand's
/// SIBLINGS and never the column sum; ADR-1210 §9 measures that. What IS reused
/// is the INDEX and RANGE layer ADR-1155 landed, not ADR-1185's summand layer —
/// there is no `Rat.laplaceSummand`, no `Rat.unskip`, no `Nat.beq` diagonal
/// guard and no `Rat.sumRange_congr_lt` anywhere below.
///
/// One induction on the dimension, with the matrix under the motive:
///
/// - **Base.** `det A 1` and the column sum at bound `1` are the SAME term:
///   both reduce to `zero + altSign 0 * (A 0 0 * det (matMinor A 0 0) 0)`.
///   `Eq.refl`.
/// - **Step,** at `m = succ m'`. `det_succ` opens the row-`0` expansion;
///   [`declare_sum_range_peel_head`] peels the index-`0` summand off each side,
///   and **the two heads are the same term**, so nothing has to be proved about
///   them. Under the tails, the induction hypothesis (left) and `det_succ`
///   (right) expand each minor one more step, and two `Rat.mul_sumRange` pulls
///   take the cofactor coefficients inside. What is left is one rectangle
///   summed in the two orders, so `Rat.sumRange_swap` is the entire reindexing
///   and [`l_eq_r_term`] is the termwise agreement.
///
/// The head split is what replaces ADR-1185's diagonal guard: there both
/// expansions ran over the same index space and the `p = q` cell had to be
/// shown to vanish; here the surviving row index and the surviving column index
/// are independent, and the only cell needing separate treatment is the one
/// both peels remove.
fn declare_det_col_expansion(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let motive = |d: &mut IntDev<'_>, m: ExprId| -> ExprId {
        let mty = mat_ty(d);
        let a_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(a_fv);
        let sm = d.succ(m);
        let lhs = rdet(d, p, mat, sm);
        let summand = col_zero_expansion_fn(d, p, mat, m);
        let rhs = rsum_range(d, p, summand, sm);
        let eq = req(d, lhs, rhs);
        d.pi_fv(a_fv, mty, eq)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let mty = mat_ty(d);
        let a_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(a_fv);
        let zero_n = d.zero();
        let one_n = d.succ(zero_n);
        let lhs = rdet(d, p, mat, one_n);
        let refl = rrefl(d, lhs);
        d.lam_fv(a_fv, mty, refl)
    };

    let step = |d: &mut IntDev<'_>, mp: ExprId, ih: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let mty = mat_ty(d);
        let a_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(a_fv);
        let zero_n = d.zero();
        let n1 = d.succ(mp);
        let n2 = d.succ(n1);

        let row_fn = row_zero_expansion_fn(d, p, mat, n1);
        let col_fn = col_zero_expansion_fn(d, p, mat, n1);
        let head = d.apply(row_fn, &[zero_n]);

        let l_shift = shift_fn(d, row_fn);
        let r_shift = shift_fn(d, col_fn);

        // `fun c => sumRange (fun p => L c p) n1`.
        let l_double = {
            let c_fv = d.fresh_fvar();
            let col = d.kernel().fvar(c_fv);
            let inner = {
                let r_fv = d.fresh_fvar();
                let row = d.kernel().fvar(r_fv);
                let body = l_term_body(d, p, mat, mp, col, row);
                d.lam_fv(r_fv, nat, body)
            };
            let body = rsum_range(d, p, inner, n1);
            d.lam_fv(c_fv, nat, body)
        };
        // `fun c p => L c p`, the square `sumRange_swap` transposes.
        let square = {
            let c_fv = d.fresh_fvar();
            let col = d.kernel().fvar(c_fv);
            let r_fv = d.fresh_fvar();
            let row = d.kernel().fvar(r_fv);
            let body = l_term_body(d, p, mat, mp, col, row);
            let inner = d.lam_fv(r_fv, nat, body);
            d.lam_fv(c_fv, nat, inner)
        };
        // `fun p => sumRange (fun c => L c p) n1`, the same square by rows.
        let l_swapped = {
            let r_fv = d.fresh_fvar();
            let row = d.kernel().fvar(r_fv);
            let inner = {
                let c_fv = d.fresh_fvar();
                let col = d.kernel().fvar(c_fv);
                let body = l_term_body(d, p, mat, mp, col, row);
                d.lam_fv(c_fv, nat, body)
            };
            let body = rsum_range(d, p, inner, n1);
            d.lam_fv(r_fv, nat, body)
        };
        // `fun p => sumRange (fun c => R p c) n1`.
        let r_double = {
            let r_fv = d.fresh_fvar();
            let row = d.kernel().fvar(r_fv);
            let inner = {
                let c_fv = d.fresh_fvar();
                let col = d.kernel().fvar(c_fv);
                let body = r_term_body(d, p, mat, mp, row, col);
                d.lam_fv(c_fv, nat, body)
            };
            let body = rsum_range(d, p, inner, n1);
            d.lam_fv(r_fv, nat, body)
        };

        // --- the row-0 tail: the induction hypothesis, twice pulled in -------
        let pointwise_l = {
            let c_fv = d.fresh_fvar();
            let col = d.kernel().fvar(c_fv);
            let sc = d.succ(col);
            let sign = ralt_sign(d, p, sc);
            let entry = d.apply(mat, &[zero_n, sc]);
            let minor = rmat_minor_of(d, p, mat, zero_n, sc);
            let sub = rdet(d, p, minor, n1);
            let start = {
                let product = rmul(d, entry, sub);
                rmul(d, sign, product)
            };

            let inner_fn = col_zero_expansion_fn(d, p, minor, mp);
            let inner_sum = rsum_range(d, p, inner_fn, n1);
            let mid1 = {
                let product = rmul(d, entry, inner_sum);
                rmul(d, sign, product)
            };
            let s1 = {
                let pf = d.apply(ih, &[minor]);
                rcongr(d, sub, inner_sum, pf, &|d, t| {
                    let product = rmul(d, entry, t);
                    rmul(d, sign, product)
                })
            };

            let scaled_fn = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let at_k = d.apply(inner_fn, &[k]);
                let body = rmul(d, entry, at_k);
                d.lam_fv(k_fv, nat, body)
            };
            let scaled_sum = rsum_range(d, p, scaled_fn, n1);
            let mid2 = rmul(d, sign, scaled_sum);
            let s2 = {
                let pf = d.lemma(p.mul_sum_range, &[entry, inner_fn, n1]);
                let from = rmul(d, entry, inner_sum);
                rcongr(d, from, scaled_sum, pf, &|d, t| rmul(d, sign, t))
            };

            let signed_fn = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let body = l_term_body(d, p, mat, mp, col, k);
                d.lam_fv(k_fv, nat, body)
            };
            let end = rsum_range(d, p, signed_fn, n1);
            let s3 = d.lemma(p.mul_sum_range, &[sign, scaled_fn, n1]);

            let (_e, pf) = rchain(d, start, &[(mid1, s1), (mid2, s2), (end, s3)]);
            d.lam_fv(c_fv, nat, pf)
        };

        // --- the column-0 tail: `det_succ`, twice pulled in ------------------
        let pointwise_r = {
            let r_fv = d.fresh_fvar();
            let row = d.kernel().fvar(r_fv);
            let sr = d.succ(row);
            let sign = ralt_sign(d, p, sr);
            let entry = d.apply(mat, &[sr, zero_n]);
            let minor = rmat_minor_of(d, p, mat, sr, zero_n);
            let sub = rdet(d, p, minor, n1);
            let start = {
                let product = rmul(d, entry, sub);
                rmul(d, sign, product)
            };

            let inner_fn = row_zero_expansion_fn(d, p, minor, mp);
            let inner_sum = rsum_range(d, p, inner_fn, n1);
            let mid1 = {
                let product = rmul(d, entry, inner_sum);
                rmul(d, sign, product)
            };
            let s1 = {
                let pf = d.lemma(p.det_succ, &[minor, mp]);
                rcongr(d, sub, inner_sum, pf, &|d, t| {
                    let product = rmul(d, entry, t);
                    rmul(d, sign, product)
                })
            };

            let scaled_fn = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let at_k = d.apply(inner_fn, &[k]);
                let body = rmul(d, entry, at_k);
                d.lam_fv(k_fv, nat, body)
            };
            let scaled_sum = rsum_range(d, p, scaled_fn, n1);
            let mid2 = rmul(d, sign, scaled_sum);
            let s2 = {
                let pf = d.lemma(p.mul_sum_range, &[entry, inner_fn, n1]);
                let from = rmul(d, entry, inner_sum);
                rcongr(d, from, scaled_sum, pf, &|d, t| rmul(d, sign, t))
            };

            let signed_fn = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let body = r_term_body(d, p, mat, mp, row, k);
                d.lam_fv(k_fv, nat, body)
            };
            let end = rsum_range(d, p, signed_fn, n1);
            let s3 = d.lemma(p.mul_sum_range, &[sign, scaled_fn, n1]);

            let (_e, pf) = rchain(d, start, &[(mid1, s1), (mid2, s2), (end, s3)]);
            d.lam_fv(r_fv, nat, pf)
        };

        // --- the two orders of summation, termwise ---------------------------
        let pointwise_swap = {
            let r_fv = d.fresh_fvar();
            let row = d.kernel().fvar(r_fv);
            let l_at_row = {
                let c_fv = d.fresh_fvar();
                let col = d.kernel().fvar(c_fv);
                let body = l_term_body(d, p, mat, mp, col, row);
                d.lam_fv(c_fv, nat, body)
            };
            let r_at_row = {
                let c_fv = d.fresh_fvar();
                let col = d.kernel().fvar(c_fv);
                let body = r_term_body(d, p, mat, mp, row, col);
                d.lam_fv(c_fv, nat, body)
            };
            let termwise = {
                let c_fv = d.fresh_fvar();
                let col = d.kernel().fvar(c_fv);
                let body = l_eq_r_term(d, p, mat, mp, col, row);
                d.lam_fv(c_fv, nat, body)
            };
            let pf = d.lemma(p.sum_range_congr, &[l_at_row, r_at_row, n1, termwise]);
            d.lam_fv(r_fv, nat, pf)
        };

        let start = rdet(d, p, mat, n2);
        let l1 = rsum_range(d, p, row_fn, n2);
        let s1 = d.lemma(p.det_succ, &[mat, n1]);

        let l2 = {
            let tail = rsum_range(d, p, l_shift, n1);
            radd(d, head, tail)
        };
        let s2 = d.lemma(p.sum_range_peel_head, &[row_fn, n1]);

        let l3 = {
            let tail = rsum_range(d, p, l_double, n1);
            radd(d, head, tail)
        };
        let s3 = {
            let pf = d.lemma(p.sum_range_congr, &[l_shift, l_double, n1, pointwise_l]);
            let from = rsum_range(d, p, l_shift, n1);
            let to = rsum_range(d, p, l_double, n1);
            rcongr(d, from, to, pf, &|d, t| radd(d, head, t))
        };

        let l4 = {
            let tail = rsum_range(d, p, l_swapped, n1);
            radd(d, head, tail)
        };
        let s4 = {
            let pf = d.lemma(p.sum_range_swap, &[square, n1, n1]);
            let from = rsum_range(d, p, l_double, n1);
            let to = rsum_range(d, p, l_swapped, n1);
            rcongr(d, from, to, pf, &|d, t| radd(d, head, t))
        };

        let l5 = {
            let tail = rsum_range(d, p, r_double, n1);
            radd(d, head, tail)
        };
        let s5 = {
            let pf = d.lemma(
                p.sum_range_congr,
                &[l_swapped, r_double, n1, pointwise_swap],
            );
            let from = rsum_range(d, p, l_swapped, n1);
            let to = rsum_range(d, p, r_double, n1);
            rcongr(d, from, to, pf, &|d, t| radd(d, head, t))
        };

        let l6 = {
            let tail = rsum_range(d, p, r_shift, n1);
            radd(d, head, tail)
        };
        let s6 = {
            let pf = d.lemma(p.sum_range_congr, &[r_shift, r_double, n1, pointwise_r]);
            let from = rsum_range(d, p, r_shift, n1);
            let to = rsum_range(d, p, r_double, n1);
            let flipped = super::ops::rsymm(d, from, to, pf);
            rcongr(d, to, from, flipped, &|d, t| radd(d, head, t))
        };

        let target = rsum_range(d, p, col_fn, n2);
        let s7 = {
            let pf = d.lemma(p.sum_range_peel_head, &[col_fn, n1]);
            super::ops::rsymm(d, target, l6, pf)
        };

        let (_e, proof) = rchain(
            d,
            start,
            &[
                (l1, s1),
                (l2, s2),
                (l3, s3),
                (l4, s4),
                (l5, s5),
                (l6, s6),
                (target, s7),
            ],
        );
        d.lam_fv(a_fv, mty, proof)
    };

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let stmt = motive(d, m);
    let proof = d.induct(&motive, &base, &step, m);
    let ty = d.pi_fv(m_fv, nat, stmt);
    let value = d.lam_fv(m_fv, nat, proof);
    d.declare_theorem(p.det_col_expansion, ty, value)
}

/// Admit `Rat.matMinor_transpose : ∀ A q r c,
/// matMinor (matTranspose A) 0 q r c = matTranspose (matMinor A q 0) r c` —
/// POINTWISE, and `Eq.refl`.
///
/// Both sides delta-beta-iota-reduce to `A (matSkip q c) (matSkip 0 r)`:
/// deleting row `0` and column `q` from `Aᵀ` is deleting row `q` and column `0`
/// from `A` and then transposing. Stated at an index pair because `funext` is
/// absent, which is also why [`declare_det_congr`] has to carry it to the
/// determinant.
fn declare_mat_minor_transpose(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let mat = d.kernel().fvar(a_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let zero_n = d.zero();
    let transposed = rmat_transpose_of(d, p, mat);
    let lhs = rmat_minor(d, p, transposed, zero_n, q, r, c);
    let rhs = {
        let minor = rmat_minor_of(d, p, mat, q, zero_n);
        let t = rmat_transpose_of(d, p, minor);
        d.apply(t, &[r, c])
    };
    let stmt = req(d, lhs, rhs);
    let proof = rrefl(d, lhs);

    let ty = {
        let over_c = d.pi_fv(c_fv, nat, stmt);
        let over_r = d.pi_fv(r_fv, nat, over_c);
        let over_q = d.pi_fv(q_fv, nat, over_r);
        d.pi_fv(a_fv, mty, over_q)
    };
    let value = {
        let over_c = d.lam_fv(c_fv, nat, proof);
        let over_r = d.lam_fv(r_fv, nat, over_c);
        let over_q = d.lam_fv(q_fv, nat, over_r);
        d.lam_fv(a_fv, mty, over_q)
    };
    d.declare_theorem(p.mat_minor_transpose, ty, value)
}

/// Admit `Rat.det_transpose : ∀ n A, det (matTranspose A) n = det A n` — the
/// THIRD of the four determinant laws ADR-1120 named, at a **symbolic**
/// dimension.
///
/// One induction on the dimension with the matrix under the motive. The step is
/// three moves and no case split:
///
/// 1. `det_succ` expands `det Aᵀ (succ m)` along `Aᵀ`'s first row, whose
///    entries are `A`'s first COLUMN — `matTranspose A 0 q ≡ A q 0` by delta
///    and beta alone.
/// 2. Under `Rat.sumRange_congr`, [`declare_mat_minor_transpose`] plus
///    [`declare_det_congr`] rewrite each `matMinor Aᵀ 0 q` into
///    `matTranspose (matMinor A q 0)`, which the induction hypothesis strips.
/// 3. What remains is expansion along `A`'s first column, and
///    [`declare_det_col_expansion`] closes it.
///
/// [`declare_det_row_expansion`] is NOT used, and cannot be: expansion along a
/// column of `A` IS expansion along a row of `Aᵀ`, so reaching for the row law
/// here is circular. The column law had to be proved on its own, and that is
/// where this lane's work went.
fn declare_det_transpose(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let motive = |d: &mut IntDev<'_>, n: ExprId| -> ExprId {
        let mty = mat_ty(d);
        let a_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(a_fv);
        let transposed = rmat_transpose_of(d, p, mat);
        let lhs = rdet(d, p, transposed, n);
        let rhs = rdet(d, p, mat, n);
        let eq = req(d, lhs, rhs);
        d.pi_fv(a_fv, mty, eq)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        // `det _ 0 ≡ one` on both sides.
        let mty = mat_ty(d);
        let a_fv = d.fresh_fvar();
        let one = rone(d, p);
        let refl = rrefl(d, one);
        d.lam_fv(a_fv, mty, refl)
    };

    let step = |d: &mut IntDev<'_>, m: ExprId, ih: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let mty = mat_ty(d);
        let a_fv = d.fresh_fvar();
        let mat = d.kernel().fvar(a_fv);
        let zero_n = d.zero();
        let sm = d.succ(m);
        let transposed = rmat_transpose_of(d, p, mat);

        let row_fn = row_zero_expansion_fn(d, p, transposed, m);
        let col_fn = col_zero_expansion_fn(d, p, mat, m);

        let pointwise = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let sign = ralt_sign(d, p, q);
            let entry = d.apply(transposed, &[zero_n, q]);
            let minor_t = rmat_minor_of(d, p, transposed, zero_n, q);
            let minor = rmat_minor_of(d, p, mat, q, zero_n);
            let minor_transposed = rmat_transpose_of(d, p, minor);

            let det_t = rdet(d, p, minor_t, m);
            let det_mid = rdet(d, p, minor_transposed, m);
            let det_plain = rdet(d, p, minor, m);

            let h_pointwise = d.const_app(p.mat_minor_transpose, &[mat, q]);
            let h1 = d.lemma(p.det_congr, &[m, minor_t, minor_transposed, h_pointwise]);
            let h2 = d.apply(ih, &[minor]);
            let h = rtrans(d, det_t, det_mid, det_plain, h1, h2);

            let body = rcongr(d, det_t, det_plain, h, &|d, t| {
                let product = rmul(d, entry, t);
                rmul(d, sign, product)
            });
            d.lam_fv(q_fv, nat, body)
        };

        let start = rdet(d, p, transposed, sm);
        let l1 = rsum_range(d, p, row_fn, sm);
        let s1 = d.lemma(p.det_succ, &[transposed, m]);

        let l2 = rsum_range(d, p, col_fn, sm);
        let s2 = d.lemma(p.sum_range_congr, &[row_fn, col_fn, sm, pointwise]);

        let target = rdet(d, p, mat, sm);
        let s3 = {
            let pf = d.lemma(p.det_col_expansion, &[m, mat]);
            super::ops::rsymm(d, target, l2, pf)
        };

        let (_e, proof) = rchain(d, start, &[(l1, s1), (l2, s2), (target, s3)]);
        d.lam_fv(a_fv, mty, proof)
    };

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let stmt = motive(d, n);
    let proof = d.induct(&motive, &base, &step, n);
    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.det_transpose, ty, value)
}

// --- alternating property (ADR-1310 step 2) ---------------------------------

/// `h : Eq Nat a b ⊢ Eq Bool (f a) (f b)` — the `Nat`-hypothesis, `Bool`-
/// conclusion twin of [`super::ops::nat_eq_to_rat`] (same shape, `Bool`
/// conclusion instead of `Rat`). Needed wherever a `Nat.ble`/`Nat.beq` fact
/// about one value must be transported to a DIFFERENT but Nat-equal value —
/// [`declare_det_alternating`]'s bound derivations.
fn congr_nat_to_bool(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(d, a);
    let motive = NatOps::eq_motive(d, a, &|d, x| {
        let fx = f(d, x);
        d.bool_eq(fa, fx)
    });
    let refl_case = d.bool_refl(fa);
    NatOps::transport(d, a, motive, refl_case, b, h)
}

/// From `h : Eq Nat a b` and a proof that `f b` reduces to `Bool.true` by
/// pure iota (the caller's responsibility — checked only by the trusted
/// gate accepting the declaration), derive `Eq Bool (f a) true`.
fn bool_true_via_eq(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    f: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let true_ = d.bool_true();
    let fb_true = d.bool_refl(true_);
    let step = congr_nat_to_bool(d, a, b, h, f);
    let fa = f(d, a);
    let fb = f(d, b);
    d.bool_trans(fa, fb, true_, step, fb_true)
}

/// From `hi : Eq i v`, `hj : Eq j v` (the SAME concrete `v`, needed so that
/// `Nat.beq v v` iota-reduces to `Bool.true`) and `hne : Eq Bool (beq i j)
/// false`, derive `target` (any `Prop`) via `False.elim` — the contradiction
/// every base-dimension leaf of [`declare_det_alternating`] closes with.
fn contradiction_of_eq_via_beq(
    d: &mut IntDev<'_>,
    i: ExprId,
    j: ExprId,
    v: ExprId,
    hi: ExprId,
    hj: ExprId,
    hne: ExprId,
    target: ExprId,
) -> ExprId {
    let false_ = d.bool_false();
    let beq_ij = d.beq(i, j);
    let beq_vj = d.beq(v, j);
    let beq_vv = d.beq(v, v);

    let step1 = congr_nat_to_bool(d, i, v, hi, &|d, x| d.beq(x, j));
    let step2 = congr_nat_to_bool(d, j, v, hj, &|d, x| d.beq(v, x));
    let chain = d.bool_trans(beq_ij, beq_vj, beq_vv, step1, step2);
    let symm_chain = d.bool_symm(beq_ij, beq_vv, chain);
    let at_vv = d.bool_trans(beq_vv, beq_ij, false_, symm_chain, hne);
    let swapped = d.bool_symm(beq_vv, false_, at_vv);
    d.false_true_elim(target, swapped)
}

/// From `h : Eq Bool (ble x 0) true`, derive `Eq x 0`. Induction on `x`,
/// discarding the IH: `x = 0` is `Eq.refl`; `x = succ x'` makes `h` defeq
/// `Eq Bool false true` (`ble (succ _) 0` is the ONE-step base case), so
/// any conclusion follows via `false_true_elim`.
fn nat_eq_zero_of_ble_zero_true(d: &mut IntDev<'_>, x: ExprId, h: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let zero_n = d.zero();
        let hyp = ble_true_ty(d, x, zero_n);
        let concl = NatOps::eq(d, x, zero_n);
        d.arrow(hyp, concl)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let zero_n = d.zero();
        let hyp = ble_true_ty(d, zero_n, zero_n);
        let h_fv = d.fresh_fvar();
        let pf = NatOps::refl(d, zero_n);
        d.lam_fv(h_fv, hyp, pf)
    };
    let step = |d: &mut IntDev<'_>, xp: ExprId, _ih: ExprId| -> ExprId {
        let zero_n = d.zero();
        let sxp = d.succ(xp);
        let hyp = ble_true_ty(d, sxp, zero_n);
        let h_fv = d.fresh_fvar();
        let hh = d.kernel().fvar(h_fv);
        let concl = NatOps::eq(d, sxp, zero_n);
        let pf = d.false_true_elim(concl, hh);
        d.lam_fv(h_fv, hyp, pf)
    };
    let proof_fn = d.induct(&motive, &base, &step, x);
    d.apply(proof_fn, &[h])
}

/// From `h : Eq Bool (beq x 0) true`, derive `Eq x 0`. Same shape as
/// [`nat_eq_zero_of_ble_zero_true`], `Nat.beq` in place of `Nat.ble`.
fn nat_eq_zero_of_beq_zero_true(d: &mut IntDev<'_>, x: ExprId, h: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let zero_n = d.zero();
        let b = d.beq(x, zero_n);
        let t = d.bool_true();
        let hyp = d.bool_eq(b, t);
        let concl = NatOps::eq(d, x, zero_n);
        d.arrow(hyp, concl)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let zero_n = d.zero();
        let b = d.beq(zero_n, zero_n);
        let t = d.bool_true();
        let hyp = d.bool_eq(b, t);
        let h_fv = d.fresh_fvar();
        let pf = NatOps::refl(d, zero_n);
        d.lam_fv(h_fv, hyp, pf)
    };
    let step = |d: &mut IntDev<'_>, xp: ExprId, _ih: ExprId| -> ExprId {
        let zero_n = d.zero();
        let sxp = d.succ(xp);
        let b = d.beq(sxp, zero_n);
        let t = d.bool_true();
        let hyp = d.bool_eq(b, t);
        let h_fv = d.fresh_fvar();
        let hh = d.kernel().fvar(h_fv);
        let target = NatOps::eq(d, sxp, zero_n);
        let pf = d.false_true_elim(target, hh);
        d.lam_fv(h_fv, hyp, pf)
    };
    let proof_fn = d.induct(&motive, &base, &step, x);
    d.apply(proof_fn, &[h])
}

/// From `h : Eq Bool (beq x 0) false`, derive `Eq x (succ (pred x))` — `x`
/// is nonzero, exhibited via its OWN `pred`, not a fresh unrelated variable
/// (which would be useless: a case-split via `Nat.rec` on an already-fixed
/// free variable does not hand the branch any usable fact connecting the
/// two). Induction on `x`, discarding the IH: `x = 0` makes `h` defeq
/// `Eq Bool true false`, contradiction; `x = succ x'` is `Eq.refl` since
/// `pred (succ x') ≡ x'`.
fn nat_succ_pred_of_beq_zero_false(d: &mut IntDev<'_>, x: ExprId, h: ExprId) -> ExprId {
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let zero_n = d.zero();
        let b = d.beq(x, zero_n);
        let f_ = d.bool_false();
        let hyp = d.bool_eq(b, f_);
        let px = d.pred(x);
        let spx = d.succ(px);
        let concl = NatOps::eq(d, x, spx);
        d.arrow(hyp, concl)
    };
    let base = |d: &mut IntDev<'_>| -> ExprId {
        let zero_n = d.zero();
        let beq00 = d.beq(zero_n, zero_n);
        let f_ = d.bool_false();
        let hyp = d.bool_eq(beq00, f_);
        let h_fv = d.fresh_fvar();
        let hh = d.kernel().fvar(h_fv);
        let px = d.pred(zero_n);
        let spx = d.succ(px);
        let target = NatOps::eq(d, zero_n, spx);
        let swapped = d.bool_symm(beq00, f_, hh);
        let pf = d.false_true_elim(target, swapped);
        d.lam_fv(h_fv, hyp, pf)
    };
    let step = |d: &mut IntDev<'_>, xp: ExprId, _ih: ExprId| -> ExprId {
        let zero_n = d.zero();
        let sxp = d.succ(xp);
        let b = d.beq(sxp, zero_n);
        let f_ = d.bool_false();
        let hyp = d.bool_eq(b, f_);
        let h_fv = d.fresh_fvar();
        let pf = NatOps::refl(d, sxp);
        d.lam_fv(h_fv, hyp, pf)
    };
    let proof_fn = d.induct(&motive, &base, &step, x);
    d.apply(proof_fn, &[h])
}

/// `Eq Bool (Nat.beq i j) false`, the distinctness hypothesis
/// [`declare_det_alternating`] carries.
pub(super) fn alt_hyp_ne(d: &mut IntDev<'_>, i: ExprId, j: ExprId) -> ExprId {
    let b = d.beq(i, j);
    let f_ = d.bool_false();
    d.bool_eq(b, f_)
}

/// `∀ c, A i c = A j c` — the pointwise row-equality hypothesis.
fn alt_row_eq_ty(d: &mut IntDev<'_>, mat: ExprId, i: ExprId, j: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let ai = d.apply(mat, &[i, c]);
    let aj = d.apply(mat, &[j, c]);
    let eq = req(d, ai, aj);
    d.pi_fv(c_fv, nat, eq)
}

/// `Nat.beq i j = false → Nat.ble i (succ mp) = true → Nat.ble j (succ mp) =
/// true → (∀ c, A i c = A j c) → det A (succ (succ mp)) = 0` at fixed `mat`,
/// `i`, `j`, `mp` — the arrow chain every leaf of
/// [`declare_det_alternating`]'s step case produces a value of.
fn alt_arrow_chain_ty(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    i: ExprId,
    j: ExprId,
    mp: ExprId,
) -> ExprId {
    let smp = d.succ(mp);
    let hne_ty = alt_hyp_ne(d, i, j);
    let hbi_ty = ble_true_ty(d, i, smp);
    let hbj_ty = ble_true_ty(d, j, smp);
    let hrow_ty = alt_row_eq_ty(d, mat, i, j);
    let ssmp = d.succ(smp);
    let det_val = rdet(d, p, mat, ssmp);
    let zero_r = rzero(d, p);
    let concl = req(d, det_val, zero_r);
    let arr = d.arrow(hrow_ty, concl);
    let arr = d.arrow(hbj_ty, arr);
    let arr = d.arrow(hbi_ty, arr);
    d.arrow(hne_ty, arr)
}

/// `∀ j, <alt_arrow_chain_ty at this i,j,mp>` — the `Prop`-valued motive
/// [`alt_step`]'s outer case split on `i` uses.
fn alt_inner_over_j(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    i: ExprId,
    mp: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let body = alt_arrow_chain_ty(d, p, mat, i, j, mp);
    d.pi_fv(j_fv, nat, body)
}

/// Expand `mat` (dimension `succ n1`) along row `k` (`hk : ble k n1 = true`)
/// and collapse the resulting sum to `0`, given a proof (for an ARBITRARY
/// column `q`) that the cofactor determinant `det (matMinor mat k q) n1`
/// vanishes. Every summand is then `sign * (entry * 0) = 0` via
/// `Rat.mul_zero` twice, and `Rat.sumRange_eq_zero_of_lt` collapses the sum.
/// Shared by every branch of [`declare_det_alternating`] that expands.
fn zero_sum_via_expansion(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    k: ExprId,
    hk: ExprId,
    n1: ExprId,
    minor_zero: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let sn1 = d.succ(n1);

    let expand = d.lemma(p.det_row_expansion, &[n1, mat, k, hk]);

    let summand = row_expansion_fn(d, p, mat, k, n1);
    let summed = rsum_range(d, p, summand, sn1);
    let zero_r = rzero(d, p);

    let per_q = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let lt_fv = d.fresh_fvar();
        let lt_ty = d.lt(q, sn1);

        let mz = minor_zero(d, q);
        let index = d.add(q, k);
        let sign = ralt_sign(d, p, index);
        let entry = d.apply(mat, &[k, q]);
        let minor = rmat_minor_of(d, p, mat, k, q);
        let sub = rdet(d, p, minor, n1);

        let step1 = rcongr(d, sub, zero_r, mz, &|d, t| rmul(d, entry, t));
        let ez1 = d.lemma(p.mul_zero, &[entry]);
        let product = rmul(d, entry, sub);
        let ez_prod = rmul(d, entry, zero_r);
        let prod_zero = rtrans(d, product, ez_prod, zero_r, step1, ez1);

        let step2 = rcongr(d, product, zero_r, prod_zero, &|d, t| rmul(d, sign, t));
        let ez2 = d.lemma(p.mul_zero, &[sign]);
        let body = rmul(d, sign, product);
        let ez_body = rmul(d, sign, zero_r);
        let sign_zero = rtrans(d, body, ez_body, zero_r, step2, ez2);

        let with_lt = d.lam_fv(lt_fv, lt_ty, sign_zero);
        d.lam_fv(q_fv, nat, with_lt)
    };
    let collapse = d.lemma(p.sum_range_eq_zero_of_lt, &[summand, sn1, per_q]);

    let det_val = rdet(d, p, mat, sn1);
    let (_e, proof) = rchain(d, det_val, &[(summed, expand), (zero_r, collapse)]);
    proof
}

/// The `i = 0`, `j = succ (succ jpp)` leaf (`j >= 2`): expand along row `1`.
/// `matSkip 1` fixes `0` (below the cut) and shifts `succ jpp` to `j`
/// (above it) — both by pure iota once the case split has put the `succ` in
/// place, so no extra `matSkip` lemma is needed. The induction hypothesis's
/// bounds on the minor's rows `0`/`succ jpp` are either vacuous (`ble 0 _ =
/// true`, `beq 0 (succ _) = false`, always) or the ORIGINAL `hbj_other`
/// reduced by one `succ`/`succ` peel — never rebuilt from scratch.
fn alt_core_ge2(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    other_pp: ExprId,
    mp: ExprId,
    ih: ExprId,
    hbj_other: ExprId,
    hrow_zero_other: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let smp = d.succ(mp);
    let other_p = d.succ(other_pp);

    let hk = {
        let t = d.bool_true();
        d.bool_refl(t)
    };

    zero_sum_via_expansion(d, p, mat, one_n, hk, smp, &|d, q| {
        let minor = rmat_minor_of(d, p, mat, one_n, q);
        let hne2 = {
            let f_ = d.bool_false();
            d.bool_refl(f_)
        };
        let hbi2 = {
            let t = d.bool_true();
            d.bool_refl(t)
        };
        let hbj2 = hbj_other;
        let hrow2 = {
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let shifted = rmat_skip(d, p, q, c);
            let body = d.apply(hrow_zero_other, &[shifted]);
            d.lam_fv(c_fv, nat, body)
        };
        d.apply(ih, &[minor, zero_n, other_p, hne2, hbi2, hbj2, hrow2])
    })
}

/// The `i = 0`, `j = 1` corner: no third row exists, so this closes
/// directly via `det_eq_det2` when `mp = 0`, and via row-`2` expansion
/// (which needs `mp >= 1`, derived from `Nat.beq mp 0 = false`) otherwise.
fn alt_core_eq1(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    mp: ExprId,
    ih: ExprId,
    hrow_zero_one: ExprId,
) -> ExprId {
    let zero_n = d.zero();
    let cond = d.beq(mp, zero_n);
    let target = {
        let smp = d.succ(mp);
        let ssmp = d.succ(smp);
        let det_val = rdet(d, p, mat, ssmp);
        let zero_r = rzero(d, p);
        req(d, det_val, zero_r)
    };

    let at_true = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp_ty = {
            let t = d.bool_true();
            d.bool_eq(cond, t)
        };
        let body = alt_2x2_via_beq(d, p, mat, mp, h, hrow_zero_one);
        d.lam_fv(h_fv, hyp_ty, body)
    };
    let at_false = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp_ty = {
            let f_ = d.bool_false();
            d.bool_eq(cond, f_)
        };
        let body = alt_k2_via_beq(d, p, mat, mp, h, ih, hrow_zero_one);
        d.lam_fv(h_fv, hyp_ty, body)
    };
    bool_cases_eq(d, cond, target, at_true, at_false)
}

/// `mp = 0` half of [`alt_core_eq1`]: `det A 2 = 0` from `A00 = A10`,
/// `A01 = A11` (the row-equality hypothesis at columns `0`,`1`) via
/// `Rat.mul_comm` and [`det2_zero_of_ad_eq_bc`], lifted from dimension `2`
/// to `succ (succ mp)` along `h : beq mp 0 = true`.
fn alt_2x2_via_beq(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    mp: ExprId,
    h: ExprId,
    hrow: ExprId,
) -> ExprId {
    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let heq0 = nat_eq_zero_of_beq_zero_true(d, mp, h);

    let a00 = d.apply(mat, &[zero_n, zero_n]);
    let a01 = d.apply(mat, &[zero_n, one_n]);
    let a10 = d.apply(mat, &[one_n, zero_n]);
    let a11 = d.apply(mat, &[one_n, one_n]);

    let h0 = d.apply(hrow, &[zero_n]);
    let h1 = d.apply(hrow, &[one_n]);

    let step1 = rcongr(d, a00, a10, h0, &|d, t| rmul(d, t, a11));
    let h1_symm = super::ops::rsymm(d, a01, a11, h1);
    let step2 = rcongr(d, a11, a01, h1_symm, &|d, t| rmul(d, a10, t));
    let step3 = d.lemma(p.mul_comm, &[a10, a01]);

    let ad = rmul(d, a00, a11);
    let mid1 = rmul(d, a10, a11);
    let mid2 = rmul(d, a10, a01);
    let bc = rmul(d, a01, a10);
    let (_e, ad_eq_bc) = rchain(d, ad, &[(mid1, step1), (mid2, step2), (bc, step3)]);

    let det2_zero = det2_zero_of_ad_eq_bc(d, p, a00, a01, a10, a11, ad_eq_bc);
    let two_n = d.succ(one_n);
    let det_at_2 = rdet(d, p, mat, two_n);
    let det_eq = d.lemma(p.det_eq_det2, &[mat]);
    let det2_val = rdet2(d, p, a00, a01, a10, a11);
    let zero_r = rzero(d, p);
    let body0 = rtrans(d, det_at_2, det2_val, zero_r, det_eq, det2_zero);

    let heq2 = NatOps::congr(d, mp, zero_n, heq0, &|d, t| {
        let s1 = d.succ(t);
        d.succ(s1)
    });
    let smp = d.succ(mp);
    let ssmp = d.succ(smp);
    let lifted = nat_eq_to_rat(d, ssmp, two_n, heq2, &|d, t| rdet(d, p, mat, t));
    let det_at_mp = rdet(d, p, mat, ssmp);
    rtrans(d, det_at_mp, det_at_2, zero_r, lifted, body0)
}

/// `mp = succ mpp` half of [`alt_core_eq1`]: expand along row `2`, which
/// needs `Nat.ble 2 (succ mp) = true` — derived from `h : beq mp 0 = false`
/// via [`nat_succ_pred_of_beq_zero_false`] and [`bool_true_via_eq`], since
/// `ble 2 (succ (succ mpp)) = true` reduces by pure iota for ANY `mpp`.
fn alt_k2_via_beq(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    mp: ExprId,
    h: ExprId,
    ih: ExprId,
    hrow: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let two_n = d.succ(one_n);
    let smp = d.succ(mp);

    let heq = nat_succ_pred_of_beq_zero_false(d, mp, h);
    let mpp = d.pred(mp);
    let smpp = d.succ(mpp);

    let heq_s = NatOps::congr(d, mp, smpp, heq, &|d, t| d.succ(t));
    let ssmpp = d.succ(smpp);
    let hk = bool_true_via_eq(d, smp, ssmpp, heq_s, &|d, t| d.ble(two_n, t));
    let hbj2 = bool_true_via_eq(d, mp, smpp, heq, &|d, t| d.ble(one_n, t));

    zero_sum_via_expansion(d, p, mat, two_n, hk, smp, &|d, q| {
        let minor = rmat_minor_of(d, p, mat, two_n, q);
        let hne2 = {
            let f_ = d.bool_false();
            d.bool_refl(f_)
        };
        let hbi2 = {
            let t = d.bool_true();
            d.bool_refl(t)
        };
        let hrow2 = {
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let shifted = rmat_skip(d, p, q, c);
            let body = d.apply(hrow, &[shifted]);
            d.lam_fv(c_fv, nat, body)
        };
        d.apply(ih, &[minor, zero_n, one_n, hne2, hbi2, hbj2, hrow2])
    })
}

/// `i = j = 0` leaf: `Nat.beq 0 0` reduces to `true`, contradicting `hne`.
fn alt_zero_zero(d: &mut IntDev<'_>, p: RatPrelude, mat: ExprId, mp: ExprId) -> ExprId {
    let zero_n = d.zero();
    let smp = d.succ(mp);
    let hne_ty = alt_hyp_ne(d, zero_n, zero_n);
    let hbi_ty = ble_true_ty(d, zero_n, smp);
    let hbj_ty = ble_true_ty(d, zero_n, smp);
    let hrow_ty = alt_row_eq_ty(d, mat, zero_n, zero_n);
    let ssmp = d.succ(smp);
    let det_val = rdet(d, p, mat, ssmp);
    let zero_r = rzero(d, p);
    let target = req(d, det_val, zero_r);

    let hne_fv = d.fresh_fvar();
    let hne = d.kernel().fvar(hne_fv);
    let beq00 = d.beq(zero_n, zero_n);
    let false_ = d.bool_false();
    let swapped = d.bool_symm(beq00, false_, hne);
    let body = d.false_true_elim(target, swapped);

    let hbi_fv = d.fresh_fvar();
    let hbj_fv = d.fresh_fvar();
    let hrow_fv = d.fresh_fvar();
    let with_hrow = d.lam_fv(hrow_fv, hrow_ty, body);
    let with_hbj = d.lam_fv(hbj_fv, hbj_ty, with_hrow);
    let with_hbi = d.lam_fv(hbi_fv, hbi_ty, with_hbj);
    d.lam_fv(hne_fv, hne_ty, with_hbi)
}

/// `i = 0`, `j = 1` leaf: bind the outer hypotheses (only `hrow` is used —
/// [`alt_core_eq1`] rebuilds `hne`/`hbi`/`hbj` at the minor's dimension
/// itself, since the bound ones are at the WRONG dimension to reuse).
fn alt_zero_one(d: &mut IntDev<'_>, p: RatPrelude, mat: ExprId, mp: ExprId, ih: ExprId) -> ExprId {
    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let smp = d.succ(mp);
    let hne_ty = alt_hyp_ne(d, zero_n, one_n);
    let hbi_ty = ble_true_ty(d, zero_n, smp);
    let hbj_ty = ble_true_ty(d, one_n, smp);
    let hrow_ty = alt_row_eq_ty(d, mat, zero_n, one_n);

    let hrow_fv = d.fresh_fvar();
    let hrow = d.kernel().fvar(hrow_fv);
    let body = alt_core_eq1(d, p, mat, mp, ih, hrow);

    let hne_fv = d.fresh_fvar();
    let hbi_fv = d.fresh_fvar();
    let hbj_fv = d.fresh_fvar();
    let with_hrow = d.lam_fv(hrow_fv, hrow_ty, body);
    let with_hbj = d.lam_fv(hbj_fv, hbj_ty, with_hrow);
    let with_hbi = d.lam_fv(hbi_fv, hbi_ty, with_hbj);
    d.lam_fv(hne_fv, hne_ty, with_hbi)
}

/// `i = 0`, `j = succ (succ jpp)` leaf.
fn alt_zero_ge2(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    jpp: ExprId,
    mp: ExprId,
    ih: ExprId,
) -> ExprId {
    let zero_n = d.zero();
    let jp2 = d.succ(jpp);
    let j = d.succ(jp2);
    let smp = d.succ(mp);
    let hne_ty = alt_hyp_ne(d, zero_n, j);
    let hbi_ty = ble_true_ty(d, zero_n, smp);
    let hbj_ty = ble_true_ty(d, j, smp);
    let hrow_ty = alt_row_eq_ty(d, mat, zero_n, j);

    let hbj_fv = d.fresh_fvar();
    let hbj = d.kernel().fvar(hbj_fv);
    let hrow_fv = d.fresh_fvar();
    let hrow = d.kernel().fvar(hrow_fv);
    let body = alt_core_ge2(d, p, mat, jpp, mp, ih, hbj, hrow);

    let hne_fv = d.fresh_fvar();
    let hbi_fv = d.fresh_fvar();
    let with_hrow = d.lam_fv(hrow_fv, hrow_ty, body);
    let with_hbj = d.lam_fv(hbj_fv, hbj_ty, with_hrow);
    let with_hbi = d.lam_fv(hbi_fv, hbi_ty, with_hbj);
    d.lam_fv(hne_fv, hne_ty, with_hbi)
}

/// `i = 0` branch of [`alt_step`]'s outer case split: further case-splits
/// `j`.
fn alt_branch_i_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    mp: ExprId,
    ih: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let zero_n = d.zero();

    let motive_j =
        |d: &mut IntDev<'_>, j: ExprId| -> ExprId { alt_arrow_chain_ty(d, p, mat, zero_n, j, mp) };
    let j_at_zero = |d: &mut IntDev<'_>| -> ExprId { alt_zero_zero(d, p, mat, mp) };
    let j_at_succ = |d: &mut IntDev<'_>, jp: ExprId, _ihj: ExprId| -> ExprId {
        alt_zero_succ(d, p, mat, jp, mp, ih)
    };

    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let per_j = d.induct(
        &motive_j,
        &j_at_zero,
        &|d, jp, ihj| j_at_succ(d, jp, ihj),
        j,
    );
    d.lam_fv(j_fv, nat, per_j)
}

/// `i = 0`, `j = succ jp`: further case-split on `jp` (`j = 1` vs `j >= 2`).
fn alt_zero_succ(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    jp: ExprId,
    mp: ExprId,
    ih: ExprId,
) -> ExprId {
    let zero_n = d.zero();

    let motive_jp = |d: &mut IntDev<'_>, jpv: ExprId| -> ExprId {
        let j = d.succ(jpv);
        alt_arrow_chain_ty(d, p, mat, zero_n, j, mp)
    };
    let jp_at_zero = |d: &mut IntDev<'_>| -> ExprId { alt_zero_one(d, p, mat, mp, ih) };
    let jp_at_succ = |d: &mut IntDev<'_>, jpp: ExprId, _ihj: ExprId| -> ExprId {
        alt_zero_ge2(d, p, mat, jpp, mp, ih)
    };
    d.induct(
        &motive_jp,
        &jp_at_zero,
        &|d, jpp, ihj| jp_at_succ(d, jpp, ihj),
        jp,
    )
}

/// `i = succ ip`, `j = succ jp` leaf (LEAF 1: both rows nonzero): expand
/// along row `0`. `matSkip 0` is unconditionally `succ` ([`declare_mat_skip_zero`]),
/// so the minor's rows `ip`,`jp` are the original `i`,`j` by pure iota, and
/// because `Nat.beq`/`Nat.ble` at two `succ`s iota-reduce by peeling one
/// layer, the OUTER `hne`/`hbi`/`hbj` are already, up to defeq, exactly what
/// the induction hypothesis wants at `ip`,`jp` — reused verbatim, no
/// rebuilding.
fn alt_succ_succ(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    ip: ExprId,
    jp: ExprId,
    mp: ExprId,
    ih: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let zero_n = d.zero();
    let i = d.succ(ip);
    let j = d.succ(jp);
    let smp = d.succ(mp);
    let hne_ty = alt_hyp_ne(d, i, j);
    let hbi_ty = ble_true_ty(d, i, smp);
    let hbj_ty = ble_true_ty(d, j, smp);
    let hrow_ty = alt_row_eq_ty(d, mat, i, j);

    let hne_fv = d.fresh_fvar();
    let hne = d.kernel().fvar(hne_fv);
    let hbi_fv = d.fresh_fvar();
    let hbi = d.kernel().fvar(hbi_fv);
    let hbj_fv = d.fresh_fvar();
    let hbj = d.kernel().fvar(hbj_fv);
    let hrow_fv = d.fresh_fvar();
    let hrow = d.kernel().fvar(hrow_fv);

    let hk = {
        let t = d.bool_true();
        d.bool_refl(t)
    };

    let body = zero_sum_via_expansion(d, p, mat, zero_n, hk, smp, &|d, q| {
        let minor = rmat_minor_of(d, p, mat, zero_n, q);
        let hrow2 = {
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let shifted = rmat_skip(d, p, q, c);
            let bd = d.apply(hrow, &[shifted]);
            d.lam_fv(c_fv, nat, bd)
        };
        d.apply(ih, &[minor, ip, jp, hne, hbi, hbj, hrow2])
    });

    let with_hrow = d.lam_fv(hrow_fv, hrow_ty, body);
    let with_hbj = d.lam_fv(hbj_fv, hbj_ty, with_hrow);
    let with_hbi = d.lam_fv(hbi_fv, hbi_ty, with_hbj);
    d.lam_fv(hne_fv, hne_ty, with_hbi)
}

/// `i = 1`, `j = 0` leaf: [`alt_core_eq1`] with the row-equality hypothesis
/// flipped by `rsymm`.
fn alt_one_zero(d: &mut IntDev<'_>, p: RatPrelude, mat: ExprId, mp: ExprId, ih: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let zero_n = d.zero();
    let one_n = d.succ(zero_n);
    let smp = d.succ(mp);
    let hne_ty = alt_hyp_ne(d, one_n, zero_n);
    let hbi_ty = ble_true_ty(d, one_n, smp);
    let hbj_ty = ble_true_ty(d, zero_n, smp);
    let hrow_ty = alt_row_eq_ty(d, mat, one_n, zero_n);

    let hrow_fv = d.fresh_fvar();
    let hrow = d.kernel().fvar(hrow_fv);
    let hrow_swapped = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let m1c = d.apply(mat, &[one_n, c]);
        let m0c = d.apply(mat, &[zero_n, c]);
        let hc = d.apply(hrow, &[c]);
        let sw = super::ops::rsymm(d, m1c, m0c, hc);
        d.lam_fv(c_fv, nat, sw)
    };
    let body = alt_core_eq1(d, p, mat, mp, ih, hrow_swapped);

    let hne_fv = d.fresh_fvar();
    let hbi_fv = d.fresh_fvar();
    let hbj_fv = d.fresh_fvar();
    let with_hrow = d.lam_fv(hrow_fv, hrow_ty, body);
    let with_hbj = d.lam_fv(hbj_fv, hbj_ty, with_hrow);
    let with_hbi = d.lam_fv(hbi_fv, hbi_ty, with_hbj);
    d.lam_fv(hne_fv, hne_ty, with_hbi)
}

/// `i = succ (succ ipp)`, `j = 0` leaf: [`alt_core_ge2`] with the
/// row-equality hypothesis flipped and `hbi` supplying the bound
/// [`alt_core_ge2`] expects for the nonzero row.
fn alt_ge2_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    ipp: ExprId,
    mp: ExprId,
    ih: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let zero_n = d.zero();
    let ip2 = d.succ(ipp);
    let i = d.succ(ip2);
    let smp = d.succ(mp);
    let hne_ty = alt_hyp_ne(d, i, zero_n);
    let hbi_ty = ble_true_ty(d, i, smp);
    let hbj_ty = ble_true_ty(d, zero_n, smp);
    let hrow_ty = alt_row_eq_ty(d, mat, i, zero_n);

    let hbi_fv = d.fresh_fvar();
    let hbi = d.kernel().fvar(hbi_fv);
    let hrow_fv = d.fresh_fvar();
    let hrow = d.kernel().fvar(hrow_fv);
    let hrow_swapped = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let mic = d.apply(mat, &[i, c]);
        let m0c = d.apply(mat, &[zero_n, c]);
        let hc = d.apply(hrow, &[c]);
        let sw = super::ops::rsymm(d, mic, m0c, hc);
        d.lam_fv(c_fv, nat, sw)
    };
    let body = alt_core_ge2(d, p, mat, ipp, mp, ih, hbi, hrow_swapped);

    let hne_fv = d.fresh_fvar();
    let hbj_fv = d.fresh_fvar();
    let with_hrow = d.lam_fv(hrow_fv, hrow_ty, body);
    let with_hbj = d.lam_fv(hbj_fv, hbj_ty, with_hrow);
    let with_hbi = d.lam_fv(hbi_fv, hbi_ty, with_hbj);
    d.lam_fv(hne_fv, hne_ty, with_hbi)
}

/// `i = succ ip`, `j = 0`: further case-split on `ip` (`i = 1` vs `i >= 2`),
/// mirroring [`alt_zero_succ`].
fn alt_succ_zero(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    ip: ExprId,
    mp: ExprId,
    ih: ExprId,
) -> ExprId {
    let zero_n = d.zero();

    let motive_ip = |d: &mut IntDev<'_>, ipv: ExprId| -> ExprId {
        let i = d.succ(ipv);
        alt_arrow_chain_ty(d, p, mat, i, zero_n, mp)
    };
    let ip_at_zero = |d: &mut IntDev<'_>| -> ExprId { alt_one_zero(d, p, mat, mp, ih) };
    let ip_at_succ = |d: &mut IntDev<'_>, ipp: ExprId, _ih2: ExprId| -> ExprId {
        alt_ge2_zero(d, p, mat, ipp, mp, ih)
    };
    d.induct(
        &motive_ip,
        &ip_at_zero,
        &|d, ipp, ih2| ip_at_succ(d, ipp, ih2),
        ip,
    )
}

/// `i = succ ip` branch of [`alt_step`]'s outer case split: further
/// case-splits `j` (`j = 0`, the symmetric branch, vs `j = succ jp`, LEAF 1).
fn alt_branch_i_succ(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    ip: ExprId,
    mp: ExprId,
    ih: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let i = d.succ(ip);

    let motive_j =
        |d: &mut IntDev<'_>, j: ExprId| -> ExprId { alt_arrow_chain_ty(d, p, mat, i, j, mp) };
    let j_at_zero = |d: &mut IntDev<'_>| -> ExprId { alt_succ_zero(d, p, mat, ip, mp, ih) };
    let j_at_succ = |d: &mut IntDev<'_>, jp: ExprId, _ihj: ExprId| -> ExprId {
        alt_succ_succ(d, p, mat, ip, jp, mp, ih)
    };

    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let per_j = d.induct(
        &motive_j,
        &j_at_zero,
        &|d, jp, ihj| j_at_succ(d, jp, ihj),
        j,
    );
    d.lam_fv(j_fv, nat, per_j)
}

/// `∀ A i j, ...` at a fixed dimension `m` — [`declare_det_alternating`]'s
/// motive.
fn alt_motive_at(d: &mut IntDev<'_>, p: RatPrelude, m: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let a_fv = d.fresh_fvar();
    let mat = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let hne = alt_hyp_ne(d, i, j);
    let hbi = ble_true_ty(d, i, m);
    let hbj = ble_true_ty(d, j, m);
    let hrow = alt_row_eq_ty(d, mat, i, j);
    let sm = d.succ(m);
    let det_val = rdet(d, p, mat, sm);
    let zero_r = rzero(d, p);
    let concl = req(d, det_val, zero_r);

    let arr = d.arrow(hrow, concl);
    let arr = d.arrow(hbj, arr);
    let arr = d.arrow(hbi, arr);
    let arr = d.arrow(hne, arr);
    let over_j = d.pi_fv(j_fv, nat, arr);
    let over_i = d.pi_fv(i_fv, nat, over_j);
    d.pi_fv(a_fv, mty, over_i)
}

/// `m = 0` base case: `ble i 0 = true` and `ble j 0 = true` force `i = j =
/// 0`, contradicting `hne`.
fn alt_base(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let a_fv = d.fresh_fvar();
    let mat = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let zero_n = d.zero();
    let hne_ty = alt_hyp_ne(d, i, j);
    let hbi_ty = ble_true_ty(d, i, zero_n);
    let hbj_ty = ble_true_ty(d, j, zero_n);
    let hrow_ty = alt_row_eq_ty(d, mat, i, j);
    let one_n = d.succ(zero_n);
    let det_val = rdet(d, p, mat, one_n);
    let zero_r = rzero(d, p);
    let target = req(d, det_val, zero_r);

    let hne_fv = d.fresh_fvar();
    let hne = d.kernel().fvar(hne_fv);
    let hbi_fv = d.fresh_fvar();
    let hbi = d.kernel().fvar(hbi_fv);
    let hbj_fv = d.fresh_fvar();
    let hbj = d.kernel().fvar(hbj_fv);
    let hrow_fv = d.fresh_fvar();

    let hi0 = nat_eq_zero_of_ble_zero_true(d, i, hbi);
    let hj0 = nat_eq_zero_of_ble_zero_true(d, j, hbj);
    let body = contradiction_of_eq_via_beq(d, i, j, zero_n, hi0, hj0, hne, target);

    let with_hrow = d.lam_fv(hrow_fv, hrow_ty, body);
    let with_hbj = d.lam_fv(hbj_fv, hbj_ty, with_hrow);
    let with_hbi = d.lam_fv(hbi_fv, hbi_ty, with_hbj);
    let with_hne = d.lam_fv(hne_fv, hne_ty, with_hbi);
    let over_j = d.lam_fv(j_fv, nat, with_hne);
    let over_i = d.lam_fv(i_fv, nat, over_j);
    d.lam_fv(a_fv, mty, over_i)
}

/// `m = succ mp` step: case-split `i`, then `j`, into the four shapes
/// described on [`RatPrelude::det_alternating`].
fn alt_step(d: &mut IntDev<'_>, p: RatPrelude, mp: ExprId, ih: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let a_fv = d.fresh_fvar();
    let mat = d.kernel().fvar(a_fv);

    let motive_i = |d: &mut IntDev<'_>, i: ExprId| -> ExprId { alt_inner_over_j(d, p, mat, i, mp) };
    let i_at_zero = |d: &mut IntDev<'_>| -> ExprId { alt_branch_i_zero(d, p, mat, mp, ih) };
    let i_at_succ = |d: &mut IntDev<'_>, ip: ExprId, _ihi: ExprId| -> ExprId {
        alt_branch_i_succ(d, p, mat, ip, mp, ih)
    };

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let per_i = d.induct(
        &motive_i,
        &i_at_zero,
        &|d, ip, ihi| i_at_succ(d, ip, ihi),
        i,
    );
    let over_i = d.lam_fv(i_fv, nat, per_i);
    d.lam_fv(a_fv, mty, over_i)
}

/// Admit `Rat.det_alternating` — see [`RatPrelude::det_alternating`] for the
/// statement and the proof outline.
fn declare_det_alternating(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let motive = |d: &mut IntDev<'_>, m: ExprId| -> ExprId { alt_motive_at(d, p, m) };
    let base = |d: &mut IntDev<'_>| -> ExprId { alt_base(d, p) };
    let step = |d: &mut IntDev<'_>, mp: ExprId, ih: ExprId| -> ExprId { alt_step(d, p, mp, ih) };

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let stmt = motive(d, m);
    let proof = d.induct(&motive, &base, &step, m);
    let ty = d.pi_fv(m_fv, nat, stmt);
    let value = d.lam_fv(m_fv, nat, proof);
    d.declare_theorem(p.det_alternating, ty, value)
}

// --- sign under a row swap (`matrix_det`, ADR-1310 step 3) -----------------
//
// `Rat.det_row_swap : det B (succ m) = neg (det A (succ m))`, where `B` is
// `A` with distinct rows `i`,`j` exchanged, stated EXTENSIONALLY (three
// pointwise hypotheses relating `B` to `A`) rather than via a named
// `matSwapRows` definition — the file's own rule, from its module doc: no
// statement here is an `Eq` between two `Nat → Nat → Rat` values, because
// `funext` is absent, so a matrix relationship is always a hypothesis, never
// a defined function related back through `det_congr`.
//
// The proof is the standard `det(A + swap) = 0` argument: build `C`, the
// matrix with BOTH rows `i` and `j` set to `A i + A j` (same function in both
// slots); `Rat.det_alternating` gives `det C = 0` directly (the two rows are
// literally equal). Expand `C` bilinearly in rows `i` and `j` via
// [`row_add_split`] (below) — additivity in a single row, built from THREE
// applications of `Rat.det_row_expansion` (the cofactor sum is linear in the
// row it expands along, since a minor never depends on the value of the row
// it deletes) plus `Rat.sumRange_add`/`Rat.sumRange_congr` and
// distributivity — giving four terms: both-rows-`A i`, both-rows-`A j`
// (each `0` by `det_alternating` again), row `i`=`A i`/row `j`=`A j` (which
// is `A` itself, pointwise), and row `i`=`A j`/row `j`=`A i` (the swap).
// `0 = 0 + det A + det B + 0` rearranges to `det B = neg (det A)` via
// `Rat.neg_eq_of_add_eq_zero` and `Rat.neg_neg`.
//
// **Contrary to ADR-1310's expectation, no NEW induction is needed here**:
// every fact this proof combines (`det_row_expansion`, `det_alternating`,
// `sumRange_add`, `sumRange_congr`, distributivity) is already
// dimension-general, so the whole argument is a straight-line term at a
// SYMBOLIC `m` — no case split on `i`/`j` beyond what `Nat.beq i j = false`
// already supplies directly. Row-multilinearity (`row_add_split`) did NOT
// exist and had to be built; `Rat.det_congr` WAS needed, twice (bridging the
// two "unmoved" terms of the four back to `A` and to the caller's `B`).

/// `rset_row(base, target, h) r c := if Nat.beq r target then h c else base
/// r c` — `base` with row `target` replaced by the function `h`. A pure
/// Rust-level term builder, never a registered kernel `Definition`: every
/// statement in this section is extensional (see the section doc above), so
/// nothing downstream needs this to have a name.
fn rset_row(d: &mut IntDev<'_>, base: ExprId, target: ExprId, h: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let cond = d.beq(r, target);
    let on_true = d.apply(h, &[c]);
    let base_rc = d.apply(base, &[r, c]);
    let body = bool_select_rat(d, cond, on_true, base_rc);
    let inner = d.lam_fv(c_fv, nat, body);
    d.lam_fv(r_fv, nat, inner)
}

/// `∀ c, rset_row(base,target,h) r c = h c`, given `hcond : Nat.beq r target
/// = true` (for ANY `r`, not necessarily syntactically `target` — the
/// hypothesis carries the identification).
fn rset_row_eval_true(
    d: &mut IntDev<'_>,
    base: ExprId,
    target: ExprId,
    h: ExprId,
    r: ExprId,
    hcond: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let cond = d.beq(r, target);
    let on_true = d.apply(h, &[c]);
    let base_rc = d.apply(base, &[r, c]);
    let sel = select_rat_true(d, cond, on_true, base_rc, hcond);
    d.lam_fv(c_fv, nat, sel)
}

/// `∀ c, rset_row(base,target,h) r c = base r c`, given `hcond : Nat.beq r
/// target = false`.
fn rset_row_eval_false(
    d: &mut IntDev<'_>,
    base: ExprId,
    target: ExprId,
    h: ExprId,
    r: ExprId,
    hcond: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let cond = d.beq(r, target);
    let on_true = d.apply(h, &[c]);
    let base_rc = d.apply(base, &[r, c]);
    let sel = select_rat_false(d, cond, on_true, base_rc, hcond);
    d.lam_fv(c_fv, nat, sel)
}

/// `∀ c, rset_row(base,target,h) target c = h c` — [`rset_row_eval_true`] at
/// the DIAGONAL, driven by `Nat.beq_refl` (needed because `target` is a
/// symbolic `Nat`, so `Nat.beq target target` does not iota-reduce).
fn rset_row_self(d: &mut IntDev<'_>, base: ExprId, target: ExprId, h: ExprId) -> ExprId {
    let np = d.prelude();
    let hcond = d.lemma(np.beq_refl, &[target]);
    rset_row_eval_true(d, base, target, h, target, hcond)
}

/// `rset_row(base,t,h)`, optionally wrapped by ONE further `rset_row` on a
/// DIFFERENT row (`outer = Some((outer_t, outer_v, _))`) — the shape every
/// matrix in this section takes: row `i` set, then row `j` set on top (or
/// vice versa), never more than two layers.
fn wrapped_matrix(
    d: &mut IntDev<'_>,
    base: ExprId,
    t: ExprId,
    h: ExprId,
    outer: Option<(ExprId, ExprId, ExprId)>,
) -> ExprId {
    let inner = rset_row(d, base, t, h);
    match outer {
        None => inner,
        Some((ot, ov, _)) => rset_row(d, inner, ot, ov),
    }
}

/// `∀ c, wrapped_matrix(base,t,h,outer) t c = h c`.
fn row_entry_eq(
    d: &mut IntDev<'_>,
    base: ExprId,
    t: ExprId,
    h: ExprId,
    outer: Option<(ExprId, ExprId, ExprId)>,
) -> ExprId {
    let nat = d.nat_ty();
    let self_eq = rset_row_self(d, base, t, h);
    match outer {
        None => self_eq,
        Some((ot, ov, h_ne)) => {
            let inner = rset_row(d, base, t, h);
            let other_eq = rset_row_eval_false(d, inner, ot, ov, t, h_ne);
            let wrapped = rset_row(d, inner, ot, ov);
            let c_fv = d.fresh_fvar();
            let c = d.kernel().fvar(c_fv);
            let a_val = d.apply(wrapped, &[t, c]);
            let b_val = d.apply(inner, &[t, c]);
            let c_val = d.apply(h, &[c]);
            let step1 = d.apply(other_eq, &[c]);
            let step2 = d.apply(self_eq, &[c]);
            let chained = rtrans(d, a_val, b_val, c_val, step1, step2);
            d.lam_fv(c_fv, nat, chained)
        }
    }
}

/// `∀ r c, matMinor(rset_row(base,target,h)) target q r c = matMinor(base)
/// target q r c` — deleting row `target` erases any dependence on what row
/// `target` was set to, via [`RatPrelude::beq_mat_skip_left`] (`matSkip
/// target r` never equals `target`) and [`select_rat_false`].
fn minor_indep_of_set_row(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    base: ExprId,
    target: ExprId,
    h: ExprId,
    q: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let skip_r = rmat_skip(d, p, target, r);
    let skip_c = rmat_skip(d, p, q, c);
    let cond = d.beq(skip_r, target);
    let heq = d.lemma(p.beq_mat_skip_left, &[target, r]);
    let on_true = d.apply(h, &[skip_c]);
    let base_val = d.apply(base, &[skip_r, skip_c]);
    let sel = select_rat_false(d, cond, on_true, base_val, heq);
    let inner = d.lam_fv(c_fv, nat, sel);
    d.lam_fv(r_fv, nat, inner)
}

/// `∀ r c, matMinor(wrapped_matrix(base,t,h,Some((outer_t,outer_v,_)))) t q r
/// c = matMinor(rset_row(base,outer_t,outer_v)) t q r c` — the ONE-LAYER-BURIED
/// version of [`minor_indep_of_set_row`]: the row-`t` minor still never sees
/// row `t`'s own value, even wrapped by one further row set on top, because
/// the inner reduction (`beq_mat_skip_left` again) lifts through the outer
/// `bool_select_rat`'s `on_false` slot by a single congruence step.
#[allow(clippy::too_many_arguments)]
fn minor_indep_of_set_row_wrapped(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    base: ExprId,
    t: ExprId,
    h: ExprId,
    outer_t: ExprId,
    outer_v: ExprId,
    q: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let skip_r = rmat_skip(d, p, t, r);
    let skip_c = rmat_skip(d, p, q, c);

    let inner_matrix = rset_row(d, base, t, h);
    let x_inner = d.apply(inner_matrix, &[skip_r, skip_c]);
    let base_val = d.apply(base, &[skip_r, skip_c]);

    let inner_cond = d.beq(skip_r, t);
    let inner_heq = d.lemma(p.beq_mat_skip_left, &[t, r]);
    let inner_on_true = d.apply(h, &[skip_c]);
    let inner_reduces = select_rat_false(d, inner_cond, inner_on_true, base_val, inner_heq);

    let outer_cond = d.beq(skip_r, outer_t);
    let outer_on_true = d.apply(outer_v, &[skip_c]);
    let lifted = rcongr(d, x_inner, base_val, inner_reduces, &|d, v| {
        bool_select_rat(d, outer_cond, outer_on_true, v)
    });

    let inner_body = d.lam_fv(c_fv, nat, lifted);
    d.lam_fv(r_fv, nat, inner_body)
}

/// The minor-independence pointwise fact for [`row_add_split`], dispatched
/// on `outer`. Returns `(base_for_minor, proof)`: `base_for_minor` is what
/// the row-`t` minor reduces to (`base` unwrapped, or `base` with the outer
/// row set, wrapped) — the SAME value regardless of `h`, which is the whole
/// point.
fn row_minor_indep(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    base: ExprId,
    t: ExprId,
    h: ExprId,
    outer: Option<(ExprId, ExprId, ExprId)>,
    q: ExprId,
) -> (ExprId, ExprId) {
    match outer {
        None => {
            let proof = minor_indep_of_set_row(d, p, base, t, h, q);
            (base, proof)
        }
        Some((ot, ov, _)) => {
            let wrapped_base = rset_row(d, base, ot, ov);
            let proof = minor_indep_of_set_row_wrapped(d, p, base, t, h, ot, ov, q);
            (wrapped_base, proof)
        }
    }
}

/// Row-`t` ADDITIVITY: `det(wrapped_matrix(base,t,λc.f c+g c,outer))(succ m)
/// = det(wrapped_matrix(base,t,f,outer))(succ m) +
/// det(wrapped_matrix(base,t,g,outer))(succ m)`, given `ble t m = true`.
/// Returns `(m_sum, m_f, m_g, proof)`.
///
/// The minor at row `t` never depends on what row `t` itself holds
/// ([`row_minor_indep`]), so all three matrices share every cofactor
/// determinant TERMWISE — the whole additivity is `Rat.det_row_expansion`
/// applied three times, plus `Rat.sumRange_add`/`Rat.sumRange_congr` and
/// distributivity. No new induction: `det_row_expansion` is already
/// dimension-general.
#[allow(clippy::too_many_arguments)]
fn row_add_split(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    base: ExprId,
    t: ExprId,
    f: ExprId,
    g: ExprId,
    outer: Option<(ExprId, ExprId, ExprId)>,
    m: ExprId,
    hble_t: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId) {
    let nat = d.nat_ty();
    let f_plus_g = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let fc = d.apply(f, &[c]);
        let gc = d.apply(g, &[c]);
        let body = radd(d, fc, gc);
        d.lam_fv(c_fv, nat, body)
    };

    let m_sum = wrapped_matrix(d, base, t, f_plus_g, outer);
    let m_f = wrapped_matrix(d, base, t, f, outer);
    let m_g = wrapped_matrix(d, base, t, g, outer);

    let sm = d.succ(m);
    let exp_sum = {
        let l = d.lemma(p.det_row_expansion, &[m, m_sum, t]);
        d.apply(l, &[hble_t])
    };
    let exp_f = {
        let l = d.lemma(p.det_row_expansion, &[m, m_f, t]);
        d.apply(l, &[hble_t])
    };
    let exp_g = {
        let l = d.lemma(p.det_row_expansion, &[m, m_g, t]);
        d.apply(l, &[hble_t])
    };

    let summand_sum_fn = row_expansion_fn(d, p, m_sum, t, m);
    let summand_f_fn = row_expansion_fn(d, p, m_f, t, m);
    let summand_g_fn = row_expansion_fn(d, p, m_g, t, m);

    let entry_sum_all = row_entry_eq(d, base, t, f_plus_g, outer);
    let entry_f_all = row_entry_eq(d, base, t, f, outer);
    let entry_g_all = row_entry_eq(d, base, t, g, outer);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let entry_sum_q = d.apply(entry_sum_all, &[q]);
    let entry_f_q = d.apply(entry_f_all, &[q]);
    let entry_g_q = d.apply(entry_g_all, &[q]);

    let (base_for_minor, minor_sum_pw) = row_minor_indep(d, p, base, t, f_plus_g, outer, q);
    let (_, minor_f_pw) = row_minor_indep(d, p, base, t, f, outer, q);
    let (_, minor_g_pw) = row_minor_indep(d, p, base, t, g, outer, q);

    let minor_m_sum = rmat_minor_of(d, p, m_sum, t, q);
    let minor_m_f = rmat_minor_of(d, p, m_f, t, q);
    let minor_m_g = rmat_minor_of(d, p, m_g, t, q);
    let minor_base = rmat_minor_of(d, p, base_for_minor, t, q);

    let det_ms = rdet(d, p, minor_m_sum, m);
    let det_mf = rdet(d, p, minor_m_f, m);
    let det_mg = rdet(d, p, minor_m_g, m);
    let dbase = rdet(d, p, minor_base, m);

    let det_minor_sum_eq = {
        let l = d.lemma(p.det_congr, &[m, minor_m_sum, minor_base]);
        d.apply(l, &[minor_sum_pw])
    };
    let det_minor_f_eq = {
        let l = d.lemma(p.det_congr, &[m, minor_m_f, minor_base]);
        d.apply(l, &[minor_f_pw])
    };
    let det_minor_g_eq = {
        let l = d.lemma(p.det_congr, &[m, minor_m_g, minor_base]);
        d.apply(l, &[minor_g_pw])
    };

    let sign = {
        let idx = d.add(q, t);
        ralt_sign(d, p, idx)
    };

    let fq = d.apply(f, &[q]);
    let gq = d.apply(g, &[q]);
    let fq_plus_gq = radd(d, fq, gq);

    // LHS chain: `App(summand_sum_fn,q)` (defeq `l0`) down to `l4`.
    let entry_ms_raw = d.apply(m_sum, &[t, q]);
    let l0 = {
        let prod = rmul(d, entry_ms_raw, det_ms);
        rmul(d, sign, prod)
    };
    let l1 = {
        let prod = rmul(d, fq_plus_gq, det_ms);
        rmul(d, sign, prod)
    };
    let s1 = rcongr(d, entry_ms_raw, fq_plus_gq, entry_sum_q, &|d, v| {
        let prod = rmul(d, v, det_ms);
        rmul(d, sign, prod)
    });
    let l2 = {
        let prod = rmul(d, fq_plus_gq, dbase);
        rmul(d, sign, prod)
    };
    let s2 = rcongr(d, det_ms, dbase, det_minor_sum_eq, &|d, v| {
        let prod = rmul(d, fq_plus_gq, v);
        rmul(d, sign, prod)
    });
    let fq_dbase = rmul(d, fq, dbase);
    let gq_dbase = rmul(d, gq, dbase);
    let raw_sum = radd(d, fq_dbase, gq_dbase);
    let l3 = rmul(d, sign, raw_sum);
    let s3 = {
        let rd = d.lemma(p.right_distrib, &[fq, gq, dbase]);
        let fq_plus_gq_dbase = rmul(d, fq_plus_gq, dbase);
        rcongr(d, fq_plus_gq_dbase, raw_sum, rd, &|d, v| rmul(d, sign, v))
    };
    let sign_fq_dbase = rmul(d, sign, fq_dbase);
    let sign_gq_dbase = rmul(d, sign, gq_dbase);
    let l4 = radd(d, sign_fq_dbase, sign_gq_dbase);
    let s4 = d.lemma(p.left_distrib, &[sign, fq_dbase, gq_dbase]);
    let (_e1, lhs_proof) = rchain(d, l0, &[(l1, s1), (l2, s2), (l3, s3), (l4, s4)]);

    // `f`-side reduction: `App(summand_f_fn,q)` down to `sign_fq_dbase`.
    let entry_mf_raw = d.apply(m_f, &[t, q]);
    let rf0 = {
        let prod = rmul(d, entry_mf_raw, det_mf);
        rmul(d, sign, prod)
    };
    let sf1 = rcongr(d, entry_mf_raw, fq, entry_f_q, &|d, v| {
        let prod = rmul(d, v, det_mf);
        rmul(d, sign, prod)
    });
    let rf1 = {
        let prod = rmul(d, fq, det_mf);
        rmul(d, sign, prod)
    };
    let sf2 = rcongr(d, det_mf, dbase, det_minor_f_eq, &|d, v| {
        let prod = rmul(d, fq, v);
        rmul(d, sign, prod)
    });
    let (_ef, rf_proof) = rchain(d, rf0, &[(rf1, sf1), (sign_fq_dbase, sf2)]);

    // `g`-side reduction: `App(summand_g_fn,q)` down to `sign_gq_dbase`.
    let entry_mg_raw = d.apply(m_g, &[t, q]);
    let rg0 = {
        let prod = rmul(d, entry_mg_raw, det_mg);
        rmul(d, sign, prod)
    };
    let sg1 = rcongr(d, entry_mg_raw, gq, entry_g_q, &|d, v| {
        let prod = rmul(d, v, det_mg);
        rmul(d, sign, prod)
    });
    let rg1 = {
        let prod = rmul(d, gq, det_mg);
        rmul(d, sign, prod)
    };
    let sg2 = rcongr(d, det_mg, dbase, det_minor_g_eq, &|d, v| {
        let prod = rmul(d, gq, v);
        rmul(d, sign, prod)
    });
    let (_eg, rg_proof) = rchain(d, rg0, &[(rg1, sg1), (sign_gq_dbase, sg2)]);

    // Combine: `rf0 + rg0 = l4`.
    let rhs_start = radd(d, rf0, rg0);
    let mid = radd(d, sign_fq_dbase, rg0);
    let step_a = rcongr(d, rf0, sign_fq_dbase, rf_proof, &|d, v| radd(d, v, rg0));
    let step_b = rcongr(d, rg0, sign_gq_dbase, rg_proof, &|d, v| {
        radd(d, sign_fq_dbase, v)
    });
    let (_e2, combined_proof) = rchain(d, rhs_start, &[(mid, step_a), (l4, step_b)]);

    let rhs_symm = rsymm(d, rhs_start, l4, combined_proof);
    let pointwise_q = rtrans(d, l0, l4, rhs_start, lhs_proof, rhs_symm);
    let pointwise = d.lam_fv(q_fv, nat, pointwise_q);

    let combined_fn = {
        let q2_fv = d.fresh_fvar();
        let q2 = d.kernel().fvar(q2_fv);
        let fq2 = d.apply(summand_f_fn, &[q2]);
        let gq2 = d.apply(summand_g_fn, &[q2]);
        let body = radd(d, fq2, gq2);
        d.lam_fv(q2_fv, nat, body)
    };

    let sum_congr = {
        let l = d.lemma(p.sum_range_congr, &[summand_sum_fn, combined_fn, sm]);
        d.apply(l, &[pointwise])
    };
    let sum_add = d.lemma(p.sum_range_add, &[summand_f_fn, summand_g_fn, sm]);

    let det_msum = rdet(d, p, m_sum, sm);
    let sr_sum = rsum_range(d, p, summand_sum_fn, sm);
    let sr_combined = rsum_range(d, p, combined_fn, sm);
    let det_mf_val = rdet(d, p, m_f, sm);
    let det_mg_val = rdet(d, p, m_g, sm);
    let sr_f = rsum_range(d, p, summand_f_fn, sm);
    let sr_g = rsum_range(d, p, summand_g_fn, sm);
    let sr_f_plus_g = radd(d, sr_f, sr_g);

    let step4a = rsymm(d, det_mf_val, sr_f, exp_f);
    let step4b = rsymm(d, det_mg_val, sr_g, exp_g);
    let final_target = radd(d, det_mf_val, det_mg_val);
    let step4 = {
        let mid4 = radd(d, det_mf_val, sr_g);
        let sa = rcongr(d, sr_f, det_mf_val, step4a, &|d, v| radd(d, v, sr_g));
        let sb = rcongr(d, sr_g, det_mg_val, step4b, &|d, v| radd(d, det_mf_val, v));
        let (_e, chained) = rchain(d, sr_f_plus_g, &[(mid4, sa), (final_target, sb)]);
        chained
    };

    let (_e, overall) = rchain(
        d,
        det_msum,
        &[
            (sr_sum, exp_sum),
            (sr_combined, sum_congr),
            (sr_f_plus_g, sum_add),
            (final_target, step4),
        ],
    );

    (m_sum, m_f, m_g, overall)
}

/// `∀ c, rset_row(rset_row(base,i,h),j,h) i c = rset_row(rset_row(base,i,h),j,h)
/// j c` — BOTH rows are the SAME function `h`, so `Rat.det_alternating`
/// applies directly.
fn double_set_same_row_eq(
    d: &mut IntDev<'_>,
    base: ExprId,
    i: ExprId,
    j: ExprId,
    h: ExprId,
    hne: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let inner = rset_row(d, base, i, h);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let m = rset_row(d, inner, j, h);
    let mi_c = d.apply(m, &[i, c]);
    let mj_c = d.apply(m, &[j, c]);
    let hc = d.apply(h, &[c]);
    let inner_ic = d.apply(inner, &[i, c]);

    let step_outer = {
        let ev = rset_row_eval_false(d, inner, j, h, i, hne);
        d.apply(ev, &[c])
    };
    let step_inner = {
        let ev = rset_row_self(d, base, i, h);
        d.apply(ev, &[c])
    };
    let (_e1, mi_eq_hc) = rchain(d, mi_c, &[(inner_ic, step_outer), (hc, step_inner)]);

    let mj_eq_hc = {
        let ev = rset_row_self(d, inner, j, h);
        d.apply(ev, &[c])
    };
    let hc_eq_mj = rsymm(d, mj_c, hc, mj_eq_hc);

    let (_e2, chained) = rchain(d, mi_c, &[(hc, mi_eq_hc), (mj_c, hc_eq_mj)]);
    d.lam_fv(c_fv, nat, chained)
}

/// `∀ r c, rset_row(rset_row(A,i,λc.A i c),j,λc.A j c) r c = A r c` —
/// replacing rows `i` and `j` by their OWN current values is a NO-OP,
/// pointwise, for EVERY `r` (including `r = i` or `r = j`): a `Bool.rec` case
/// split on `Nat.beq r j`, then (in the `false` branch) `Nat.beq r i`. Each
/// `true` branch uses `Nat.eq_of_beq_eq_true` to rewrite the row index back
/// to `r` via [`nat_eq_to_rat`]; the innermost `false` branch is direct.
fn double_set_own_rows_noop(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    i: ExprId,
    j: ExprId,
) -> ExprId {
    let _ = p;
    let np = d.prelude();
    let nat = d.nat_ty();
    let fi = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let body = d.apply(a, &[i, c]);
        d.lam_fv(c_fv, nat, body)
    };
    let fj = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let body = d.apply(a, &[j, c]);
        d.lam_fv(c_fv, nat, body)
    };
    let inner = rset_row(d, a, i, fi);
    let m = rset_row(d, inner, j, fj);

    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let cond_j = d.beq(r, j);
    let mr_c = d.apply(m, &[r, c]);
    let ar_c = d.apply(a, &[r, c]);
    let target_ty = req(d, mr_c, ar_c);

    let at_true = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let l7236_bv = d.bool_true();
        let hyp_ty = d.bool_eq(cond_j, l7236_bv);
        let step1 = {
            let ev = rset_row_eval_true(d, inner, j, fj, r, h);
            d.apply(ev, &[c])
        };
        let aj_c = d.apply(a, &[j, c]);
        let r_eq_j = {
            let l = d.lemma(np.eq_of_beq_eq_true, &[r, j]);
            d.apply(l, &[h])
        };
        let ar_eq_aj = nat_eq_to_rat(d, r, j, r_eq_j, &|d, x| d.apply(a, &[x, c]));
        let aj_eq_ar = rsymm(d, ar_c, aj_c, ar_eq_aj);
        let (_e, chained) = rchain(d, mr_c, &[(aj_c, step1), (ar_c, aj_eq_ar)]);
        d.lam_fv(h_fv, hyp_ty, chained)
    };
    let at_false = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let l7254_bv = d.bool_false();
        let hyp_ty = d.bool_eq(cond_j, l7254_bv);
        let step1 = {
            let ev = rset_row_eval_false(d, inner, j, fj, r, h);
            d.apply(ev, &[c])
        };
        let inner_rc = d.apply(inner, &[r, c]);

        let cond_i = d.beq(r, i);
        let inner_target = req(d, inner_rc, ar_c);
        let at_true2 = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let l7266_bv = d.bool_true();
            let hyp2_ty = d.bool_eq(cond_i, l7266_bv);
            let step2 = {
                let ev = rset_row_eval_true(d, a, i, fi, r, h2);
                d.apply(ev, &[c])
            };
            let ai_c = d.apply(a, &[i, c]);
            let r_eq_i = {
                let l = d.lemma(np.eq_of_beq_eq_true, &[r, i]);
                d.apply(l, &[h2])
            };
            let ar_eq_ai = nat_eq_to_rat(d, r, i, r_eq_i, &|d, x| d.apply(a, &[x, c]));
            let ai_eq_ar = rsymm(d, ar_c, ai_c, ar_eq_ai);
            let (_e, chained2) = rchain(d, inner_rc, &[(ai_c, step2), (ar_c, ai_eq_ar)]);
            d.lam_fv(h2_fv, hyp2_ty, chained2)
        };
        let at_false2 = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let l7284_bv = d.bool_false();
            let hyp2_ty = d.bool_eq(cond_i, l7284_bv);
            let ev = rset_row_eval_false(d, a, i, fi, r, h2);
            let step2 = d.apply(ev, &[c]);
            d.lam_fv(h2_fv, hyp2_ty, step2)
        };
        let inner_proof = bool_cases_eq(d, cond_i, inner_target, at_true2, at_false2);
        let chained_final = rtrans(d, mr_c, inner_rc, ar_c, step1, inner_proof);
        d.lam_fv(h_fv, hyp_ty, chained_final)
    };
    let body = bool_cases_eq(d, cond_j, target_ty, at_true, at_false);
    let inner2 = d.lam_fv(c_fv, nat, body);
    d.lam_fv(r_fv, nat, inner2)
}

/// `∀ r c, rset_row(rset_row(A,i,λc.A j c),j,λc.A i c) r c = B r c` — the
/// swap (row `i` gets `A`'s row `j`, row `j` gets `A`'s row `i`), bridged to
/// the CALLER's `B` via `h_row_i : ∀c, B i c = A j c`, `h_row_j : ∀c, B j c =
/// A i c`, and `h_other`. Same case-split shape as
/// [`double_set_own_rows_noop`], with the `r = i`/`r = j` branches routed
/// through `h_row_j`/`h_row_i` instead of a direct index rewrite, and the
/// "neither" branch through `h_other`.
#[allow(clippy::too_many_arguments)]
fn bridge_swap_to_b(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b_mat: ExprId,
    i: ExprId,
    j: ExprId,
    h_row_i: ExprId,
    h_row_j: ExprId,
    h_other: ExprId,
) -> ExprId {
    let _ = p;
    let np = d.prelude();
    let nat = d.nat_ty();
    let fj = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let body = d.apply(a, &[j, c]);
        d.lam_fv(c_fv, nat, body)
    };
    let fi = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let body = d.apply(a, &[i, c]);
        d.lam_fv(c_fv, nat, body)
    };
    let inner = rset_row(d, a, i, fj);
    let m = rset_row(d, inner, j, fi);

    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);

    let cond_j = d.beq(r, j);
    let mr_c = d.apply(m, &[r, c]);
    let br_c = d.apply(b_mat, &[r, c]);
    let target_ty = req(d, mr_c, br_c);

    let at_true = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let l7348_bv = d.bool_true();
        let hyp_ty = d.bool_eq(cond_j, l7348_bv);
        let step1 = {
            let ev = rset_row_eval_true(d, inner, j, fi, r, h);
            d.apply(ev, &[c])
        };
        let ai_c = d.apply(a, &[i, c]);
        let r_eq_j = {
            let l = d.lemma(np.eq_of_beq_eq_true, &[r, j]);
            d.apply(l, &[h])
        };
        let br_eq_bj = nat_eq_to_rat(d, r, j, r_eq_j, &|d, x| d.apply(b_mat, &[x, c]));
        let bj_c = d.apply(b_mat, &[j, c]);
        let bj_eq_ai = d.apply(h_row_j, &[c]);
        let (_e, br_eq_ai) = rchain(d, br_c, &[(bj_c, br_eq_bj), (ai_c, bj_eq_ai)]);
        let ai_eq_br = rsymm(d, br_c, ai_c, br_eq_ai);
        let (_e2, chained) = rchain(d, mr_c, &[(ai_c, step1), (br_c, ai_eq_br)]);
        d.lam_fv(h_fv, hyp_ty, chained)
    };
    let at_false = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let l7369_bv = d.bool_false();
        let hyp_ty = d.bool_eq(cond_j, l7369_bv);
        let step1 = {
            let ev = rset_row_eval_false(d, inner, j, fi, r, h);
            d.apply(ev, &[c])
        };
        let inner_rc = d.apply(inner, &[r, c]);

        let cond_i = d.beq(r, i);
        let inner_target = req(d, inner_rc, br_c);
        let at_true2 = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let l7381_bv = d.bool_true();
            let hyp2_ty = d.bool_eq(cond_i, l7381_bv);
            let step2 = {
                let ev = rset_row_eval_true(d, a, i, fj, r, h2);
                d.apply(ev, &[c])
            };
            let aj_c = d.apply(a, &[j, c]);
            let r_eq_i = {
                let l = d.lemma(np.eq_of_beq_eq_true, &[r, i]);
                d.apply(l, &[h2])
            };
            let br_eq_bi = nat_eq_to_rat(d, r, i, r_eq_i, &|d, x| d.apply(b_mat, &[x, c]));
            let bi_c = d.apply(b_mat, &[i, c]);
            let bi_eq_aj = d.apply(h_row_i, &[c]);
            let (_e, br_eq_aj) = rchain(d, br_c, &[(bi_c, br_eq_bi), (aj_c, bi_eq_aj)]);
            let aj_eq_br = rsymm(d, br_c, aj_c, br_eq_aj);
            let (_e2, chained2) = rchain(d, inner_rc, &[(aj_c, step2), (br_c, aj_eq_br)]);
            d.lam_fv(h2_fv, hyp2_ty, chained2)
        };
        let at_false2 = {
            let h2_fv = d.fresh_fvar();
            let h2 = d.kernel().fvar(h2_fv);
            let l7402_bv = d.bool_false();
            let hyp2_ty = d.bool_eq(cond_i, l7402_bv);
            let ev = rset_row_eval_false(d, a, i, fj, r, h2);
            let step2 = d.apply(ev, &[c]);
            let ar_c = d.apply(a, &[r, c]);
            let other = {
                let l = d.apply(h_other, &[r]);
                let l = d.apply(l, &[h2, h]);
                d.apply(l, &[c])
            };
            let ar_eq_br = rsymm(d, br_c, ar_c, other);
            let (_e, chained2) = rchain(d, inner_rc, &[(ar_c, step2), (br_c, ar_eq_br)]);
            d.lam_fv(h2_fv, hyp2_ty, chained2)
        };
        let inner_proof = bool_cases_eq(d, cond_i, inner_target, at_true2, at_false2);
        let chained_final = rtrans(d, mr_c, inner_rc, br_c, step1, inner_proof);
        d.lam_fv(h_fv, hyp_ty, chained_final)
    };
    let body = bool_cases_eq(d, cond_j, target_ty, at_true, at_false);
    let inner2 = d.lam_fv(c_fv, nat, body);
    d.lam_fv(r_fv, nat, inner2)
}

/// `∀ c, B i c = A j c` — the swap's row-`i` hypothesis.
pub(super) fn swap_row_i_ty(
    d: &mut IntDev<'_>,
    a: ExprId,
    b_mat: ExprId,
    i: ExprId,
    j: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let bi = d.apply(b_mat, &[i, c]);
    let aj = d.apply(a, &[j, c]);
    let eq = req(d, bi, aj);
    d.pi_fv(c_fv, nat, eq)
}

/// `∀ c, B j c = A i c` — the swap's row-`j` hypothesis.
pub(super) fn swap_row_j_ty(
    d: &mut IntDev<'_>,
    a: ExprId,
    b_mat: ExprId,
    i: ExprId,
    j: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let bj = d.apply(b_mat, &[j, c]);
    let ai = d.apply(a, &[i, c]);
    let eq = req(d, bj, ai);
    d.pi_fv(c_fv, nat, eq)
}

/// `∀ r, Nat.beq r i = false → Nat.beq r j = false → ∀ c, B r c = A r c` —
/// every OTHER row of `B` is unchanged.
pub(super) fn swap_other_ty(
    d: &mut IntDev<'_>,
    a: ExprId,
    b_mat: ExprId,
    i: ExprId,
    j: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let h1 = alt_hyp_ne(d, r, i);
    let h2 = alt_hyp_ne(d, r, j);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let br = d.apply(b_mat, &[r, c]);
    let ar = d.apply(a, &[r, c]);
    let eq = req(d, br, ar);
    let inner = d.pi_fv(c_fv, nat, eq);
    let arr = d.arrow(h2, inner);
    let arr = d.arrow(h1, arr);
    d.pi_fv(r_fv, nat, arr)
}

/// Admit `Rat.det_row_swap` — see [`RatPrelude::det_row_swap`] for the
/// statement and the proof outline (the section doc above has the full
/// argument).
fn declare_det_row_swap(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b_mat = d.kernel().fvar(b_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let hne_ty = alt_hyp_ne(d, i, j);
    let hbi_ty = ble_true_ty(d, i, m);
    let hbj_ty = ble_true_ty(d, j, m);
    let h_row_i_ty = swap_row_i_ty(d, a, b_mat, i, j);
    let h_row_j_ty = swap_row_j_ty(d, a, b_mat, i, j);
    let h_other_ty = swap_other_ty(d, a, b_mat, i, j);

    let sm0 = d.succ(m);
    let det_b_ty = rdet(d, p, b_mat, sm0);
    let det_a_ty = rdet(d, p, a, sm0);
    let neg_det_a_ty = rneg(d, det_a_ty);
    let concl_ty = req(d, det_b_ty, neg_det_a_ty);

    let arr = d.arrow(h_other_ty, concl_ty);
    let arr = d.arrow(h_row_j_ty, arr);
    let arr = d.arrow(h_row_i_ty, arr);
    let arr = d.arrow(hbj_ty, arr);
    let arr = d.arrow(hbi_ty, arr);
    let arr = d.arrow(hne_ty, arr);
    let over_j = d.pi_fv(j_fv, nat, arr);
    let over_i = d.pi_fv(i_fv, nat, over_j);
    let over_b = d.pi_fv(b_fv, mty, over_i);
    let over_a = d.pi_fv(a_fv, mty, over_b);
    let ty = d.pi_fv(m_fv, nat, over_a);

    // --- the proof value, mirroring the Pi nesting above ---
    let hne_fv = d.fresh_fvar();
    let hne = d.kernel().fvar(hne_fv);
    let hbi_fv = d.fresh_fvar();
    let hbi = d.kernel().fvar(hbi_fv);
    let hbj_fv = d.fresh_fvar();
    let hbj = d.kernel().fvar(hbj_fv);
    let h_row_i_fv = d.fresh_fvar();
    let h_row_i = d.kernel().fvar(h_row_i_fv);
    let h_row_j_fv = d.fresh_fvar();
    let h_row_j = d.kernel().fvar(h_row_j_fv);
    let h_other_fv = d.fresh_fvar();
    let h_other = d.kernel().fvar(h_other_fv);

    let f_fn = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let body = d.apply(a, &[i, c]);
        d.lam_fv(c_fv, nat, body)
    };
    let g_fn = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let body = d.apply(a, &[j, c]);
        d.lam_fv(c_fv, nat, body)
    };
    let h_fn = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let ai_c = d.apply(a, &[i, c]);
        let aj_c = d.apply(a, &[j, c]);
        let body = radd(d, ai_c, aj_c);
        d.lam_fv(c_fv, nat, body)
    };

    let a1 = rset_row(d, a, i, h_fn);

    // Split row `j` on `A1` (row `i` already `H`, row `j` unsplit).
    let (c_mat, d1, d2, proof_c_eq_d1d2) = row_add_split(d, p, a1, j, f_fn, g_fn, None, m, hbj);

    let hrow_c = double_set_same_row_eq(d, a, i, j, h_fn, hne);
    let det_c_zero = {
        let l = d.lemma(p.det_alternating, &[m, c_mat, i, j]);
        d.apply(l, &[hne, hbi, hbj, hrow_c])
    };

    let sm = d.succ(m);
    let zero_r = rzero(d, p);
    let det_d1 = rdet(d, p, d1, sm);
    let det_d2 = rdet(d, p, d2, sm);
    let sum_d1d2 = radd(d, det_d1, det_d2);
    let det_c = rdet(d, p, c_mat, sm);
    let sum_eq_c = rsymm(d, det_c, sum_d1d2, proof_c_eq_d1d2);
    let sum_eq_zero = rtrans(d, sum_d1d2, det_c, zero_r, sum_eq_c, det_c_zero);

    // Split row `i` under the "row `j` = `A i`" wrap (the `D1` shape):
    // both-rows-`A i` (zero) and the swap.
    let (_m_sum2, z1, swap1, proof2) =
        row_add_split(d, p, a, i, f_fn, g_fn, Some((j, f_fn, hne)), m, hbi);
    let hrow_z1 = double_set_same_row_eq(d, a, i, j, f_fn, hne);
    let det_z1_zero = {
        let l = d.lemma(p.det_alternating, &[m, z1, i, j]);
        d.apply(l, &[hne, hbi, hbj, hrow_z1])
    };

    // Split row `i` under the "row `j` = `A j`" wrap (the `D2` shape): the
    // untouched matrix (`A` itself) and both-rows-`A j` (zero).
    let (_m_sum3, id2, z2, proof3) =
        row_add_split(d, p, a, i, f_fn, g_fn, Some((j, g_fn, hne)), m, hbi);
    let hrow_z2 = double_set_same_row_eq(d, a, i, j, g_fn, hne);
    let det_z2_zero = {
        let l = d.lemma(p.det_alternating, &[m, z2, i, j]);
        d.apply(l, &[hne, hbi, hbj, hrow_z2])
    };

    // `det_d1 = det_z1 + det_swap1 = 0 + det_swap1 = det_swap1`.
    let det_swap1 = rdet(d, p, swap1, sm);
    let det_z1 = rdet(d, p, z1, sm);
    let det_z1_plus_swap1 = radd(d, det_z1, det_swap1);
    let zero_plus_swap1 = radd(d, zero_r, det_swap1);
    let s_z1 = rcongr(d, det_z1, zero_r, det_z1_zero, &|d, v| {
        radd(d, v, det_swap1)
    });
    let s_za = d.lemma(p.zero_add, &[det_swap1]);
    let (_e, d1_collapse) = rchain(
        d,
        det_z1_plus_swap1,
        &[(zero_plus_swap1, s_z1), (det_swap1, s_za)],
    );
    let det_d1_eq_swap1 = rtrans(d, det_d1, det_z1_plus_swap1, det_swap1, proof2, d1_collapse);

    // `det_d2 = det_id2 + det_z2 = det_id2 + 0 = det_id2`.
    let det_id2 = rdet(d, p, id2, sm);
    let det_z2 = rdet(d, p, z2, sm);
    let det_id2_plus_z2 = radd(d, det_id2, det_z2);
    let id2_plus_zero = radd(d, det_id2, zero_r);
    let s_z2 = rcongr(d, det_z2, zero_r, det_z2_zero, &|d, v| radd(d, det_id2, v));
    let s_za2 = d.lemma(p.add_zero, &[det_id2]);
    let (_e, d2_collapse) = rchain(
        d,
        det_id2_plus_z2,
        &[(id2_plus_zero, s_z2), (det_id2, s_za2)],
    );
    let det_d2_eq_id2 = rtrans(d, det_d2, det_id2_plus_z2, det_id2, proof3, d2_collapse);

    // `sum_eq_zero : det_d1 + det_d2 = 0` becomes `det_swap1 + det_id2 = 0`.
    let swap1_plus_d2 = radd(d, det_swap1, det_d2);
    let swap1_plus_id2 = radd(d, det_swap1, det_id2);
    let s_sub1 = rcongr(d, det_d1, det_swap1, det_d1_eq_swap1, &|d, v| {
        radd(d, v, det_d2)
    });
    let s_sub2 = rcongr(d, det_d2, det_id2, det_d2_eq_id2, &|d, v| {
        radd(d, det_swap1, v)
    });
    let (_e, rewritten) = rchain(
        d,
        sum_d1d2,
        &[(swap1_plus_d2, s_sub1), (swap1_plus_id2, s_sub2)],
    );
    let rewritten_symm = rsymm(d, sum_d1d2, swap1_plus_id2, rewritten);
    let swap1_id2_eq_zero = rtrans(
        d,
        swap1_plus_id2,
        sum_d1d2,
        zero_r,
        rewritten_symm,
        sum_eq_zero,
    );

    // `det_swap1 + det_id2 = 0` gives `neg(det_swap1) = det_id2`, hence
    // `det_swap1 = neg(det_id2)` via `neg_neg`.
    let neg_swap1_eq_id2 = {
        let l = d.lemma(p.neg_eq_of_add_eq_zero, &[det_swap1, det_id2]);
        d.apply(l, &[swap1_id2_eq_zero])
    };
    let neg_swap1 = rneg(d, det_swap1);
    let neg_neg_swap1 = rneg(d, neg_swap1);
    let neg_det_id2 = rneg(d, det_id2);
    let neg_swap1_val = rneg(d, det_swap1);
    let step_nn_congr = rcongr(d, neg_swap1_val, det_id2, neg_swap1_eq_id2, &|d, v| {
        rneg(d, v)
    });
    let nn = d.lemma(p.neg_neg, &[det_swap1]);
    let nn_symm = rsymm(d, neg_neg_swap1, det_swap1, nn);
    let swap1_eq_neg_id2 = rtrans(
        d,
        det_swap1,
        neg_neg_swap1,
        neg_det_id2,
        nn_symm,
        step_nn_congr,
    );

    // Bridge `swap1` to the caller's `B`, and `id2` to `A`.

    let bridge_swap = bridge_swap_to_b(d, p, a, b_mat, i, j, h_row_i, h_row_j, h_other);
    let bridge_id2 = double_set_own_rows_noop(d, p, a, i, j);
    let congr_swap = {
        let l = d.lemma(p.det_congr, &[sm, swap1, b_mat]);
        d.apply(l, &[bridge_swap])
    };
    let congr_id2 = {
        let l = d.lemma(p.det_congr, &[sm, id2, a]);
        d.apply(l, &[bridge_id2])
    };

    let det_b = rdet(d, p, b_mat, sm);
    let det_a = rdet(d, p, a, sm);
    let det_b_eq_swap1 = rsymm(d, det_swap1, det_b, congr_swap);
    let det_b_eq_neg_id2 = rtrans(
        d,
        det_b,
        det_swap1,
        neg_det_id2,
        det_b_eq_swap1,
        swap1_eq_neg_id2,
    );
    let neg_id2_eq_neg_a = rcongr(d, det_id2, det_a, congr_id2, &|d, v| rneg(d, v));
    let neg_a = rneg(d, det_a);

    let goal_proof = rtrans(
        d,
        det_b,
        neg_det_id2,
        neg_a,
        det_b_eq_neg_id2,
        neg_id2_eq_neg_a,
    );

    let body = d.lam_fv(h_other_fv, h_other_ty, goal_proof);
    let body = d.lam_fv(h_row_j_fv, h_row_j_ty, body);
    let body = d.lam_fv(h_row_i_fv, h_row_i_ty, body);
    let body = d.lam_fv(hbj_fv, hbj_ty, body);
    let body = d.lam_fv(hbi_fv, hbi_ty, body);
    let body = d.lam_fv(hne_fv, hne_ty, body);
    let body = d.lam_fv(j_fv, nat, body);
    let body = d.lam_fv(i_fv, nat, body);
    let body = d.lam_fv(b_fv, mty, body);
    let body = d.lam_fv(a_fv, mty, body);
    let value = d.lam_fv(m_fv, nat, body);

    d.declare_theorem(p.det_row_swap, ty, value)
}

// --- row multilinearity (`matrix_det`, ADR-1440 / ADR-1310 step 4) ---------
//
// ADR-1310's route to `det (A·B) = det A · det B` is Cauchy–Binet: expand
// each row of `A·B` — which is a `Rat.sumRange` of rows of `B` — by
// LINEARITY IN THAT ROW, `n` times, and collect the result as a sum over all
// maps `[0,n) → [0,n)`. Nothing in this file supplied that linearity. What
// existed was [`row_add_split`], a PRIVATE two-term additivity phrased in
// terms of the private `rset_row`/`wrapped_matrix` builders and therefore
// unusable from outside; `Rat.det_row_swap` was its only consumer.
//
// The four theorems below are that gap, stated EXTENSIONALLY like everything
// else in this file (`funext` is absent, so a matrix relationship is a
// hypothesis, never a defined function):
//
// - `Rat.det_row_replaced` — the workhorse. Expanding along row `t` sees the
//   rest of the matrix ONLY through `A`'s minors, so a matrix agreeing with
//   `A` off row `t` has its determinant fixed by that row's own values.
// - `Rat.det_row_zero` — a zero row kills the determinant.
// - `Rat.det_row_smul` — scaling a row scales the determinant.
// - `Rat.det_row_multilinear` — row `t` given as a `sumRange` of `n`
//   coefficient rows splits into a `sumRange` of `n` determinants.
//
// **No new induction.** Every one is straight-line at a symbolic `m`:
// `Rat.det_row_expansion` is already dimension-general, and the only new
// observation is the one `row_add_split` already used privately — the row-`t`
// minor never mentions row `t`, because `Rat.beq_matSkip_left` says
// `matSkip t r` is never `t`. `Rat.det_congr` IS needed (once, inside
// `det_row_replaced`; every other theorem here reaches it through that one),
// which is a third data point against reading `det_alternating`'s "did not
// need it" as a rule.

/// `∀ c, M t c = h c` — row `t` of `M` is the function `h`.
fn row_value_ty(d: &mut IntDev<'_>, m_mat: ExprId, t: ExprId, h: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let lhs = d.apply(m_mat, &[t, c]);
    let rhs = d.apply(h, &[c]);
    let eq = req(d, lhs, rhs);
    d.pi_fv(c_fv, nat, eq)
}

/// `∀ r, Nat.beq r t = false → ∀ c, M r c = A r c` — every row of `M` OTHER
/// than `t` agrees with `A`. Same shape as [`swap_other_ty`], one excluded
/// row instead of two.
fn row_other_ty(d: &mut IntDev<'_>, a: ExprId, m_mat: ExprId, t: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let hne = alt_hyp_ne(d, r, t);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let mr = d.apply(m_mat, &[r, c]);
    let ar = d.apply(a, &[r, c]);
    let eq = req(d, mr, ar);
    let inner = d.pi_fv(c_fv, nat, eq);
    let arr = d.arrow(hne, inner);
    d.pi_fv(r_fv, nat, arr)
}

/// `fun q => altSign (q + t) * (h q * det (matMinor A t q) m)` — the cofactor
/// summand with the row entries taken from `h` and the minors from `A`.
/// [`row_expansion_fn`] is the special case `h := A t`, `A := M`.
fn row_replaced_fn(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    h: ExprId,
    t: ExprId,
    m: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let index = d.add(q, t);
    let sign = ralt_sign(d, p, index);
    let entry = d.apply(h, &[q]);
    let minor = rmat_minor_of(d, p, a, t, q);
    let sub = rdet(d, p, minor, m);
    let product = rmul(d, entry, sub);
    let body = rmul(d, sign, product);
    d.lam_fv(q_fv, nat, body)
}

/// `∀ r c, matMinor M t q r c = matMinor A t q r c`, from `hoff` — deleting
/// row `t` erases every dependence on row `t`, so two matrices agreeing OFF
/// row `t` have literally the same row-`t` minor.
///
/// `Rat.beq_matSkip_left` (`Nat.beq (matSkip t r) t = false`) discharges
/// `hoff`'s side condition at every `r`; the same fact
/// [`minor_indep_of_set_row`] uses, lifted from the private `rset_row`
/// encoding to an arbitrary hypothesis.
fn minor_agrees_off_row(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    t: ExprId,
    q: ExprId,
    hoff: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let skip_r = rmat_skip(d, p, t, r);
    let skip_c = rmat_skip(d, p, q, c);
    let hne = d.lemma(p.beq_mat_skip_left, &[t, r]);
    let inst = d.apply(hoff, &[skip_r, hne, skip_c]);
    let inner = d.lam_fv(c_fv, nat, inst);
    d.lam_fv(r_fv, nat, inner)
}

/// Admit `Rat.det_row_replaced` — see [`RatPrelude::det_row_replaced`].
fn declare_det_row_replaced(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let carrier = rat_ty(d);
    let row_ty = d.arrow(nat, carrier);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let mm_fv = d.fresh_fvar();
    let mm = d.kernel().fvar(mm_fv);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let hble_ty = ble_true_ty(d, t, m);
    let hrow_ty = row_value_ty(d, mm, t, h);
    let hoff_ty = row_other_ty(d, a, mm, t);

    let sm = d.succ(m);
    let det_mm = rdet(d, p, mm, sm);
    let target_fn = row_replaced_fn(d, p, a, h, t, m);
    let target_sum = rsum_range(d, p, target_fn, sm);
    let concl = req(d, det_mm, target_sum);

    let arr = d.arrow(hoff_ty, concl);
    let arr = d.arrow(hrow_ty, arr);
    let arr = d.arrow(hble_ty, arr);
    let over_t = d.pi_fv(t_fv, nat, arr);
    let over_h = d.pi_fv(h_fv, row_ty, over_t);
    let over_mm = d.pi_fv(mm_fv, mty, over_h);
    let over_a = d.pi_fv(a_fv, mty, over_mm);
    let ty = d.pi_fv(m_fv, nat, over_a);

    // --- the proof ---
    let hble_fv = d.fresh_fvar();
    let hble = d.kernel().fvar(hble_fv);
    let hrow_fv = d.fresh_fvar();
    let hrow = d.kernel().fvar(hrow_fv);
    let hoff_fv = d.fresh_fvar();
    let hoff = d.kernel().fvar(hoff_fv);

    let expand = {
        let l = d.lemma(p.det_row_expansion, &[m, mm, t]);
        d.apply(l, &[hble])
    };
    let source_fn = row_expansion_fn(d, p, mm, t, m);
    let source_sum = rsum_range(d, p, source_fn, sm);

    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sign = {
        let idx = d.add(q, t);
        ralt_sign(d, p, idx)
    };
    let entry_raw = d.apply(mm, &[t, q]);
    let entry_h = d.apply(h, &[q]);
    let hrow_q = d.apply(hrow, &[q]);
    let minor_mm = rmat_minor_of(d, p, mm, t, q);
    let minor_a = rmat_minor_of(d, p, a, t, q);
    let det_minor_mm = rdet(d, p, minor_mm, m);
    let det_minor_a = rdet(d, p, minor_a, m);
    let minor_pw = minor_agrees_off_row(d, p, t, q, hoff);
    let det_minor_eq = {
        let l = d.lemma(p.det_congr, &[m, minor_mm, minor_a]);
        d.apply(l, &[minor_pw])
    };

    let l0 = {
        let prod = rmul(d, entry_raw, det_minor_mm);
        rmul(d, sign, prod)
    };
    let l1 = {
        let prod = rmul(d, entry_h, det_minor_mm);
        rmul(d, sign, prod)
    };
    let s1 = rcongr(d, entry_raw, entry_h, hrow_q, &|d, v| {
        let prod = rmul(d, v, det_minor_mm);
        rmul(d, sign, prod)
    });
    let l2 = {
        let prod = rmul(d, entry_h, det_minor_a);
        rmul(d, sign, prod)
    };
    let s2 = rcongr(d, det_minor_mm, det_minor_a, det_minor_eq, &|d, v| {
        let prod = rmul(d, entry_h, v);
        rmul(d, sign, prod)
    });
    let (_end, pointwise_q) = rchain(d, l0, &[(l1, s1), (l2, s2)]);
    let pointwise = d.lam_fv(q_fv, nat, pointwise_q);

    let congr = {
        let l = d.lemma(p.sum_range_congr, &[source_fn, target_fn, sm]);
        d.apply(l, &[pointwise])
    };
    let proof = rtrans(d, det_mm, source_sum, target_sum, expand, congr);

    let body = d.lam_fv(hoff_fv, hoff_ty, proof);
    let body = d.lam_fv(hrow_fv, hrow_ty, body);
    let body = d.lam_fv(hble_fv, hble_ty, body);
    let body = d.lam_fv(t_fv, nat, body);
    let body = d.lam_fv(h_fv, row_ty, body);
    let body = d.lam_fv(mm_fv, mty, body);
    let body = d.lam_fv(a_fv, mty, body);
    let value = d.lam_fv(m_fv, nat, body);

    d.declare_theorem(p.det_row_replaced, ty, value)
}

/// Admit `Rat.det_row_zero` — see [`RatPrelude::det_row_zero`].
fn declare_det_row_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let zero_r = rzero(d, p);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let mm_fv = d.fresh_fvar();
    let mm = d.kernel().fvar(mm_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let hble_ty = ble_true_ty(d, t, m);
    let hrow_ty = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let lhs = d.apply(mm, &[t, c]);
        let eq = req(d, lhs, zero_r);
        d.pi_fv(c_fv, nat, eq)
    };

    let sm = d.succ(m);
    let det_mm = rdet(d, p, mm, sm);
    let concl = req(d, det_mm, zero_r);
    let arr = d.arrow(hrow_ty, concl);
    let arr = d.arrow(hble_ty, arr);
    let over_t = d.pi_fv(t_fv, nat, arr);
    let over_mm = d.pi_fv(mm_fv, mty, over_t);
    let ty = d.pi_fv(m_fv, nat, over_mm);

    let hble_fv = d.fresh_fvar();
    let hble = d.kernel().fvar(hble_fv);
    let hrow_fv = d.fresh_fvar();
    let hrow = d.kernel().fvar(hrow_fv);

    let expand = {
        let l = d.lemma(p.det_row_expansion, &[m, mm, t]);
        d.apply(l, &[hble])
    };
    let source_fn = row_expansion_fn(d, p, mm, t, m);
    let source_sum = rsum_range(d, p, source_fn, sm);

    // `∀ q, Lt q (succ m) → source_fn q = 0`.
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let hlt_fv = d.fresh_fvar();
    let hlt_ty = d.lt(q, sm);
    let sign = {
        let idx = d.add(q, t);
        ralt_sign(d, p, idx)
    };
    let entry_raw = d.apply(mm, &[t, q]);
    let hrow_q = d.apply(hrow, &[q]);
    let minor_mm = rmat_minor_of(d, p, mm, t, q);
    let det_minor_mm = rdet(d, p, minor_mm, m);

    let z0 = {
        let prod = rmul(d, entry_raw, det_minor_mm);
        rmul(d, sign, prod)
    };
    let zero_times = rmul(d, zero_r, det_minor_mm);
    let z1 = rmul(d, sign, zero_times);
    let sz1 = rcongr(d, entry_raw, zero_r, hrow_q, &|d, v| {
        let prod = rmul(d, v, det_minor_mm);
        rmul(d, sign, prod)
    });
    // `0 * X = X * 0 = 0`: this prelude has `mul_zero` but no `zero_mul`.
    let times_zero = rmul(d, det_minor_mm, zero_r);
    let comm = d.lemma(p.mul_comm, &[zero_r, det_minor_mm]);
    let mz = d.lemma(p.mul_zero, &[det_minor_mm]);
    let (_e, zero_mul) = rchain(d, zero_times, &[(times_zero, comm), (zero_r, mz)]);
    let z2 = rmul(d, sign, zero_r);
    let sz2 = rcongr(d, zero_times, zero_r, zero_mul, &|d, v| rmul(d, sign, v));
    let sz3 = d.lemma(p.mul_zero, &[sign]);
    let (_e2, summand_zero) = rchain(d, z0, &[(z1, sz1), (z2, sz2), (zero_r, sz3)]);
    let bounded = {
        let inner = d.lam_fv(hlt_fv, hlt_ty, summand_zero);
        d.lam_fv(q_fv, nat, inner)
    };

    let sum_zero = {
        let l = d.lemma(p.sum_range_eq_zero_of_lt, &[source_fn, sm]);
        d.apply(l, &[bounded])
    };
    let proof = rtrans(d, det_mm, source_sum, zero_r, expand, sum_zero);

    let body = d.lam_fv(hrow_fv, hrow_ty, proof);
    let body = d.lam_fv(hble_fv, hble_ty, body);
    let body = d.lam_fv(t_fv, nat, body);
    let body = d.lam_fv(mm_fv, mty, body);
    let value = d.lam_fv(m_fv, nat, body);

    d.declare_theorem(p.det_row_zero, ty, value)
}

/// Admit `Rat.det_row_smul` — see [`RatPrelude::det_row_smul`].
fn declare_det_row_smul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let carrier = rat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let mm_fv = d.fresh_fvar();
    let mm = d.kernel().fvar(mm_fv);
    let z_fv = d.fresh_fvar();
    let z = d.kernel().fvar(z_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    // `h := fun c => z * A t c`.
    let h_lam = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let atc = d.apply(a, &[t, c]);
        let body = rmul(d, z, atc);
        d.lam_fv(c_fv, nat, body)
    };

    let hble_ty = ble_true_ty(d, t, m);
    // Written REDUCED rather than as `row_value_ty(.., h_lam)`, which would
    // leave a `(fun c => z * A t c) c` beta-redex in the rendered hypothesis
    // and make every caller stare at it. Defeq to what `det_row_replaced`
    // wants, so `hrow` passes straight through.
    let hrow_ty = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let lhs = d.apply(mm, &[t, c]);
        let atc = d.apply(a, &[t, c]);
        let rhs = rmul(d, z, atc);
        let eq = req(d, lhs, rhs);
        d.pi_fv(c_fv, nat, eq)
    };
    let hoff_ty = row_other_ty(d, a, mm, t);

    let sm = d.succ(m);
    let det_mm = rdet(d, p, mm, sm);
    let det_a = rdet(d, p, a, sm);
    let z_det_a = rmul(d, z, det_a);
    let concl = req(d, det_mm, z_det_a);

    let arr = d.arrow(hoff_ty, concl);
    let arr = d.arrow(hrow_ty, arr);
    let arr = d.arrow(hble_ty, arr);
    let over_t = d.pi_fv(t_fv, nat, arr);
    let over_z = d.pi_fv(z_fv, carrier, over_t);
    let over_mm = d.pi_fv(mm_fv, mty, over_z);
    let over_a = d.pi_fv(a_fv, mty, over_mm);
    let ty = d.pi_fv(m_fv, nat, over_a);

    // --- the proof ---
    let hble_fv = d.fresh_fvar();
    let hble = d.kernel().fvar(hble_fv);
    let hrow_fv = d.fresh_fvar();
    let hrow = d.kernel().fvar(hrow_fv);
    let hoff_fv = d.fresh_fvar();
    let hoff = d.kernel().fvar(hoff_fv);

    let replaced = {
        let l = d.lemma(p.det_row_replaced, &[m, a, mm, h_lam, t]);
        d.apply(l, &[hble, hrow, hoff])
    };
    let scaled_fn = row_replaced_fn(d, p, a, h_lam, t, m);
    let scaled_sum = rsum_range(d, p, scaled_fn, sm);

    let plain_fn = row_expansion_fn(d, p, a, t, m);
    let plain_sum = rsum_range(d, p, plain_fn, sm);
    let expand_a = {
        let l = d.lemma(p.det_row_expansion, &[m, a, t]);
        d.apply(l, &[hble])
    };

    // `pulled_fn q := z * (altSign (q+t) * (A t q * det (matMinor A t q) m))`.
    let pulled_fn = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let idx = d.add(q, t);
        let sign = ralt_sign(d, p, idx);
        let atq = d.apply(a, &[t, q]);
        let minor = rmat_minor_of(d, p, a, t, q);
        let sub = rdet(d, p, minor, m);
        let prod = rmul(d, atq, sub);
        let signed = rmul(d, sign, prod);
        let body = rmul(d, z, signed);
        d.lam_fv(q_fv, nat, body)
    };
    let pulled_sum = rsum_range(d, p, pulled_fn, sm);

    // pointwise: `sign * ((z * a1) * X) = z * (sign * (a1 * X))`.
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sign = {
        let idx = d.add(q, t);
        ralt_sign(d, p, idx)
    };
    let a1 = d.apply(a, &[t, q]);
    let minor = rmat_minor_of(d, p, a, t, q);
    let xx = rdet(d, p, minor, m);
    let z_a1 = rmul(d, z, a1);
    let a1_x = rmul(d, a1, xx);
    let z_a1_x = rmul(d, z_a1, xx);
    let x0 = rmul(d, sign, z_a1_x);
    let z_of_a1x = rmul(d, z, a1_x);
    let x1 = rmul(d, sign, z_of_a1x);
    let step_a = {
        let pf = d.lemma(p.mul_assoc, &[z, a1, xx]);
        rcongr(d, z_a1_x, z_of_a1x, pf, &|d, v| rmul(d, sign, v))
    };
    let sign_z = rmul(d, sign, z);
    let x2 = rmul(d, sign_z, a1_x);
    let step_b = {
        let pf = d.lemma(p.mul_assoc, &[sign, z, a1_x]);
        rsymm(d, x2, x1, pf)
    };
    let z_sign = rmul(d, z, sign);
    let x3 = rmul(d, z_sign, a1_x);
    let step_c = {
        let pf = d.lemma(p.mul_comm, &[sign, z]);
        rcongr(d, sign_z, z_sign, pf, &|d, v| rmul(d, v, a1_x))
    };
    let sign_a1x = rmul(d, sign, a1_x);
    let x4 = rmul(d, z, sign_a1x);
    let step_d = d.lemma(p.mul_assoc, &[z, sign, a1_x]);
    let (_e, pointwise_q) = rchain(
        d,
        x0,
        &[(x1, step_a), (x2, step_b), (x3, step_c), (x4, step_d)],
    );
    let pointwise = d.lam_fv(q_fv, nat, pointwise_q);

    let congr = {
        let l = d.lemma(p.sum_range_congr, &[scaled_fn, pulled_fn, sm]);
        d.apply(l, &[pointwise])
    };
    // `z * sumRange plain_fn sm = sumRange pulled_fn sm`, read backwards.
    let pull = d.lemma(p.mul_sum_range, &[z, plain_fn, sm]);
    let z_plain = rmul(d, z, plain_sum);
    let pull_back = rsymm(d, z_plain, pulled_sum, pull);
    let expand_a_rev = rsymm(d, det_a, plain_sum, expand_a);
    let last = rcongr(d, plain_sum, det_a, expand_a_rev, &|d, v| rmul(d, z, v));

    let (_e2, proof) = rchain(
        d,
        det_mm,
        &[
            (scaled_sum, replaced),
            (pulled_sum, congr),
            (z_plain, pull_back),
            (z_det_a, last),
        ],
    );

    let body = d.lam_fv(hoff_fv, hoff_ty, proof);
    let body = d.lam_fv(hrow_fv, hrow_ty, body);
    let body = d.lam_fv(hble_fv, hble_ty, body);
    let body = d.lam_fv(t_fv, nat, body);
    let body = d.lam_fv(z_fv, carrier, body);
    let body = d.lam_fv(mm_fv, mty, body);
    let body = d.lam_fv(a_fv, mty, body);
    let value = d.lam_fv(m_fv, nat, body);

    d.declare_theorem(p.det_row_smul, ty, value)
}

/// Admit `Rat.det_row_multilinear` — see [`RatPrelude::det_row_multilinear`].
///
/// The Cauchy–Binet expansion step. Row `t` of `M` is a `sumRange` of `n`
/// coefficient rows; the determinant splits into a `sumRange` of `n` cofactor
/// sums, one per coefficient row, all sharing `A`'s minors.
///
/// The whole content after [`declare_det_row_replaced`] is moving a
/// `Rat.sumRange` out of the middle of a product and then exchanging the two
/// summations: two applications of `Rat.mul_sumRange` around one
/// `Rat.mul_comm`, then `Rat.sumRange_swap`. `sumRange_swap`'s binder order is
/// `(f, INNER bound, OUTER bound)` — the transposition `matrix_n.rs`'s
/// associativity proof paid a kernel rejection for.
fn declare_det_row_multilinear(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);
    let carrier = rat_ty(d);
    let row_ty = d.arrow(nat, carrier);
    let coef_ty = d.arrow(nat, row_ty);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let mm_fv = d.fresh_fvar();
    let mm = d.kernel().fvar(mm_fv);
    let coef_fv = d.fresh_fvar();
    let coef = d.kernel().fvar(coef_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    // `h := fun c => sumRange (fun k => coef k c) n`.
    let h_lam = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let inner = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = d.apply(coef, &[k, c]);
            d.lam_fv(k_fv, nat, body)
        };
        let body = rsum_range(d, p, inner, n);
        d.lam_fv(c_fv, nat, body)
    };

    let hble_ty = ble_true_ty(d, t, m);
    // Reduced, for the same reason as [`declare_det_row_smul`]'s.
    let hrow_ty = {
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let lhs = d.apply(mm, &[t, c]);
        let over_k = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let body = d.apply(coef, &[k, c]);
            d.lam_fv(k_fv, nat, body)
        };
        let rhs = rsum_range(d, p, over_k, n);
        let eq = req(d, lhs, rhs);
        d.pi_fv(c_fv, nat, eq)
    };
    let hoff_ty = row_other_ty(d, a, mm, t);

    let sm = d.succ(m);
    let det_mm = rdet(d, p, mm, sm);

    // `outer_fn k := sumRange (fun q => altSign (q+t) * (coef k q *
    //                 det (matMinor A t q) m)) (succ m)`.
    let outer_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let inner = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let idx = d.add(q, t);
            let sign = ralt_sign(d, p, idx);
            let ckq = d.apply(coef, &[k, q]);
            let minor = rmat_minor_of(d, p, a, t, q);
            let sub = rdet(d, p, minor, m);
            let prod = rmul(d, ckq, sub);
            let body = rmul(d, sign, prod);
            d.lam_fv(q_fv, nat, body)
        };
        let body = rsum_range(d, p, inner, sm);
        d.lam_fv(k_fv, nat, body)
    };
    let target_sum = rsum_range(d, p, outer_fn, n);
    let concl = req(d, det_mm, target_sum);

    let arr = d.arrow(hoff_ty, concl);
    let arr = d.arrow(hrow_ty, arr);
    let arr = d.arrow(hble_ty, arr);
    let over_n = d.pi_fv(n_fv, nat, arr);
    let over_t = d.pi_fv(t_fv, nat, over_n);
    let over_coef = d.pi_fv(coef_fv, coef_ty, over_t);
    let over_mm = d.pi_fv(mm_fv, mty, over_coef);
    let over_a = d.pi_fv(a_fv, mty, over_mm);
    let ty = d.pi_fv(m_fv, nat, over_a);

    // --- the proof ---
    let hble_fv = d.fresh_fvar();
    let hble = d.kernel().fvar(hble_fv);
    let hrow_fv = d.fresh_fvar();
    let hrow = d.kernel().fvar(hrow_fv);
    let hoff_fv = d.fresh_fvar();
    let hoff = d.kernel().fvar(hoff_fv);

    let replaced = {
        let l = d.lemma(p.det_row_replaced, &[m, a, mm, h_lam, t]);
        d.apply(l, &[hble, hrow, hoff])
    };
    let start_fn = row_replaced_fn(d, p, a, h_lam, t, m);
    let start_sum = rsum_range(d, p, start_fn, sm);

    // `pair_fn q k := altSign (q+t) * (coef k q * det (matMinor A t q) m)`.
    let pair_fn = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let idx = d.add(q, t);
        let sign = ralt_sign(d, p, idx);
        let ckq = d.apply(coef, &[k, q]);
        let minor = rmat_minor_of(d, p, a, t, q);
        let sub = rdet(d, p, minor, m);
        let prod = rmul(d, ckq, sub);
        let body = rmul(d, sign, prod);
        let inner = d.lam_fv(k_fv, nat, body);
        d.lam_fv(q_fv, nat, inner)
    };
    // `inner_fn q := sumRange (fun k => pair_fn q k) n`, written reduced.
    let inner_fn = {
        let q_fv = d.fresh_fvar();
        let q = d.kernel().fvar(q_fv);
        let over_k = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let idx = d.add(q, t);
            let sign = ralt_sign(d, p, idx);
            let ckq = d.apply(coef, &[k, q]);
            let minor = rmat_minor_of(d, p, a, t, q);
            let sub = rdet(d, p, minor, m);
            let prod = rmul(d, ckq, sub);
            let body = rmul(d, sign, prod);
            d.lam_fv(k_fv, nat, body)
        };
        let body = rsum_range(d, p, over_k, n);
        d.lam_fv(q_fv, nat, body)
    };
    let inner_sum = rsum_range(d, p, inner_fn, sm);

    // pointwise at `q`: `sign * (S * X) = sumRange (fun k => sign * (coef k q * X)) n`
    // where `S = sumRange (fun k => coef k q) n`.
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);
    let sign = {
        let idx = d.add(q, t);
        ralt_sign(d, p, idx)
    };
    let minor_q = rmat_minor_of(d, p, a, t, q);
    let xx = rdet(d, p, minor_q, m);
    let coef_q = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = d.apply(coef, &[k, q]);
        d.lam_fv(k_fv, nat, body)
    };
    let s_val = rsum_range(d, p, coef_q, n);

    let s_x = rmul(d, s_val, xx);
    let y0 = rmul(d, sign, s_x);
    let x_s = rmul(d, xx, s_val);
    let y1 = rmul(d, sign, x_s);
    let step1 = {
        let pf = d.lemma(p.mul_comm, &[s_val, xx]);
        rcongr(d, s_x, x_s, pf, &|d, v| rmul(d, sign, v))
    };
    // `X * S = sumRange (fun k => X * coef k q) n`.
    let x_coef_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ckq = d.apply(coef, &[k, q]);
        let body = rmul(d, xx, ckq);
        d.lam_fv(k_fv, nat, body)
    };
    let x_coef_sum = rsum_range(d, p, x_coef_fn, n);
    let y2 = rmul(d, sign, x_coef_sum);
    let step2 = {
        let pf = d.lemma(p.mul_sum_range, &[xx, coef_q, n]);
        rcongr(d, x_s, x_coef_sum, pf, &|d, v| rmul(d, sign, v))
    };
    // `sign * sumRange x_coef_fn n = sumRange (fun k => sign * (X * coef k q)) n`.
    let sign_x_coef_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ckq = d.apply(coef, &[k, q]);
        let prod = rmul(d, xx, ckq);
        let body = rmul(d, sign, prod);
        d.lam_fv(k_fv, nat, body)
    };
    let y3 = rsum_range(d, p, sign_x_coef_fn, n);
    let step3 = d.lemma(p.mul_sum_range, &[sign, x_coef_fn, n]);
    // termwise `sign * (X * coef k q) = sign * (coef k q * X)`.
    let final_k_fn = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ckq = d.apply(coef, &[k, q]);
        let prod = rmul(d, ckq, xx);
        let body = rmul(d, sign, prod);
        d.lam_fv(k_fv, nat, body)
    };
    let y4 = rsum_range(d, p, final_k_fn, n);
    let step4 = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let ckq = d.apply(coef, &[k, q]);
        let x_ck = rmul(d, xx, ckq);
        let ck_x = rmul(d, ckq, xx);
        let pf = d.lemma(p.mul_comm, &[xx, ckq]);
        let termwise = rcongr(d, x_ck, ck_x, pf, &|d, v| rmul(d, sign, v));
        let pw = d.lam_fv(k_fv, nat, termwise);
        let l = d.lemma(p.sum_range_congr, &[sign_x_coef_fn, final_k_fn, n]);
        d.apply(l, &[pw])
    };
    let (_e, pointwise_q) = rchain(d, y0, &[(y1, step1), (y2, step2), (y3, step3), (y4, step4)]);
    let pointwise = d.lam_fv(q_fv, nat, pointwise_q);

    let congr = {
        let l = d.lemma(p.sum_range_congr, &[start_fn, inner_fn, sm]);
        d.apply(l, &[pointwise])
    };
    // `sumRange_swap` binder order: `(f, INNER bound, OUTER bound)`.
    let swap = d.lemma(p.sum_range_swap, &[pair_fn, n, sm]);

    let (_e2, proof) = rchain(
        d,
        det_mm,
        &[
            (start_sum, replaced),
            (inner_sum, congr),
            (target_sum, swap),
        ],
    );

    let body = d.lam_fv(hoff_fv, hoff_ty, proof);
    let body = d.lam_fv(hrow_fv, hrow_ty, body);
    let body = d.lam_fv(hble_fv, hble_ty, body);
    let body = d.lam_fv(n_fv, nat, body);
    let body = d.lam_fv(t_fv, nat, body);
    let body = d.lam_fv(coef_fv, coef_ty, body);
    let body = d.lam_fv(mm_fv, mty, body);
    let body = d.lam_fv(a_fv, mty, body);
    let value = d.lam_fv(m_fv, nat, body);

    d.declare_theorem(p.det_row_multilinear, ty, value)
}

// --- multiplicativity at a CONCRETE dimension (`matrix_det`, ADR-1440) -----
//
// `Rat.det_matMul_2 : ∀ A B, det (matMul A B 2) 2 = det A 2 * det B 2`.
//
// The symbolic-`n` statement is NOT proved (see the "what is still missing"
// account in ADR-1440); this is the `n = 2` instance, and it is cheap for a
// reason worth recording rather than for a reason that generalizes. The
// eight-variable ring identity underneath it — `Rat.det2_mul`, landed with the
// fixed-dimension `matrix` module long before `Rat.det` existed — is already
// proved, and `Rat.det_eq_det2` already identifies `det A 2` with `det2` on
// the four entries SYMBOLICALLY in `A`. So all this declaration does is reduce
// `matMul A B 2 i j` at the four index pairs and line the entries up.
//
// That reduction is where the whole `n = 2` shortcut lives: `Rat.sumRange`'s
// base case is `Rat.zero`, so `matMul A B 2 i j` iota-reduces to
// `(0 + A i 0 * B 0 j) + A i 1 * B 1 j` — one stray `zero +` per entry, killed
// by `Rat.zero_add` under a congruence. At symbolic `n` nothing reduces at
// all (a recursor applied to a bare free variable is stuck), which is exactly
// why the general case needs `Rat.det_row_multilinear` and an induction over
// the rows instead.
//
// `n = 3` is NOT done and is not cheap the same way: there is no `det3_mul`,
// and the corresponding identity has eighteen variables.

/// Admit `Rat.det_matMul_2` — see [`RatPrelude::det_mat_mul_2`].
fn declare_det_mat_mul_2(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);

    let i0 = d.zero();
    let i1 = d.num(1);
    let i2 = d.num(2);

    let a00 = d.apply(a, &[i0, i0]);
    let a01 = d.apply(a, &[i0, i1]);
    let a10 = d.apply(a, &[i1, i0]);
    let a11 = d.apply(a, &[i1, i1]);
    let b00 = d.apply(b, &[i0, i0]);
    let b01 = d.apply(b, &[i0, i1]);
    let b10 = d.apply(b, &[i1, i0]);
    let b11 = d.apply(b, &[i1, i1]);

    // `C := matMul A B 2`, a `Nat → Nat → Rat` in its own right.
    let c_mat = d.const_app(p.mat_mul, &[a, b, i2]);

    let det_c = rdet(d, p, c_mat, i2);
    let det_a = rdet(d, p, a, i2);
    let det_b = rdet(d, p, b, i2);
    let rhs = rmul(d, det_a, det_b);
    let ty = {
        let stmt = req(d, det_c, rhs);
        let over_b = d.pi_fv(b_fv, mty, stmt);
        d.pi_fv(a_fv, mty, over_b)
    };

    // The four entries of `C`, each in the shape `matMul` iota-reduces to,
    // and each in the shape `det2_mul` states.
    let zero_r = rzero(d, p);
    let entry = |d: &mut IntDev<'_>, x: ExprId, y: ExprId, u: ExprId, v: ExprId| {
        let xy = rmul(d, x, y);
        let uv = rmul(d, u, v);
        let raw = {
            let head = radd(d, zero_r, xy);
            radd(d, head, uv)
        };
        let tidy = radd(d, xy, uv);
        // `(0 + xy) + uv = xy + uv`.
        let head = radd(d, zero_r, xy);
        let za = d.lemma(p.zero_add, &[xy]);
        let pf = rcongr(d, head, xy, za, &|d, w| radd(d, w, uv));
        (raw, tidy, pf)
    };

    let (c00_raw, c00, p00) = entry(d, a00, b00, a01, b10);
    let (c01_raw, c01, p01) = entry(d, a00, b01, a01, b11);
    let (c10_raw, c10, p10) = entry(d, a10, b00, a11, b10);
    let (c11_raw, c11, p11) = entry(d, a10, b01, a11, b11);

    // `det C 2 = det2 (C 0 0) (C 0 1) (C 1 0) (C 1 1)`, whose right-hand side
    // is defeq to `det2 c00_raw c01_raw c10_raw c11_raw`.
    let expand_c = d.lemma(p.det_eq_det2, &[c_mat]);
    let d_raw = rdet2(d, p, c00_raw, c01_raw, c10_raw, c11_raw);

    let d_1 = rdet2(d, p, c00, c01_raw, c10_raw, c11_raw);
    let s_1 = rcongr(d, c00_raw, c00, p00, &|d, w| {
        rdet2(d, p, w, c01_raw, c10_raw, c11_raw)
    });
    let d_2 = rdet2(d, p, c00, c01, c10_raw, c11_raw);
    let s_2 = rcongr(d, c01_raw, c01, p01, &|d, w| {
        rdet2(d, p, c00, w, c10_raw, c11_raw)
    });
    let d_3 = rdet2(d, p, c00, c01, c10, c11_raw);
    let s_3 = rcongr(d, c10_raw, c10, p10, &|d, w| {
        rdet2(d, p, c00, c01, w, c11_raw)
    });
    let d_4 = rdet2(d, p, c00, c01, c10, c11);
    let s_4 = rcongr(d, c11_raw, c11, p11, &|d, w| rdet2(d, p, c00, c01, c10, w));

    // `Rat.det2_mul` — the eight-variable identity, already proved.
    let det2_a = rdet2(d, p, a00, a01, a10, a11);
    let det2_b = rdet2(d, p, b00, b01, b10, b11);
    let product = rmul(d, det2_a, det2_b);
    let s_mul = d.lemma(p.det2_mul, &[a00, a01, a10, a11, b00, b01, b10, b11]);

    // Back to `det A 2` and `det B 2`.
    let expand_a = d.lemma(p.det_eq_det2, &[a]);
    let expand_b = d.lemma(p.det_eq_det2, &[b]);
    let a_back = rsymm(d, det_a, det2_a, expand_a);
    let b_back = rsymm(d, det_b, det2_b, expand_b);
    let mid = rmul(d, det_a, det2_b);
    let s_a = rcongr(d, det2_a, det_a, a_back, &|d, w| rmul(d, w, det2_b));
    let s_b = rcongr(d, det2_b, det_b, b_back, &|d, w| rmul(d, det_a, w));

    let (_end, proof) = rchain(
        d,
        det_c,
        &[
            (d_raw, expand_c),
            (d_1, s_1),
            (d_2, s_2),
            (d_3, s_3),
            (d_4, s_4),
            (product, s_mul),
            (mid, s_a),
            (rhs, s_b),
        ],
    );

    let value = {
        let over_b = d.lam_fv(b_fv, mty, proof);
        d.lam_fv(a_fv, mty, over_b)
    };
    d.declare_theorem(p.det_mat_mul_2, ty, value)
}
