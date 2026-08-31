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
use super::matrix::{rdet2, rdet3};
use super::ops::{
    radd, rat_theorem, rat_ty, rchain, rcongr, req, rmul, rneg, rone, rsum_range, rtrans, rzero,
};
use super::probability::bool_select_rat;
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
    declare_det_eval_example4(d, p)
}

// --- shared term builders --------------------------------------------------

/// `Nat → Nat → Rat`, the matrix type (a local copy of `matrix_n`'s private
/// `mat_ty`).
fn mat_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let row = d.arrow(nat, carrier);
    d.arrow(nat, row)
}

/// `Rat.matSkip p x`.
fn rmat_skip(d: &mut IntDev<'_>, p: RatPrelude, at: ExprId, x: ExprId) -> ExprId {
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
fn rmat_minor_of(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, i: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.mat_minor, &[a, i, j])
}

/// `Rat.altSign j`.
fn ralt_sign(d: &mut IntDev<'_>, p: RatPrelude, j: ExprId) -> ExprId {
    d.const_app(p.alt_sign, &[j])
}

/// `Rat.det A n`.
fn rdet(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, n: ExprId) -> ExprId {
    d.const_app(p.det, &[a, n])
}

/// `Eq Rat (Rat.mul Rat.one x) x` — this prelude has no `one_mul`, so it is
/// `mul_comm` followed by `mul_one` every time (`super::RatPrelude`'s own
/// note at `mul_one` says the same).
fn one_mul_pf(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
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
fn rq(d: &mut IntDev<'_>, p: RatPrelude, n: i64) -> ExprId {
    let z = int_numeral(d, n);
    d.const_app(p.of_int, &[z])
}

/// A closed `Nat → Nat → Rat` for a concrete `k × k` matrix given in row-major
/// order, built by nested `Nat.beq` selection exactly as
/// `super::matrix_transpose::const2x2` does.
///
/// Out-of-range indices fall into the last row/column; every use below stays
/// inside the bound, and the determinant never reads outside it.
fn const_matrix(d: &mut IntDev<'_>, p: RatPrelude, k: usize, rows: &[i64]) -> ExprId {
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
