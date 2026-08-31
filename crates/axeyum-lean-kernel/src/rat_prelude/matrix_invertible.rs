//! **`Rat.matInv2`** — the 2×2 adjugate-based matrix inverse, taking a
//! GENERAL matrix `A : Nat → Nat → Rat` (not four separate scalars), and
//! BOTH-SIDED invertibility `A · A⁻¹ = I`, `A⁻¹ · A = I` stated through
//! [`super::matrix_n`]'s general `matMul`/`matId` pointwise encoding.
//!
//! ## Step 0: what already existed, and the one genuine gap
//!
//! [`super::matrix`] already lands, at fixed dimension `n = 2`, all four
//! entries of `A⁻¹·A = I` (`inv2_top_left`/`inv2_top_right`/
//! `inv2_bottom_left`/`inv2_bottom_right`) and, unscaled, all four entries of
//! `A·adj(A) = det(A)·I` (`mul_adj2_top_left`/`_top_right`/`_bottom_left`/
//! `_bottom_right`) — determinant multiplicativity (`det2_mul`) and both
//! directions of a fixed-`n` Cramer's-rule story (`cramer2_x`/`cramer2_y`/
//! `cramer2_solves`/`cramer_two_unique_x`/`cramer_two_unique_y`) are ALSO
//! already landed there. So the curriculum note's three named candidates
//! (determinant multiplicativity, invertibility, `Ax=b` solvability, all at
//! fixed small `n`) are already landed at `n = 2`, and this file does not
//! repeat them.
//!
//! What is genuinely missing: `super::matrix`'s inverse family takes four
//! separate `Rat` scalars, never [`super::matrix_n`]'s `Nat → Nat → Rat`
//! matrix — the fixed-size family and the symbolic-dimension family are two
//! disconnected islands. And only ONE direction of invertibility
//! (`A⁻¹·A = I`) is proven at all; `A·A⁻¹ = I` is not, only its unscaled
//! cousin `A·adj(A) = det(A)·I`. This file builds the bridge: `Rat.matInv2`
//! is a genuine new `Definition` over the general encoding, and both
//! directions of `A·A⁻¹ = I` / `A⁻¹·A = I` are stated through the SAME
//! `matMul`/`matId` names [`super::matrix_n::declare_matrix_n`] and
//! [`super::matrix_transpose::declare_matrix_transpose`] already use.
//!
//! ## Graded statement family (ADR-0603, ADR-0716, ADR-0825)
//!
//! Every statement here is a pure identity conditioned on `det ≠ 0` — no
//! comparison beyond a disequality, no unbounded search — so per
//! [ADR-0716](../../../../../docs/research/09-decisions/adr-0716-row-two-of-a-decidable-subject.md)
//! there is **no row 2**, argued from shape rather than a failed search
//! (ℚ's order is decidable, `Rat.le_total` is a proved theorem here, and
//! this family never reaches a comparison at all).
//!
//! The family is **row 1 + row 3**, and
//! [ADR-0825](../../../../../docs/research/09-decisions/adr-0825-a-decidable-family-can-run-row-1-and-row-3-as-one-statement.md)'s
//! collapse applies exactly as it did for [`super::matrix_transpose`]:
//! [`declare_mat_inv2_example`] is [`RatPrelude::matmul_matinv2_top_left`]
//! itself, applied at a concrete numeral matrix rather than a symbolic one,
//! with the resulting equation bridged to a plain numeral by the kernel's
//! own delta/beta/iota computation — no separate `axeyum-cas`
//! producer/verifier pair. Row 4 (a labeled import) is not attempted.
//!
//! ## Every statement here is POINTWISE, and that is forced
//!
//! `funext` is **absent** (same discipline as [`super::matrix_n`] and
//! [`super::matrix_transpose`]): every conclusion is a scalar entry equation
//! `matMul A B 2 i j = matId i j` at one concrete `(i,j)`, never an `Eq`
//! between two `Nat → Nat → Rat` values.
//!
//! ## Why each entry needs a different amount of algebra
//!
//! `A⁻¹·A`'s entries are, term-for-term, EXACTLY `super::matrix`'s own
//! `inv2_*` statements once `matMul`/`matInv2`/`matId` are unfolded at the
//! concrete index pair (pure defeq) — no reassociation needed, so
//! [`declare_matinv2_matmul_top_left`] and its three siblings are two-step
//! proofs (the `matMul` unfold bridge, then `Rat.zero_add`, then
//! `super::matrix`'s own `inv2_*` lemma directly).
//!
//! `A·A⁻¹`'s entries are NOT already stated anywhere: `matInv2 A i j`
//! multiplies `A`'s row on the LEFT of the (already scaled) adjugate entry
//! rather than the right, so the two summands need pulling `invD` out from
//! the middle of each product (`x*(invD*y) = invD*(x*y)`, one `mul_assoc` +
//! one `mul_comm` each) before `Rat.left_distrib` combines them into EXACTLY
//! `super::matrix`'s unscaled `mul_adj2_*` statement, which is then scaled by
//! `invD` via `Rat.mul_inv_cancel_of_ne_zero` (diagonal) or `Rat.mul_zero`
//! (off-diagonal, since `mul_adj2_top_right`/`mul_adj2_bottom_left` already
//! equal `Rat.zero` unconditionally).
//!
//! ## The evaluation test this file's new `Definition` needs
//!
//! [`declare_mat_inv2_eval_example`]: `super::matrix`'s own Hard-Rules
//! discipline (the kernel accepts a well-typed `Definition` regardless of
//! whether it computes the intended value) applies here too. `A := [[2, 3],
//! [5, 7]]` has four DISTINCT entries and `det = -1`, so a `matInv2` that
//! forgot to swap the diagonal (used `A 0 0` instead of `A 1 1` at `(0,0)`)
//! or forgot a sign flip on an off-diagonal entry would produce a different
//! numeral than the one this test asserts, and the trusted gate would refuse
//! the declaration outright.

use super::RatPrelude;
use super::ops::{
    radd, rat_theorem, rat_ty, rchain, rcongr, req, rmul, rneg, rone, rrefl, rsymm, rtrans, rzero,
};
use super::probability::bool_select_rat;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.matInv2`: above [`super::matrix_transpose::MAT_TRANSPOSE_HEIGHT`]
/// worked out to `47` and above every other height declared in this prelude
/// so far, following the "outranks everything it unfolds to" convention
/// [`super::defs`] sets.
const MAT_INV2_HEIGHT: u16 = 48;

/// Admit `Rat.matInv2` and everything this file proves about it.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_matrix_invertible(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    declare_mat_inv2(d, p)?;
    declare_mat_inv2_eval_example(d, p)?;
    declare_matinv2_matmul_top_left(d, p)?;
    declare_matinv2_matmul_top_right(d, p)?;
    declare_matinv2_matmul_bottom_left(d, p)?;
    declare_matinv2_matmul_bottom_right(d, p)?;
    declare_matmul_matinv2_top_left(d, p)?;
    declare_matmul_matinv2_top_right(d, p)?;
    declare_matmul_matinv2_bottom_left(d, p)?;
    declare_matmul_matinv2_bottom_right(d, p)?;
    declare_mat_inv2_example(d, p)
}

/// `Nat → Nat → Rat`, the matrix type — duplicated from
/// [`super::matrix_n::mat_ty`] (private there), the same convention
/// [`super::matrix_transpose::mat_ty`] uses to keep this file self-contained.
fn mat_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let row = d.arrow(nat, carrier);
    d.arrow(nat, row)
}

/// `Rat.matMul A B k i j`, duplicated from [`super::matrix_n::rmat_mul`].
fn rmat_mul(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a: ExprId,
    b: ExprId,
    k: ExprId,
    i: ExprId,
    j: ExprId,
) -> ExprId {
    d.const_app(p.mat_mul, &[a, b, k, i, j])
}

/// `matInv2 A`, i.e. `Rat.matInv2` partially applied to the matrix `A`.
fn rmat_inv2(d: &mut IntDev<'_>, p: RatPrelude, a_mat: ExprId) -> ExprId {
    d.const_app(p.mat_inv2, &[a_mat])
}

/// `A`'s four entries `(A 0 0, A 0 1, A 1 0, A 1 1)`, plus `det2 a b c dd`
/// and `Rat.inv` of it — every downstream declaration in this file needs
/// exactly this tuple, rebuilt fresh (never cached across declarations, the
/// convention [`super::matrix`]'s own `stmt`/`proof` closure pairs use).
fn entries(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    a_mat: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId, ExprId) {
    let zero_n = d.zero();
    let one_n = d.num(1);
    let a = d.apply(a_mat, &[zero_n, zero_n]);
    let b = d.apply(a_mat, &[zero_n, one_n]);
    let c = d.apply(a_mat, &[one_n, zero_n]);
    let dd = d.apply(a_mat, &[one_n, one_n]);
    let det = d.const_app(p.det2, &[a, b, c, dd]);
    let inv_d = d.const_app(p.inv, &[det]);
    (a, b, c, dd, det, inv_d)
}

/// `Not (Eq Rat (det2 a b c dd) Rat.zero)` — duplicated from
/// [`super::matrix::det2_ne_zero`] (private there).
fn det2_ne_zero(d: &mut IntDev<'_>, p: RatPrelude, det: ExprId) -> ExprId {
    let zero_r = rzero(d, p);
    let eq_zero = req(d, det, zero_r);
    d.not(eq_zero)
}

/// `invD*D = 1`, given `h : D ≠ 0` — duplicated from
/// [`super::matrix::inv_det2_cancel`] (private there): `D*invD = 1` is
/// `Rat.mul_inv_cancel_of_ne_zero` verbatim; this reads it through one
/// `mul_comm`.
fn inv_det2_cancel(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    det: ExprId,
    inv_d: ExprId,
    h: ExprId,
) -> ExprId {
    let start = rmul(d, inv_d, det);
    let comm = d.lemma(p.mul_comm, &[inv_d, det]); // invD*D = D*invD
    let flipped = rmul(d, det, inv_d);
    let cancel = d.lemma(p.mul_inv_cancel_of_ne_zero, &[det, h]); // D*invD = 1
    let one = rone(d, p);
    rtrans(d, start, flipped, one, comm, cancel)
}

/// `w*(x*y) = x*(w*y)` — duplicated from [`super::matrix::middle_swap`]
/// (private there): swap the outer-left factor with the inner-left one.
fn middle_swap(d: &mut IntDev<'_>, p: RatPrelude, w: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let xy = rmul(d, x, y);
    let start = rmul(d, w, xy);
    let wx = rmul(d, w, x);
    let flat = rmul(d, wx, y);
    let step1 = {
        let forward = d.lemma(p.mul_assoc, &[w, x, y]); // (w*x)*y = w*(x*y)
        rsymm(d, flat, start, forward)
    };
    let xw = rmul(d, x, w);
    let commuted = rmul(d, xw, y);
    let step2 = {
        let swap = d.lemma(p.mul_comm, &[w, x]); // w*x = x*w
        rcongr(d, wx, xw, swap, &|d, t| rmul(d, t, y))
    };
    let wy = rmul(d, w, y);
    let target = rmul(d, x, wy);
    let step3 = d.lemma(p.mul_assoc, &[x, w, y]); // (x*w)*y = x*(w*y)
    let (_, proof) = rchain(
        d,
        start,
        &[(flat, step1), (commuted, step2), (target, step3)],
    );
    proof
}

/// Admit `Rat.matInv2 : (Nat → Nat → Rat) → Nat → Nat → Rat := fun A i j =>`
/// the adjugate entry at `(i,j)` scaled by `invD := Rat.inv (det2 (A 0 0) (A
/// 0 1) (A 1 0) (A 1 1))` — `invD*(A 1 1)` at `(0,0)`, `invD*(-(A 0 1))` at
/// `(0,1)`, `invD*(-(A 1 0))` at `(1,0)`, `invD*(A 0 0)` at `(1,1)`, built the
/// same `Nat.beq`-selected way [`super::matrix_transpose::const2x2`] builds a
/// concrete matrix and [`super::RatPrelude::mat_id`] builds its diagonal.
fn declare_mat_inv2(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a_mat = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let (a, b, c, dd, _det, inv_d) = entries(d, p, a_mat);
    let neg_b = rneg(d, b);
    let neg_c = rneg(d, c);
    let e00 = rmul(d, inv_d, dd);
    let e01 = rmul(d, inv_d, neg_b);
    let e10 = rmul(d, inv_d, neg_c);
    let e11 = rmul(d, inv_d, a);

    let zero_n = d.zero();
    let cond_j = NatOps::beq(d, j, zero_n);
    let row0 = bool_select_rat(d, cond_j, e00, e01);
    let row1 = bool_select_rat(d, cond_j, e10, e11);
    let cond_i = NatOps::beq(d, i, zero_n);
    let body = bool_select_rat(d, cond_i, row0, row1);

    let value = {
        let with_j = d.lam_fv(j_fv, nat, body);
        let with_i = d.lam_fv(i_fv, nat, with_j);
        d.lam_fv(a_fv, mty, with_i)
    };
    let ty = {
        let over_j = d.arrow(nat, carrier);
        let over_i = d.arrow(nat, over_j);
        d.arrow(mty, over_i)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mat_inv2,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAT_INV2_HEIGHT),
    })
}

/// `Nat` numeral `n`, `Rat.ofInt` of it, cast through `Int.ofNat`/`Int.negSucc`
/// as needed — duplicated from [`super::matrix_transpose::int_numeral`]/
/// [`super::matrix_transpose::my_of_int`] (both private there).
fn int_numeral(d: &mut IntDev<'_>, n: i64) -> ExprId {
    if n >= 0 {
        let nat = d.num(u32::try_from(n).expect("non-negative"));
        d.of_nat(nat)
    } else {
        let nat = d.num(u32::try_from(-n - 1).expect("negative"));
        d.neg_succ(nat)
    }
}

fn my_of_int(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    d.const_app(p.of_int, &[x])
}

/// A closed `Nat → Nat → Rat` term for the concrete 2×2 matrix `[[a00, a01],
/// [a10, a11]]` — duplicated from
/// [`super::matrix_transpose::const2x2`] (private there).
fn const2x2(d: &mut IntDev<'_>, p: RatPrelude, a00: i64, a01: i64, a10: i64, a11: i64) -> ExprId {
    let nat = d.nat_ty();
    let zero_n = d.zero();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let q00 = {
        let n = int_numeral(d, a00);
        my_of_int(d, p, n)
    };
    let q01 = {
        let n = int_numeral(d, a01);
        my_of_int(d, p, n)
    };
    let q10 = {
        let n = int_numeral(d, a10);
        my_of_int(d, p, n)
    };
    let q11 = {
        let n = int_numeral(d, a11);
        my_of_int(d, p, n)
    };

    let cond_j = NatOps::beq(d, j, zero_n);
    let row0 = bool_select_rat(d, cond_j, q00, q01);
    let row1 = bool_select_rat(d, cond_j, q10, q11);
    let cond_i = NatOps::beq(d, i, zero_n);
    let body = bool_select_rat(d, cond_i, row0, row1);

    let with_j = d.lam_fv(j_fv, nat, body);
    d.lam_fv(i_fv, nat, with_j)
}

/// `Rat.matInv2_eval_example : matInv2 A 0 0 = ofInt (-7)`, for the concrete
/// `A := [[2, 3], [5, 7]]` (`det2 2 3 5 7 = -1`, so `invD = -1` and `matInv2
/// A 0 0 = invD * (A 1 1) = (-1)*7 = -7`).
///
/// **The discriminating evaluation test [`declare_mat_inv2`]'s new
/// `Definition` needs** (module doc): `A`'s four entries `2,3,5,7` are
/// distinct, so a `matInv2` that swapped the diagonal (used `A 0 0` instead
/// of `A 1 1`) would produce `-2`, not `-7`, and one that dropped the sign
/// flip on an off-diagonal entry would produce a value with the wrong sign
/// at `(0,1)`/`(1,0)` — either mistake is refused outright by the trusted
/// gate rather than accepted vacuously.
fn declare_mat_inv2_eval_example(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.mat_inv2_eval_example, 0, &|d, _v| {
        let a_mat = const2x2(d, p, 2, 3, 5, 7);
        let ainv = rmat_inv2(d, p, a_mat);
        let zero_idx = d.num(0);
        let lhs = d.apply(ainv, &[zero_idx, zero_idx]);
        let expected = {
            let n = int_numeral(d, -7);
            my_of_int(d, p, n)
        };
        let stmt = req(d, lhs, expected);
        let proof = rrefl(d, expected);
        (stmt, proof)
    })
}

/// Declare `theorem name : ∀ (A : Nat → Nat → Rat), Not (det2 (A 0 0) (A 0 1) (A 1 0) (A 1 1) = 0) → concl`, given closures building the conclusion
/// and the proof from `A` (and the hypothesis, for the proof).
fn mat_theorem_hyp(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    name: NameId,
    build_concl: &dyn Fn(&mut IntDev<'_>, ExprId) -> ExprId,
    build_proof: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId) -> ExprId,
) -> Result<(), KernelError> {
    let mty = mat_ty(d);
    let a_fv = d.fresh_fvar();
    let a_mat = d.kernel().fvar(a_fv);
    let (_a, _b, _c, _dd, det, _inv_d) = entries(d, p, a_mat);
    let hyp = det2_ne_zero(d, p, det);
    let concl = build_concl(d, a_mat);

    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let body = build_proof(d, a_mat, h);

    let ty0 = d.arrow(hyp, concl);
    let value0 = d.lam_fv(h_fv, hyp, body);
    let ty = d.pi_fv(a_fv, mty, ty0);
    let value = d.lam_fv(a_fv, mty, value0);
    d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })
}

/// The `Ainv*A = I` entry proof: bridge `matMul (matInv2 A) A 2 i j` (a
/// named-constant term) down to the raw two-term sum via `Rat.zero_add`,
/// then finish with `super::matrix`'s own `inv2_*` lemma — term-for-term the
/// same statement (module doc's "why each entry needs a different amount of
/// algebra").
fn left_entry_proof(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    lhs_named: ExprId,
    term0: ExprId,
    term1: ExprId,
    final_target: ExprId,
    inv2_lemma: NameId,
    inv2_args: &[ExprId],
) -> ExprId {
    let zero_r = rzero(d, p);
    let zero_plus_term0 = radd(d, zero_r, term0);
    let padded = radd(d, zero_plus_term0, term1);
    let bridge = rrefl(d, padded);

    let z_add = d.lemma(p.zero_add, &[term0]); // 0+term0 = term0
    let step2 = rcongr(d, zero_plus_term0, term0, z_add, &|d, t| radd(d, t, term1));
    let unpadded = radd(d, term0, term1);

    let final_pf = d.lemma(inv2_lemma, inv2_args); // term0+term1 = final_target

    let (_, proof) = rchain(
        d,
        lhs_named,
        &[
            (padded, bridge),
            (unpadded, step2),
            (final_target, final_pf),
        ],
    );
    proof
}

/// `Rat.matInv2_matMul_top_left : ∀ A, Not (det2 (A 0 0) (A 0 1) (A 1 0) (A
/// 1 1) = 0) → matMul (matInv2 A) A 2 0 0 = matId 0 0`.
fn declare_matinv2_matmul_top_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    mat_theorem_hyp(
        d,
        p,
        p.matinv2_matmul_top_left,
        &|d, a_mat| {
            let ainv = rmat_inv2(d, p, a_mat);
            let zero_n = d.zero();
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, ainv, a_mat, two_n, zero_n, zero_n);
            let matid = d.const_app(p.mat_id, &[zero_n, zero_n]);
            req(d, lhs, matid)
        },
        &|d, a_mat, h| {
            let (a, b, c, dd, _det, inv_d) = entries(d, p, a_mat);
            let ainv = rmat_inv2(d, p, a_mat);
            let zero_n = d.zero();
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, ainv, a_mat, two_n, zero_n, zero_n);
            let neg_b = rneg(d, b);
            let e00 = rmul(d, inv_d, dd);
            let e01 = rmul(d, inv_d, neg_b);
            let term0 = rmul(d, e00, a); // (invD*d)*a
            let term1 = rmul(d, e01, c); // (invD*(-b))*c
            let one = rone(d, p);
            left_entry_proof(
                d,
                p,
                lhs,
                term0,
                term1,
                one,
                p.inv2_top_left,
                &[a, b, c, dd, h],
            )
        },
    )
}

/// `Rat.matInv2_matMul_top_right : ∀ A, Not (det2 … = 0) → matMul (matInv2
/// A) A 2 0 1 = matId 0 1`.
fn declare_matinv2_matmul_top_right(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    mat_theorem_hyp(
        d,
        p,
        p.matinv2_matmul_top_right,
        &|d, a_mat| {
            let ainv = rmat_inv2(d, p, a_mat);
            let zero_n = d.zero();
            let one_n = d.num(1);
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, ainv, a_mat, two_n, zero_n, one_n);
            let matid = d.const_app(p.mat_id, &[zero_n, one_n]);
            req(d, lhs, matid)
        },
        &|d, a_mat, h| {
            let (a, b, c, dd, _det, inv_d) = entries(d, p, a_mat);
            let ainv = rmat_inv2(d, p, a_mat);
            let zero_n = d.zero();
            let one_n = d.num(1);
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, ainv, a_mat, two_n, zero_n, one_n);
            let neg_b = rneg(d, b);
            let e00 = rmul(d, inv_d, dd);
            let e01 = rmul(d, inv_d, neg_b);
            let term0 = rmul(d, e00, b); // (invD*d)*b
            let term1 = rmul(d, e01, dd); // (invD*(-b))*d
            let zero_r = rzero(d, p);
            left_entry_proof(
                d,
                p,
                lhs,
                term0,
                term1,
                zero_r,
                p.inv2_top_right,
                &[a, b, c, dd, h],
            )
        },
    )
}

/// `Rat.matInv2_matMul_bottom_left : ∀ A, Not (det2 … = 0) → matMul (matInv2
/// A) A 2 1 0 = matId 1 0`.
fn declare_matinv2_matmul_bottom_left(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    mat_theorem_hyp(
        d,
        p,
        p.matinv2_matmul_bottom_left,
        &|d, a_mat| {
            let ainv = rmat_inv2(d, p, a_mat);
            let one_n = d.num(1);
            let zero_n = d.zero();
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, ainv, a_mat, two_n, one_n, zero_n);
            let matid = d.const_app(p.mat_id, &[one_n, zero_n]);
            req(d, lhs, matid)
        },
        &|d, a_mat, h| {
            let (a, b, c, dd, _det, inv_d) = entries(d, p, a_mat);
            let ainv = rmat_inv2(d, p, a_mat);
            let one_n = d.num(1);
            let zero_n = d.zero();
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, ainv, a_mat, two_n, one_n, zero_n);
            let neg_c = rneg(d, c);
            let e10 = rmul(d, inv_d, neg_c);
            let e11 = rmul(d, inv_d, a);
            let term0 = rmul(d, e10, a); // (invD*(-c))*a
            let term1 = rmul(d, e11, c); // (invD*a)*c
            let zero_r = rzero(d, p);
            left_entry_proof(
                d,
                p,
                lhs,
                term0,
                term1,
                zero_r,
                p.inv2_bottom_left,
                &[a, b, c, dd, h],
            )
        },
    )
}

/// `Rat.matInv2_matMul_bottom_right : ∀ A, Not (det2 … = 0) → matMul
/// (matInv2 A) A 2 1 1 = matId 1 1`.
fn declare_matinv2_matmul_bottom_right(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    mat_theorem_hyp(
        d,
        p,
        p.matinv2_matmul_bottom_right,
        &|d, a_mat| {
            let ainv = rmat_inv2(d, p, a_mat);
            let one_n = d.num(1);
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, ainv, a_mat, two_n, one_n, one_n);
            let matid = d.const_app(p.mat_id, &[one_n, one_n]);
            req(d, lhs, matid)
        },
        &|d, a_mat, h| {
            let (a, b, c, dd, _det, inv_d) = entries(d, p, a_mat);
            let ainv = rmat_inv2(d, p, a_mat);
            let one_n = d.num(1);
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, ainv, a_mat, two_n, one_n, one_n);
            let neg_c = rneg(d, c);
            let e10 = rmul(d, inv_d, neg_c);
            let e11 = rmul(d, inv_d, a);
            let term0 = rmul(d, e10, b); // (invD*(-c))*b
            let term1 = rmul(d, e11, dd); // (invD*a)*d
            let one = rone(d, p);
            left_entry_proof(
                d,
                p,
                lhs,
                term0,
                term1,
                one,
                p.inv2_bottom_right,
                &[a, b, c, dd, h],
            )
        },
    )
}

/// The `A*Ainv = I` entry proof (module doc's "why each entry needs a
/// different amount of algebra"): bridge `matMul A (matInv2 A) 2 i j` down
/// to `x*(invD*y) + w*(invD*z)` via `Rat.zero_add`, reassociate each term to
/// pull `invD` out (`middle_swap`, twice), combine via `Rat.left_distrib`
/// (reversed) into EXACTLY `adj_lemma`'s stated LHS `x*y + w*z`, rewrite via
/// `adj_lemma` to `det`/`Rat.zero`, then finish with
/// `Rat.mul_inv_cancel_of_ne_zero` (diagonal, `diag = Some((det, h))`) or
/// `Rat.mul_zero` (off-diagonal, `diag = None`).
#[allow(clippy::too_many_arguments)]
fn right_entry_proof(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    lhs_named: ExprId,
    x: ExprId,
    y: ExprId,
    w: ExprId,
    z: ExprId,
    inv_d: ExprId,
    adj_lemma: NameId,
    adj_args: &[ExprId],
    diag: Option<(ExprId, ExprId)>,
) -> ExprId {
    let zero_r = rzero(d, p);
    let invd_y = rmul(d, inv_d, y);
    let term0 = rmul(d, x, invd_y);
    let invd_z = rmul(d, inv_d, z);
    let term1 = rmul(d, w, invd_z);
    let zero_plus_term0 = radd(d, zero_r, term0);
    let padded = radd(d, zero_plus_term0, term1);
    let bridge = rrefl(d, padded);

    let z_add = d.lemma(p.zero_add, &[term0]); // 0+term0 = term0
    let step2 = rcongr(d, zero_plus_term0, term0, z_add, &|d, t| radd(d, t, term1));
    let unpadded = radd(d, term0, term1);

    // reassociate term0 = x*(invD*y) into invD*(x*y)
    let xy = rmul(d, x, y);
    let invd_xy = rmul(d, inv_d, xy);
    let ms1 = middle_swap(d, p, inv_d, x, y); // invD*(x*y) = x*(invD*y)
    let step3_pf = rsymm(d, invd_xy, term0, ms1); // x*(invD*y) = invD*(x*y)
    let step3 = rcongr(d, term0, invd_xy, step3_pf, &|d, t| radd(d, t, term1));
    let mid3 = radd(d, invd_xy, term1);

    // reassociate term1 = w*(invD*z) into invD*(w*z)
    let wz = rmul(d, w, z);
    let invd_wz = rmul(d, inv_d, wz);
    let ms2 = middle_swap(d, p, inv_d, w, z); // invD*(w*z) = w*(invD*z)
    let step4_pf = rsymm(d, invd_wz, term1, ms2); // w*(invD*z) = invD*(w*z)
    let step4 = rcongr(d, term1, invd_wz, step4_pf, &|d, t| radd(d, invd_xy, t));
    let mid4 = radd(d, invd_xy, invd_wz);

    // combine: invD*(x*y) + invD*(w*z) = invD*(x*y + w*z)
    let combined_inner = radd(d, xy, wz);
    let combined = rmul(d, inv_d, combined_inner);
    let distrib_fwd = d.lemma(p.left_distrib, &[inv_d, xy, wz]); // invD*(xy+wz) = invD*xy+invD*wz
    let step5 = rsymm(d, combined, mid4, distrib_fwd);

    let adj_pf = d.lemma(adj_lemma, adj_args); // xy+wz = det, or xy+wz = 0
    let (target, step6, final_target, final_step) = if let Some((det, h)) = diag {
        let step = rcongr(d, combined_inner, det, adj_pf, &|d, t| rmul(d, inv_d, t));
        let one = rone(d, p);
        let cancel = inv_det2_cancel(d, p, det, inv_d, h);
        (rmul(d, inv_d, det), step, one, cancel)
    } else {
        let step = rcongr(d, combined_inner, zero_r, adj_pf, &|d, t| rmul(d, inv_d, t));
        let mz = d.lemma(p.mul_zero, &[inv_d]); // invD*0 = 0
        (rmul(d, inv_d, zero_r), step, zero_r, mz)
    };

    let (_, proof) = rchain(
        d,
        lhs_named,
        &[
            (padded, bridge),
            (unpadded, step2),
            (mid3, step3),
            (mid4, step4),
            (combined, step5),
            (target, step6),
            (final_target, final_step),
        ],
    );
    proof
}

/// `Rat.matMul_matInv2_top_left : ∀ A, Not (det2 … = 0) → matMul A (matInv2
/// A) 2 0 0 = matId 0 0`.
fn declare_matmul_matinv2_top_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    mat_theorem_hyp(
        d,
        p,
        p.matmul_matinv2_top_left,
        &|d, a_mat| {
            let ainv = rmat_inv2(d, p, a_mat);
            let zero_n = d.zero();
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, a_mat, ainv, two_n, zero_n, zero_n);
            let matid = d.const_app(p.mat_id, &[zero_n, zero_n]);
            req(d, lhs, matid)
        },
        &|d, a_mat, h| {
            let (a, b, c, dd, det, inv_d) = entries(d, p, a_mat);
            let ainv = rmat_inv2(d, p, a_mat);
            let zero_n = d.zero();
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, a_mat, ainv, two_n, zero_n, zero_n);
            let neg_c = rneg(d, c);
            // matMul A Ainv 2 0 0 = A 0 0 * Ainv 0 0 + A 0 1 * Ainv 1 0
            //                     = a*(invD*d) + b*(invD*(-c))
            right_entry_proof(
                d,
                p,
                lhs,
                a,
                dd,
                b,
                neg_c,
                inv_d,
                p.mul_adj2_top_left,
                &[a, b, c, dd],
                Some((det, h)),
            )
        },
    )
}

/// `Rat.matMul_matInv2_top_right : ∀ A, Not (det2 … = 0) → matMul A
/// (matInv2 A) 2 0 1 = matId 0 1`.
fn declare_matmul_matinv2_top_right(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    mat_theorem_hyp(
        d,
        p,
        p.matmul_matinv2_top_right,
        &|d, a_mat| {
            let ainv = rmat_inv2(d, p, a_mat);
            let zero_n = d.zero();
            let one_n = d.num(1);
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, a_mat, ainv, two_n, zero_n, one_n);
            let matid = d.const_app(p.mat_id, &[zero_n, one_n]);
            req(d, lhs, matid)
        },
        &|d, a_mat, _h| {
            let (a, b, c, dd, _det, inv_d) = entries(d, p, a_mat);
            let ainv = rmat_inv2(d, p, a_mat);
            let zero_n = d.zero();
            let one_n = d.num(1);
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, a_mat, ainv, two_n, zero_n, one_n);
            let neg_b = rneg(d, b);
            // matMul A Ainv 2 0 1 = A 0 0 * Ainv 0 1 + A 0 1 * Ainv 1 1
            //                     = a*(invD*(-b)) + b*(invD*a)
            right_entry_proof(
                d,
                p,
                lhs,
                a,
                neg_b,
                b,
                a,
                inv_d,
                p.mul_adj2_top_right,
                &[a, b, c, dd],
                None,
            )
        },
    )
}

/// `Rat.matMul_matInv2_bottom_left : ∀ A, Not (det2 … = 0) → matMul A
/// (matInv2 A) 2 1 0 = matId 1 0`.
fn declare_matmul_matinv2_bottom_left(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    mat_theorem_hyp(
        d,
        p,
        p.matmul_matinv2_bottom_left,
        &|d, a_mat| {
            let ainv = rmat_inv2(d, p, a_mat);
            let one_n = d.num(1);
            let zero_n = d.zero();
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, a_mat, ainv, two_n, one_n, zero_n);
            let matid = d.const_app(p.mat_id, &[one_n, zero_n]);
            req(d, lhs, matid)
        },
        &|d, a_mat, _h| {
            let (a, b, c, dd, _det, inv_d) = entries(d, p, a_mat);
            let ainv = rmat_inv2(d, p, a_mat);
            let one_n = d.num(1);
            let zero_n = d.zero();
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, a_mat, ainv, two_n, one_n, zero_n);
            let neg_c = rneg(d, c);
            // matMul A Ainv 2 1 0 = A 1 0 * Ainv 0 0 + A 1 1 * Ainv 1 0
            //                     = c*(invD*d) + d*(invD*(-c))
            right_entry_proof(
                d,
                p,
                lhs,
                c,
                dd,
                dd,
                neg_c,
                inv_d,
                p.mul_adj2_bottom_left,
                &[a, b, c, dd],
                None,
            )
        },
    )
}

/// `Rat.matMul_matInv2_bottom_right : ∀ A, Not (det2 … = 0) → matMul A
/// (matInv2 A) 2 1 1 = matId 1 1`.
fn declare_matmul_matinv2_bottom_right(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    mat_theorem_hyp(
        d,
        p,
        p.matmul_matinv2_bottom_right,
        &|d, a_mat| {
            let ainv = rmat_inv2(d, p, a_mat);
            let one_n = d.num(1);
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, a_mat, ainv, two_n, one_n, one_n);
            let matid = d.const_app(p.mat_id, &[one_n, one_n]);
            req(d, lhs, matid)
        },
        &|d, a_mat, h| {
            let (a, b, c, dd, det, inv_d) = entries(d, p, a_mat);
            let ainv = rmat_inv2(d, p, a_mat);
            let one_n = d.num(1);
            let two_n = d.num(2);
            let lhs = rmat_mul(d, p, a_mat, ainv, two_n, one_n, one_n);
            let neg_b = rneg(d, b);
            // matMul A Ainv 2 1 1 = A 1 0 * Ainv 0 1 + A 1 1 * Ainv 1 1
            //                     = c*(invD*(-b)) + d*(invD*a)
            right_entry_proof(
                d,
                p,
                lhs,
                c,
                neg_b,
                dd,
                a,
                inv_d,
                p.mul_adj2_bottom_right,
                &[a, b, c, dd],
                Some((det, h)),
            )
        },
    )
}

/// `Rat.matInv2_example : matMul A (matInv2 A) 2 0 0 = ofInt 1`, for the
/// concrete `A := [[2, 1], [1, 1]]` (`det2 2 1 1 1 = 1`).
///
/// **Row 3 of the graded family, the ADR-0825 collapse**: the proof term is
/// [`RatPrelude::matmul_matinv2_top_left`] itself, applied at this concrete
/// matrix and the same `D ≠ 0` construction
/// `super::matrix::cramer2_solves_computes_an_explicit_two_by_two_system`
/// uses (`Rat.nat_div_succ_pos` at `Nat.le 1 1`, refuted-equality route),
/// rather than at symbolic entries. Its conclusion (`matMul A (matInv2 A) 2
/// 0 0 = matId 0 0`, still in named-constant form) is bridged to the plain
/// numeral `ofInt 1` by the kernel's own delta/beta/iota computation — no
/// separate `axeyum-cas` producer/verifier pair, per ADR-0825 §"Decision".
fn declare_mat_inv2_example(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.mat_inv2_example, 0, &|d, _v| {
        use super::ops::{rat_eq_rewrite, rlt};

        // A concrete matrix built from `Rat.natDivSucc`-literals, matching
        // `super::matrix::cramer2_solves_computes_an_explicit_two_by_two_system`'s
        // own construction EXACTLY (not `const2x2`'s `ofInt` representation)
        // so `a_mat`'s entries and `h3`'s `det` term are the SAME `ExprId`s,
        // not merely defeq across two different `Rat` numeral encodings.
        let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
            let numerator = d.num(k);
            let index = d.num(0);
            d.const_app(p.nat_div_succ, &[numerator, index])
        };
        let a2 = literal(d, 2);
        let b2 = literal(d, 1);
        let c2 = literal(d, 1);
        let dd2 = literal(d, 1);

        let nat = d.nat_ty();
        let zero_n = d.zero();
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let cond_j = NatOps::beq(d, j, zero_n);
        let row0 = bool_select_rat(d, cond_j, a2, b2);
        let row1 = bool_select_rat(d, cond_j, c2, dd2);
        let cond_i = NatOps::beq(d, i, zero_n);
        let body = bool_select_rat(d, cond_i, row0, row1);
        let a_mat = {
            let with_j = d.lam_fv(j_fv, nat, body);
            d.lam_fv(i_fv, nat, with_j)
        };

        let ainv = rmat_inv2(d, p, a_mat);
        let zero_idx = d.num(0);
        let two_n = d.num(2);
        let lhs = rmat_mul(d, p, a_mat, ainv, two_n, zero_idx, zero_idx);

        // D := det2 2 1 1 1 = 1 ≠ 0, via 0 < D (same route the cramer2_solves
        // worked example uses): D reduces to `natDivSucc 1 0`, and
        // `nat_div_succ_pos` gives `0 < natDivSucc 1 0` directly.
        let det = d.const_app(p.det2, &[a2, b2, c2, dd2]);
        let zero_r = rzero(d, p);
        let one_nat = d.num(1);
        let zero_nat = d.num(0);
        let le_pf = d.lemma(p.int.nat.le_refl, &[one_nat]); // Nat.le 1 1
        let pos = d.lemma(p.nat_div_succ_pos, &[one_nat, zero_nat, le_pf]); // 0 < natDivSucc 1 0
        let heq_fv = d.fresh_fvar();
        let heq = d.kernel().fvar(heq_fv);
        let eq_ty = req(d, det, zero_r);
        let rewritten = rat_eq_rewrite(d, det, zero_r, heq, pos, &|d, t| rlt(d, p, zero_r, t));
        let irrefl = d.lemma(p.lt_irrefl, &[zero_r]);
        let false_proof = d.apply(irrefl, &[rewritten]);
        let h3 = d.lam_fv(heq_fv, eq_ty, false_proof); // Not (Eq Rat det Rat.zero)

        let expected = rone(d, p);
        let stmt = req(d, lhs, expected);
        let proof = d.lemma(p.matmul_matinv2_top_left, &[a_mat, h3]);
        (stmt, proof)
    })
}
