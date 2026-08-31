//! **`Rat.matTranspose`** — matrix transpose at *symbolic* dimension, and
//! `(AB)^T = B^T A^T`, the classical transpose-of-product law.
//!
//! ## Graded statement family (ADR-0603, ADR-0716)
//!
//! [ADR-0716](../../../../../docs/research/09-decisions/adr-0716-row-two-of-a-decidable-subject.md)
//! measures that for ℚ the analysis-style row 2 mechanism is provably empty
//! (`Rat.le_total` is a proved, axiom-free theorem here), and that a
//! statement with no comparison and no unbounded search never reaches a
//! boundary in the first place. `matTranspose_mul` is a pure identity — no
//! comparison, no search — so it has **no row 2**, argued from shape rather
//! than from a failed search.
//!
//! The family is therefore **row 1 + row 3**, and
//! [ADR-0825](../../../../../docs/research/09-decisions/adr-0825-a-decidable-family-can-run-row-1-and-row-3-as-one-statement.md)'s
//! collapse applies directly: [`declare_mat_transpose_mul_example`] is the
//! SAME declaration, [`RatPrelude::mat_transpose_mul`], applied at concrete
//! numeral matrices rather than symbolic ones, with the resulting equation
//! bridged to a plain numeral (`ofInt 174`) by the kernel's own delta/beta/
//! iota computation — no separate CAS producer/verifier pair. Row 4 (a
//! labeled import) is not attempted.
//!
//! ## The encoding, reusing [`super::matrix_n`]'s
//!
//! An `m × n` matrix is a function `Nat → Nat → Rat` plus explicit bounds,
//! exactly [`super::matrix_n`]'s own encoding — no `List`, `Finset` or
//! product type, none of which this kernel has in any prelude.
//! `Rat.matTranspose A i j := A j i` needs no bound at all: like
//! [`super::RatPrelude::mat_id`], it is defined at every index pair at once,
//! and only ever appears under a bound hypothesis supplied by whichever
//! theorem consumes it.
//!
//! ## Every statement here is POINTWISE, and that is forced
//!
//! `funext` is **absent** from this kernel (positive control of the same
//! kind, present: `congrFun'`). So `matTranspose_transpose` and
//! `matTranspose_mul` both conclude at a scalar entry
//! (`… i j = … i j`), never as an `Eq` between two `Nat → Nat → Rat` values —
//! the same discipline [`super::matrix_n`]'s module doc states and
//! [`super::RatPrelude::sum_range_congr`] already uses.
//!
//! ## Why `matTranspose_mul` is assembly, not new induction
//!
//! `matTranspose (matMul A B k) i j` unfolds (delta `matTranspose`, delta
//! `matMul`) to `sumRange (fun t => A j t * B t i) k`; `matMul (matTranspose
//! B) (matTranspose A) k i j` unfolds to `sumRange (fun t => B t i * A j t)
//! k`. The two summands differ by exactly one `Rat.mul_comm`, applied
//! pointwise through [`super::RatPrelude::sum_range_congr`] — no interchange
//! of summation order is needed (unlike `matMul_assoc`, which needs
//! `sumRange_swap`), because transpose only swaps the two INDEX arguments,
//! never the two matrices being summed over.
//!
//! ## The evaluation test this file's new `Definition` needs
//!
//! [`super::matrix_n`]'s own module doc and this repository's Hard Rules both
//! require a concrete, DISCRIMINATING evaluation test for any new
//! `Definition`: the kernel accepts a well-typed `Definition` regardless of
//! whether it computes the intended value. A transpose that forgot to swap
//! its two index arguments (`matTranspose A i j := A i j`, a no-op) would
//! still type-check, and would still satisfy the involution law
//! `matTranspose_transpose` (composing a no-op with itself is still a
//! no-op) — so that algebraic law is NOT a substitute for a concrete check.
//! [`declare_mat_transpose_eval_example`] uses a 2×2 matrix with two
//! DISTINCT off-diagonal entries (`3` at `(0,1)`, `5` at `(1,0)`) so a
//! forgotten swap would produce `3` where the theorem demands `5`, and the
//! kernel's trusted gate would refuse the declaration outright.

use super::RatPrelude;
use super::ops::{rat_theorem, rat_ty, req, rmul, rrefl};
use super::probability::bool_select_rat;
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.matTranspose`: above [`super::matrix_n::MAT_MUL_HEIGHT`]
/// (46) and above every other height declared in this prelude so far,
/// following the "outranks everything it unfolds to" convention
/// [`super::defs`] sets. `matTranspose` does not call `matMul` in its own
/// value, but the monotone-bump convention keeps heights linear rather than
/// encoding a real dependency (`super::matrix::DET3_HEIGHT` does the same
/// relative to `DET2_HEIGHT`).
const MAT_TRANSPOSE_HEIGHT: u16 = 47;

/// Admit `Rat.matTranspose` and everything this file proves about it.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_matrix_transpose(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    declare_mat_transpose(d, p)?;
    declare_mat_transpose_transpose(d, p)?;
    declare_mat_transpose_mul(d, p)?;
    declare_mat_transpose_eval_example(d, p)?;
    declare_mat_transpose_mul_example(d, p)
}

/// `Nat → Nat → Rat`, the matrix type — duplicated from
/// [`super::matrix_n::mat_ty`] (private there) rather than promoting it,
/// to keep this file's diff to `matrix_n.rs` at zero.
fn mat_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let row = d.arrow(nat, carrier);
    d.arrow(nat, row)
}

/// `Rat.matTranspose A i j`.
fn rmat_transpose(d: &mut IntDev<'_>, p: RatPrelude, a: ExprId, i: ExprId, j: ExprId) -> ExprId {
    d.const_app(p.mat_transpose, &[a, i, j])
}

/// `Rat.matMul A B k i j`, duplicated from [`super::matrix_n::rmat_mul`]
/// (`pub(super)` there, but re-derived here to keep this file self-contained
/// against the same "outranks everything" convention as [`mat_ty`]).
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

/// Admit `Rat.matTranspose : (Nat → Nat → Rat) → Nat → Nat → Rat := fun A i
/// j => A j i` — the transpose, at every dimension at once (no bound
/// argument, matching [`super::RatPrelude::mat_id`]'s shape).
fn declare_mat_transpose(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let body = d.apply(a, &[j, i]);

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
        name: p.mat_transpose,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAT_TRANSPOSE_HEIGHT),
    })
}

/// `Rat.matTranspose_transpose : ∀ A i j, matTranspose (matTranspose A) i j
/// = A i j` — the involution law, `Eq.refl` (swapping the two index
/// arguments twice is the identity by pure computation).
fn declare_mat_transpose_transpose(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let at_matrix = d.const_app(p.mat_transpose, &[a]);
    let ata_matrix = d.const_app(p.mat_transpose, &[at_matrix]);
    let lhs = d.apply(ata_matrix, &[i, j]);
    let rhs = d.apply(a, &[i, j]);
    let stmt = req(d, lhs, rhs);
    let proof = rrefl(d, rhs);

    let ty = {
        let t = d.pi_fv(j_fv, nat, stmt);
        let t = d.pi_fv(i_fv, nat, t);
        d.pi_fv(a_fv, mty, t)
    };
    let value = {
        let v = d.lam_fv(j_fv, nat, proof);
        let v = d.lam_fv(i_fv, nat, v);
        d.lam_fv(a_fv, mty, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_transpose_transpose,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.matTranspose_mul : ∀ A B k i j, matTranspose (matMul A B k) i j =
/// matMul (matTranspose B) (matTranspose A) k i j` — `(AB)^T = B^T A^T`,
/// stated pointwise at symbolic dimension `k`.
///
/// **Row 1 of the graded family** (module doc). The proof is one
/// `sum_range_congr` around one `mul_comm`, applied pointwise to the summand
/// — see the module doc's "assembly, not new induction" section for why no
/// `sumRange_swap` interchange is needed here, unlike `matMul_assoc`.
fn declare_mat_transpose_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    // stmt: matTranspose (matMul A B k) i j = matMul (matTranspose B) (matTranspose A) k i j
    let ab_matrix = d.const_app(p.mat_mul, &[a, b, k]);
    let lhs = rmat_transpose(d, p, ab_matrix, i, j);
    let at_matrix = d.const_app(p.mat_transpose, &[a]);
    let bt_matrix = d.const_app(p.mat_transpose, &[b]);
    let rhs = rmat_mul(d, p, bt_matrix, at_matrix, k, i, j);
    let stmt = req(d, lhs, rhs);

    // F1 := fun t => A j t * B t i   (the unfolded LHS summand)
    let f1 = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ajt = d.apply(a, &[j, t]);
        let bti = d.apply(b, &[t, i]);
        let body = rmul(d, ajt, bti);
        d.lam_fv(t_fv, nat, body)
    };
    // F2 := fun t => B t i * A j t   (the unfolded RHS summand)
    let f2 = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let bti = d.apply(b, &[t, i]);
        let ajt = d.apply(a, &[j, t]);
        let body = rmul(d, bti, ajt);
        d.lam_fv(t_fv, nat, body)
    };
    // pointwise: fun t => mul_comm (A j t) (B t i) : Eq (A j t * B t i) (B t i * A j t)
    let pointwise = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ajt = d.apply(a, &[j, t]);
        let bti = d.apply(b, &[t, i]);
        let body = d.lemma(p.mul_comm, &[ajt, bti]);
        d.lam_fv(t_fv, nat, body)
    };
    // proof : Eq (sumRange F1 k) (sumRange F2 k) -- defeq-bridges back to `stmt`
    // via delta-unfolding `matTranspose`/`matMul` on both sides (module doc).
    let proof = d.lemma(p.sum_range_congr, &[f1, f2, k, pointwise]);

    let ty = {
        let t = d.pi_fv(j_fv, nat, stmt);
        let t = d.pi_fv(i_fv, nat, t);
        let t = d.pi_fv(k_fv, nat, t);
        let t = d.pi_fv(b_fv, mty, t);
        d.pi_fv(a_fv, mty, t)
    };
    let value = {
        let v = d.lam_fv(j_fv, nat, proof);
        let v = d.lam_fv(i_fv, nat, v);
        let v = d.lam_fv(k_fv, nat, v);
        let v = d.lam_fv(b_fv, mty, v);
        d.lam_fv(a_fv, mty, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_transpose_mul,
        uparams: vec![],
        ty,
        value,
    })
}

/// The `Int` numeral `n` (`Int.ofNat`/`Int.negSucc` normal form) — a local
/// copy of [`super::matrix::int_numeral`] (private there), needed for the
/// two concrete examples below.
fn int_numeral(d: &mut IntDev<'_>, n: i64) -> ExprId {
    if n >= 0 {
        let nat = d.num(u32::try_from(n).expect("non-negative"));
        d.of_nat(nat)
    } else {
        let nat = d.num(u32::try_from(-n - 1).expect("negative"));
        d.neg_succ(nat)
    }
}

/// `Rat.ofInt x`, a local copy of [`super::matrix::of_int`] (private there).
fn my_of_int(d: &mut IntDev<'_>, p: RatPrelude, x: ExprId) -> ExprId {
    d.const_app(p.of_int, &[x])
}

/// A closed `Nat → Nat → Rat` term for the concrete 2×2 matrix `[[a00, a01],
/// [a10, a11]]`, built the same way [`super::RatPrelude::mat_id`] builds its
/// `Nat.beq`-selected diagonal — never registered as a named `Definition`,
/// since it exists only to instantiate the two examples below.
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

/// `Rat.matTranspose_eval_example : matTranspose A 0 1 = ofInt 5`, for the
/// concrete `A := [[2, 3], [5, 7]]`.
///
/// **The discriminating evaluation test [`declare_mat_transpose`]'s new
/// `Definition` needs** (module doc): `A`'s off-diagonal entries `3` (at
/// `(0,1)`) and `5` (at `(1,0)`) are distinct, so a transpose that forgot to
/// swap its index arguments would produce `3` here, not `5`, and the trusted
/// gate would refuse this declaration outright rather than accept it
/// vacuously.
fn declare_mat_transpose_eval_example(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    rat_theorem(d, p.mat_transpose_eval_example, 0, &|d, _v| {
        let a_mat = const2x2(d, p, 2, 3, 5, 7);
        let zero_idx = d.num(0);
        let one_idx = d.num(1);
        let lhs = rmat_transpose(d, p, a_mat, zero_idx, one_idx);
        let expected = {
            let n = int_numeral(d, 5);
            my_of_int(d, p, n)
        };
        let stmt = req(d, lhs, expected);
        let proof = rrefl(d, expected);
        (stmt, proof)
    })
}

/// `Rat.matTranspose_mul_example : matTranspose (matMul A B 2) 0 1 = ofInt
/// 174`, for the concrete `A := [[2, 3], [5, 7]]`, `B := [[11, 13], [17,
/// 19]]`.
///
/// **Row 3 of the graded family, and the ADR-0825 collapse**: the proof
/// term is [`RatPrelude::mat_transpose_mul`] itself, applied at these four
/// concrete matrices/dimension/indices rather than at symbolic ones — the
/// SAME declaration used for row 1, executed a second time. Its conclusion
/// (`matTranspose (matMul A B 2) 0 1 = matMul (matTranspose B) (matTranspose
/// A) 2 0 1`, still in named-constant form) is bridged to the plain numeral
/// `ofInt 174` by the kernel's own delta/beta/iota computation — no separate
/// `axeyum-cas` producer/verifier pair, per ADR-0825 §"Decision".
///
/// `174` is independently computed as `(AB)^T(0,1) = (AB)(1,0)`, i.e.
/// `A(1,0)*B(0,0) + A(1,1)*B(1,0) = 5*11 + 7*17 = 55 + 119 = 174`. It also
/// discriminates the WRONG transpose-of-product law `(AB)^T = A^T B^T`
/// (forgetting to reverse the order): that product's `(0,1)` entry is
/// `A(0,0)*B(0,1) + A(1,0)*B(1,1) = 2*13 + 5*19 = 26 + 95 = 121`, not `174`.
fn declare_mat_transpose_mul_example(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    rat_theorem(d, p.mat_transpose_mul_example, 0, &|d, _v| {
        let a_mat = const2x2(d, p, 2, 3, 5, 7);
        let b_mat = const2x2(d, p, 11, 13, 17, 19);
        let two = d.num(2);
        let zero_idx = d.num(0);
        let one_idx = d.num(1);

        let ab_matrix = d.const_app(p.mat_mul, &[a_mat, b_mat, two]);
        let lhs = rmat_transpose(d, p, ab_matrix, zero_idx, one_idx);

        let expected = {
            let n = int_numeral(d, 174);
            my_of_int(d, p, n)
        };
        let stmt = req(d, lhs, expected);
        let proof = d.lemma(p.mat_transpose_mul, &[a_mat, b_mat, two, zero_idx, one_idx]);
        (stmt, proof)
    })
}
