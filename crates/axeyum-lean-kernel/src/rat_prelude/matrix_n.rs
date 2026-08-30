//! **`Rat.matMul`** — matrix multiplication over ℚ at *symbolic* dimension,
//! the first matrix content in this kernel that is not fixed at 2×2 or 3×3.
//!
//! ## The encoding, and why no container type is needed
//!
//! [`super::vector`] represents an `n`-vector as a coefficient function
//! `Nat → Rat` plus an explicit bound, and gets Cauchy–Schwarz at arbitrary
//! `n` out of it. A matrix is the same idea one index up: an `m × n` matrix is
//! a function `Nat → Nat → Rat` together with explicit bounds. No `List`, no
//! `Finset`, no product type — none of which this kernel has in any prelude —
//! and `Rat.sumRange` already accepts exactly this shape (63 declarations in
//! this prelude take a `Nat → Nat → Rat`).
//!
//! `Rat.matMul A B k` has type `Nat → Nat → Rat`, i.e. **it is itself a
//! matrix**, so `matMul (matMul A B k) C m` is well-typed with no coercion and
//! associativity can be stated directly.
//!
//! ## Every statement here is POINTWISE, and that is forced
//!
//! `funext` is **absent** from this kernel (positive control of the same kind,
//! present: `congrFun'`). So two pointwise-equal functions are not
//! propositionally equal, and a matrix identity **cannot** be stated as an
//! `Eq` between two `Nat → Nat → Rat` values. Every theorem below therefore
//! concludes at a scalar:
//!
//! > `∀ … i j, matMul (matMul A B k) C m i j = matMul A (matMul B C m) k i j`
//!
//! This is not a workaround invented here — [`super::RatPrelude::sum_range_congr`]
//! already takes pointwise equality as its hypothesis for the same reason.
//!
//! ## Associativity is assembly, not new mathematics
//!
//! `(AB)C` and `A(BC)` differ by an interchange of summation order, and
//! [`super::RatPrelude::sum_range_swap`] (Fubini over a ℚ-valued double sum)
//! is exactly that interchange. The proof is four rewrites around it:
//!
//! 1. pull `C s j` inside the inner sum ([`sum_mul_const_right`], itself
//!    `mul_comm` + [`super::RatPrelude::mul_sum_range`] + `mul_comm`);
//! 2. `sum_range_swap`;
//! 3. `mul_assoc` under two nested [`super::RatPrelude::sum_range_congr`]s;
//! 4. pull `A i t` back out of the inner sum (`mul_sum_range`, symm).
//!
//! No induction on any dimension is performed in this file; every induction it
//! rests on was already done in [`super::sum`].

use super::RatPrelude;
use super::ops::{
    nat_eq_to_rat, radd, rat_ty, rchain, rcongr, req, rmul, rone, rrefl, rsum_range, rsymm, rzero,
};
use super::probability::{bool_select_rat, select_rat_false, select_rat_true};
use crate::KernelError;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Delta height for `Rat.matMul`: above `Rat.sumRange`
/// ([`super::sum::SUM_HEIGHT`] = 34), above `Rat.mul`, and above every other
/// height declared in this prelude (the highest so far is 44), following the
/// "outranks everything it unfolds to" convention [`super::defs`] sets.
const MAT_MUL_HEIGHT: u16 = 46;

/// Admit `Rat.matMul` and everything this file proves about it.
///
/// # Errors
///
/// Returns the trusted gate's rejection.
pub(super) fn declare_matrix_n(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_mat_mul(d, p)?;
    declare_mat_mul_zero(d, p)?;
    declare_mat_mul_succ(d, p)?;
    declare_mat_mul_assoc(d, p)?;
    declare_mat_mul_add_left(d, p)?;
    declare_mat_mul_add_right(d, p)?;
    declare_mat_mul_smul_left(d, p)?;
    declare_sum_range_delta(d, p)?;
    declare_mat_id(d, p)?;
    declare_mat_id_diag(d, p)?;
    declare_mat_id_off_diag(d, p)?;
    declare_mat_mul_id_left(d, p)?;
    declare_mat_mul_id_right(d, p)
}

/// `Nat → Nat → Rat`, the matrix type.
fn mat_ty(d: &mut IntDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let row = d.arrow(nat, carrier);
    d.arrow(nat, row)
}

/// `fun t => A i t * B t j` — the `(i, j)` summand of `A · B`.
fn mat_summand(d: &mut IntDev<'_>, a: ExprId, b: ExprId, i: ExprId, j: ExprId) -> ExprId {
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let ait = d.apply(a, &[i, t]);
    let btj = d.apply(b, &[t, j]);
    let body = rmul(d, ait, btj);
    let nat = d.nat_ty();
    d.lam_fv(t_fv, nat, body)
}

/// `Rat.matMul A B k i j`.
pub(super) fn rmat_mul(
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

/// Admit `Rat.matMul : (Nat → Nat → Rat) → (Nat → Nat → Rat) → Nat → Nat →
/// Nat → Rat := fun A B k i j => sumRange (fun t => A i t * B t j) k`.
fn declare_mat_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
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

    let summand = mat_summand(d, a, b, i, j);
    let body = rsum_range(d, p, summand, k);
    let value = {
        let with_j = d.lam_fv(j_fv, nat, body);
        let with_i = d.lam_fv(i_fv, nat, with_j);
        let with_k = d.lam_fv(k_fv, nat, with_i);
        let with_b = d.lam_fv(b_fv, mty, with_k);
        d.lam_fv(a_fv, mty, with_b)
    };
    let ty = {
        let over_j = d.arrow(nat, carrier);
        let over_i = d.arrow(nat, over_j);
        let over_k = d.arrow(nat, over_i);
        let over_b = d.arrow(mty, over_k);
        d.arrow(mty, over_b)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mat_mul,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAT_MUL_HEIGHT),
    })
}

/// `Rat.matMul_zero : ∀ A B i j, matMul A B zero i j = zero` — `Eq.refl`,
/// mirroring [`super::sum`]'s `sumRange_zero`.
fn declare_mat_mul_zero(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let zero_n = d.zero();
    let lhs = rmat_mul(d, p, a, b, zero_n, i, j);
    let zero_r = rzero(d, p);
    let stmt = req(d, lhs, zero_r);
    let proof = rrefl(d, zero_r);

    let ty = {
        let t = d.pi_fv(j_fv, nat, stmt);
        let t = d.pi_fv(i_fv, nat, t);
        let t = d.pi_fv(b_fv, mty, t);
        d.pi_fv(a_fv, mty, t)
    };
    let value = {
        let v = d.lam_fv(j_fv, nat, proof);
        let v = d.lam_fv(i_fv, nat, v);
        let v = d.lam_fv(b_fv, mty, v);
        d.lam_fv(a_fv, mty, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_mul_zero,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.matMul_succ : ∀ A B k i j,`
/// `matMul A B (succ k) i j = matMul A B k i j + A i k * B k j`
/// — `Eq.refl`, mirroring [`super::sum`]'s `sumRange_succ`.
fn declare_mat_mul_succ(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
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

    let sk = d.succ(k);
    let lhs = rmat_mul(d, p, a, b, sk, i, j);
    let prior = rmat_mul(d, p, a, b, k, i, j);
    let aik = d.apply(a, &[i, k]);
    let bkj = d.apply(b, &[k, j]);
    let term = rmul(d, aik, bkj);
    let rhs = radd(d, prior, term);
    let stmt = req(d, lhs, rhs);
    let proof = rrefl(d, rhs);

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
        name: p.mat_mul_succ,
        uparams: vec![],
        ty,
        value,
    })
}

/// `(sumRange g n) * c = sumRange (fun t => g t * c) n`, with the resulting
/// right-hand side returned alongside the proof.
///
/// [`super::RatPrelude::mul_sum_range`] pulls a constant out on the LEFT only;
/// every step of [`declare_mat_mul_assoc`] that moves `C s j` inside a sum
/// needs the right-hand form, and it is two `mul_comm`s around the existing
/// lemma rather than a second induction.
fn sum_mul_const_right(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    g: ExprId,
    n: ExprId,
    c: ExprId,
) -> (ExprId, ExprId) {
    let nat = d.nat_ty();
    let sum_g = rsum_range(d, p, g, n);
    let start = rmul(d, sum_g, c);

    // (Σ g) * c = c * (Σ g)
    let swapped = rmul(d, c, sum_g);
    let h1 = d.lemma(p.mul_comm, &[sum_g, c]);

    // c * (Σ g) = Σ (fun t => c * g t)
    let scaled = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let gt = d.apply(g, &[t]);
        let body = rmul(d, c, gt);
        d.lam_fv(t_fv, nat, body)
    };
    let scaled_sum = rsum_range(d, p, scaled, n);
    let h2 = d.lemma(p.mul_sum_range, &[c, g, n]);

    // Σ (fun t => c * g t) = Σ (fun t => g t * c)
    let flipped = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let gt = d.apply(g, &[t]);
        let body = rmul(d, gt, c);
        d.lam_fv(t_fv, nat, body)
    };
    let flipped_sum = rsum_range(d, p, flipped, n);
    let pointwise = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let gt = d.apply(g, &[t]);
        let body = d.lemma(p.mul_comm, &[c, gt]);
        d.lam_fv(t_fv, nat, body)
    };
    let h3 = d.lemma(p.sum_range_congr, &[scaled, flipped, n, pointwise]);

    let (_end, proof) = rchain(
        d,
        start,
        &[(swapped, h1), (scaled_sum, h2), (flipped_sum, h3)],
    );
    (flipped_sum, proof)
}

/// `(A i t * B t s) * C s j` — the left-nested triple product
/// [`declare_mat_mul_assoc`] carries through its Fubini swap.
fn triple_left(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    i: ExprId,
    t: ExprId,
    s: ExprId,
    j: ExprId,
) -> ExprId {
    let ait = d.apply(a, &[i, t]);
    let bts = d.apply(b, &[t, s]);
    let csj = d.apply(c, &[s, j]);
    let ab = rmul(d, ait, bts);
    rmul(d, ab, csj)
}

/// `A i t * (B t s * C s j)` — the right-nested triple product.
fn triple_right(
    d: &mut IntDev<'_>,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    i: ExprId,
    t: ExprId,
    s: ExprId,
    j: ExprId,
) -> ExprId {
    let ait = d.apply(a, &[i, t]);
    let bts = d.apply(b, &[t, s]);
    let csj = d.apply(c, &[s, j]);
    let bc = rmul(d, bts, csj);
    rmul(d, ait, bc)
}

/// `Rat.matMul_assoc : ∀ A B C k m i j,`
/// `matMul (matMul A B k) C m i j = matMul A (matMul B C m) k i j`.
///
/// **Pointwise**, as the module doc's "every statement here is POINTWISE"
/// section requires — there is no `funext` to lift it to an equation between
/// the two product matrices.
///
/// The four steps are the module doc's; the interchange in the middle is
/// [`super::RatPrelude::sum_range_swap`] verbatim, which is why this is
/// assembly rather than a new induction.
fn declare_mat_mul_assoc(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let ab = d.const_app(p.mat_mul, &[a, b, k]);
    let bc = d.const_app(p.mat_mul, &[b, c, m]);
    let lhs = rmat_mul(d, p, ab, c, m, i, j);
    let rhs = rmat_mul(d, p, a, bc, k, i, j);
    let stmt = req(d, lhs, rhs);

    // L0 := Σ_{s<m} (Σ_{t<k} A i t * B t s) * C s j
    let l0_fn = {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let row = mat_summand(d, a, b, i, s);
        let inner = rsum_range(d, p, row, k);
        let csj = d.apply(c, &[s, j]);
        let body = rmul(d, inner, csj);
        d.lam_fv(s_fv, nat, body)
    };
    let l0 = rsum_range(d, p, l0_fn, m);

    // step 1: pull `C s j` inside the inner sum, pointwise in `s`.
    let l1_fn = {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let tri = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let body = triple_left(d, a, b, c, i, t, s, j);
            d.lam_fv(t_fv, nat, body)
        };
        let body = rsum_range(d, p, tri, k);
        d.lam_fv(s_fv, nat, body)
    };
    let l1 = rsum_range(d, p, l1_fn, m);
    let step1 = {
        let pointwise = {
            let s_fv = d.fresh_fvar();
            let s = d.kernel().fvar(s_fv);
            let row = mat_summand(d, a, b, i, s);
            let csj = d.apply(c, &[s, j]);
            let (_flipped, body) = sum_mul_const_right(d, p, row, k, csj);
            d.lam_fv(s_fv, nat, body)
        };
        d.lemma(p.sum_range_congr, &[l0_fn, l1_fn, m, pointwise])
    };

    // step 2: Fubini. F s t := (A i t * B t s) * C s j.
    let swap_f = {
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let body = triple_left(d, a, b, c, i, t, s, j);
        let over_t = d.lam_fv(t_fv, nat, body);
        d.lam_fv(s_fv, nat, over_t)
    };
    let l2_fn = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let col = {
            let s_fv = d.fresh_fvar();
            let s = d.kernel().fvar(s_fv);
            let body = triple_left(d, a, b, c, i, t, s, j);
            d.lam_fv(s_fv, nat, body)
        };
        let body = rsum_range(d, p, col, m);
        d.lam_fv(t_fv, nat, body)
    };
    let l2 = rsum_range(d, p, l2_fn, k);
    let step2 = d.lemma(p.sum_range_swap, &[swap_f, k, m]);

    // step 3: `mul_assoc` under two nested congrs.
    let l3_fn = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let col = {
            let s_fv = d.fresh_fvar();
            let s = d.kernel().fvar(s_fv);
            let body = triple_right(d, a, b, c, i, t, s, j);
            d.lam_fv(s_fv, nat, body)
        };
        let body = rsum_range(d, p, col, m);
        d.lam_fv(t_fv, nat, body)
    };
    let l3 = rsum_range(d, p, l3_fn, k);
    let step3 = {
        let outer_pointwise = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let left_col = {
                let s_fv = d.fresh_fvar();
                let s = d.kernel().fvar(s_fv);
                let body = triple_left(d, a, b, c, i, t, s, j);
                d.lam_fv(s_fv, nat, body)
            };
            let right_col = {
                let s_fv = d.fresh_fvar();
                let s = d.kernel().fvar(s_fv);
                let body = triple_right(d, a, b, c, i, t, s, j);
                d.lam_fv(s_fv, nat, body)
            };
            let inner_pointwise = {
                let s_fv = d.fresh_fvar();
                let s = d.kernel().fvar(s_fv);
                let ait = d.apply(a, &[i, t]);
                let bts = d.apply(b, &[t, s]);
                let csj = d.apply(c, &[s, j]);
                let body = d.lemma(p.mul_assoc, &[ait, bts, csj]);
                d.lam_fv(s_fv, nat, body)
            };
            let body = d.lemma(
                p.sum_range_congr,
                &[left_col, right_col, m, inner_pointwise],
            );
            d.lam_fv(t_fv, nat, body)
        };
        d.lemma(p.sum_range_congr, &[l2_fn, l3_fn, k, outer_pointwise])
    };

    // step 4: pull `A i t` back out of the inner sum.
    let l4_fn = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let col = mat_summand(d, b, c, t, j);
        let inner = rsum_range(d, p, col, m);
        let ait = d.apply(a, &[i, t]);
        let body = rmul(d, ait, inner);
        d.lam_fv(t_fv, nat, body)
    };
    let l4 = rsum_range(d, p, l4_fn, k);
    let step4 = {
        let pointwise = {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let col = mat_summand(d, b, c, t, j);
            let inner = rsum_range(d, p, col, m);
            let ait = d.apply(a, &[i, t]);
            let forward_lhs = rmul(d, ait, inner);
            let forward_rhs = {
                let s_fv = d.fresh_fvar();
                let s = d.kernel().fvar(s_fv);
                let inner_body = triple_right(d, a, b, c, i, t, s, j);
                let scaled = d.lam_fv(s_fv, nat, inner_body);
                rsum_range(d, p, scaled, m)
            };
            let forward = d.lemma(p.mul_sum_range, &[ait, col, m]);
            let body = rsymm(d, forward_lhs, forward_rhs, forward);
            d.lam_fv(t_fv, nat, body)
        };
        d.lemma(p.sum_range_congr, &[l3_fn, l4_fn, k, pointwise])
    };

    let (_end, proof) = rchain(d, l0, &[(l1, step1), (l2, step2), (l3, step3), (l4, step4)]);

    let ty = {
        let t = d.pi_fv(j_fv, nat, stmt);
        let t = d.pi_fv(i_fv, nat, t);
        let t = d.pi_fv(m_fv, nat, t);
        let t = d.pi_fv(k_fv, nat, t);
        let t = d.pi_fv(c_fv, mty, t);
        let t = d.pi_fv(b_fv, mty, t);
        d.pi_fv(a_fv, mty, t)
    };
    let value = {
        let v = d.lam_fv(j_fv, nat, proof);
        let v = d.lam_fv(i_fv, nat, v);
        let v = d.lam_fv(m_fv, nat, v);
        let v = d.lam_fv(k_fv, nat, v);
        let v = d.lam_fv(c_fv, mty, v);
        let v = d.lam_fv(b_fv, mty, v);
        d.lam_fv(a_fv, mty, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_mul_assoc,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.matMul_add_left : ∀ A1 A2 B k i j,`
/// `matMul (fun r t => A1 r t + A2 r t) B k i j = matMul A1 B k i j + matMul A2 B k i j`.
///
/// [`super::RatPrelude::right_distrib`] pointwise under
/// [`super::RatPrelude::sum_range_congr`], then
/// [`super::RatPrelude::sum_range_add`] splits the sum — the same two-step
/// shape [`super::vector`]'s `dotN_add_left` uses one index down.
fn declare_mat_mul_add_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a1_fv = d.fresh_fvar();
    let a1 = d.kernel().fvar(a1_fv);
    let a2_fv = d.fresh_fvar();
    let a2 = d.kernel().fvar(a2_fv);
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let combined = pointwise_add_matrix(d, a1, a2);
    let lhs = rmat_mul(d, p, combined, b, k, i, j);
    let m1 = rmat_mul(d, p, a1, b, k, i, j);
    let m2 = rmat_mul(d, p, a2, b, k, i, j);
    let rhs = radd(d, m1, m2);
    let stmt = req(d, lhs, rhs);

    // Σ_t (A1 i t + A2 i t) * B t j
    let start_fn = mat_summand(d, combined, b, i, j);
    let start = rsum_range(d, p, start_fn, k);
    // Σ_t (A1 i t * B t j + A2 i t * B t j)
    let split_fn = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let a1it = d.apply(a1, &[i, t]);
        let a2it = d.apply(a2, &[i, t]);
        let btj = d.apply(b, &[t, j]);
        let l = rmul(d, a1it, btj);
        let r = rmul(d, a2it, btj);
        let body = radd(d, l, r);
        d.lam_fv(t_fv, nat, body)
    };
    let split = rsum_range(d, p, split_fn, k);
    let pointwise = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let a1it = d.apply(a1, &[i, t]);
        let a2it = d.apply(a2, &[i, t]);
        let btj = d.apply(b, &[t, j]);
        let body = d.lemma(p.right_distrib, &[a1it, a2it, btj]);
        d.lam_fv(t_fv, nat, body)
    };
    let step1 = d.lemma(p.sum_range_congr, &[start_fn, split_fn, k, pointwise]);

    let f1 = mat_summand(d, a1, b, i, j);
    let f2 = mat_summand(d, a2, b, i, j);
    let s1 = rsum_range(d, p, f1, k);
    let s2 = rsum_range(d, p, f2, k);
    let sum_pair = radd(d, s1, s2);
    let step2 = d.lemma(p.sum_range_add, &[f1, f2, k]);

    let (_end, proof) = rchain(d, start, &[(split, step1), (sum_pair, step2)]);

    let ty = {
        let t = d.pi_fv(j_fv, nat, stmt);
        let t = d.pi_fv(i_fv, nat, t);
        let t = d.pi_fv(k_fv, nat, t);
        let t = d.pi_fv(b_fv, mty, t);
        let t = d.pi_fv(a2_fv, mty, t);
        d.pi_fv(a1_fv, mty, t)
    };
    let value = {
        let v = d.lam_fv(j_fv, nat, proof);
        let v = d.lam_fv(i_fv, nat, v);
        let v = d.lam_fv(k_fv, nat, v);
        let v = d.lam_fv(b_fv, mty, v);
        let v = d.lam_fv(a2_fv, mty, v);
        d.lam_fv(a1_fv, mty, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_mul_add_left,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.matMul_add_right : ∀ A B1 B2 k i j,`
/// `matMul A (fun t r => B1 t r + B2 t r) k i j = matMul A B1 k i j + matMul A B2 k i j`.
///
/// [`super::RatPrelude::left_distrib`] where the left form used
/// `right_distrib`; the split is the same [`super::RatPrelude::sum_range_add`].
fn declare_mat_mul_add_right(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let b1_fv = d.fresh_fvar();
    let b1 = d.kernel().fvar(b1_fv);
    let b2_fv = d.fresh_fvar();
    let b2 = d.kernel().fvar(b2_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let combined = pointwise_add_matrix(d, b1, b2);
    let lhs = rmat_mul(d, p, a, combined, k, i, j);
    let m1 = rmat_mul(d, p, a, b1, k, i, j);
    let m2 = rmat_mul(d, p, a, b2, k, i, j);
    let rhs = radd(d, m1, m2);
    let stmt = req(d, lhs, rhs);

    let start_fn = mat_summand(d, a, combined, i, j);
    let start = rsum_range(d, p, start_fn, k);
    let split_fn = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ait = d.apply(a, &[i, t]);
        let b1tj = d.apply(b1, &[t, j]);
        let b2tj = d.apply(b2, &[t, j]);
        let l = rmul(d, ait, b1tj);
        let r = rmul(d, ait, b2tj);
        let body = radd(d, l, r);
        d.lam_fv(t_fv, nat, body)
    };
    let split = rsum_range(d, p, split_fn, k);
    let pointwise = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ait = d.apply(a, &[i, t]);
        let b1tj = d.apply(b1, &[t, j]);
        let b2tj = d.apply(b2, &[t, j]);
        let body = d.lemma(p.left_distrib, &[ait, b1tj, b2tj]);
        d.lam_fv(t_fv, nat, body)
    };
    let step1 = d.lemma(p.sum_range_congr, &[start_fn, split_fn, k, pointwise]);

    let f1 = mat_summand(d, a, b1, i, j);
    let f2 = mat_summand(d, a, b2, i, j);
    let s1 = rsum_range(d, p, f1, k);
    let s2 = rsum_range(d, p, f2, k);
    let sum_pair = radd(d, s1, s2);
    let step2 = d.lemma(p.sum_range_add, &[f1, f2, k]);

    let (_end, proof) = rchain(d, start, &[(split, step1), (sum_pair, step2)]);

    let ty = {
        let t = d.pi_fv(j_fv, nat, stmt);
        let t = d.pi_fv(i_fv, nat, t);
        let t = d.pi_fv(k_fv, nat, t);
        let t = d.pi_fv(b2_fv, mty, t);
        let t = d.pi_fv(b1_fv, mty, t);
        d.pi_fv(a_fv, mty, t)
    };
    let value = {
        let v = d.lam_fv(j_fv, nat, proof);
        let v = d.lam_fv(i_fv, nat, v);
        let v = d.lam_fv(k_fv, nat, v);
        let v = d.lam_fv(b2_fv, mty, v);
        let v = d.lam_fv(b1_fv, mty, v);
        d.lam_fv(a_fv, mty, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_mul_add_right,
        uparams: vec![],
        ty,
        value,
    })
}

/// `fun r t => M1 r t + M2 r t` — the pointwise sum of two matrices, the only
/// place this file forms a matrix-valued expression at all (and it is
/// immediately applied, never compared for equality: see the module doc's
/// `funext` note).
fn pointwise_add_matrix(d: &mut IntDev<'_>, m1: ExprId, m2: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);
    let x = d.apply(m1, &[r, t]);
    let y = d.apply(m2, &[r, t]);
    let body = radd(d, x, y);
    let over_t = d.lam_fv(t_fv, nat, body);
    d.lam_fv(r_fv, nat, over_t)
}

/// `Rat.matMul_smul_left : ∀ c A B k i j,`
/// `matMul (fun r t => c * A r t) B k i j = c * matMul A B k i j`.
///
/// `mul_assoc` pointwise, then [`super::RatPrelude::mul_sum_range`] read
/// right-to-left.
fn declare_mat_mul_smul_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let mty = mat_ty(d);

    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
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

    let scaled_a = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let art = d.apply(a, &[r, t]);
        let body = rmul(d, c, art);
        let over_t = d.lam_fv(t_fv, nat, body);
        d.lam_fv(r_fv, nat, over_t)
    };
    let lhs = rmat_mul(d, p, scaled_a, b, k, i, j);
    let plain = rmat_mul(d, p, a, b, k, i, j);
    let rhs = rmul(d, c, plain);
    let stmt = req(d, lhs, rhs);

    // Σ_t (c * A i t) * B t j
    let start_fn = mat_summand(d, scaled_a, b, i, j);
    let start = rsum_range(d, p, start_fn, k);
    // Σ_t c * (A i t * B t j)
    let regrouped_fn = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ait = d.apply(a, &[i, t]);
        let btj = d.apply(b, &[t, j]);
        let ab = rmul(d, ait, btj);
        let body = rmul(d, c, ab);
        d.lam_fv(t_fv, nat, body)
    };
    let regrouped = rsum_range(d, p, regrouped_fn, k);
    let pointwise = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let ait = d.apply(a, &[i, t]);
        let btj = d.apply(b, &[t, j]);
        let body = d.lemma(p.mul_assoc, &[c, ait, btj]);
        d.lam_fv(t_fv, nat, body)
    };
    let step1 = d.lemma(p.sum_range_congr, &[start_fn, regrouped_fn, k, pointwise]);

    let base_fn = mat_summand(d, a, b, i, j);
    let base_sum = rsum_range(d, p, base_fn, k);
    let target = rmul(d, c, base_sum);
    let forward = d.lemma(p.mul_sum_range, &[c, base_fn, k]);
    let step2 = rsymm(d, target, regrouped, forward);

    let (_end, proof) = rchain(d, start, &[(regrouped, step1), (target, step2)]);

    let ty = {
        let t = d.pi_fv(j_fv, nat, stmt);
        let t = d.pi_fv(i_fv, nat, t);
        let t = d.pi_fv(k_fv, nat, t);
        let t = d.pi_fv(b_fv, mty, t);
        let t = d.pi_fv(a_fv, mty, t);
        d.pi_fv(c_fv, carrier, t)
    };
    let value = {
        let v = d.lam_fv(j_fv, nat, proof);
        let v = d.lam_fv(i_fv, nat, v);
        let v = d.lam_fv(k_fv, nat, v);
        let v = d.lam_fv(b_fv, mty, v);
        let v = d.lam_fv(a_fv, mty, v);
        d.lam_fv(c_fv, carrier, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_mul_smul_left,
        uparams: vec![],
        ty,
        value,
    })
}

/// Delta height for `Rat.matId`: one above [`MAT_MUL_HEIGHT`], following this
/// prelude's convention of a monotone bump per new definition.
const MAT_ID_HEIGHT: u16 = 47;

/// `Rat.matId` as a bare constant — the identity matrix is a closed
/// `Nat -> Nat -> Rat`, so it takes no arguments.
fn rmat_id(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    d.kernel().const_(p.mat_id, vec![])
}

/// `Not (Eq Nat b a)` from `hne : Not (Eq Nat a b)`.
///
/// The `IntDev` counterpart of `nat_prelude::finite::ne_symm`, which is
/// written against `NatDev` and cannot be called from this prelude.
fn ne_symm(d: &mut IntDev<'_>, a: ExprId, b: ExprId, hne: ExprId) -> ExprId {
    let eq_ba = d.eq(b, a);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let flipped = NatOps::symm(d, b, a, e);
    let contra = d.apply(hne, &[flipped]);
    d.lam_fv(e_fv, eq_ba, contra)
}

/// `Not (Eq Nat a b)` from `h : Lt a b`.
///
/// The `IntDev` counterpart of `nat_prelude::finite::ne_of_lt`. Both
/// directions are needed and they are NOT interchangeable — see
/// [`ne_of_lt_symm`].
fn ne_of_lt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let np = d.prelude();
    let eq_ab = d.eq(a, b);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let h_rev = NatOps::symm(d, a, b, e);
    let motive = NatOps::eq_motive(d, b, &|d, x| d.lt(a, x));
    let laa = NatOps::transport(d, b, motive, h, a, h_rev);
    let contra = d.lemma(np.lt_irrefl, &[a, laa]);
    d.lam_fv(e_fv, eq_ab, contra)
}

/// `Not (Eq Nat b a)` from `h : Lt a b` — assume the equality, transport `h`
/// along it to `Lt a a`, and apply `Nat.lt_irrefl`.
///
/// The direction is deliberately the REVERSED one (`b != a`, not `a != b`):
/// [`declare_sum_range_delta`] always needs "the index being summed differs
/// from the distinguished point", and the strict inequality it has in hand
/// points the other way.
fn ne_of_lt_symm(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let np = d.prelude();
    let eq_ba = d.eq(b, a);
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    // e : Eq Nat b a, so rewriting `b` to `a` in `Lt a b` gives `Lt a a`.
    let motive = NatOps::eq_motive(d, b, &|d, x| d.lt(a, x));
    let laa = NatOps::transport(d, b, motive, h, a, e);
    let contra = d.lemma(np.lt_irrefl, &[a, laa]);
    d.lam_fv(e_fv, eq_ba, contra)
}

/// `Rat.sumRange_delta : ∀ f i n, (∀ t, Not (Eq Nat t i) → f t = zero) →
/// Lt i n → sumRange f n = f i` — a sum whose summand vanishes away from one
/// index collapses to the value at that index.
///
/// The strict bound comes LAST because it lives inside the induction motive
/// (`fun n => Lt i n → …`), which is what lets the base case discharge by
/// `Nat.not_lt_zero` instead of needing a separate impossible-case lemma.
///
/// The hypothesis is deliberately UNRESTRICTED (`∀ t`, not `∀ t, Lt t n →`):
/// the only consumer is [`declare_mat_mul_id_left`]/[`declare_mat_mul_id_right`],
/// where `Rat.matId` vanishes off the diagonal at every index whatsoever, and
/// the restricted form would force the induction to re-derive `Lt t m → Lt t
/// (succ m)` at every step for nothing.
///
/// Induction on `n` with the strict bound INSIDE the motive (`fun n => Lt i n
/// → …`), so the base case discharges by [`NatPrelude::not_lt_zero`] rather
/// than needing a separate impossible-case lemma.
fn declare_sum_range_delta(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let np = d.prelude();
    let nat = d.nat_ty();
    let carrier = rat_ty(d);
    let fn_ty = d.arrow(nat, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let hz_fv = d.fresh_fvar();
    let hz = d.kernel().fvar(hz_fv);

    // hz : ∀ t, Not (Eq Nat t i) → f t = zero
    let hz_ty = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let eq_ti = d.eq(t, i);
        let ne_ti = d.not(eq_ti);
        let ft = d.apply(f, &[t]);
        let zero_r = rzero(d, p);
        let concl = req(d, ft, zero_r);
        let with_ne = d.arrow(ne_ti, concl);
        d.pi_fv(t_fv, nat, with_ne)
    };

    let fi = d.apply(f, &[i]);
    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let sum_x = rsum_range(d, p, f, x);
        let concl = req(d, sum_x, fi);
        let bound = d.lt(i, x);
        d.arrow(bound, concl)
    };
    let stmt_inner = motive(d, n);

    let proof_inner = d.induct(
        &motive,
        &|d| {
            let zero_n = d.zero();
            let bound = d.lt(i, zero_n);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let sum_zero = rsum_range(d, p, f, zero_n);
            let target = req(d, sum_zero, fi);
            let not_lt = d.lemma(np.not_lt_zero, &[i]);
            let contra = d.apply(not_lt, &[h]);
            let body = d.absurd(target, contra);
            d.lam_fv(h_fv, bound, body)
        },
        &|d, m, ih| {
            let sm = d.succ(m);
            let bound = d.lt(i, sm);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let sum_m = rsum_range(d, p, f, m);
            let fm = d.apply(f, &[m]);
            let start = radd(d, sum_m, fm);
            let target = {
                let sum_sm = rsum_range(d, p, f, sm);
                req(d, sum_sm, fi)
            };

            let h_le = d.lemma(np.le_of_lt_succ, &[i, m, h]);
            let disj = d.lemma(np.lt_or_eq_of_le, &[i, m, h_le]);
            let lt_ty = d.lt(i, m);
            let eq_ty = d.eq(i, m);

            let body = d.or_elim(
                lt_ty,
                eq_ty,
                target,
                disj,
                // i < m: the induction hypothesis applies, and `f m = 0`
                // because `m != i`.
                &|d, hlt| {
                    let ih_applied = d.apply(ih, &[hlt]);
                    let ne_mi = ne_of_lt_symm(d, i, m, hlt);
                    let h_fm = d.apply(hz, &[m, ne_mi]);
                    let zero_r = rzero(d, p);
                    let with_zero = radd(d, sum_m, zero_r);
                    let step_a = rcongr(d, fm, zero_r, h_fm, &|d, x| radd(d, sum_m, x));
                    let step_b = d.lemma(p.add_zero, &[sum_m]);
                    let (_end, proof) = rchain(
                        d,
                        start,
                        &[(with_zero, step_a), (sum_m, step_b), (fi, ih_applied)],
                    );
                    proof
                },
                // i = m: everything below `m` is off the diagonal, so the
                // prefix sum is zero and the last term IS `f i`.
                &|d, heq| {
                    let pointwise = {
                        let t_fv = d.fresh_fvar();
                        let t = d.kernel().fvar(t_fv);
                        let t_lt_m = d.lt(t, m);
                        let ht_fv = d.fresh_fvar();
                        let ht = d.kernel().fvar(ht_fv);
                        // Lt t m, i = m  ⊢  Lt t i  ⊢  t != i
                        let heq_rev = NatOps::symm(d, i, m, heq);
                        let motive_lt = NatOps::eq_motive(d, m, &|d, x| d.lt(t, x));
                        let t_lt_i = NatOps::transport(d, m, motive_lt, ht, i, heq_rev);
                        let ne_ti = ne_of_lt(d, t, i, t_lt_i);
                        let inner = d.apply(hz, &[t, ne_ti]);
                        let with_ht = d.lam_fv(ht_fv, t_lt_m, inner);
                        d.lam_fv(t_fv, nat, with_ht)
                    };
                    let h_prefix = d.lemma(p.sum_range_eq_zero_of_lt, &[f, m, pointwise]);
                    let zero_r = rzero(d, p);
                    let zero_plus = radd(d, zero_r, fm);
                    let step_a = rcongr(d, sum_m, zero_r, h_prefix, &|d, x| radd(d, x, fm));
                    let step_b = d.lemma(p.zero_add, &[fm]);
                    let heq_rev = NatOps::symm(d, i, m, heq);
                    let step_c = nat_eq_to_rat(d, m, i, heq_rev, &|d, x| d.apply(f, &[x]));
                    let (_end, proof) =
                        rchain(d, start, &[(zero_plus, step_a), (fm, step_b), (fi, step_c)]);
                    proof
                },
            );
            d.lam_fv(h_fv, bound, body)
        },
        n,
    );

    let ty = {
        let t = d.arrow(hz_ty, stmt_inner);
        let t = d.pi_fv(n_fv, nat, t);
        let t = d.pi_fv(i_fv, nat, t);
        d.pi_fv(f_fv, fn_ty, t)
    };
    let value = {
        let v = d.lam_fv(hz_fv, hz_ty, proof_inner);
        let v = d.lam_fv(n_fv, nat, v);
        let v = d.lam_fv(i_fv, nat, v);
        d.lam_fv(f_fv, fn_ty, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.sum_range_delta,
        uparams: vec![],
        ty,
        value,
    })
}

/// Admit `Rat.matId : Nat → Nat → Rat := fun i j => if Nat.beq i j then
/// Rat.one else Rat.zero` — the identity matrix, at every dimension at once.
///
/// It carries no dimension argument: the delta is defined at every index
/// pair, and the bound enters only where it belongs, as the `Lt i n`
/// hypothesis of the two unit laws.
fn declare_mat_id(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let carrier = rat_ty(d);

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let cond = NatOps::beq(d, i, j);
    let one_r = rone(d, p);
    let zero_r = rzero(d, p);
    let body = bool_select_rat(d, cond, one_r, zero_r);

    let value = {
        let with_j = d.lam_fv(j_fv, nat, body);
        d.lam_fv(i_fv, nat, with_j)
    };
    let ty = {
        let inner = d.arrow(nat, carrier);
        d.arrow(nat, inner)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.mat_id,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(MAT_ID_HEIGHT),
    })
}

/// `Rat.matId_diag : ∀ i, matId i i = one`.
fn declare_mat_id_diag(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let np = d.prelude();
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);

    let mat_id = rmat_id(d, p);
    let lhs = d.apply(mat_id, &[i, i]);
    let one_r = rone(d, p);
    let stmt = req(d, lhs, one_r);

    let refl_i = NatOps::refl(d, i);
    let h_true = d.lemma(np.beq_eq_true_of_eq, &[i, i, refl_i]);
    let cond = NatOps::beq(d, i, i);
    let zero_r = rzero(d, p);
    let proof = select_rat_true(d, cond, one_r, zero_r, h_true);

    let ty = d.pi_fv(i_fv, nat, stmt);
    let value = d.lam_fv(i_fv, nat, proof);
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_id_diag,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.matId_off_diag : ∀ i j, Not (Eq Nat i j) → matId i j = zero`.
fn declare_mat_id_off_diag(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let np = d.prelude();
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let hne_fv = d.fresh_fvar();
    let hne = d.kernel().fvar(hne_fv);

    let eq_ij = d.eq(i, j);
    let ne_ty = d.not(eq_ij);

    let mat_id = rmat_id(d, p);
    let lhs = d.apply(mat_id, &[i, j]);
    let zero_r = rzero(d, p);
    let stmt = req(d, lhs, zero_r);

    let h_false = d.lemma(np.beq_eq_false_of_ne, &[i, j, hne]);
    let cond = NatOps::beq(d, i, j);
    let one_r = rone(d, p);
    let proof = select_rat_false(d, cond, one_r, zero_r, h_false);

    let ty = {
        let t = d.arrow(ne_ty, stmt);
        let t = d.pi_fv(j_fv, nat, t);
        d.pi_fv(i_fv, nat, t)
    };
    let value = {
        let v = d.lam_fv(hne_fv, ne_ty, proof);
        let v = d.lam_fv(j_fv, nat, v);
        d.lam_fv(i_fv, nat, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_id_off_diag,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.matMul_id_left : ∀ A n i j, Lt i n → matMul matId A n i j = A i j`.
///
/// The `Lt i n` hypothesis is not decoration: `matMul matId A n i j` sums
/// `matId i t · A t j` over `t < n`, and if the row index `i` is outside that
/// range the delta never fires and the whole sum is zero. It is the pointwise
/// price of an identity matrix that carries no dimension of its own.
fn declare_mat_mul_id_left(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);
    let bound = d.lt(i, n);

    let mat_id = rmat_id(d, p);
    let lhs = rmat_mul(d, p, mat_id, a, n, i, j);
    let aij = d.apply(a, &[i, j]);
    let stmt = req(d, lhs, aij);

    let g = mat_summand(d, mat_id, a, i, j);
    let start = rsum_range(d, p, g, n);

    let hz = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let eq_ti = d.eq(t, i);
        let ne_ti = d.not(eq_ti);
        let ht_fv = d.fresh_fvar();
        let ht = d.kernel().fvar(ht_fv);

        let ne_it = ne_symm(d, t, i, ht);
        let h_zero = d.lemma(p.mat_id_off_diag, &[i, t, ne_it]);
        let id_it = d.apply(mat_id, &[i, t]);
        let atj = d.apply(a, &[t, j]);
        let term = rmul(d, id_it, atj);
        let zero_r = rzero(d, p);
        let zero_times = rmul(d, zero_r, atj);
        let step_a = rcongr(d, id_it, zero_r, h_zero, &|d, x| rmul(d, x, atj));
        let flipped = rmul(d, atj, zero_r);
        let step_b = d.lemma(p.mul_comm, &[zero_r, atj]);
        let step_c = d.lemma(p.mul_zero, &[atj]);
        let (_end, inner) = rchain(
            d,
            term,
            &[(zero_times, step_a), (flipped, step_b), (zero_r, step_c)],
        );
        let with_ht = d.lam_fv(ht_fv, ne_ti, inner);
        d.lam_fv(t_fv, nat, with_ht)
    };

    let delta = d.lemma(p.sum_range_delta, &[g, i, n, hz, hlt]);
    let id_ii = d.apply(mat_id, &[i, i]);
    let at_point = rmul(d, id_ii, aij);
    let one_r = rone(d, p);
    let one_times = rmul(d, one_r, aij);
    let h_diag = d.lemma(p.mat_id_diag, &[i]);
    let step_a = rcongr(d, id_ii, one_r, h_diag, &|d, x| rmul(d, x, aij));
    let flipped = rmul(d, aij, one_r);
    let step_b = d.lemma(p.mul_comm, &[one_r, aij]);
    let step_c = d.lemma(p.mul_one, &[aij]);
    let (_end, proof) = rchain(
        d,
        start,
        &[
            (at_point, delta),
            (one_times, step_a),
            (flipped, step_b),
            (aij, step_c),
        ],
    );

    let ty = {
        let t = d.arrow(bound, stmt);
        let t = d.pi_fv(j_fv, nat, t);
        let t = d.pi_fv(i_fv, nat, t);
        let t = d.pi_fv(n_fv, nat, t);
        d.pi_fv(a_fv, mty, t)
    };
    let value = {
        let v = d.lam_fv(hlt_fv, bound, proof);
        let v = d.lam_fv(j_fv, nat, v);
        let v = d.lam_fv(i_fv, nat, v);
        let v = d.lam_fv(n_fv, nat, v);
        d.lam_fv(a_fv, mty, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_mul_id_left,
        uparams: vec![],
        ty,
        value,
    })
}

/// `Rat.matMul_id_right : ∀ A n i j, Lt j n → matMul A matId n i j = A i j`.
///
/// The mirror of [`declare_mat_mul_id_left`], and shorter: the delta's
/// hypothesis wants `t != j`, which is exactly the shape
/// [`RatPrelude::mat_id_off_diag`] takes here, so no `ne_symm` is needed and
/// the tail closes with `mul_one` without a `mul_comm`.
fn declare_mat_mul_id_right(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let mty = mat_ty(d);

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);
    let bound = d.lt(j, n);

    let mat_id = rmat_id(d, p);
    let lhs = rmat_mul(d, p, a, mat_id, n, i, j);
    let aij = d.apply(a, &[i, j]);
    let stmt = req(d, lhs, aij);

    let g = mat_summand(d, a, mat_id, i, j);
    let start = rsum_range(d, p, g, n);

    let hz = {
        let t_fv = d.fresh_fvar();
        let t = d.kernel().fvar(t_fv);
        let eq_tj = d.eq(t, j);
        let ne_tj = d.not(eq_tj);
        let ht_fv = d.fresh_fvar();
        let ht = d.kernel().fvar(ht_fv);

        let h_zero = d.lemma(p.mat_id_off_diag, &[t, j, ht]);
        let ait = d.apply(a, &[i, t]);
        let id_tj = d.apply(mat_id, &[t, j]);
        let term = rmul(d, ait, id_tj);
        let zero_r = rzero(d, p);
        let times_zero = rmul(d, ait, zero_r);
        let step_a = rcongr(d, id_tj, zero_r, h_zero, &|d, x| rmul(d, ait, x));
        let step_b = d.lemma(p.mul_zero, &[ait]);
        let (_end, inner) = rchain(d, term, &[(times_zero, step_a), (zero_r, step_b)]);
        let with_ht = d.lam_fv(ht_fv, ne_tj, inner);
        d.lam_fv(t_fv, nat, with_ht)
    };

    let delta = d.lemma(p.sum_range_delta, &[g, j, n, hz, hlt]);
    let id_jj = d.apply(mat_id, &[j, j]);
    let at_point = rmul(d, aij, id_jj);
    let one_r = rone(d, p);
    let times_one = rmul(d, aij, one_r);
    let h_diag = d.lemma(p.mat_id_diag, &[j]);
    let step_a = rcongr(d, id_jj, one_r, h_diag, &|d, x| rmul(d, aij, x));
    let step_b = d.lemma(p.mul_one, &[aij]);
    let (_end, proof) = rchain(
        d,
        start,
        &[(at_point, delta), (times_one, step_a), (aij, step_b)],
    );

    let ty = {
        let t = d.arrow(bound, stmt);
        let t = d.pi_fv(j_fv, nat, t);
        let t = d.pi_fv(i_fv, nat, t);
        let t = d.pi_fv(n_fv, nat, t);
        d.pi_fv(a_fv, mty, t)
    };
    let value = {
        let v = d.lam_fv(hlt_fv, bound, proof);
        let v = d.lam_fv(j_fv, nat, v);
        let v = d.lam_fv(i_fv, nat, v);
        let v = d.lam_fv(n_fv, nat, v);
        d.lam_fv(a_fv, mty, v)
    };
    d.kernel().add_declaration(Declaration::Theorem {
        name: p.mat_mul_id_right,
        uparams: vec![],
        ty,
        value,
    })
}
