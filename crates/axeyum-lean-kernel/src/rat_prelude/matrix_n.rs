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
    radd, rat_ty, rchain, req, rmul, rrefl, rsum_range, rsymm, rzero,
};
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
    declare_mat_mul_smul_left(d, p)
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

/// `Rat.matMul_succ : ∀ A B k i j, matMul A B (succ k) i j = matMul A B k i j
/// + A i k * B k j` — `Eq.refl`, mirroring [`super::sum`]'s `sumRange_succ`.
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

    let (_end, proof) = rchain(
        d,
        l0,
        &[(l1, step1), (l2, step2), (l3, step3), (l4, step4)],
    );

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
