//! **`CReal.fermat_interiorExtremum`** (Spivak ch. 11, Theorem 1): if `F` is
//! differentiable on `[lo, hi]`, `c` is an INTERIOR point (`lt lo c`, `lt c
//! hi`), and `F` attains a maximum over `[lo, hi]` at `c`, then `F'(c)` is
//! `Equiv`-zero.
//!
//! ## Why this theorem is unconditionally constructive
//!
//! The classical proof of Fermat's theorem has exactly one non-constructive
//! ingredient: producing the maximiser in the first place, which is the
//! Extreme Value Theorem (`creal/extreme_value.rs` shows this kernel cannot
//! do that in general — `evt_attained_max_decides_sign` reduces an attained
//! max to a decision principle this development lacks). Fermat's theorem
//! itself takes the maximiser as a HYPOTHESIS, not a conclusion, so that
//! ingredient never enters here. Everything else in the classical proof —
//! bounding a difference quotient above and below by an epsilon, from either
//! side — is ordinary order/field algebra over an undecidable `le`, exactly
//! the kind of argument this prelude already has the tools for. So the
//! statement below carries no side condition, no graded family, and no
//! unprovability witness: it is proved outright, for every `F`, `F'`, `lo`,
//! `hi`, `c` satisfying the (constructively meaningful) hypotheses.
//!
//! ## The route
//!
//! Fix an accuracy `e : Nat`; the goal is `le (abs (F' c)) (ofRat (natDivSucc
//! 1 e))`, and `CReal.equiv_zero_of small` (`archimedean_squeeze.rs`) turns
//! "for every `e`" of that into the target `Equiv (F' c) zero`.
//!
//! `lt lo c` and `lt c hi` each carry an EXACT rational gap
//! (`CReal.lt x y := ∃ q, 0 < q ∧ le (add x (ofRat q)) y`), eliminated via
//! `gap_elim`/`gap_halves` (`creal.rs`'s own private helpers, reused via
//! `super::`) to give `g1 : 0 < g1 ∧ lo + g1 ≤ c` and `g2 : 0 < g2 ∧ c + g2 ≤
//! hi` — WITHOUT any decision about where `c` sits (`CReal.le` is
//! undecidable, but these are exact `Rat`s, so `Rat.le_or_lt` may freely
//! decide among them). A three-way rational minimum of `g1`, `g2`, and
//! `hd_spec`'s own modulus bound at `e` (via two nested `Rat.le_or_lt` splits,
//! mirroring `deriv_unique.rs`'s own `q := min(q0, bound_k)` construction)
//! produces one exact positive rational `q` small enough for all three
//! purposes at once.
//!
//! The two perturbed points `c + q` and `c - q` both land in `[lo, hi]` BY
//! CONSTRUCTION (no sign decision on `F'(c)` or on `c`'s position is ever
//! needed — the two points are built from the same `q`, in both directions,
//! unconditionally). `hd_spec` at `(c, c+q)` and `(c, c-q)` — each combined
//! with the max hypothesis, which bounds `F(c±q) - F(c)` above by zero —
//! gives, after cancelling the known-positive scalar `q` via
//! `CReal.le_of_mul_le_mul_left`, `le (F' c) (ofRat (natDivSucc 1 e))` from
//! the `+q` side and `le (neg (F' c)) (ofRat (natDivSucc 1 e))` from the `-q`
//! side. `CReal.abs_le` combines the two into exactly the per-`e` goal.
//!
//! This needed **no** case split on `c`'s position and **no** disjunction
//! anywhere except the two decidable `Rat.le_or_lt` splits that build `q` —
//! unlike `deriv_unique.rs`'s uniqueness theorem, which needs `lt_cotrans`'s
//! genuine disjunction because it does not know in advance which side of `z`
//! its nearby point should fall on. Here both sides are needed regardless, so
//! there is nothing to branch on.

#![allow(
    clippy::doc_markdown,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines
)]

use super::{CRealPrelude, cadd, cle, clt, creal_ty, div_succ, embed, gap_elim, gap_halves};
use crate::KernelError;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::rat_prelude::ops::{rat_ty, rle, rlt, rzero};

/// Admit `CReal.fermat_interiorExtremum`. See the module documentation for
/// the route and for why this theorem needs no case split and no
/// unprovability witness.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub(super) fn declare_fermat(d: &mut IntDev<'_>, p: CRealPrelude) -> Result<(), KernelError> {
    declare_fermat_interior_extremum(d, p)
}

// --- shared term builders (private copies of idioms this development
// rebuilds per-module; see `derivative.rs`/`deriv_unique.rs`'s own identical
// disclaimers for why) --------------------------------------------------------

fn cneg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.neg, &[x])
}

fn cmul(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    d.const_app(p.mul, &[x, y])
}

fn cabs(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    d.const_app(p.abs, &[x])
}

fn czero(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    d.kernel().const_(p.zero, vec![])
}

fn pos_bound(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, k: ExprId) -> ExprId {
    d.const_app(p.pos_bound, &[x, k])
}

fn erefl(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId) -> ExprId {
    d.lemma(p.equiv_refl, &[a])
}

fn esymm(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    d.lemma(p.equiv_symm, &[a, b, h])
}

/// Chain `Equiv start ...` through `(next, step)` pairs — the `echain` idiom
/// used throughout this development.
fn echain(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    start: ExprId,
    steps: &[(ExprId, ExprId)],
) -> ExprId {
    let mut current = start;
    let mut proof = d.lemma(p.equiv_refl, &[start]);
    for &(next, step) in steps {
        proof = d.lemma(p.equiv_trans, &[start, current, next, proof, step]);
        current = next;
    }
    proof
}

/// `Equiv (add (neg x) x) zero` — the commuted form of `add_neg`. Copied
/// verbatim from `derivative.rs`/`deriv_unique.rs`'s private helper.
fn neg_add_self(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let nx = cneg(d, p, x);
    let x_nx = cadd(d, p, x, nx);
    let nx_x = cadd(d, p, nx, x);
    let comm = d.lemma(p.add_comm, &[x, nx]);
    let comm_symm = esymm(d, p, x_nx, nx_x, comm);
    let cancel = d.lemma(p.add_neg, &[x]);
    echain(d, p, nx_x, &[(x_nx, comm_symm), (zero_c, cancel)])
}

/// From `h_ab_zero : Equiv (add a b) zero`, derive `Equiv b (neg a)`. Copied
/// verbatim from `derivative.rs`'s private helper of the same shape.
fn neg_unique(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    a: ExprId,
    b: ExprId,
    h_ab_zero: ExprId,
) -> ExprId {
    let zero_c = czero(d, p);
    let neg_a = cneg(d, p, a);

    let add_a_nega = cadd(d, p, a, neg_a);
    let add_nega_a = cadd(d, p, neg_a, a);
    let h_add_neg = d.lemma(p.add_neg, &[a]);
    let comm0 = d.lemma(p.add_comm, &[a, neg_a]);
    let symm_h = esymm(d, p, add_a_nega, zero_c, h_add_neg);
    let zero_equiv_nega_a = d.lemma(
        p.equiv_trans,
        &[zero_c, add_a_nega, add_nega_a, symm_h, comm0],
    );

    let add_b_zero = cadd(d, p, b, zero_c);
    let add_zero_b = cadd(d, p, zero_c, b);
    let h_addzero_b = d.lemma(p.add_zero, &[b]);
    let b_equiv_addbzero = esymm(d, p, add_b_zero, b, h_addzero_b);
    let comm_b0 = d.lemma(p.add_comm, &[b, zero_c]);
    let b_equiv_addzerob = d.lemma(
        p.equiv_trans,
        &[b, add_b_zero, add_zero_b, b_equiv_addbzero, comm_b0],
    );

    let addnega_a = cadd(d, p, neg_a, a);
    let addnega_a_plus_b = cadd(d, p, addnega_a, b);
    let refl_b = erefl(d, p, b);
    let subst1 = d.lemma(
        p.add_congr,
        &[zero_c, addnega_a, b, b, zero_equiv_nega_a, refl_b],
    );

    let a_plus_b = cadd(d, p, a, b);
    let nega_plus_aplusb = cadd(d, p, neg_a, a_plus_b);
    let assoc = d.lemma(p.add_assoc, &[neg_a, a, b]);

    let nega_plus_zero = cadd(d, p, neg_a, zero_c);
    let refl_nega = erefl(d, p, neg_a);
    let subst2 = d.lemma(
        p.add_congr,
        &[neg_a, neg_a, a_plus_b, zero_c, refl_nega, h_ab_zero],
    );

    let final_step = d.lemma(p.add_zero, &[neg_a]);

    echain(
        d,
        p,
        b,
        &[
            (add_zero_b, b_equiv_addzerob),
            (addnega_a_plus_b, subst1),
            (nega_plus_aplusb, assoc),
            (nega_plus_zero, subst2),
            (neg_a, final_step),
        ],
    )
}

/// `Equiv (neg (neg x)) x`. Copied verbatim from `derivative.rs`'s private
/// helper.
fn double_neg(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);
    let h = neg_add_self(d, p, x);
    let nu = neg_unique(d, p, nx, x, h);
    esymm(d, p, x, nnx, nu)
}

/// `Equiv (neg (add a b)) (add (neg a) (neg b))`. Copied verbatim from
/// `derivative.rs`'s private helper.
fn neg_add_distrib(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let na = cneg(d, p, a);
    let nb = cneg(d, p, b);
    let ab = cadd(d, p, a, b);
    let na_nb = cadd(d, p, na, nb);
    let b_na = cadd(d, p, b, na);
    let na_b = cadd(d, p, na, b);
    let b_nanb = cadd(d, p, b, na_nb);
    let b_na_nb = cadd(d, p, b_na, nb);
    let na_b_nb = cadd(d, p, na_b, nb);
    let b_nb = cadd(d, p, b, nb);
    let na_bnb = cadd(d, p, na, b_nb);
    let na_zero = cadd(d, p, na, zero_c);
    let ab_nanb = cadd(d, p, ab, na_nb);
    let a_bnanb = cadd(d, p, a, b_nanb);
    let a_na = cadd(d, p, a, na);
    let neg_ab = cneg(d, p, ab);

    let step2 = d.lemma(p.add_assoc, &[b, na, nb]);
    let step2_symm = esymm(d, p, b_na_nb, b_nanb, step2);

    let step3 = d.lemma(p.add_comm, &[b, na]);
    let refl_nb = erefl(d, p, nb);
    let step4 = d.lemma(p.add_congr, &[b_na, na_b, nb, nb, step3, refl_nb]);

    let step5 = d.lemma(p.add_assoc, &[na, b, nb]);

    let step6 = d.lemma(p.add_neg, &[b]);
    let refl_na = erefl(d, p, na);
    let step7 = d.lemma(p.add_congr, &[na, na, b_nb, zero_c, refl_na, step6]);

    let step8 = d.lemma(p.add_zero, &[na]);

    let middle_result = echain(
        d,
        p,
        b_nanb,
        &[
            (b_na_nb, step2_symm),
            (na_b_nb, step4),
            (na_bnb, step5),
            (na_zero, step7),
            (na, step8),
        ],
    );

    let refl_a = erefl(d, p, a);
    let step9 = d.lemma(p.add_congr, &[a, a, b_nanb, na, refl_a, middle_result]);
    let step10 = d.lemma(p.add_neg, &[a]);

    let step1 = d.lemma(p.add_assoc, &[a, b, na_nb]);

    let h = echain(
        d,
        p,
        ab_nanb,
        &[(a_bnanb, step1), (a_na, step9), (zero_c, step10)],
    );

    let nu = neg_unique(d, p, ab, na_nb, h);
    esymm(d, p, na_nb, neg_ab, nu)
}

/// `Equiv (mul x (neg y)) (neg (mul x y))`. Copied verbatim from
/// `derivative.rs`'s private helper.
fn mul_neg_equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId, y: ExprId) -> ExprId {
    let zero_c = czero(d, p);
    let ny = cneg(d, p, y);
    let xy = cmul(d, p, x, y);
    let x_ny = cmul(d, p, x, ny);
    let y_plus_ny = cadd(d, p, y, ny);
    let x_times_sum = cmul(d, p, x, y_plus_ny);

    let h_add_neg_y = d.lemma(p.add_neg, &[y]);
    let refl_x = erefl(d, p, x);
    let h_mulcongr = d.lemma(p.mul_congr, &[x, x, y_plus_ny, zero_c, refl_x, h_add_neg_y]);
    let x_zero = cmul(d, p, x, zero_c);
    let h_mulzero = d.lemma(p.mul_zero, &[x]);
    let sum_equiv_zero = echain(
        d,
        p,
        x_times_sum,
        &[(x_zero, h_mulcongr), (zero_c, h_mulzero)],
    );

    let h_ld = d.lemma(p.left_distrib, &[x, y, ny]);
    let sum_of_products = cadd(d, p, xy, x_ny);
    let symm_ld = esymm(d, p, x_times_sum, sum_of_products, h_ld);
    let h_sum_zero = d.lemma(
        p.equiv_trans,
        &[
            sum_of_products,
            x_times_sum,
            zero_c,
            symm_ld,
            sum_equiv_zero,
        ],
    );

    neg_unique(d, p, xy, x_ny, h_sum_zero)
}

/// From `h : le (add x q) y`, derive `le x (add y (neg q))`. Copied verbatim
/// from `deriv_unique.rs`'s private helper of the same shape.
fn le_sub_of_add_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    q: ExprId,
    y: ExprId,
    h: ExprId,
) -> ExprId {
    let nq = cneg(d, p, q);
    let refl_nq = d.lemma(p.le_refl, &[nq]);
    let xq = cadd(d, p, x, q);
    let step = d.lemma(p.add_le_add, &[xq, y, nq, nq, h, refl_nq]);

    let lhs_equiv_x = {
        let assoc = d.lemma(p.add_assoc, &[x, q, nq]);
        let qnq = cadd(d, p, q, nq);
        let x_qnq = cadd(d, p, x, qnq);
        let an = d.lemma(p.add_neg, &[q]);
        let refl_x = erefl(d, p, x);
        let zero_c = czero(d, p);
        let cong = d.lemma(p.add_congr, &[x, x, qnq, zero_c, refl_x, an]);
        let x_zero = cadd(d, p, x, zero_c);
        let trim = d.lemma(p.add_zero, &[x]);
        let start = cadd(d, p, xq, nq);
        echain(d, p, start, &[(x_qnq, assoc), (x_zero, cong), (x, trim)])
    };
    let y_nq = cadd(d, p, y, nq);
    let refl_target = erefl(d, p, y_nq);
    let start = cadd(d, p, xq, nq);
    d.lemma(
        p.le_congr,
        &[start, x, y_nq, y_nq, lhs_equiv_x, refl_target, step],
    )
}

/// `Equiv (add (add v u) (neg v)) u` — for ANY `u`. Copied verbatim from
/// `deriv_unique.rs`'s private helper of the same shape.
fn add_sub_cancel(d: &mut IntDev<'_>, p: CRealPrelude, v: ExprId, u: ExprId) -> ExprId {
    let nv = cneg(d, p, v);
    let vu = cadd(d, p, v, u);
    let start = cadd(d, p, vu, nv);

    let uv = cadd(d, p, u, v);
    let comm1 = d.lemma(p.add_comm, &[v, u]);
    let refl_nv = erefl(d, p, nv);
    let step1 = d.lemma(p.add_congr, &[vu, uv, nv, nv, comm1, refl_nv]);
    let uv_nv = cadd(d, p, uv, nv);

    let assoc = d.lemma(p.add_assoc, &[u, v, nv]);
    let vnv = cadd(d, p, v, nv);
    let u_vnv = cadd(d, p, u, vnv);

    let an = d.lemma(p.add_neg, &[v]);
    let refl_u = erefl(d, p, u);
    let zero_c = czero(d, p);
    let step2 = d.lemma(p.add_congr, &[u, u, vnv, zero_c, refl_u, an]);
    let u_zero = cadd(d, p, u, zero_c);

    let trim = d.lemma(p.add_zero, &[u]);

    echain(
        d,
        p,
        start,
        &[(uv_nv, step1), (u_vnv, assoc), (u_zero, step2), (u, trim)],
    )
}

/// `Equiv (neg zero) zero`. Copied verbatim from `derivative.rs`'s private
/// helper.
fn neg_zero_equiv(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let zero_c = czero(d, p);
    let nz = cneg(d, p, zero_c);
    let padded = cadd(d, p, nz, zero_c);
    let flipped = cadd(d, p, zero_c, nz);
    let h1 = d.lemma(p.add_zero, &[nz]);
    let step1 = esymm(d, p, padded, nz, h1);
    let h2 = d.lemma(p.add_comm, &[nz, zero_c]);
    let h3 = d.lemma(p.add_neg, &[zero_c]);
    echain(d, p, nz, &[(padded, step1), (flipped, h2), (zero_c, h3)])
}

/// `Equiv (abs (ofRat q)) (ofRat q)` for `q_nonneg : Rat.le Rat.zero q`.
/// Copied verbatim from `deriv_unique.rs`'s private helper.
fn abs_of_nonneg(d: &mut IntDev<'_>, p: CRealPrelude, q: ExprId, q_nonneg: ExprId) -> ExprId {
    let rat = p.rat;
    let q_emb = embed(d, p, q);
    let abs_q = cabs(d, p, q_emb);

    let refl_q = d.lemma(p.le_refl, &[q_emb]);

    let neg_q = crate::rat_prelude::ops::rneg(d, q);
    let neg_le_zero = d.lemma(rat.neg_nonpos_of_nonneg, &[q, q_nonneg]);
    let rzero_expr = rzero(d, rat);
    let neg_q_le_q = d.lemma(rat.le_trans, &[neg_q, rzero_expr, q, neg_le_zero, q_nonneg]);
    let creal_neg_q_le_q = d.lemma(p.of_rat_le, &[neg_q, q, neg_q_le_q]);

    let neg_q_emb = cneg(d, p, q_emb);
    let of_rat_neg_q = embed(d, p, neg_q);
    let on_eq = d.lemma(p.of_rat_neg, &[q]);
    let on_eq_symm = esymm(d, p, of_rat_neg_q, neg_q_emb, on_eq);

    let refl_qemb = erefl(d, p, q_emb);
    let upper = d.lemma(
        p.le_congr,
        &[
            of_rat_neg_q,
            neg_q_emb,
            q_emb,
            q_emb,
            on_eq_symm,
            refl_qemb,
            creal_neg_q_le_q,
        ],
    );

    let abs_le_result = d.lemma(p.abs_le, &[q_emb, q_emb, refl_q, upper]);
    let le_abs_self_q = d.lemma(p.le_abs_self, &[q_emb]);

    d.lemma(
        p.equiv_of_le_le,
        &[abs_q, q_emb, abs_le_result, le_abs_self_q],
    )
}

/// From `h : le (abs x) bound`, derive `le (abs (neg x)) bound`. Copied
/// verbatim from `derivative.rs`'s private helper of the same shape.
fn le_abs_neg_of_le_abs(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    bound: ExprId,
    h: ExprId,
) -> ExprId {
    let abs_x = cabs(d, p, x);
    let nx = cneg(d, p, x);
    let nnx = cneg(d, p, nx);

    let nle = d.lemma(p.neg_le_abs, &[x]);
    let upper = d.lemma(p.le_trans, &[nx, abs_x, bound, nle, h]);

    let le_x_bound = {
        let sle = d.lemma(p.le_abs_self, &[x]);
        d.lemma(p.le_trans, &[x, abs_x, bound, sle, h])
    };
    let nn = double_neg(d, p, x);
    let nn_symm = esymm(d, p, nnx, x, nn);
    let refl_bound = erefl(d, p, bound);
    let lower = d.lemma(
        p.le_congr,
        &[x, nnx, bound, bound, nn_symm, refl_bound, le_x_bound],
    );

    d.lemma(p.abs_le, &[nx, bound, upper, lower])
}

/// `Equiv (abs (neg x)) (abs x)`. Copied verbatim from `deriv_unique.rs`'s
/// private helper.
fn abs_neg_equiv(d: &mut IntDev<'_>, p: CRealPrelude, x: ExprId) -> ExprId {
    let abs_x = cabs(d, p, x);
    let nx = cneg(d, p, x);
    let abs_nx = cabs(d, p, nx);

    let refl_absx = d.lemma(p.le_refl, &[abs_x]);
    let le1 = le_abs_neg_of_le_abs(d, p, x, abs_x, refl_absx);

    let refl_absnx = d.lemma(p.le_refl, &[abs_nx]);
    let le2_pre = le_abs_neg_of_le_abs(d, p, nx, abs_nx, refl_absnx);
    let nnx = cneg(d, p, nx);
    let abs_nnx = cabs(d, p, nnx);
    let dn = double_neg(d, p, x);
    let abs_congr_dn = d.lemma(p.abs_congr, &[nnx, x, dn]);
    let refl_absnx2 = erefl(d, p, abs_nx);
    let le2 = d.lemma(
        p.le_congr,
        &[
            abs_nnx,
            abs_x,
            abs_nx,
            abs_nx,
            abs_congr_dn,
            refl_absnx2,
            le2_pre,
        ],
    );

    d.lemma(p.equiv_of_le_le, &[abs_nx, abs_x, le1, le2])
}

/// From `h : le (abs v) bound`, derive `le (neg v) bound`.
fn neg_le_of_abs_le(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    v: ExprId,
    bound: ExprId,
    h: ExprId,
) -> ExprId {
    let av = cabs(d, p, v);
    let nle = d.lemma(p.neg_le_abs, &[v]);
    let nv = cneg(d, p, v);
    d.lemma(p.le_trans, &[nv, av, bound, nle, h])
}

/// From `h : le a b`, derive `le (add a (neg b)) zero`.
fn nonpos_of_le(d: &mut IntDev<'_>, p: CRealPrelude, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let nb = cneg(d, p, b);
    let refl_nb = d.lemma(p.le_refl, &[nb]);
    let step = d.lemma(p.add_le_add, &[a, b, nb, nb, h, refl_nb]);
    let an = d.lemma(p.add_neg, &[b]);
    let ab_nb = cadd(d, p, a, nb);
    let b_nb = cadd(d, p, b, nb);
    let refl_lhs = erefl(d, p, ab_nb);
    let zero_c = czero(d, p);
    d.lemma(
        p.le_congr,
        &[ab_nb, ab_nb, b_nb, zero_c, refl_lhs, an, step],
    )
}

/// From `dd_le_zero : le dd zero` and `h_lower : le (neg (add dd (neg fpq)))
/// bound`, derive `le fpq bound` — the shared "finish" step both the `+q` and
/// `-q` branches use. `error := add dd (neg fpq)` is exactly the shape
/// `derivative.rs::deriv_spec_body` builds (`dd` is `F(y) - F(c)`, `fpq` is
/// `F'(c) * (y - c)`), so `h_lower` is the lower half of `hd_spec`'s own
/// output bound, already extracted via `neg_le_of_abs_le`.
///
/// Route: `neg (add dd (neg fpq)) ~ add (neg dd) fpq ~ add fpq (neg dd)`
/// (`neg_add_distrib` + `double_neg` + `add_comm`), so `h_lower` transports
/// into `le (add fpq (neg dd)) bound`; `le_sub_of_add_le` then isolates `fpq
/// <= add bound dd`; and `dd <= zero` weakens that to `fpq <= bound`.
fn fpq_le_bound_from_lower(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    dd: ExprId,
    fpq: ExprId,
    bound: ExprId,
    h_lower: ExprId,
    dd_le_zero: ExprId,
) -> ExprId {
    let ndd = cneg(d, p, dd);
    let nfpq = cneg(d, p, fpq);
    let nnfpq = cneg(d, p, nfpq);
    let sum = cadd(d, p, dd, nfpq);
    let neg_sum = cneg(d, p, sum);

    let nad = neg_add_distrib(d, p, dd, nfpq);
    let dn = double_neg(d, p, fpq);
    let add_ndd_nnfpq = cadd(d, p, ndd, nnfpq);
    let add_ndd_fpq = cadd(d, p, ndd, fpq);
    let congr1 = {
        let refl_ndd = erefl(d, p, ndd);
        d.lemma(p.add_congr, &[ndd, ndd, nnfpq, fpq, refl_ndd, dn])
    };
    let step1 = d.lemma(
        p.equiv_trans,
        &[neg_sum, add_ndd_nnfpq, add_ndd_fpq, nad, congr1],
    );

    let comm = d.lemma(p.add_comm, &[ndd, fpq]);
    let add_fpq_ndd = cadd(d, p, fpq, ndd);
    let step2 = d.lemma(
        p.equiv_trans,
        &[neg_sum, add_ndd_fpq, add_fpq_ndd, step1, comm],
    );

    let refl_bound = erefl(d, p, bound);
    let h_lower2 = d.lemma(
        p.le_congr,
        &[
            neg_sum,
            add_fpq_ndd,
            bound,
            bound,
            step2,
            refl_bound,
            h_lower,
        ],
    );

    let step3 = le_sub_of_add_le(d, p, fpq, ndd, bound, h_lower2);
    let nndd = cneg(d, p, ndd);
    let dn2 = double_neg(d, p, dd);
    let add_bound_nndd = cadd(d, p, bound, nndd);
    let add_bound_dd = cadd(d, p, bound, dd);
    let congr2 = {
        let refl_bound2 = erefl(d, p, bound);
        d.lemma(p.add_congr, &[bound, bound, nndd, dd, refl_bound2, dn2])
    };
    let refl_fpq = erefl(d, p, fpq);
    let step4 = d.lemma(
        p.le_congr,
        &[
            fpq,
            fpq,
            add_bound_nndd,
            add_bound_dd,
            refl_fpq,
            congr2,
            step3,
        ],
    );

    let refl_bound3 = d.lemma(p.le_refl, &[bound]);
    let zero_c_step5 = czero(d, p);
    let step5 = d.lemma(
        p.add_le_add,
        &[bound, bound, dd, zero_c_step5, refl_bound3, dd_le_zero],
    );
    let zero_c_step5b = czero(d, p);
    let add_bound_zero = cadd(d, p, bound, zero_c_step5b);
    let az = d.lemma(p.add_zero, &[bound]);
    let refl_addbounddd = erefl(d, p, add_bound_dd);
    let step6 = d.lemma(
        p.le_congr,
        &[
            add_bound_dd,
            add_bound_dd,
            add_bound_zero,
            bound,
            refl_addbounddd,
            az,
            step5,
        ],
    );

    d.lemma(p.le_trans, &[fpq, add_bound_dd, bound, step4, step6])
}

/// Given `x_pos : Rat.lt 0 x`, `y_pos : Rat.lt 0 y`, and a continuation
/// `cont(d, m, m_pos, m_le_x, m_le_y) -> target`, produce `target` by
/// deciding `Rat.le_or_lt x y` and picking `m := x` or `m := y` accordingly.
/// Mirrors `deriv_unique.rs`'s own `Rat.le_or_lt`-based `q := min(q0,
/// bound_k)` construction (private to that module, rebuilt here), generalised
/// to an explicit continuation so it can be nested.
fn rat_min_elim(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    x: ExprId,
    y: ExprId,
    x_pos: ExprId,
    y_pos: ExprId,
    target: ExprId,
    cont: &dyn Fn(&mut IntDev<'_>, ExprId, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let rat = p.rat;
    let case = d.lemma(rat.le_or_lt, &[x, y]);
    let left_ty = rle(d, rat, x, y);
    let right_ty = rlt(d, rat, y, x);
    d.or_elim(
        left_ty,
        right_ty,
        target,
        case,
        &|d, h_le| {
            let m_le_x = d.lemma(rat.le_refl, &[x]);
            cont(d, x, x_pos, m_le_x, h_le)
        },
        &|d, h_lt| {
            let m_le_y = d.lemma(rat.le_refl, &[y]);
            let m_le_x = d.lemma(rat.le_of_lt, &[y, x, h_lt]);
            cont(d, y, y_pos, m_le_x, m_le_y)
        },
    )
}

// --- the theorem itself ------------------------------------------------------

/// `CReal -> CReal`.
fn fn_ty(d: &mut IntDev<'_>, p: CRealPrelude) -> ExprId {
    let carrier = creal_ty(d, p);
    d.arrow(carrier, carrier)
}

/// `HasDerivativeOn F F' lo hi`.
fn hd_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    fp: ExprId,
    lo: ExprId,
    hi: ExprId,
) -> ExprId {
    d.const_app(p.has_derivative_on, &[f, fp, lo, hi])
}

/// `∀ x : CReal, le lo x → le x hi → le (F x) (F c)` — "`F` attains a maximum
/// at `c` over `[lo, hi]`".
fn hmax_ty(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    lo: ExprId,
    hi: ExprId,
    c: ExprId,
) -> ExprId {
    let carrier = creal_ty(d, p);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let le_lo_x = cle(d, p, lo, x);
    let le_x_hi = cle(d, p, x, hi);
    let fx = d.apply(f, &[x]);
    let fc = d.apply(f, &[c]);
    let concl = cle(d, p, fx, fc);
    let after2 = d.arrow(le_x_hi, concl);
    let after1 = d.arrow(le_lo_x, after2);
    d.pi_fv(x_fv, carrier, after1)
}

/// The innermost step: given the exact rational gaps `q1` (`lo + q1 <= c`)
/// and `q2` (`c + q2 <= hi`), the `hd_spec` modulus bound at `e`, and a
/// candidate `q` already known `<= q1`, `<= q2`, and `<= bound_mod` (as an
/// exact `Rat` inequality), build the two perturbed points `c ± q`, show they
/// lie in `[lo, hi]`, apply `hd_spec` at each, and close `target`.
#[allow(clippy::too_many_arguments)]
fn final_with_q(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    fp: ExprId,
    lo: ExprId,
    hi: ExprId,
    hd: ExprId,
    c: ExprId,
    hmax: ExprId,
    e: ExprId,
    fp_c: ExprId,
    bound_mod_rat: ExprId,
    q1: ExprId,
    lo_q1_le_c: ExprId,
    q2: ExprId,
    c_q2_le_hi: ExprId,
    le_lo_c: ExprId,
    le_c_hi: ExprId,
    q: ExprId,
    q_pos: ExprId,
    q_le_q1: ExprId,
    q_le_q2: ExprId,
    q_le_boundmod: ExprId,
    target: ExprId,
) -> ExprId {
    let rat = p.rat;
    let zero_r = rzero(d, rat);
    let zero_le_q = d.lemma(rat.le_of_lt, &[zero_r, q, q_pos]);

    let q_emb = embed(d, p, q);
    let neg_q_emb = cneg(d, p, q_emb);
    let y_plus = cadd(d, p, c, q_emb);
    let y_minus = cadd(d, p, c, neg_q_emb);
    let refl_c = d.lemma(p.le_refl, &[c]);

    // --- range containment ---------------------------------------------
    let c_le_yplus = d.lemma(p.le_add_of_nonneg, &[c, q, zero_le_q]);
    let le_lo_yplus = d.lemma(p.le_trans, &[lo, c, y_plus, le_lo_c, c_le_yplus]);

    let q1_emb = embed(d, p, q1);
    let q2_emb = embed(d, p, q2);
    let q_le_q2_emb = d.lemma(p.of_rat_le, &[q, q2, q_le_q2]);
    let c_plus_q2 = cadd(d, p, c, q2_emb);
    let yplus_le_cq2 = d.lemma(p.add_le_add, &[c, c, q_emb, q2_emb, refl_c, q_le_q2_emb]);
    let le_yplus_hi = d.lemma(
        p.le_trans,
        &[y_plus, c_plus_q2, hi, yplus_le_cq2, c_q2_le_hi],
    );

    let lo_le_c_minus_q1 = le_sub_of_add_le(d, p, lo, q1_emb, c, lo_q1_le_c);
    let q_le_q1_emb = d.lemma(p.of_rat_le, &[q, q1, q_le_q1]);
    let negq1_le_negq = d.lemma(p.neg_le_neg, &[q_emb, q1_emb, q_le_q1_emb]);
    let neg_q1_emb_a = cneg(d, p, q1_emb);
    let c_minus_q1 = cadd(d, p, c, neg_q1_emb_a);
    let neg_q1_emb_b = cneg(d, p, q1_emb);
    let cminusq1_le_yminus = d.lemma(
        p.add_le_add,
        &[c, c, neg_q1_emb_b, neg_q_emb, refl_c, negq1_le_negq],
    );
    let le_lo_yminus = d.lemma(
        p.le_trans,
        &[
            lo,
            c_minus_q1,
            y_minus,
            lo_le_c_minus_q1,
            cminusq1_le_yminus,
        ],
    );

    let neg_zero_eq = neg_zero_equiv(d, p);
    let zero_le_q_emb = d.lemma(p.of_rat_le, &[zero_r, q, zero_le_q]);
    let zero_c_a = czero(d, p);
    let negq_le_negzero = d.lemma(p.neg_le_neg, &[zero_c_a, q_emb, zero_le_q_emb]);
    let refl_negqemb = erefl(d, p, neg_q_emb);
    let zero_c_b = czero(d, p);
    let neg_zero_c = cneg(d, p, zero_c_b);
    let zero_c_c = czero(d, p);
    let negq_le_zero = d.lemma(
        p.le_congr,
        &[
            neg_q_emb,
            neg_q_emb,
            neg_zero_c,
            zero_c_c,
            refl_negqemb,
            neg_zero_eq,
            negq_le_negzero,
        ],
    );
    let zero_c_d = czero(d, p);
    let c_plus_zero = cadd(d, p, c, zero_c_d);
    let zero_c_e = czero(d, p);
    let yminus_le_cplus0 = d.lemma(
        p.add_le_add,
        &[c, c, neg_q_emb, zero_c_e, refl_c, negq_le_zero],
    );
    let az = d.lemma(p.add_zero, &[c]);
    let refl_yminus = erefl(d, p, y_minus);
    let yminus_le_c = d.lemma(
        p.le_congr,
        &[
            y_minus,
            y_minus,
            c_plus_zero,
            c,
            refl_yminus,
            az,
            yminus_le_cplus0,
        ],
    );
    let le_yminus_hi = d.lemma(p.le_trans, &[y_minus, c, hi, yminus_le_c, le_c_hi]);

    // --- diff_yx identities ----------------------------------------------
    let neg_c_plus = cneg(d, p, c);
    let diff_yx_plus = cadd(d, p, y_plus, neg_c_plus);
    let diff_plus_eq = add_sub_cancel(d, p, c, q_emb); // Equiv diff_yx_plus q_emb
    let neg_c_minus = cneg(d, p, c);
    let diff_yx_minus = cadd(d, p, y_minus, neg_c_minus);
    let diff_minus_eq = add_sub_cancel(d, p, c, neg_q_emb); // Equiv diff_yx_minus neg_q_emb

    let abs_diff_plus_eq_q = {
        let abs_diff_plus = cabs(d, p, diff_yx_plus);
        let abs_qemb = cabs(d, p, q_emb);
        let step1 = d.lemma(p.abs_congr, &[diff_yx_plus, q_emb, diff_plus_eq]);
        let step2 = abs_of_nonneg(d, p, q, zero_le_q);
        d.lemma(
            p.equiv_trans,
            &[abs_diff_plus, abs_qemb, q_emb, step1, step2],
        )
    };
    let abs_diff_minus_eq_q = {
        let abs_diff_minus = cabs(d, p, diff_yx_minus);
        let abs_negqemb = cabs(d, p, neg_q_emb);
        let abs_qemb = cabs(d, p, q_emb);
        let step1 = d.lemma(p.abs_congr, &[diff_yx_minus, neg_q_emb, diff_minus_eq]);
        let step2 = abs_neg_equiv(d, p, q_emb);
        let step3 = abs_of_nonneg(d, p, q, zero_le_q);
        let chain1 = d.lemma(
            p.equiv_trans,
            &[abs_diff_minus, abs_negqemb, abs_qemb, step1, step2],
        );
        d.lemma(
            p.equiv_trans,
            &[abs_diff_minus, abs_qemb, q_emb, chain1, step3],
        )
    };

    // --- hd_spec hypotheses and calls -------------------------------------
    let bound_mod_emb = embed(d, p, bound_mod_rat);
    let build_hyp = |d: &mut IntDev<'_>, diff_term: ExprId, abs_diff_eq_q: ExprId| -> ExprId {
        let q_le_ofr_mod = d.lemma(p.of_rat_le, &[q, bound_mod_rat, q_le_boundmod]);
        let abs_diff = cabs(d, p, diff_term);
        let abs_diff_eq_q_symm = esymm(d, p, abs_diff, q_emb, abs_diff_eq_q);
        let refl_bound = erefl(d, p, bound_mod_emb);
        d.lemma(
            p.le_congr,
            &[
                q_emb,
                abs_diff,
                bound_mod_emb,
                bound_mod_emb,
                abs_diff_eq_q_symm,
                refl_bound,
                q_le_ofr_mod,
            ],
        )
    };
    let hyp_plus = build_hyp(d, diff_yx_plus, abs_diff_plus_eq_q);
    let hyp_minus = build_hyp(d, diff_yx_minus, abs_diff_minus_eq_q);

    let spec_plus = d.lemma(
        p.hd_spec,
        &[
            f,
            fp,
            lo,
            hi,
            hd,
            e,
            c,
            y_plus,
            le_lo_c,
            le_c_hi,
            le_lo_yplus,
            le_yplus_hi,
            hyp_plus,
        ],
    );
    let spec_minus = d.lemma(
        p.hd_spec,
        &[
            f,
            fp,
            lo,
            hi,
            hd,
            e,
            c,
            y_minus,
            le_lo_c,
            le_c_hi,
            le_lo_yminus,
            le_yminus_hi,
            hyp_minus,
        ],
    );

    let bound_e_out_rat = div_succ(d, p, 1, e);
    let c_emb_out = embed(d, p, bound_e_out_rat);
    let new_bound = cmul(d, p, c_emb_out, q_emb);

    let fc = d.apply(f, &[c]);
    let fy_plus = d.apply(f, &[y_plus]);
    let fy_minus = d.apply(f, &[y_minus]);

    let neg_fc_a = cneg(d, p, fc);
    let d_plus = cadd(d, p, fy_plus, neg_fc_a);
    let fpq_plus = cmul(d, p, fp_c, diff_yx_plus);
    let neg_fpq_plus = cneg(d, p, fpq_plus);
    let error_plus = cadd(d, p, d_plus, neg_fpq_plus);

    let neg_fc_b = cneg(d, p, fc);
    let d_minus = cadd(d, p, fy_minus, neg_fc_b);
    let fpq_minus = cmul(d, p, fp_c, diff_yx_minus);
    let neg_fpq_minus = cneg(d, p, fpq_minus);
    let error_minus = cadd(d, p, d_minus, neg_fpq_minus);

    // rewrite each spec's RHS bound `mul c_emb_out (abs diff)` down to `mul
    // c_emb_out q_emb` (the same `new_bound` for both branches).
    let rewrite_bound = |d: &mut IntDev<'_>,
                         spec: ExprId,
                         diff_term: ExprId,
                         abs_diff_eq_q: ExprId,
                         error_term: ExprId|
     -> ExprId {
        let abs_diff = cabs(d, p, diff_term);
        let raw_bound = cmul(d, p, c_emb_out, abs_diff);
        let mc = {
            let refl_c_emb_out = erefl(d, p, c_emb_out);
            d.lemma(
                p.mul_congr,
                &[
                    c_emb_out,
                    c_emb_out,
                    abs_diff,
                    q_emb,
                    refl_c_emb_out,
                    abs_diff_eq_q,
                ],
            )
        };
        let abs_error = cabs(d, p, error_term);
        let refl_abs_error = erefl(d, p, abs_error);
        d.lemma(
            p.le_congr,
            &[
                abs_error,
                abs_error,
                raw_bound,
                new_bound,
                refl_abs_error,
                mc,
                spec,
            ],
        )
    };
    let spec_plus_rw = rewrite_bound(d, spec_plus, diff_yx_plus, abs_diff_plus_eq_q, error_plus);
    let spec_minus_rw = rewrite_bound(
        d,
        spec_minus,
        diff_yx_minus,
        abs_diff_minus_eq_q,
        error_minus,
    );

    let h_lower_plus = neg_le_of_abs_le(d, p, error_plus, new_bound, spec_plus_rw);
    let h_lower_minus = neg_le_of_abs_le(d, p, error_minus, new_bound, spec_minus_rw);

    let hmax_at_yplus = d.apply(hmax, &[y_plus, le_lo_yplus, le_yplus_hi]);
    let hmax_at_yminus = d.apply(hmax, &[y_minus, le_lo_yminus, le_yminus_hi]);
    let d_plus_le_zero = nonpos_of_le(d, p, fy_plus, fc, hmax_at_yplus);
    let d_minus_le_zero = nonpos_of_le(d, p, fy_minus, fc, hmax_at_yminus);

    // fpq_plus <= new_bound, fpq_minus <= new_bound.
    let fpq_plus_le_bound = fpq_le_bound_from_lower(
        d,
        p,
        d_plus,
        fpq_plus,
        new_bound,
        h_lower_plus,
        d_plus_le_zero,
    );
    let fpq_minus_le_bound = fpq_le_bound_from_lower(
        d,
        p,
        d_minus,
        fpq_minus,
        new_bound,
        h_lower_minus,
        d_minus_le_zero,
    );

    // --- rewrite fpq_plus/fpq_minus in terms of fp_c and q_emb ------------
    // fpq_plus = mul fp_c diff_yx_plus ~ mul fp_c q_emb.
    let fpq_plus_eq = {
        let refl_fpc = erefl(d, p, fp_c);
        d.lemma(
            p.mul_congr,
            &[fp_c, fp_c, diff_yx_plus, q_emb, refl_fpc, diff_plus_eq],
        )
    };
    let mul_fpc_qemb = cmul(d, p, fp_c, q_emb);
    let refl_newbound1 = erefl(d, p, new_bound);
    let le_mul_fpc_qemb_bound = d.lemma(
        p.le_congr,
        &[
            fpq_plus,
            mul_fpc_qemb,
            new_bound,
            new_bound,
            fpq_plus_eq,
            refl_newbound1,
            fpq_plus_le_bound,
        ],
    );
    // commute both sides: mul fp_c q_emb ~ mul q_emb fp_c; new_bound = mul
    // c_emb_out q_emb ~ mul q_emb c_emb_out.
    let comm1 = d.lemma(p.mul_comm, &[fp_c, q_emb]);
    let mul_qemb_fpc = cmul(d, p, q_emb, fp_c);
    let comm2 = d.lemma(p.mul_comm, &[c_emb_out, q_emb]);
    let mul_qemb_cout = cmul(d, p, q_emb, c_emb_out);
    let le_mul_qemb_fpc_qcout = d.lemma(
        p.le_congr,
        &[
            mul_fpc_qemb,
            mul_qemb_fpc,
            new_bound,
            mul_qemb_cout,
            comm1,
            comm2,
            le_mul_fpc_qemb_bound,
        ],
    );
    // le_mul_qemb_fpc_qcout : le (mul q_emb fp_c) (mul q_emb c_emb_out)

    // fpq_minus = mul fp_c diff_yx_minus ~ mul fp_c neg_q_emb ~ neg (mul fp_c
    // q_emb) ~ neg (mul q_emb fp_c) ~ mul q_emb (neg fp_c).
    let fpq_minus_eq1 = {
        let refl_fpc = erefl(d, p, fp_c);
        d.lemma(
            p.mul_congr,
            &[
                fp_c,
                fp_c,
                diff_yx_minus,
                neg_q_emb,
                refl_fpc,
                diff_minus_eq,
            ],
        )
    };
    let mul_fpc_negqemb = cmul(d, p, fp_c, neg_q_emb);
    let mn1 = mul_neg_equiv(d, p, fp_c, q_emb); // Equiv (mul fp_c neg_q_emb) (neg (mul fp_c q_emb))
    let neg_mul_fpc_qemb = cneg(d, p, mul_fpc_qemb);
    let fpq_minus_eq = d.lemma(
        p.equiv_trans,
        &[
            fpq_minus,
            mul_fpc_negqemb,
            neg_mul_fpc_qemb,
            fpq_minus_eq1,
            mn1,
        ],
    );
    let refl_newbound2 = erefl(d, p, new_bound);
    let le_negmulfpcqemb_bound = d.lemma(
        p.le_congr,
        &[
            fpq_minus,
            neg_mul_fpc_qemb,
            new_bound,
            new_bound,
            fpq_minus_eq,
            refl_newbound2,
            fpq_minus_le_bound,
        ],
    );
    // rewrite neg (mul fp_c q_emb) ~ neg (mul q_emb fp_c) via mul_comm+neg_congr
    let neg_mul_qemb_fpc = cneg(d, p, mul_qemb_fpc);
    let neg_comm = d.lemma(p.neg_congr, &[mul_fpc_qemb, mul_qemb_fpc, comm1]);
    let refl_newbound3 = erefl(d, p, new_bound);
    let le_negmulqembfpc_bound = d.lemma(
        p.le_congr,
        &[
            neg_mul_fpc_qemb,
            neg_mul_qemb_fpc,
            new_bound,
            new_bound,
            neg_comm,
            refl_newbound3,
            le_negmulfpcqemb_bound,
        ],
    );
    // neg (mul q_emb fp_c) ~ mul q_emb (neg fp_c), via esymm(mul_neg_equiv(q_emb, fp_c))
    let mn2 = mul_neg_equiv(d, p, q_emb, fp_c); // Equiv (mul q_emb (neg fp_c)) (neg (mul q_emb fp_c))
    let mul_qemb_negfpc = mul_qemb_fpc_neg(d, p, q_emb, fp_c);
    let mn2_symm = esymm(d, p, mul_qemb_negfpc, neg_mul_qemb_fpc, mn2);
    let refl_newbound4 = erefl(d, p, new_bound);
    let le_mulqembnegfpc_bound = d.lemma(
        p.le_congr,
        &[
            neg_mul_qemb_fpc,
            mul_qemb_negfpc,
            new_bound,
            new_bound,
            mn2_symm,
            refl_newbound4,
            le_negmulqembfpc_bound,
        ],
    );
    // rewrite RHS new_bound ~ mul q_emb c_emb_out (reuse comm2)
    let refl_mul_qemb_negfpc = erefl(d, p, mul_qemb_negfpc);
    let le_mulqembnegfpc_mulqembcout = d.lemma(
        p.le_congr,
        &[
            mul_qemb_negfpc,
            mul_qemb_negfpc,
            new_bound,
            mul_qemb_cout,
            refl_mul_qemb_negfpc,
            comm2,
            le_mulqembnegfpc_bound,
        ],
    );

    // --- cancel q_emb via a PosBound witness, closing both directions -----
    let nat = d.nat_ty();
    let lt_zero_qemb = d.lemma(p.of_rat_pos, &[q, q_pos]);
    let ex_witness = d.lemma(p.pos_bound_of_lt, &[q_emb, lt_zero_qemb]);
    let predicate_k = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = pos_bound(d, p, q_emb, k);
        d.lam_fv(k_fv, nat, body)
    };
    let minor_k = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let pb_ty = pos_bound(d, p, q_emb, k);
        let pb_fv = d.fresh_fvar();
        let pb = d.kernel().fvar(pb_fv);

        let h_upper_final = d.lemma(
            p.le_of_mul_le_mul_left,
            &[q_emb, fp_c, c_emb_out, k, pb, le_mul_qemb_fpc_qcout],
        );
        let neg_fp_c = cneg(d, p, fp_c);
        let h_lower_final = d.lemma(
            p.le_of_mul_le_mul_left,
            &[
                q_emb,
                neg_fp_c,
                c_emb_out,
                k,
                pb,
                le_mulqembnegfpc_mulqembcout,
            ],
        );
        let body = d.lemma(p.abs_le, &[fp_c, c_emb_out, h_upper_final, h_lower_final]);

        let with_pb = d.lam_fv(pb_fv, pb_ty, body);
        d.lam_fv(k_fv, nat, with_pb)
    };
    crate::int_prelude::ops::exists_elim(d, predicate_k, target, ex_witness, minor_k)
}

/// `mul q_emb (neg fp_c)` — split out only so the (identical) term used on
/// both sides of an `esymm` call above is built once, avoiding an accidental
/// mismatch between two independently-built copies.
fn mul_qemb_fpc_neg(d: &mut IntDev<'_>, p: CRealPrelude, q_emb: ExprId, fp_c: ExprId) -> ExprId {
    let neg_fp_c = cneg(d, p, fp_c);
    cmul(d, p, q_emb, neg_fp_c)
}

/// Build the `q2`-eliminating minor (the inner `gap_elim` over `lt c hi`),
/// given the already-eliminated `q1` gap.
#[allow(clippy::too_many_arguments)]
fn build_minor2(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    fp: ExprId,
    lo: ExprId,
    hi: ExprId,
    hd: ExprId,
    c: ExprId,
    hmax: ExprId,
    e: ExprId,
    fp_c: ExprId,
    le_lo_c: ExprId,
    le_c_hi: ExprId,
    bound_mod_rat: ExprId,
    bound_mod_pos: ExprId,
    q1: ExprId,
    q1_pos: ExprId,
    lo_q1_le_c: ExprId,
    target: ExprId,
) -> ExprId {
    let rat_carrier = rat_ty(d);
    let rat = p.rat;
    let zero_r = rzero(d, rat);

    let q2_fv = d.fresh_fvar();
    let q2 = d.kernel().fvar(q2_fv);
    let q2_pos_ty = rlt(d, rat, zero_r, q2);
    let q2_emb = embed(d, p, q2);
    let c_plus_q2_for_gap = cadd(d, p, c, q2_emb);
    let c_q2_le_hi_ty = cle(d, p, c_plus_q2_for_gap, hi);
    let w2_ty = d.and(q2_pos_ty, c_q2_le_hi_ty);
    let w2_fv = d.fresh_fvar();
    let w2 = d.kernel().fvar(w2_fv);
    let (q2_pos, c_q2_le_hi) = gap_halves(d, p, c, hi, q2, w2);

    let body = rat_min_elim(
        d,
        p,
        q1,
        q2,
        q1_pos,
        q2_pos,
        target,
        &|d, m12, m12_pos, m12_le_q1, m12_le_q2| {
            rat_min_elim(
                d,
                p,
                m12,
                bound_mod_rat,
                m12_pos,
                bound_mod_pos,
                target,
                &|d, q, q_pos, q_le_m12, q_le_boundmod| {
                    let q_le_q1 = d.lemma(rat.le_trans, &[q, m12, q1, q_le_m12, m12_le_q1]);
                    let q_le_q2 = d.lemma(rat.le_trans, &[q, m12, q2, q_le_m12, m12_le_q2]);
                    final_with_q(
                        d,
                        p,
                        f,
                        fp,
                        lo,
                        hi,
                        hd,
                        c,
                        hmax,
                        e,
                        fp_c,
                        bound_mod_rat,
                        q1,
                        lo_q1_le_c,
                        q2,
                        c_q2_le_hi,
                        le_lo_c,
                        le_c_hi,
                        q,
                        q_pos,
                        q_le_q1,
                        q_le_q2,
                        q_le_boundmod,
                        target,
                    )
                },
            )
        },
    );

    let with_w2 = d.lam_fv(w2_fv, w2_ty, body);
    d.lam_fv(q2_fv, rat_carrier, with_w2)
}

/// Build the `q1`-eliminating minor (the outer `gap_elim` over `lt lo c`).
#[allow(clippy::too_many_arguments)]
fn build_minor1(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
    f: ExprId,
    fp: ExprId,
    lo: ExprId,
    hi: ExprId,
    hd: ExprId,
    c: ExprId,
    hmax: ExprId,
    hch: ExprId,
    e: ExprId,
    fp_c: ExprId,
    le_lo_c: ExprId,
    le_c_hi: ExprId,
    bound_mod_rat: ExprId,
    bound_mod_pos: ExprId,
    target: ExprId,
) -> ExprId {
    let rat_carrier = rat_ty(d);
    let rat = p.rat;
    let zero_r = rzero(d, rat);

    let q1_fv = d.fresh_fvar();
    let q1 = d.kernel().fvar(q1_fv);
    let q1_pos_ty = rlt(d, rat, zero_r, q1);
    let q1_emb = embed(d, p, q1);
    let lo_plus_q1_for_gap = cadd(d, p, lo, q1_emb);
    let lo_q1_le_c_ty = cle(d, p, lo_plus_q1_for_gap, c);
    let w1_ty = d.and(q1_pos_ty, lo_q1_le_c_ty);
    let w1_fv = d.fresh_fvar();
    let w1 = d.kernel().fvar(w1_fv);
    let (q1_pos, lo_q1_le_c) = gap_halves(d, p, lo, c, q1, w1);

    let minor2 = build_minor2(
        d,
        p,
        f,
        fp,
        lo,
        hi,
        hd,
        c,
        hmax,
        e,
        fp_c,
        le_lo_c,
        le_c_hi,
        bound_mod_rat,
        bound_mod_pos,
        q1,
        q1_pos,
        lo_q1_le_c,
        target,
    );
    let body = gap_elim(d, p, c, hi, target, hch, minor2);

    let with_w1 = d.lam_fv(w1_fv, w1_ty, body);
    d.lam_fv(q1_fv, rat_carrier, with_w1)
}

/// Admit `CReal.fermat_interiorExtremum`.
fn declare_fermat_interior_extremum(
    d: &mut IntDev<'_>,
    p: CRealPrelude,
) -> Result<(), KernelError> {
    let carrier = creal_ty(d, p);
    let nat = d.nat_ty();
    let fn_carrier = fn_ty(d, p);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    let fp_fv = d.fresh_fvar();
    let fp = d.kernel().fvar(fp_fv);
    let lo_fv = d.fresh_fvar();
    let lo = d.kernel().fvar(lo_fv);
    let hi_fv = d.fresh_fvar();
    let hi = d.kernel().fvar(hi_fv);
    let hd_type = hd_ty(d, p, f, fp, lo, hi);
    let hd_fv = d.fresh_fvar();
    let hd = d.kernel().fvar(hd_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hlc_ty = clt(d, p, lo, c);
    let hlc_fv = d.fresh_fvar();
    let hlc = d.kernel().fvar(hlc_fv);
    let hch_ty = clt(d, p, c, hi);
    let hch_fv = d.fresh_fvar();
    let hch = d.kernel().fvar(hch_fv);
    let hmax_type = hmax_ty(d, p, f, lo, hi, c);
    let hmax_fv = d.fresh_fvar();
    let hmax = d.kernel().fvar(hmax_fv);

    let fp_c = d.apply(fp, &[c]);

    // --- the per-e goal and its proof --------------------------------------
    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let abs_fp_c = cabs(d, p, fp_c);
    let bound_e_rat = div_succ(d, p, 1, e);
    let bound_e_emb = embed(d, p, bound_e_rat);
    let target = cle(d, p, abs_fp_c, bound_e_emb);

    let le_lo_c = d.lemma(p.le_of_lt, &[lo, c, hlc]);
    let le_c_hi = d.lemma(p.le_of_lt, &[c, hi, hch]);

    let mod_fn = d.const_app(p.hd_modulus, &[f, fp, lo, hi, hd]);
    let mod_e = d.apply(mod_fn, &[e]);
    let bound_mod_rat = div_succ(d, p, 1, mod_e);
    let bound_mod_pos = {
        let one_nat = d.num(1);
        let unit_le = d.lemma(p.rat.int.nat.le_refl, &[one_nat]);
        d.lemma(p.rat.nat_div_succ_pos, &[one_nat, mod_e, unit_le])
    };

    let minor1 = build_minor1(
        d,
        p,
        f,
        fp,
        lo,
        hi,
        hd,
        c,
        hmax,
        hch,
        e,
        fp_c,
        le_lo_c,
        le_c_hi,
        bound_mod_rat,
        bound_mod_pos,
        target,
    );
    let core = gap_elim(d, p, lo, c, target, hlc, minor1);

    let per_e = d.lam_fv(e_fv, nat, core);
    let zero_c = czero(d, p);
    let result = d.lemma(p.equiv_zero_of_small, &[fp_c, per_e]);

    let value = {
        let with_hmax = d.lam_fv(hmax_fv, hmax_type, result);
        let with_hch = d.lam_fv(hch_fv, hch_ty, with_hmax);
        let with_hlc = d.lam_fv(hlc_fv, hlc_ty, with_hch);
        let with_c = d.lam_fv(c_fv, carrier, with_hlc);
        let with_hd = d.lam_fv(hd_fv, hd_type, with_c);
        let with_hi = d.lam_fv(hi_fv, carrier, with_hd);
        let with_lo = d.lam_fv(lo_fv, carrier, with_hi);
        let with_fp = d.lam_fv(fp_fv, fn_carrier, with_lo);
        d.lam_fv(f_fv, fn_carrier, with_fp)
    };
    let ty = {
        let conclusion = super::equiv(d, p, fp_c, zero_c);
        let after_hmax = d.arrow(hmax_type, conclusion);
        let after_hch = d.arrow(hch_ty, after_hmax);
        let after_hlc = d.arrow(hlc_ty, after_hch);
        let with_c = d.pi_fv(c_fv, carrier, after_hlc);
        let with_hd = d.pi_fv(hd_fv, hd_type, with_c);
        let with_hi = d.pi_fv(hi_fv, carrier, with_hd);
        let with_lo = d.pi_fv(lo_fv, carrier, with_hi);
        let with_fp = d.pi_fv(fp_fv, fn_carrier, with_lo);
        d.pi_fv(f_fv, fn_carrier, with_fp)
    };

    d.kernel().add_declaration(Declaration::Theorem {
        name: p.fermat_interior_extremum,
        uparams: vec![],
        ty,
        value,
    })
}
