//! Toward `det (A·B) n = det A n * det B n` at a **symbolic** `n` — the last
//! of the four laws ADR-1120 named over `Rat.det` and the one ADR-1440 /
//! ADR-1470 reduced to two obligations.
//!
//! ## Where the target stands
//!
//! Multiplicativity is proved at dimension 2 (`Rat.det_matMul_2`, whose
//! shortcut is a literal-`2` iota reduction and does not generalize). At a
//! symbolic `n` the classical route is:
//!
//! 1. **obligation 1** — expand `det (A·B) n` in the rows of `A·B`, each of
//!    which is a `Rat.sumRange` of rows of `B` with coefficients `A r k`,
//!    using `Rat.det_row_multilinear` once per row. This produces a sum
//!    indexed by the FUNCTION SPACE `[0,n) -> [0,n)` (the `Int.sumMaps` shape,
//!    for which no `Rat` analogue exists yet).
//! 2. **obligation 2** — the SELECTION lemma
//!    `MapsInto g n -> det (B o g) n = det (matId o g) n * det B n`. Its free
//!    (non-injective) half is `Rat.det_row_selection_of_duplicate`
//!    (`matrix_det_selection.rs`); the injective half is a cursor induction
//!    over "how many trailing positions `g` already fixes", using pigeonhole,
//!    a two-point swap and `Rat.det_row_swap` (ADR-1470's route).
//!
//! ## What this module supplies
//!
//! `Rat.det_congr_lt`, the ROW-BOUNDED determinant congruence.
//! `Rat.det_congr` requires the two matrices to agree at EVERY index pair;
//! both obligations above need them to agree only on the rows the determinant
//! can actually read, because every reindexing map they build (`g` from a
//! `sumMaps`-style fold, or `g` corrected to fix everything above the cursor)
//! is under no control at all outside `[0,n)`.
//!
//! It is the row index alone that has to be bounded, not the column: `det A n`
//! reads `A` at `(r,c)` with `r < n` AND `c < n`, but the cofactor recursion
//! reaches a column only through `Rat.matSkip`, so bounding the row is enough
//! to carry the induction and it needs no `matSkip` bound lemma. Bounding both
//! would need `Lt (matSkip j c) (succ m)` from `Lt c m`, which nothing in this
//! prelude supplies.

use super::RatPrelude;
use super::matrix_det::{
    alt_hyp_ne, bool_cases, mat_ty, one_mul_pf, ralt_sign, rdet, rmat_id, rmat_minor_of, rmat_skip,
};
use super::matrix_det_selection::row_compose;
use super::ops::{nat_eq_to_rat, rchain, rcongr, req, rmul, rneg, rone, rrefl, rsymm, rtrans};
use crate::BinderInfo;
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::{IntDev, exists_elim};
use crate::nat_prelude::NatOps;

/// Declare everything this file proves.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_matrix_det_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_det_congr_lt(d, p)?;
    declare_mat_skip_lt_succ(d, p)?;
    declare_det_congr_entry_lt(d, p)?;
    declare_det_row_selection_injective(d, p)?;
    declare_det_row_selection_full(d, p)?;
    Ok(())
}

/// `∀ r, Lt r bound → ∀ c, Eq Rat (A r c) (B r c)` — two matrices agreeing on
/// every row the bound admits, at every column.
fn row_bounded_eq_ty(d: &mut IntDev<'_>, a: ExprId, b: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let hr = d.lt(r, bound);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let ar = d.apply(a, &[r, c]);
    let br = d.apply(b, &[r, c]);
    let eq = req(d, ar, br);
    let inner = d.pi_fv(c_fv, nat, eq);
    let with_h = d.arrow(hr, inner);
    d.pi_fv(r_fv, nat, with_h)
}

/// `fun c => altSign c * (M 0 c * det (matMinor M 0 c) j)` — the cofactor
/// summand `Rat.det_succ` unfolds to, at dimension `succ j`.
fn cofactor_summand(d: &mut IntDev<'_>, p: RatPrelude, m: ExprId, j: ExprId) -> ExprId {
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
}

/// Admit `Rat.det_congr_lt : ∀ n A B, (∀ r, Lt r n → ∀ c, A r c = B r c) →
/// det A n = det B n`.
///
/// The same induction as `matrix_det.rs`'s `Rat.det_congr` — dimension
/// outermost, both matrices under the `Nat.rec` motive so the induction
/// hypothesis can be applied at the two MINORS — with the unrestricted
/// pointwise premise replaced by a row-bounded one. Two order facts carry the
/// bound through the successor step and nothing else changes:
///
/// - the expanded row is `0`, admitted by `Nat.zero_lt_succ`;
/// - the minor's row `r` is the matrix's row `succ r`, and `Lt r j` gives
///   `Lt (succ r) (succ j)` by `Nat.succ_le_succ` (`Lt x y` is definitionally
///   `Le (succ x) y`, so no unfolding lemma is needed).
///
/// The COLUMN is deliberately left unbounded — see the module doc.
fn declare_det_congr_lt(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let mty = mat_ty(d);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let hyp = row_bounded_eq_ty(d, a, b, x);
        let lhs = rdet(d, p, a, x);
        let rhs = rdet(d, p, b, x);
        let eq = req(d, lhs, rhs);
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
            let zero_n = d.zero();
            let hyp = row_bounded_eq_ty(d, a, b, zero_n);
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
            let sj = d.succ(j);
            let hyp = row_bounded_eq_ty(d, a, b, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let zero_n = d.zero();
            let f_a = cofactor_summand(d, p, a, j);
            let f_b = cofactor_summand(d, p, b, j);

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

                // `fun r hr c' => h (succ r) (succ_le_succ (succ r) j hr)
                //   (matSkip c c')` inhabits the minor's row-bounded premise,
                // because `matMinor A 0 c r c'` δβ-reduces to
                // `A (matSkip 0 r) (matSkip c c') ≡ A (succ r) (matSkip c c')`.
                let minor_pointwise = {
                    let np = d.prelude();
                    let r_fv = d.fresh_fvar();
                    let r = d.kernel().fvar(r_fv);
                    let hr_ty = d.lt(r, j);
                    let hr_fv = d.fresh_fvar();
                    let hr = d.kernel().fvar(hr_fv);
                    let cc_fv = d.fresh_fvar();
                    let cc = d.kernel().fvar(cc_fv);
                    let sr = d.succ(r);
                    let lifted = d.lemma(np.succ_le_succ, &[sr, j, hr]);
                    let col = rmat_skip(d, p, c, cc);
                    let body = d.apply(h, &[sr, lifted, col]);
                    let inner = d.lam_fv(cc_fv, nat, body);
                    let with_hr = d.lam_fv(hr_fv, hr_ty, inner);
                    d.lam_fv(r_fv, nat, with_hr)
                };
                let h_det = d.apply(ih, &[sub_a, sub_b, minor_pointwise]);

                let np = d.prelude();
                let lt_zero = d.lemma(np.zero_lt_succ, &[j]);
                let h_entry = d.apply(h, &[zero_n, lt_zero, c]);

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

            let sum_pf = d.lemma(p.sum_range_congr, &[f_a, f_b, sj, pointwise]);

            let with_h = d.lam_fv(h_fv, hyp, sum_pf);
            let over_b = d.lam_fv(b_fv, mty, with_h);
            d.lam_fv(a_fv, mty, over_b)
        },
        n,
    );

    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.det_congr_lt, ty, value)
}

// ---------------------------------------------------------------------------
// The SELECTION lemma's injective half -- ADR-1470's cursor induction
// ---------------------------------------------------------------------------

/// `False.rec` into `goal` from a proof of `False`.
fn ex_falso(d: &mut IntDev<'_>, goal: ExprId, contradiction: ExprId) -> ExprId {
    let logic = d.prelude().logic;
    let anon = d.anon_name();
    let false_ty = d.kernel().const_(logic.false_, vec![]);
    let motive = d.kernel().lam(anon, false_ty, goal, BinderInfo::Default);
    let zero = d.kernel().level_zero();
    let rec = d.kernel().const_(logic.false_rec, vec![zero]);
    d.apply(rec, &[motive, contradiction])
}

/// `∀ c, Eq Rat (mat u c) (mat v c)` from `heq : Eq Nat u v` — the pointwise
/// row equality every `Rat` matrix lemma wants, out of a `Nat` index equation.
/// `nat_eq_to_rat`, never `NatOps::congr`, whose conclusion is hard-wired to
/// `Eq Nat`.
fn row_eq_of_nat_eq(d: &mut IntDev<'_>, mat: ExprId, u: ExprId, v: ExprId, heq: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let step = nat_eq_to_rat(d, u, v, heq, &|d, t| d.apply(mat, &[t, c]));
    d.lam_fv(c_fv, nat, step)
}

/// `Eq Rat (det (mat∘g) n) (mul (det (matId∘g) n) (det mat n))` — the
/// selection lemma's conclusion at one reindexing map.
fn selection_concl(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    b_mat: ExprId,
    g: ExprId,
    n: ExprId,
) -> ExprId {
    let bc = row_compose(d, b_mat, g);
    let mid = rmat_id(d, p);
    let mi = row_compose(d, mid, g);
    let lhs = rdet(d, p, bc, n);
    let d_mi = rdet(d, p, mi, n);
    let d_b = rdet(d, p, b_mat, n);
    let rhs = rmul(d, d_mi, d_b);
    req(d, lhs, rhs)
}

/// `∀ i, Le cursor i → Lt i n → Eq Nat (g i) i` — "`g` already fixes every
/// position from `cursor` up", the induction variable of the cursor argument.
fn fix_hyp_ty(d: &mut IntDev<'_>, g: ExprId, cursor: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let hle = d.le(cursor, i);
    let hlt = d.lt(i, n);
    let gi = d.apply(g, &[i]);
    let eqn = d.eq(gi, i);
    let inner = d.arrow(hlt, eqn);
    let with_le = d.arrow(hle, inner);
    d.pi_fv(i_fv, nat, with_le)
}

/// `Nat.transposition lo hi x`.
fn tswap(d: &mut IntDev<'_>, lo: ExprId, hi: ExprId, x: ExprId) -> ExprId {
    let name = d.prelude().transposition;
    d.const_app(name, &[lo, hi, x])
}

/// `Eq Rat (det (mat∘(g∘swap)) (succ m)) (Rat.neg (det (mat∘g) (succ m)))`,
/// where `swap` is `Nat.transposition lo hi` — one application of
/// `Rat.det_row_swap` at the two rows the transposition exchanges.
///
/// The third hypothesis is the one that needs `Nat.transposition_eq_of_ne`:
/// `det_row_swap` quantifies over every row that is NEITHER of the exchanged
/// pair, and a transposition fixes exactly those.
#[allow(clippy::too_many_arguments)]
fn swapped_det(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    mat: ExprId,
    g: ExprId,
    lo: ExprId,
    hi: ExprId,
    m: ExprId,
    h_lo_hi: ExprId,
    h_lo_n: ExprId,
    h_hi_n: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let np = d.prelude();

    let sigma = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let sx = tswap(d, lo, hi, x);
        let body = d.apply(g, &[sx]);
        d.lam_fv(x_fv, nat, body)
    };
    let a_mat = row_compose(d, mat, g);
    let b_mat = row_compose(d, mat, sigma);

    // `Nat.beq lo hi = false`, from `Lt lo hi` by refutation.
    let hne = {
        let eq_ty = d.eq(lo, hi);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let motive = d.eq_motive(lo, &|d, t| d.lt(t, hi));
        let lt_hi_hi = d.transport(lo, motive, h_lo_hi, hi, h);
        let irr = d.lemma(np.lt_irrefl, &[hi]);
        let contradiction = d.apply(irr, &[lt_hi_hi]);
        let not_eq = d.lam_fv(h_fv, eq_ty, contradiction);
        d.lemma(np.beq_eq_false_of_ne, &[lo, hi, not_eq])
    };

    let ble_of = |d: &mut IntDev<'_>, x: ExprId, h: ExprId| -> ExprId {
        let np = d.prelude();
        let le = d.lemma(np.le_of_lt_succ, &[x, m]);
        let le = d.apply(le, &[h]);
        d.lemma(np.ble_eq_true_of_le, &[x, m, le])
    };
    let hble_lo = ble_of(d, lo, h_lo_n);
    let hble_hi = ble_of(d, hi, h_hi_n);

    // `∀ c, (mat∘σ) lo c = (mat∘g) hi c` -- `σ lo = g (swap lo) = g hi`.
    let h_row_lo = {
        let at_i = d.lemma(np.transposition_at_i, &[lo, hi]);
        let t_lo = tswap(d, lo, hi, lo);
        let g_t = d.apply(g, &[t_lo]);
        let g_hi = d.apply(g, &[hi]);
        let lifted = d.congr(t_lo, hi, at_i, &|d, t| d.apply(g, &[t]));
        row_eq_of_nat_eq(d, mat, g_t, g_hi, lifted)
    };
    // `∀ c, (mat∘σ) hi c = (mat∘g) lo c` -- `σ hi = g (swap hi) = g lo`.
    let h_row_hi = {
        let at_j = d.lemma(np.transposition_at_j, &[lo, hi, h_lo_hi]);
        let t_hi = tswap(d, lo, hi, hi);
        let g_t = d.apply(g, &[t_hi]);
        let g_lo = d.apply(g, &[lo]);
        let lifted = d.congr(t_hi, lo, at_j, &|d, t| d.apply(g, &[t]));
        row_eq_of_nat_eq(d, mat, g_t, g_lo, lifted)
    };
    // `∀ r c, beq r lo = false → beq r hi = false → (mat∘σ) r c = (mat∘g) r c`.
    // NOTE the binder order: `swap_other_ty` is `∀ r, beq r i = false →
    // beq r j = false → ∀ c, …`, with the column bound LAST and inside the two
    // boolean hypotheses, not `∀ r c, …` as the field doc reads.
    let h_rest = {
        let r_fv = d.fresh_fvar();
        let r = d.kernel().fvar(r_fv);
        let hb1_ty = alt_hyp_ne(d, r, lo);
        let hb1_fv = d.fresh_fvar();
        let hb1 = d.kernel().fvar(hb1_fv);
        let hb2_ty = alt_hyp_ne(d, r, hi);
        let hb2_fv = d.fresh_fvar();
        let hb2 = d.kernel().fvar(hb2_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);

        let np = d.prelude();
        let ne_lo = d.lemma(np.ne_of_beq_eq_false, &[r, lo, hb1]);
        let ne_hi = d.lemma(np.ne_of_beq_eq_false, &[r, hi, hb2]);
        let fixed = d.lemma(
            np.transposition_eq_of_ne,
            &[lo, hi, r, h_lo_hi, ne_lo, ne_hi],
        );
        let t_r = tswap(d, lo, hi, r);
        let g_t = d.apply(g, &[t_r]);
        let g_r = d.apply(g, &[r]);
        let lifted = d.congr(t_r, r, fixed, &|d, t| d.apply(g, &[t]));
        let body = nat_eq_to_rat(d, g_t, g_r, lifted, &|d, t| d.apply(mat, &[t, c]));
        let with_c = d.lam_fv(c_fv, nat, body);
        let with_b2 = d.lam_fv(hb2_fv, hb2_ty, with_c);
        let with_b1 = d.lam_fv(hb1_fv, hb1_ty, with_b2);
        d.lam_fv(r_fv, nat, with_b1)
    };

    d.lemma(
        p.det_row_swap,
        &[
            m, a_mat, b_mat, lo, hi, hne, hble_lo, hble_hi, h_row_lo, h_row_hi, h_rest,
        ],
    )
}

/// Admit `Rat.det_row_selection_injective : ∀ m B g, InjectiveOn g (succ m) →
/// MapsInto g (succ m) → det (B∘g) (succ m) =
/// det (matId∘g) (succ m) * det B (succ m)` — the SELECTION lemma's injective
/// half, ADR-1440's obligation 2 and the half ADR-1470 designed but did not
/// build.
///
/// A CURSOR induction on "how many trailing positions `g` already fixes",
/// with the dimension `succ m` and the matrix `B` OUTSIDE the induction and
/// the map `g` inside it (the step applies the induction hypothesis at a
/// DIFFERENT map, so `g` cannot be fixed outside):
///
/// ```text
/// P(k) := ∀ g, InjectiveOn g n → MapsInto g n →
///         (∀ i, Le k i → Lt i n → g i = i) →
///         det (B∘g) n = det (matId∘g) n * det B n
/// ```
///
/// - `P(0)`'s hypothesis (with `Nat.zero_le`) makes `g` the identity on all of
///   `[0,n)`, which is exactly what `Rat.det_congr_lt` — and NOT
///   `Rat.det_congr` — can consume: `g` is under no control at all outside
///   `[0,n)`. Then `Rat.det_matId` and `one * x = x`.
/// - `P(k) → P(succ k)` splits on `Nat.lt_or_ge k n`. When `Le n k` both
///   fixed-point ranges are empty, so `P(k)`'s hypothesis is derivable by
///   contradiction and the induction hypothesis applies to the SAME `g`.
///   When `Lt k n`, pigeonhole
///   (`Nat.injective_on_imp_surjective_on`) produces `w < n` with `g w = k`,
///   and `Nat.lt_or_ge`/`Nat.lt_or_eq_of_le` split it three ways: `Lt k w` is
///   impossible (`g`'s own hypothesis would force `g w = w = k`, against
///   `k < w`), `Eq k w` means `g` already fixes `k` so the hypothesis applies
///   directly, and `Lt w k` is the real case — compose with
///   `Nat.transposition w k`, which moves `k` into place, and relate the two
///   determinants by `Rat.det_row_swap`. The double negation cancels through
///   `Rat.neg_mul` and `Rat.neg_neg`.
///
/// Stated at `succ m` rather than a bare `n` because `Rat.det_row_swap` and
/// `Rat.det_alternating` are, and the `n = 0` instance is content-free
/// (`det _ 0 ≡ 1` on both sides).
fn declare_det_row_selection_injective(
    d: &mut IntDev<'_>,
    p: RatPrelude,
) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let mty = mat_ty(d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n = d.succ(m);
    let b_fv = d.fresh_fvar();
    let b_mat = d.kernel().fvar(b_fv);

    let inj_ty = |d: &mut IntDev<'_>, g: ExprId| -> ExprId {
        let name = d.prelude().injective_on;
        d.const_app(name, &[g, n])
    };
    let maps_ty = |d: &mut IntDev<'_>, g: ExprId| -> ExprId {
        let name = d.prelude().maps_into;
        d.const_app(name, &[g, n])
    };

    let motive = |d: &mut IntDev<'_>, cursor: ExprId| -> ExprId {
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let hinj = inj_ty(d, g);
        let hmaps = maps_ty(d, g);
        let hfix = fix_hyp_ty(d, g, cursor, n);
        let concl = selection_concl(d, p, b_mat, g, n);
        let with_fix = d.arrow(hfix, concl);
        let with_maps = d.arrow(hmaps, with_fix);
        let with_inj = d.arrow(hinj, with_maps);
        d.pi_fv(g_fv, fn_ty, with_inj)
    };

    let base = |d: &mut IntDev<'_>| -> ExprId {
        let zero_n = d.zero();
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let hinj_ty = inj_ty(d, g);
        let hinj_fv = d.fresh_fvar();
        let hmaps_ty = maps_ty(d, g);
        let hmaps_fv = d.fresh_fvar();
        let hfix_ty = fix_hyp_ty(d, g, zero_n, n);
        let hfix_fv = d.fresh_fvar();
        let hfix = d.kernel().fvar(hfix_fv);

        // `∀ r, Lt r n → ∀ c, mat (g r) c = mat r c`, for either matrix.
        let pointwise = |d: &mut IntDev<'_>, mat: ExprId| -> ExprId {
            let nat = d.nat_ty();
            let r_fv = d.fresh_fvar();
            let r = d.kernel().fvar(r_fv);
            let hr_ty = d.lt(r, n);
            let hr_fv = d.fresh_fvar();
            let hr = d.kernel().fvar(hr_fv);
            let np = d.prelude();
            let zle = d.lemma(np.zero_le, &[r]);
            let heq = d.apply(hfix, &[r, zle, hr]);
            let gr = d.apply(g, &[r]);
            let row = row_eq_of_nat_eq(d, mat, gr, r, heq);
            let with_hr = d.lam_fv(hr_fv, hr_ty, row);
            d.lam_fv(r_fv, nat, with_hr)
        };

        let bc = row_compose(d, b_mat, g);
        let mid = rmat_id(d, p);
        let mi = row_compose(d, mid, g);

        let pt_b = pointwise(d, b_mat);
        let pt_i = pointwise(d, mid);
        let e_b = d.lemma(p.det_congr_lt, &[n, bc, b_mat, pt_b]);
        let e_i = d.lemma(p.det_congr_lt, &[n, mi, mid, pt_i]);
        let e_id = d.lemma(p.det_mat_id, &[n]);

        let d_bc = rdet(d, p, bc, n);
        let d_mi = rdet(d, p, mi, n);
        let d_mid = rdet(d, p, mid, n);
        let d_b = rdet(d, p, b_mat, n);
        let one = rone(d, p);

        let rhs = rmul(d, d_mi, d_b);
        let mid1 = rmul(d, d_mid, d_b);
        let s1 = rcongr(d, d_mi, d_mid, e_i, &|d, t| rmul(d, t, d_b));
        let mid2 = rmul(d, one, d_b);
        let s2 = rcongr(d, d_mid, one, e_id, &|d, t| rmul(d, t, d_b));
        let s3 = one_mul_pf(d, p, d_b);
        let (_e, rhs_chain) = rchain(d, rhs, &[(mid1, s1), (mid2, s2), (d_b, s3)]);
        let back = rsymm(d, rhs, d_b, rhs_chain);
        let body = rtrans(d, d_bc, d_b, rhs, e_b, back);

        let with_fix = d.lam_fv(hfix_fv, hfix_ty, body);
        let with_maps = d.lam_fv(hmaps_fv, hmaps_ty, with_fix);
        let with_inj = d.lam_fv(hinj_fv, hinj_ty, with_maps);
        d.lam_fv(g_fv, fn_ty, with_inj)
    };

    let step = |d: &mut IntDev<'_>, cur: ExprId, ih: ExprId| -> ExprId {
        let nat = d.nat_ty();
        let s_cur = d.succ(cur);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let hinj_ty = inj_ty(d, g);
        let hinj_fv = d.fresh_fvar();
        let hinj = d.kernel().fvar(hinj_fv);
        let hmaps_ty = maps_ty(d, g);
        let hmaps_fv = d.fresh_fvar();
        let hmaps = d.kernel().fvar(hmaps_fv);
        let hfix_ty = fix_hyp_ty(d, g, s_cur, n);
        let hfix_fv = d.fresh_fvar();
        let hfix = d.kernel().fvar(hfix_fv);

        let goal = selection_concl(d, p, b_mat, g, n);
        let logic = d.prelude().logic;

        // --- `Le n cur`: both fixed-point ranges are empty ------------------
        let lt_cur_n = d.lt(cur, n);
        let le_n_cur = d.le(n, cur);
        let branch_ge = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let hfix_cur = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hle_ty = d.le(cur, i);
                let hle_fv = d.fresh_fvar();
                let hle = d.kernel().fvar(hle_fv);
                let hlt_ty = d.lt(i, n);
                let hlt_fv = d.fresh_fvar();
                let hlt = d.kernel().fvar(hlt_fv);
                let np = d.prelude();
                let lt_i_cur = d.lemma(np.lt_of_lt_of_le, &[i, n, cur, hlt, h]);
                let lt_i_i = d.lemma(np.lt_of_lt_of_le, &[i, cur, i, lt_i_cur, hle]);
                let irr = d.lemma(np.lt_irrefl, &[i]);
                let contradiction = d.apply(irr, &[lt_i_i]);
                let gi = d.apply(g, &[i]);
                let target = d.eq(gi, i);
                let body = ex_falso(d, target, contradiction);
                let with_lt = d.lam_fv(hlt_fv, hlt_ty, body);
                let with_le = d.lam_fv(hle_fv, hle_ty, with_lt);
                d.lam_fv(i_fv, nat, with_le)
            };
            let body = d.apply(ih, &[g, hinj, hmaps, hfix_cur]);
            d.lam_fv(h_fv, le_n_cur, body)
        };

        // --- `Lt cur n`: pigeonhole, then the three-way split ---------------
        let branch_lt = {
            let hcn_fv = d.fresh_fvar();
            let hcn = d.kernel().fvar(hcn_fv);
            let np = d.prelude();
            let surj = d.lemma(np.injective_on_imp_surjective_on, &[n, g, hinj, hmaps]);
            let witness = d.apply(surj, &[cur, hcn]);

            let predicate = {
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let bound = d.lt(i, n);
                let gi = d.apply(g, &[i]);
                let eqk = d.eq(gi, cur);
                let body = d.const_app(logic.and, &[bound, eqk]);
                d.lam_fv(i_fv, nat, body)
            };

            let minor = {
                let w_fv = d.fresh_fvar();
                let w = d.kernel().fvar(w_fv);
                let lt_w_n = d.lt(w, n);
                let gw = d.apply(g, &[w]);
                let eq_gw = d.eq(gw, cur);
                let hw_ty = d.const_app(logic.and, &[lt_w_n, eq_gw]);
                let hw_fv = d.fresh_fvar();
                let hw = d.kernel().fvar(hw_fv);
                let hwn = d.const_app(logic.and_left, &[lt_w_n, eq_gw, hw]);
                let hgw = d.const_app(logic.and_right, &[lt_w_n, eq_gw, hw]);

                let lt_w_cur = d.lt(w, cur);
                let le_cur_w = d.le(cur, w);
                let lt_cur_w = d.lt(cur, w);
                let eq_cur_w = d.eq(cur, w);

                // `Le cur w` -- `g` already fixes `cur`, or the witness is
                // above the cursor and `g`'s own hypothesis contradicts it.
                let side_ge = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let np = d.prelude();
                    let sub = d.lemma(np.lt_or_eq_of_le, &[cur, w, h]);

                    let case_lt = {
                        let h2_fv = d.fresh_fvar();
                        let h2 = d.kernel().fvar(h2_fv);
                        let fixed = d.apply(hfix, &[w, h2, hwn]);
                        let back = d.symm(gw, w, fixed);
                        let w_eq_cur = d.trans(w, gw, cur, back, hgw);
                        let motive = d.eq_motive(w, &|d, t| d.lt(cur, t));
                        let lt_cc = d.transport(w, motive, h2, cur, w_eq_cur);
                        let np = d.prelude();
                        let irr = d.lemma(np.lt_irrefl, &[cur]);
                        let contradiction = d.apply(irr, &[lt_cc]);
                        let body = ex_falso(d, goal, contradiction);
                        d.lam_fv(h2_fv, lt_cur_w, body)
                    };

                    let case_eq = {
                        let h2_fv = d.fresh_fvar();
                        let h2 = d.kernel().fvar(h2_fv);
                        let w_eq_cur = d.symm(cur, w, h2);
                        let motive = d.eq_motive(w, &|d, t| {
                            let gt = d.apply(g, &[t]);
                            d.eq(gt, cur)
                        });
                        let g_cur_fixed = d.transport(w, motive, hgw, cur, w_eq_cur);
                        let hfix_cur = {
                            let i_fv = d.fresh_fvar();
                            let i = d.kernel().fvar(i_fv);
                            let hle_ty = d.le(cur, i);
                            let hle_fv = d.fresh_fvar();
                            let hle = d.kernel().fvar(hle_fv);
                            let hlt_ty = d.lt(i, n);
                            let hlt_fv = d.fresh_fvar();
                            let hlt = d.kernel().fvar(hlt_fv);
                            let gi = d.apply(g, &[i]);
                            let target = d.eq(gi, i);
                            let np = d.prelude();
                            let sub2 = d.lemma(np.lt_or_eq_of_le, &[cur, i, hle]);
                            let lt_cur_i = d.lt(cur, i);
                            let eq_cur_i = d.eq(cur, i);
                            let inner_lt = {
                                let h3_fv = d.fresh_fvar();
                                let h3 = d.kernel().fvar(h3_fv);
                                let body = d.apply(hfix, &[i, h3, hlt]);
                                d.lam_fv(h3_fv, lt_cur_i, body)
                            };
                            let inner_eq = {
                                let h3_fv = d.fresh_fvar();
                                let h3 = d.kernel().fvar(h3_fv);
                                let motive = d.eq_motive(cur, &|d, t| {
                                    let gt = d.apply(g, &[t]);
                                    d.eq(gt, t)
                                });
                                let body = d.transport(cur, motive, g_cur_fixed, i, h3);
                                d.lam_fv(h3_fv, eq_cur_i, body)
                            };
                            let body = d.const_app(
                                logic.or_elim,
                                &[lt_cur_i, eq_cur_i, target, sub2, inner_lt, inner_eq],
                            );
                            let with_lt = d.lam_fv(hlt_fv, hlt_ty, body);
                            let with_le = d.lam_fv(hle_fv, hle_ty, with_lt);
                            d.lam_fv(i_fv, nat, with_le)
                        };
                        let body = d.apply(ih, &[g, hinj, hmaps, hfix_cur]);
                        d.lam_fv(h2_fv, eq_cur_w, body)
                    };

                    let body = d.const_app(
                        logic.or_elim,
                        &[lt_cur_w, eq_cur_w, goal, sub, case_lt, case_eq],
                    );
                    d.lam_fv(h_fv, le_cur_w, body)
                };

                // `Lt w cur` -- the real case: compose with the transposition
                // that brings `cur` into place.
                let side_swap = {
                    let hwc_fv = d.fresh_fvar();
                    let hwc = d.kernel().fvar(hwc_fv);
                    let np = d.prelude();

                    let swap_fn = {
                        let x_fv = d.fresh_fvar();
                        let x = d.kernel().fvar(x_fv);
                        let body = tswap(d, w, cur, x);
                        d.lam_fv(x_fv, nat, body)
                    };
                    let sigma = {
                        let x_fv = d.fresh_fvar();
                        let x = d.kernel().fvar(x_fv);
                        let sx = tswap(d, w, cur, x);
                        let body = d.apply(g, &[sx]);
                        d.lam_fv(x_fv, nat, body)
                    };

                    // `∀ i j, Lt i j → ∀ n, …` — the ordering hypothesis is
                    // bound BEFORE the dimension in both, not after it as the
                    // field docs read.
                    let hswap_maps = d.lemma(np.transposition_maps_into, &[w, cur, hwc, n, hcn]);
                    let hswap_inj = d.lemma(np.transposition_injective, &[w, cur, hwc, n]);
                    let hsig_inj = d.lemma(
                        np.injective_on_comp,
                        &[n, g, swap_fn, hswap_maps, hswap_inj, hinj],
                    );
                    let hsig_maps = {
                        let x_fv = d.fresh_fvar();
                        let x = d.kernel().fvar(x_fv);
                        let hx_ty = d.lt(x, n);
                        let hx_fv = d.fresh_fvar();
                        let hx = d.kernel().fvar(hx_fv);
                        let sx = tswap(d, w, cur, x);
                        let bound = d.apply(hswap_maps, &[x, hx]);
                        let body = d.apply(hmaps, &[sx, bound]);
                        let with_hx = d.lam_fv(hx_fv, hx_ty, body);
                        d.lam_fv(x_fv, nat, with_hx)
                    };
                    let hsig_fix = {
                        let i_fv = d.fresh_fvar();
                        let i = d.kernel().fvar(i_fv);
                        let hle_ty = d.le(cur, i);
                        let hle_fv = d.fresh_fvar();
                        let hle = d.kernel().fvar(hle_fv);
                        let hlt_ty = d.lt(i, n);
                        let hlt_fv = d.fresh_fvar();
                        let hlt = d.kernel().fvar(hlt_fv);
                        let si = d.apply(sigma, &[i]);
                        let target = d.eq(si, i);
                        let np = d.prelude();
                        let sub2 = d.lemma(np.lt_or_eq_of_le, &[cur, i, hle]);
                        let lt_cur_i = d.lt(cur, i);
                        let eq_cur_i = d.eq(cur, i);

                        let inner_lt = {
                            let h3_fv = d.fresh_fvar();
                            let h3 = d.kernel().fvar(h3_fv);
                            let np = d.prelude();
                            let fixed = d.lemma(np.transposition_gt_j, &[w, cur, i, hwc, h3]);
                            let t_i = tswap(d, w, cur, i);
                            let g_t = d.apply(g, &[t_i]);
                            let g_i = d.apply(g, &[i]);
                            let lifted = d.congr(t_i, i, fixed, &|d, t| d.apply(g, &[t]));
                            let tail = d.apply(hfix, &[i, h3, hlt]);
                            let body = d.trans(g_t, g_i, i, lifted, tail);
                            d.lam_fv(h3_fv, lt_cur_i, body)
                        };
                        let inner_eq = {
                            let h3_fv = d.fresh_fvar();
                            let h3 = d.kernel().fvar(h3_fv);
                            let np = d.prelude();
                            let at_j = d.lemma(np.transposition_at_j, &[w, cur, hwc]);
                            let t_cur = tswap(d, w, cur, cur);
                            let g_t = d.apply(g, &[t_cur]);
                            let lifted = d.congr(t_cur, w, at_j, &|d, t| d.apply(g, &[t]));
                            let at_cur = d.trans(g_t, gw, cur, lifted, hgw);
                            let motive = d.eq_motive(cur, &|d, t| {
                                let st = tswap(d, w, cur, t);
                                let gst = d.apply(g, &[st]);
                                d.eq(gst, t)
                            });
                            let body = d.transport(cur, motive, at_cur, i, h3);
                            d.lam_fv(h3_fv, eq_cur_i, body)
                        };
                        let body = d.const_app(
                            logic.or_elim,
                            &[lt_cur_i, eq_cur_i, target, sub2, inner_lt, inner_eq],
                        );
                        let with_lt = d.lam_fv(hlt_fv, hlt_ty, body);
                        let with_le = d.lam_fv(hle_fv, hle_ty, with_lt);
                        d.lam_fv(i_fv, nat, with_le)
                    };

                    let ih_at = d.apply(ih, &[sigma, hsig_inj, hsig_maps, hsig_fix]);

                    let mid_term = rmat_id(d, p);
                    let swap_b = swapped_det(d, p, b_mat, g, w, cur, m, hwc, hwn, hcn);
                    let swap_i = swapped_det(d, p, mid_term, g, w, cur, m, hwc, hwn, hcn);

                    let bc_g = row_compose(d, b_mat, g);
                    let mi_g = row_compose(d, mid_term, g);
                    let bc_s = row_compose(d, b_mat, sigma);
                    let mi_s = row_compose(d, mid_term, sigma);
                    let x_val = rdet(d, p, bc_g, n);
                    let y_val = rdet(d, p, mi_g, n);
                    let z_val = rdet(d, p, b_mat, n);
                    let d_bc_s = rdet(d, p, bc_s, n);
                    let d_mi_s = rdet(d, p, mi_s, n);

                    let neg_x = rneg(d, x_val);
                    let neg_y = rneg(d, y_val);
                    let yz = rmul(d, y_val, z_val);
                    let neg_yz = rneg(d, yz);

                    let back_b = rsymm(d, d_bc_s, neg_x, swap_b);
                    let prod_s = rmul(d, d_mi_s, z_val);
                    let prod_neg = rmul(d, neg_y, z_val);
                    let s3 = rcongr(d, d_mi_s, neg_y, swap_i, &|d, t| rmul(d, t, z_val));
                    let s4 = d.lemma(p.neg_mul, &[y_val, z_val]);
                    let (_e1, h_neg) = rchain(
                        d,
                        neg_x,
                        &[
                            (d_bc_s, back_b),
                            (prod_s, ih_at),
                            (prod_neg, s3),
                            (neg_yz, s4),
                        ],
                    );

                    let nn_x = rneg(d, neg_x);
                    let nn_yz = rneg(d, neg_yz);
                    let nn_x_eq = d.lemma(p.neg_neg, &[x_val]);
                    let up = rsymm(d, nn_x, x_val, nn_x_eq);
                    let mid_step = rcongr(d, neg_x, neg_yz, h_neg, &|d, t| rneg(d, t));
                    let down = d.lemma(p.neg_neg, &[yz]);
                    let (_e2, body) =
                        rchain(d, x_val, &[(nn_x, up), (nn_yz, mid_step), (yz, down)]);
                    d.lam_fv(hwc_fv, lt_w_cur, body)
                };

                let np = d.prelude();
                let tri = d.lemma(np.lt_or_ge, &[w, cur]);
                let body = d.const_app(
                    logic.or_elim,
                    &[lt_w_cur, le_cur_w, goal, tri, side_swap, side_ge],
                );
                let with_hw = d.lam_fv(hw_fv, hw_ty, body);
                d.lam_fv(w_fv, nat, with_hw)
            };

            let body = exists_elim(d, predicate, goal, witness, minor);
            d.lam_fv(hcn_fv, lt_cur_n, body)
        };

        let np = d.prelude();
        let split = d.lemma(np.lt_or_ge, &[cur, n]);
        let body = d.const_app(
            logic.or_elim,
            &[lt_cur_n, le_n_cur, goal, split, branch_lt, branch_ge],
        );

        let with_fix = d.lam_fv(hfix_fv, hfix_ty, body);
        let with_maps = d.lam_fv(hmaps_fv, hmaps_ty, with_fix);
        let with_inj = d.lam_fv(hinj_fv, hinj_ty, with_maps);
        d.lam_fv(g_fv, fn_ty, with_inj)
    };

    let proof = d.induct(&motive, &base, &step, n);

    // `P(n)`: the fixed-point hypothesis is vacuous, since `Le n i` and
    // `Lt i n` cannot both hold.
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);
    let hinj_ty = inj_ty(d, g);
    let hinj_fv = d.fresh_fvar();
    let hinj = d.kernel().fvar(hinj_fv);
    let hmaps_ty = maps_ty(d, g);
    let hmaps_fv = d.fresh_fvar();
    let hmaps = d.kernel().fvar(hmaps_fv);

    let vacuous = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let hle_ty = d.le(n, i);
        let hle_fv = d.fresh_fvar();
        let hle = d.kernel().fvar(hle_fv);
        let hlt_ty = d.lt(i, n);
        let hlt_fv = d.fresh_fvar();
        let hlt = d.kernel().fvar(hlt_fv);
        let np = d.prelude();
        let lt_i_i = d.lemma(np.lt_of_lt_of_le, &[i, n, i, hlt, hle]);
        let irr = d.lemma(np.lt_irrefl, &[i]);
        let contradiction = d.apply(irr, &[lt_i_i]);
        let gi = d.apply(g, &[i]);
        let target = d.eq(gi, i);
        let body = ex_falso(d, target, contradiction);
        let with_lt = d.lam_fv(hlt_fv, hlt_ty, body);
        let with_le = d.lam_fv(hle_fv, hle_ty, with_lt);
        d.lam_fv(i_fv, nat, with_le)
    };

    let applied = d.apply(proof, &[g, hinj, hmaps, vacuous]);
    let concl = selection_concl(d, p, b_mat, g, n);

    let ty = {
        let with_maps = d.arrow(hmaps_ty, concl);
        let with_inj = d.arrow(hinj_ty, with_maps);
        let over_g = d.pi_fv(g_fv, fn_ty, with_inj);
        let over_b = d.pi_fv(b_fv, mty, over_g);
        d.pi_fv(m_fv, nat, over_b)
    };
    let value = {
        let with_maps = d.lam_fv(hmaps_fv, hmaps_ty, applied);
        let with_inj = d.lam_fv(hinj_fv, hinj_ty, with_maps);
        let over_g = d.lam_fv(g_fv, fn_ty, with_inj);
        let over_b = d.lam_fv(b_fv, mty, over_g);
        d.lam_fv(m_fv, nat, over_b)
    };
    d.declare_theorem(p.det_row_selection_injective, ty, value)
}

// ---------------------------------------------------------------------------
// The SELECTION lemma, whole (ADR-1440 obligation 2, closed)
// ---------------------------------------------------------------------------

/// `Not (Eq Nat a b)` from `h : Lt a b`.
fn ne_of_lt(d: &mut IntDev<'_>, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
    let eq_ty = d.eq(a, b);
    let hh_fv = d.fresh_fvar();
    let hh = d.kernel().fvar(hh_fv);
    let motive = d.eq_motive(a, &|d, t| d.lt(t, b));
    let lt_b_b = d.transport(a, motive, h, b, hh);
    let np = d.prelude();
    let irr = d.lemma(np.lt_irrefl, &[b]);
    let contradiction = d.apply(irr, &[lt_b_b]);
    d.lam_fv(hh_fv, eq_ty, contradiction)
}

/// `Eq Bool (Nat.ble x m) Bool.true` from `h : Lt x (succ m)`.
fn ble_of_lt_succ(d: &mut IntDev<'_>, x: ExprId, m: ExprId, h: ExprId) -> ExprId {
    let np = d.prelude();
    let le = d.lemma(np.le_of_lt_succ, &[x, m]);
    let le = d.apply(le, &[h]);
    d.lemma(np.ble_eq_true_of_le, &[x, m, le])
}

/// `fun b => And (Lt a n) (And (Lt b n) (And (Lt a b) (Eq Nat (g a) (g b))))`
/// — `Nat.injective_on_or_duplicate`'s inner `Exists` predicate, rebuilt here
/// term for term (it is a private helper on the `Nat` side).
fn dup_inner_pred(d: &mut IntDev<'_>, g: ExprId, n: ExprId, a: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let logic = d.prelude().logic;
    let b_fv = d.fresh_fvar();
    let b = d.kernel().fvar(b_fv);
    let lt_a_n = d.lt(a, n);
    let lt_b_n = d.lt(b, n);
    let lt_a_b = d.lt(a, b);
    let ga = d.apply(g, &[a]);
    let gb = d.apply(g, &[b]);
    let eqn = d.eq(ga, gb);
    let level3 = d.const_app(logic.and, &[lt_a_b, eqn]);
    let level2 = d.const_app(logic.and, &[lt_b_n, level3]);
    let body = d.const_app(logic.and, &[lt_a_n, level2]);
    d.lam_fv(b_fv, nat, body)
}

/// `fun a => ∃ b, …` — the same predicate's outer layer.
fn dup_outer_pred(d: &mut IntDev<'_>, g: ExprId, n: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let logic = d.prelude().logic;
    let one = d.level_one();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let inner = dup_inner_pred(d, g, n, a);
    let ex = d.kernel().const_(logic.exists_, vec![one]);
    let body = d.apply(ex, &[nat, inner]);
    d.lam_fv(a_fv, nat, body)
}

/// Admit `Rat.det_row_selection : ∀ m B g, MapsInto g (succ m) →
/// det (B∘g) (succ m) = det (matId∘g) (succ m) * det B (succ m)` — **the
/// selection lemma, with no injectivity hypothesis**, which is ADR-1440's
/// obligation 2 in the corrected form ADR-1470 states.
///
/// One `Or.elim` over `Nat.injective_on_or_duplicate g (succ m)`: the
/// injective side is [`declare_det_row_selection_injective`], the duplicate
/// side is `Rat.det_row_selection_of_duplicate`, and the two boolean
/// hypotheses that side wants come out of the disjunction's own `Lt a b` and
/// `Lt _ (succ m)`.
///
/// `MapsInto` is load-bearing on the STATEMENT and cannot be dropped:
/// ADR-1470's counterexample is `n = 1`, `g 0 = 5`, `B 5 0 = 7`, where the
/// left side is `B 5 0 = 7` and the right side is `matId 5 0 * det B 1 = 0`.
fn declare_det_row_selection_full(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let fn_ty = d.arrow(nat, nat);
    let mty = mat_ty(d);
    let logic = d.prelude().logic;
    let one_lvl = d.level_one();

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n = d.succ(m);
    let b_fv = d.fresh_fvar();
    let b_mat = d.kernel().fvar(b_fv);
    let g_fv = d.fresh_fvar();
    let g = d.kernel().fvar(g_fv);

    let hmaps_ty = {
        let name = d.prelude().maps_into;
        d.const_app(name, &[g, n])
    };
    let hmaps_fv = d.fresh_fvar();
    let hmaps = d.kernel().fvar(hmaps_fv);

    let goal = selection_concl(d, p, b_mat, g, n);

    let np = d.prelude();
    let inj_ty = d.const_app(np.injective_on, &[g, n]);
    let outer_pred = dup_outer_pred(d, g, n);
    let dup_ty = {
        let ex = d.kernel().const_(logic.exists_, vec![one_lvl]);
        d.apply(ex, &[nat, outer_pred])
    };
    let split = d.lemma(np.injective_on_or_duplicate, &[g, n]);

    let on_inj = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.lemma(p.det_row_selection_injective, &[m, b_mat, g, h, hmaps]);
        d.lam_fv(h_fv, inj_ty, body)
    };

    let on_dup = {
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let outer_minor = {
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let inner_pred = dup_inner_pred(d, g, n, a);
            let inner_ex_ty = {
                let ex = d.kernel().const_(logic.exists_, vec![one_lvl]);
                d.apply(ex, &[nat, inner_pred])
            };
            let ha_fv = d.fresh_fvar();
            let ha = d.kernel().fvar(ha_fv);

            let inner_minor = {
                let bb_fv = d.fresh_fvar();
                let bb = d.kernel().fvar(bb_fv);
                let lt_a_n = d.lt(a, n);
                let lt_b_n = d.lt(bb, n);
                let lt_a_b = d.lt(a, bb);
                let ga = d.apply(g, &[a]);
                let gb = d.apply(g, &[bb]);
                let eqn = d.eq(ga, gb);
                let level3 = d.const_app(logic.and, &[lt_a_b, eqn]);
                let level2 = d.const_app(logic.and, &[lt_b_n, level3]);
                let hb_ty = d.const_app(logic.and, &[lt_a_n, level2]);
                let hb_fv = d.fresh_fvar();
                let hb = d.kernel().fvar(hb_fv);

                let h_lt_a_n = d.const_app(logic.and_left, &[lt_a_n, level2, hb]);
                let rest2 = d.const_app(logic.and_right, &[lt_a_n, level2, hb]);
                let h_lt_b_n = d.const_app(logic.and_left, &[lt_b_n, level3, rest2]);
                let rest3 = d.const_app(logic.and_right, &[lt_b_n, level3, rest2]);
                let h_lt_a_b = d.const_app(logic.and_left, &[lt_a_b, eqn, rest3]);
                let h_eq = d.const_app(logic.and_right, &[lt_a_b, eqn, rest3]);

                let not_eq = ne_of_lt(d, a, bb, h_lt_a_b);
                let np = d.prelude();
                let hne = d.lemma(np.beq_eq_false_of_ne, &[a, bb, not_eq]);
                let hba = ble_of_lt_succ(d, a, m, h_lt_a_n);
                let hbb = ble_of_lt_succ(d, bb, m, h_lt_b_n);
                let body = d.lemma(
                    p.det_row_selection_of_duplicate,
                    &[m, b_mat, g, a, bb, hne, hba, hbb, h_eq],
                );
                let with_hb = d.lam_fv(hb_fv, hb_ty, body);
                d.lam_fv(bb_fv, nat, with_hb)
            };
            let body = exists_elim(d, inner_pred, goal, ha, inner_minor);
            let with_ha = d.lam_fv(ha_fv, inner_ex_ty, body);
            d.lam_fv(a_fv, nat, with_ha)
        };
        let body = exists_elim(d, outer_pred, goal, h, outer_minor);
        d.lam_fv(h_fv, dup_ty, body)
    };

    let proof_body = d.const_app(
        logic.or_elim,
        &[inj_ty, dup_ty, goal, split, on_inj, on_dup],
    );

    let ty = {
        let with_maps = d.arrow(hmaps_ty, goal);
        let over_g = d.pi_fv(g_fv, fn_ty, with_maps);
        let over_b = d.pi_fv(b_fv, mty, over_g);
        d.pi_fv(m_fv, nat, over_b)
    };
    let value = {
        let with_maps = d.lam_fv(hmaps_fv, hmaps_ty, proof_body);
        let over_g = d.lam_fv(g_fv, fn_ty, with_maps);
        let over_b = d.lam_fv(b_fv, mty, over_g);
        d.lam_fv(m_fv, nat, over_b)
    };
    d.declare_theorem(p.det_row_selection, ty, value)
}

// ---------------------------------------------------------------------------
// The ENTRY-bounded congruence -- the one obligation 1's final step needs
// ---------------------------------------------------------------------------

/// `∀ r, Lt r bound → ∀ c, Lt c bound → Eq Rat (A r c) (B r c)` — two matrices
/// agreeing on exactly the square the determinant reads.
fn entry_bounded_eq_ty(d: &mut IntDev<'_>, a: ExprId, b: ExprId, bound: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let hr = d.lt(r, bound);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let hc = d.lt(c, bound);
    let ar = d.apply(a, &[r, c]);
    let br = d.apply(b, &[r, c]);
    let eq = req(d, ar, br);
    let with_hc = d.arrow(hc, eq);
    let inner = d.pi_fv(c_fv, nat, with_hc);
    let with_hr = d.arrow(hr, inner);
    d.pi_fv(r_fv, nat, with_hr)
}

/// Admit `Rat.matSkip_lt_succ : ∀ p c m, Lt c m → Lt (matSkip p c) (succ m)` —
/// the column bound the entry-bounded congruence needs, and the only reason
/// `Rat.det_congr_lt` stops at the row.
///
/// `matSkip p c` is `bool_select_nat (ble p c) (succ c) c`, and BOTH branches
/// are below `succ m`: `succ c` by `Nat.succ_le_succ` on the hypothesis, `c`
/// by `Nat.le_succ`. A bound that holds either way holds for the selector, so
/// this is one `Bool.rec` on the guard and never a decision about it.
fn declare_mat_skip_lt_succ(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let at_fv = d.fresh_fvar();
    let at = d.kernel().fvar(at_fv);
    let c_fv = d.fresh_fvar();
    let c = d.kernel().fvar(c_fv);
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let sm = d.succ(m);
    let hyp_ty = d.lt(c, m);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let skipped = rmat_skip(d, p, at, c);
    let concl = d.lt(skipped, sm);

    let cond = NatOps::ble(d, at, c);
    let sc = d.succ(c);
    let proof = bool_cases(
        d,
        cond,
        &|d, b| {
            let sc = d.succ(c);
            let selected = NatOps::bool_select_nat(d, b, sc, c);
            let sm = d.succ(m);
            d.lt(selected, sm)
        },
        &|d| {
            let np = d.prelude();
            d.lemma(np.succ_le_succ, &[sc, m, h])
        },
        &|d| {
            let np = d.prelude();
            let le = d.lemma(np.le_succ, &[m]);
            d.lemma(np.lt_of_lt_of_le, &[c, m, sm, h, le])
        },
    );

    let ty = {
        let with_h = d.arrow(hyp_ty, concl);
        let over_m = d.pi_fv(m_fv, nat, with_h);
        let over_c = d.pi_fv(c_fv, nat, over_m);
        d.pi_fv(at_fv, nat, over_c)
    };
    let value = {
        let with_h = d.lam_fv(h_fv, hyp_ty, proof);
        let over_m = d.lam_fv(m_fv, nat, with_h);
        let over_c = d.lam_fv(c_fv, nat, over_m);
        d.lam_fv(at_fv, nat, over_c)
    };
    d.declare_theorem(p.mat_skip_lt_succ, ty, value)
}

/// Admit `Rat.det_congr_entry_lt : ∀ n A B,
/// (∀ r, Lt r n → ∀ c, Lt c n → A r c = B r c) → det A n = det B n` — the
/// congruence bounded on BOTH indices, i.e. on exactly the square `det A n`
/// reads.
///
/// [`declare_det_congr_lt`] is the right tool when a reindexing map is under
/// no control outside `[0,n)`; this is the right tool when the two matrices
/// agree only where the determinant looks, which is what the identity laws
/// give: `Rat.matMul_id_right` is `Lt j n → matMul A matId n i j = A i j`,
/// bounded in the COLUMN, so the row-bounded form cannot consume it.
///
/// Same induction, with two changes: the outer sum needs
/// [`RatPrelude::sum_range_congr_lt`] rather than the unrestricted
/// `sum_range_congr`, and the minor's column obligation is discharged by
/// [`declare_mat_skip_lt_succ`].
fn declare_det_congr_entry_lt(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();

    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);

    let motive = |d: &mut IntDev<'_>, x: ExprId| -> ExprId {
        let mty = mat_ty(d);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let hyp = entry_bounded_eq_ty(d, a, b, x);
        let lhs = rdet(d, p, a, x);
        let rhs = rdet(d, p, b, x);
        let eq = req(d, lhs, rhs);
        let with_h = d.arrow(hyp, eq);
        let over_b = d.pi_fv(b_fv, mty, with_h);
        d.pi_fv(a_fv, mty, over_b)
    };
    let stmt = motive(d, n);

    let proof = d.induct(
        &motive,
        &|d| {
            let mty = mat_ty(d);
            let a_fv = d.fresh_fvar();
            let a = d.kernel().fvar(a_fv);
            let b_fv = d.fresh_fvar();
            let b = d.kernel().fvar(b_fv);
            let zero_n = d.zero();
            let hyp = entry_bounded_eq_ty(d, a, b, zero_n);
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
            let sj = d.succ(j);
            let hyp = entry_bounded_eq_ty(d, a, b, sj);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);

            let zero_n = d.zero();
            let f_a = cofactor_summand(d, p, a, j);
            let f_b = cofactor_summand(d, p, b, j);

            let pointwise = {
                let c_fv = d.fresh_fvar();
                let c = d.kernel().fvar(c_fv);
                let hc_ty = d.lt(c, sj);
                let hc_fv = d.fresh_fvar();
                let hc = d.kernel().fvar(hc_fv);

                let entry_a = d.apply(a, &[zero_n, c]);
                let entry_b = d.apply(b, &[zero_n, c]);
                let sub_a = rmat_minor_of(d, p, a, zero_n, c);
                let sub_b = rmat_minor_of(d, p, b, zero_n, c);
                let det_a = rdet(d, p, sub_a, j);
                let det_b = rdet(d, p, sub_b, j);
                let sign = ralt_sign(d, p, c);

                let minor_pointwise = {
                    let np = d.prelude();
                    let r_fv = d.fresh_fvar();
                    let r = d.kernel().fvar(r_fv);
                    let hr_ty = d.lt(r, j);
                    let hr_fv = d.fresh_fvar();
                    let hr = d.kernel().fvar(hr_fv);
                    let cc_fv = d.fresh_fvar();
                    let cc = d.kernel().fvar(cc_fv);
                    let hcc_ty = d.lt(cc, j);
                    let hcc_fv = d.fresh_fvar();
                    let hcc = d.kernel().fvar(hcc_fv);
                    let sr = d.succ(r);
                    let lifted = d.lemma(np.succ_le_succ, &[sr, j, hr]);
                    let col = rmat_skip(d, p, c, cc);
                    let col_bound = d.lemma(p.mat_skip_lt_succ, &[c, cc, j, hcc]);
                    let body = d.apply(h, &[sr, lifted, col, col_bound]);
                    let with_hcc = d.lam_fv(hcc_fv, hcc_ty, body);
                    let inner = d.lam_fv(cc_fv, nat, with_hcc);
                    let with_hr = d.lam_fv(hr_fv, hr_ty, inner);
                    d.lam_fv(r_fv, nat, with_hr)
                };
                let h_det = d.apply(ih, &[sub_a, sub_b, minor_pointwise]);

                let np = d.prelude();
                let lt_zero = d.lemma(np.zero_lt_succ, &[j]);
                let h_entry = d.apply(h, &[zero_n, lt_zero, c, hc]);

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
                let with_hc = d.lam_fv(hc_fv, hc_ty, body);
                d.lam_fv(c_fv, nat, with_hc)
            };

            let sum_pf = d.lemma(p.sum_range_congr_lt, &[f_a, f_b, sj, pointwise]);

            let with_h = d.lam_fv(h_fv, hyp, sum_pf);
            let over_b = d.lam_fv(b_fv, mty, with_h);
            d.lam_fv(a_fv, mty, over_b)
        },
        n,
    );

    let ty = d.pi_fv(n_fv, nat, stmt);
    let value = d.lam_fv(n_fv, nat, proof);
    d.declare_theorem(p.det_congr_entry_lt, ty, value)
}
