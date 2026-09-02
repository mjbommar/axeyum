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
use super::matrix_det::{mat_ty, ralt_sign, rdet, rmat_minor_of, rmat_skip};
use super::ops::{rchain, rcongr, req, rmul, rone, rrefl};
use crate::KernelError;
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;

/// Declare everything this file proves.
///
/// # Errors
///
/// Returns the trusted gate's rejection — an `Err` means the kernel
/// **refused** a proof, not that a script gave up.
pub(super) fn declare_matrix_det_mul(d: &mut IntDev<'_>, p: RatPrelude) -> Result<(), KernelError> {
    declare_det_congr_lt(d, p)?;
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
