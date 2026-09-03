//! Evidence for [`super::echelon_invariant`] — ADR-1554's **obligation 4**.
//!
//! Six things are checked, and they catch disjoint defects.
//!
//! 1. **The swap computes what the row-swap theorem talks about**, by reduction
//!    at a 3×2 instance, with a control at every entry.
//! 2. **That theorem applies at CONCRETE dimensions** — every index a numeral,
//!    both order hypotheses discharged by `Nat.le_of_ble_eq_true` at `Eq.refl`.
//! 3. **It applies at fully free arguments**, with a control refusing the
//!    statement a proof that forgot to apply the swap would have.
//! 4. **Both its hypotheses on `piv` are load-bearing.** Each is dropped in
//!    turn and the conclusion is FALSE by reduction at a matrix satisfying
//!    everything else — a hypothesis every matrix satisfies is decoration, and
//!    ADR-1562 §2's rule is to rule that out first.
//! 5. **The leading-index congruence reads only its own row**, checked at two
//!    matrices that agree on one row and disagree on the other, and the pivot
//!    step is checked at a matrix where it really swaps AND really sweeps, so
//!    the "leaves the prefix alone" lemma is not true by the step being the
//!    identity.
//! 6. **`Rat.rowEchelon_isEchelon` is not vacuous.** `Rat.isEchelon` is
//!    reduced to `true` on the reduced matrix AND to `false` on the input, at
//!    two matrices — a `rowEchelon` that returned its argument, or an
//!    `isEchelon` that accepted everything, fails that pair.
//!
//! Every magnitude formed is a single-digit integer, so nothing here touches
//! the unary-numeral cost `CLAUDE.md` documents.

use super::RatPrelude;
use super::echelon::{ris_echelon, rrow_echelon, rrow_swap};
use super::echelon_invariant::column_zero_from;
use super::matrix_det::{mat_ty, rq};
use super::nullity_tests::rect_matrix;
use super::ops::{req, rzero};
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{BinderInfo, ExprId, Kernel, LocalContext, LocalDecl, build_rat_prelude};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("the rational prelude must build");
    (kernel, prelude)
}

/// `Nat.le_of_ble_eq_true n m (Eq.refl Bool true)` — a concrete `Le n m` for
/// numerals, which is the only shape this file needs.
fn le_num(d: &mut IntDev<'_>, n: u32, m: u32) -> ExprId {
    let ni = d.num(n);
    let mi = d.num(m);
    let true_ = d.bool_true();
    let refl = d.bool_refl(true_);
    let name = d.prelude().le_of_ble_eq_true;
    d.lemma(name, &[ni, mi, refl])
}

/// `[[1,2],[0,3],[0,4]]` swapped at rows `1` and `2`: the zero column-`0`
/// entries change places and stay zero, and row `0` is untouched.
#[test]
fn row_swap_moves_the_two_rows_and_leaves_the_rest_alone() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 3, 2, &[1, 2, 0, 3, 0, 4]);
    let one_n = d.num(1);
    let two_n = d.num(2);
    let swapped = rrow_swap(&mut d, p, one_n, two_n, m);

    for (r, c, want) in [
        (0u32, 0u32, 1i64),
        (0, 1, 2),
        (1, 0, 0),
        (1, 1, 4),
        (2, 0, 0),
        (2, 1, 3),
    ] {
        let ri = d.num(r);
        let ci = d.num(c);
        let lhs = d.apply(swapped, &[ri, ci]);
        let rhs = rq(&mut d, p, want);
        assert!(
            d.kernel().def_eq(lhs, rhs),
            "rowSwap 1 2 [[1,2],[0,3],[0,4]] entry ({r},{c}) must be {want}"
        );
        let other = rq(&mut d, p, want + 1);
        assert!(
            !d.kernel().def_eq(lhs, other),
            "rowSwap 1 2 entry ({r},{c}) must NOT also be {}",
            want + 1
        );
    }
}

/// The theorem at concrete `pr = 1`, `piv = 2`, `rows = 3`, `k = 0`, `s = 1`:
/// every index is a numeral and the two order hypotheses are discharged by
/// reduction, so only the zero-range hypothesis stays free.
///
/// The conclusion must be the equation about the entry the swap MOVED — at
/// `s = 1` the swapped matrix reads row `2` of the original — and the control
/// refuses the equation about the unswapped entry, which is what a theorem
/// stated over `M` rather than `rowSwap pr piv M` would give.
#[test]
fn row_swap_preserves_zero_range_applies_at_concrete_dimensions() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let anon = d.anon_name();
    let m = rect_matrix(&mut d, p, 3, 2, &[1, 2, 0, 3, 0, 4]);
    let zero_n = d.num(0);
    let one_n = d.num(1);
    let two_n = d.num(2);
    let three_n = d.num(3);

    // `Le 1 2` and `Lt 2 3`, both by `ble` reduction.
    let hpiv = le_num(&mut d, 1, 2);
    let hlt = le_num(&mut d, 3, 3);

    let hz_ty = column_zero_from(&mut d, p, m, one_n, three_n, zero_n);
    let hz_fv = d.fresh_fvar();
    let hz = d.kernel().fvar(hz_fv);

    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: hz_fv,
        name: anon,
        ty: hz_ty,
        info: BinderInfo::Default,
    });

    // `Le 1 1` and `Lt 1 3`.
    let h1 = le_num(&mut d, 1, 1);
    let h2 = le_num(&mut d, 2, 3);

    let applied = d.const_app(
        p.row_swap_preserves_zero_range,
        &[
            m, one_n, two_n, three_n, zero_n, hpiv, hlt, hz, one_n, h1, h2,
        ],
    );
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("Rat.rowSwap_preserves_zero_range must apply at concrete dimensions");

    let rat_zero = rzero(&mut d, p);
    let moved = d.apply(m, &[two_n, zero_n]);
    let want = req(&mut d, moved, rat_zero);
    assert!(
        d.kernel().def_eq(inferred, want),
        "at s = 1 the swapped matrix reads row 2 of the original"
    );

    let untouched = d.apply(m, &[one_n, zero_n]);
    let control = req(&mut d, untouched, rat_zero);
    // Row 1 and row 2 both hold `0` in column `0`, so the two equations are
    // def_eq for the WRONG reason here; the discriminating control is a row
    // the swap did not move.
    let elsewhere = d.apply(m, &[zero_n, zero_n]);
    let sharp_control = req(&mut d, elsewhere, rat_zero);
    assert!(
        d.kernel().def_eq(control, want),
        "both moved rows are zero in column 0, so this pair is NOT a control"
    );
    assert!(
        !d.kernel().def_eq(inferred, sharp_control),
        "negative control: the conclusion is not about row 0, which is nonzero"
    );
}

/// The theorem applies at fully free arguments, and its conclusion is about the
/// SWAPPED matrix.
#[test]
fn row_swap_preserves_zero_range_applies_at_free_variables() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let anon = d.anon_name();
    let nat = d.nat_ty();
    let mty = mat_ty(&mut d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let pr_fv = d.fresh_fvar();
    let pr = d.kernel().fvar(pr_fv);
    let piv_fv = d.fresh_fvar();
    let piv = d.kernel().fvar(piv_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let s_fv = d.fresh_fvar();
    let s = d.kernel().fvar(s_fv);

    let hpiv_ty = NatOps::le(&mut d, pr, piv);
    let hlt_ty = NatOps::lt(&mut d, piv, rows);
    let hz_ty = column_zero_from(&mut d, p, m, pr, rows, k);
    let h1_ty = NatOps::le(&mut d, pr, s);
    let h2_ty = NatOps::lt(&mut d, s, rows);

    let hpiv_fv = d.fresh_fvar();
    let hpiv = d.kernel().fvar(hpiv_fv);
    let hlt_fv = d.fresh_fvar();
    let hlt = d.kernel().fvar(hlt_fv);
    let hz_fv = d.fresh_fvar();
    let hz = d.kernel().fvar(hz_fv);
    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);

    let mut ctx = LocalContext::new();
    for (fvar, ty) in [
        (m_fv, mty),
        (pr_fv, nat),
        (piv_fv, nat),
        (rows_fv, nat),
        (k_fv, nat),
        (s_fv, nat),
        (hpiv_fv, hpiv_ty),
        (hlt_fv, hlt_ty),
        (hz_fv, hz_ty),
        (h1_fv, h1_ty),
        (h2_fv, h2_ty),
    ] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }

    let applied = d.const_app(
        p.row_swap_preserves_zero_range,
        &[m, pr, piv, rows, k, hpiv, hlt, hz, s, h1, h2],
    );
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("Rat.rowSwap_preserves_zero_range must apply at free variables");

    let swapped = rrow_swap(&mut d, p, pr, piv, m);
    let entry = d.apply(swapped, &[s, k]);
    let rat_zero = rzero(&mut d, p);
    let want = req(&mut d, entry, rat_zero);
    assert!(
        d.kernel().def_eq(inferred, want),
        "the conclusion must be about the SWAPPED matrix at (s, k)"
    );

    let original = d.apply(m, &[s, k]);
    let control = req(&mut d, original, rat_zero);
    assert!(
        !d.kernel().def_eq(inferred, control),
        "negative control: this is not the hypothesis restated at the original matrix"
    );
}

/// Drop `Lt piv rows` and the statement is FALSE.
///
/// `[[0,9],[0,9],[5,9]]` with `rows = 2` has column `0` zero at every row in
/// `[0, 2)`, so the zero-range hypothesis holds. Swapping in row `2` — which
/// is out of range — puts `5` at `(0, 0)`.
#[test]
fn row_swap_preserves_zero_range_needs_the_pivot_inside_the_row_count() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 3, 2, &[0, 9, 0, 9, 5, 9]);
    let zero_n = d.num(0);
    let one_n = d.num(1);
    let two_n = d.num(2);

    // The hypothesis really does hold over `[0, rows)` with `rows = 2`.
    let rat_zero = rzero(&mut d, p);
    for r in [zero_n, one_n] {
        let entry = d.apply(m, &[r, zero_n]);
        assert!(
            d.kernel().def_eq(entry, rat_zero),
            "column 0 is zero at every row below 2"
        );
    }

    let swapped = rrow_swap(&mut d, p, zero_n, two_n, m);
    let broken = d.apply(swapped, &[zero_n, zero_n]);
    assert!(
        !d.kernel().def_eq(broken, rat_zero),
        "swapping an OUT-OF-RANGE pivot row in destroys the zero range"
    );
    let five = rq(&mut d, p, 5);
    assert!(
        d.kernel().def_eq(broken, five),
        "and the value it puts there is the out-of-range row's entry"
    );
}

/// Drop `Le pr piv` and the statement is FALSE.
///
/// `[[7,9],[0,9],[0,9]]` with `pr = 1`, `rows = 3` has column `0` zero at every
/// row in `[1, 3)`. Swapping in row `0` — ABOVE the cursor, so outside the
/// range the hypothesis covers — puts `7` at `(1, 0)`.
#[test]
fn row_swap_preserves_zero_range_needs_the_pivot_at_or_below_the_cursor() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 3, 2, &[7, 9, 0, 9, 0, 9]);
    let zero_n = d.num(0);
    let one_n = d.num(1);
    let two_n = d.num(2);

    let rat_zero = rzero(&mut d, p);
    for r in [one_n, two_n] {
        let entry = d.apply(m, &[r, zero_n]);
        assert!(
            d.kernel().def_eq(entry, rat_zero),
            "column 0 is zero at every row from 1 down"
        );
    }

    let swapped = rrow_swap(&mut d, p, one_n, zero_n, m);
    let broken = d.apply(swapped, &[one_n, zero_n]);
    assert!(
        !d.kernel().def_eq(broken, rat_zero),
        "swapping a row from ABOVE the cursor in destroys the zero range"
    );
    let seven = rq(&mut d, p, 7);
    assert!(
        d.kernel().def_eq(broken, seven),
        "and the value it puts there is the above-cursor row's entry"
    );
}

/// `Rat.leadingIndex_congr_row` at a CONCRETE pair of matrices that share one
/// row and differ everywhere else.
///
/// `M = [[0,0,5],[1,2,3]]` and `N = [[9,9,9],[0,0,5]]` agree on `M`'s row `0`
/// and `N`'s row `1`, so both read leading index `2`. The control is the OTHER
/// row of each: they read `0`, so the congruence is not saying every row of
/// these two matrices agrees.
#[test]
fn leading_index_congr_row_reads_only_the_row_it_is_given() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 2, 3, &[0, 0, 5, 1, 2, 3]);
    let n = rect_matrix(&mut d, p, 2, 3, &[9, 9, 9, 0, 0, 5]);
    let zero_n = d.num(0);
    let one_n = d.num(1);
    let two_n = d.num(2);
    let three_n = d.num(3);

    let li_m0 = d.const_app(p.leading_index, &[m, zero_n, three_n]);
    let li_n1 = d.const_app(p.leading_index, &[n, one_n, three_n]);
    assert!(
        d.kernel().def_eq(li_m0, two_n),
        "row 0 of [[0,0,5],[1,2,3]] leads at column 2"
    );
    assert!(
        d.kernel().def_eq(li_n1, two_n),
        "row 1 of [[9,9,9],[0,0,5]] leads at column 2"
    );

    let li_m1 = d.const_app(p.leading_index, &[m, one_n, three_n]);
    let li_n0 = d.const_app(p.leading_index, &[n, zero_n, three_n]);
    assert!(
        d.kernel().def_eq(li_m1, zero_n),
        "control: the OTHER row of M leads at column 0"
    );
    assert!(
        d.kernel().def_eq(li_n0, zero_n),
        "control: the OTHER row of N leads at column 0"
    );
    assert!(
        !d.kernel().def_eq(li_m1, two_n),
        "control: those two rows do NOT share the leading index the theorem is about"
    );
}

/// `Rat.leadingIndex_congr_row` applies at fully free arguments, and the
/// hypothesis it consumes is POINTWISE — no `funext`, no equation between the
/// two matrices.
#[test]
fn leading_index_congr_row_applies_at_free_variables_from_a_pointwise_hypothesis() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let anon = d.anon_name();
    let nat = d.nat_ty();
    let mty = mat_ty(&mut d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let r2_fv = d.fresh_fvar();
    let r2 = d.kernel().fvar(r2_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let hyp_ty = {
        let j_fv = d.fresh_fvar();
        let j = d.kernel().fvar(j_fv);
        let left = d.apply(m, &[r, j]);
        let right = d.apply(n, &[r2, j]);
        let body = req(&mut d, left, right);
        d.pi_fv(j_fv, nat, body)
    };
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let mut ctx = LocalContext::new();
    for (fvar, ty) in [
        (m_fv, mty),
        (n_fv, mty),
        (r_fv, nat),
        (r2_fv, nat),
        (cols_fv, nat),
        (hyp_fv, hyp_ty),
    ] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }

    let applied = d.const_app(p.leading_index_congr_row, &[m, n, r, r2, cols, hyp]);
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("Rat.leadingIndex_congr_row must apply at free variables");

    let left = d.const_app(p.leading_index, &[m, r, cols]);
    let right = d.const_app(p.leading_index, &[n, r2, cols]);
    let want = d.eq(left, right);
    assert!(
        d.kernel().def_eq(inferred, want),
        "the conclusion equates the two rows' leading indices"
    );

    // The control: it is NOT an equation between the two MATRICES, which is
    // what a `funext`-shaped statement would have produced.
    let same_row = d.const_app(p.leading_index, &[n, r, cols]);
    let control = d.eq(left, same_row);
    assert!(
        !d.kernel().def_eq(inferred, control),
        "negative control: the right-hand row index is r', not r"
    );
}

/// `Rat.clearBelow_rowSwap_off` at concrete arguments: a whole pivot step at
/// `pr = 1`, `piv = 2`, `pc = 0`, `rows = 3` leaves row `0` byte for byte.
///
/// The matrix is chosen so the step really does something: rows 1 and 2 are
/// swapped and then the row below the pivot is cleared, and row `0` is the only
/// one that survives untouched.
#[test]
fn clear_below_row_swap_off_leaves_the_processed_prefix_alone() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 3, 2, &[1, 2, 0, 3, 2, 4]);
    let zero_n = d.num(0);
    let one_n = d.num(1);
    let two_n = d.num(2);
    let three_n = d.num(3);

    let swapped = rrow_swap(&mut d, p, one_n, two_n, m);
    let stepped = d.const_app(p.clear_below, &[swapped, one_n, zero_n, three_n]);

    for (c, want) in [(zero_n, 1i64), (one_n, 2i64)] {
        let lhs = d.apply(stepped, &[zero_n, c]);
        let rhs = rq(&mut d, p, want);
        assert!(
            d.kernel().def_eq(lhs, rhs),
            "the pivot step must leave row 0 at {want}"
        );
    }

    // The step is not the identity: row 1 became the old row 2, and row 2's
    // column-0 entry was cleared.
    let moved = d.apply(stepped, &[one_n, zero_n]);
    let two_q = rq(&mut d, p, 2);
    assert!(
        d.kernel().def_eq(moved, two_q),
        "row 1 is now the old row 2, so the step really swapped"
    );
    let cleared = d.apply(stepped, &[two_n, zero_n]);
    let rat_zero = rzero(&mut d, p);
    assert!(
        d.kernel().def_eq(cleared, rat_zero),
        "row 2 was cleared, so the step really swept"
    );

    // ... and the theorem applies at those concrete arguments.
    let hlt = le_num(&mut d, 1, 1);
    let hle = le_num(&mut d, 1, 2);
    let applied = d.const_app(
        p.clear_below_row_swap_off,
        &[m, one_n, two_n, zero_n, three_n, zero_n, zero_n, hlt, hle],
    );
    let mut ctx = LocalContext::new();
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("Rat.clearBelow_rowSwap_off must apply at concrete arguments");
    let lhs = d.apply(stepped, &[zero_n, zero_n]);
    let rhs = d.apply(m, &[zero_n, zero_n]);
    let want = req(&mut d, lhs, rhs);
    assert!(
        d.kernel().def_eq(inferred, want),
        "the conclusion is the entry equation at (0, 0)"
    );
}

/// `Rat.rowEchelon_isEchelon` at CONCRETE matrices, with the control that
/// decides whether the theorem says anything: the ORIGINAL matrix is not in
/// echelon form.
///
/// `[[0,1],[2,3]]` forces the swap — its first column is zero at row 0 — and
/// `[[0,0,2],[0,3,4],[5,6,7]]` reverses the row order entirely, so a
/// `rowEchelon` that returned its argument would fail both.
#[test]
fn row_echelon_is_echelon_computes_and_the_input_is_not_already_echelon() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let true_v = d.bool_true();
    let false_v = d.bool_false();

    for (rows, cols, entries, label) in [
        (2usize, 2usize, vec![0i64, 1, 2, 3], "[[0,1],[2,3]]"),
        (
            3,
            3,
            vec![0, 0, 2, 0, 3, 4, 5, 6, 7],
            "[[0,0,2],[0,3,4],[5,6,7]]",
        ),
    ] {
        let m = rect_matrix(&mut d, p, rows, cols, &entries);
        let rows_n = d.num(u32::try_from(rows).expect("small"));
        let cols_n = d.num(u32::try_from(cols).expect("small"));

        let reduced = rrow_echelon(&mut d, p, m, rows_n, cols_n);
        let ok = ris_echelon(&mut d, p, reduced, rows_n, cols_n);
        assert!(
            d.kernel().def_eq(ok, true_v),
            "{label}: rowEchelon must land in echelon form"
        );

        // The control. Without it the theorem could be true because
        // `isEchelon` accepts everything.
        let raw = ris_echelon(&mut d, p, m, rows_n, cols_n);
        assert!(
            d.kernel().def_eq(raw, false_v),
            "{label}: the INPUT must not already be in echelon form"
        );
    }
}

/// `Rat.rowEchelon_isEchelon` applies at fully free arguments and carries no
/// hypothesis at all.
#[test]
fn row_echelon_is_echelon_applies_at_free_variables_with_no_hypothesis() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let anon = d.anon_name();
    let nat = d.nat_ty();
    let mty = mat_ty(&mut d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let mut ctx = LocalContext::new();
    for (fvar, ty) in [(m_fv, mty), (rows_fv, nat), (cols_fv, nat)] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }

    let applied = d.const_app(p.row_echelon_is_echelon, &[m, rows, cols]);
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("Rat.rowEchelon_isEchelon must apply at free variables with no hypothesis");

    let reduced = rrow_echelon(&mut d, p, m, rows, cols);
    let ok = ris_echelon(&mut d, p, reduced, rows, cols);
    let true_v = d.bool_true();
    let want = d.bool_eq(ok, true_v);
    assert!(
        d.kernel().def_eq(inferred, want),
        "the conclusion is about the REDUCED matrix"
    );

    // The control: it is not the (false) claim about the input matrix.
    let raw = ris_echelon(&mut d, p, m, rows, cols);
    let control = d.bool_eq(raw, true_v);
    assert!(
        !d.kernel().def_eq(inferred, control),
        "negative control: this is not a claim about the input matrix"
    );
}
