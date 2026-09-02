//! Evaluation tests for [`super::nullity`], plus the bridge `rank = rankCols`
//! checked where it IS decidable.
//!
//! **The trusted gate cannot tell you a `Definition` is wrong.** `Rat.nullity`
//! has type `Mat → Nat → Nat → Nat` whether it counts free columns, counts
//! every column, or returns `0`. So every test below REDUCES `rankCols` and
//! `nullity` at a concrete matrix whose pivot columns were worked out by hand,
//! and carries a control that must FAIL to be defeq.
//!
//! ## What discriminates
//!
//! The six matrices are chosen so that no single wrong definition passes them
//! all:
//!
//! - `[[1,2],[3,4]]` → `(2, 0)` and the zero 2×2 → `(0, 2)` together kill
//!   "return `cols`" and "return `0`" on either component.
//! - `[[1,2],[2,4]]` → `(1, 1)` is the one that needs the zero ROW to
//!   contribute no pivot column: its echelon form is `[[1,2],[0,0]]`, whose
//!   second row has `leadingIndex = cols = 2`, which is not a column index at
//!   all.
//! - `[[1,2,3],[2,4,6],[1,1,1]]` → `(2, 1)` at 3×3 needs the elimination: the
//!   INPUT has three nonzero rows and its pivot columns would be `{0}` alone
//!   without it.
//! - the 3×3 identity → `(3, 0)` separates "count pivot columns" from "count
//!   columns after the first".
//! - the RECTANGULAR `[[1,0,2],[0,1,3]]` at 2×3 → `(2, 1)` is the only row
//!   where `rows ≠ cols`, so it is the only one that could catch a definition
//!   that counted over the wrong dimension. Every square case is blind to that
//!   confusion by construction.
//!
//! ## The bridge
//!
//! `rank M rows cols = rankCols M rows cols` is NOT a theorem in this tree —
//! it needs `rowEchelon_isEchelon` (ADR-1554 obligation 4), and ADR-1558
//! records the exact term that gets stuck. It is still a decidable statement at
//! a concrete matrix, so [`rank_equals_rank_cols_at_every_concrete_matrix`]
//! checks it by reduction at all six. That is the decidable-fragment row of the
//! graded family (ADR-0603), not a substitute for the general statement.

use super::RatPrelude;
use super::matrix_det::rq;
use super::nullity::{ris_pivot_col_b, rnullity, rrank_cols};
use super::probability::bool_select_rat;
use super::rank::rrank;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{ExprId, Kernel, build_rat_prelude};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("the rational prelude must build");
    (kernel, prelude)
}

/// A `rows × cols` constant matrix from row-major integer entries.
///
/// `super::matrix_det::const_matrix` asserts a SQUARE shape, and the only test
/// here that can catch a rows/cols confusion is the rectangular one — so this
/// generalises it rather than working around the assertion. Entries outside the
/// stated shape fall through to the last row / last column, which no test
/// reads.
fn rect_matrix(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    rows: usize,
    cols: usize,
    entries: &[i64],
) -> ExprId {
    assert_eq!(
        entries.len(),
        rows * cols,
        "row-major entries must fill the rectangle"
    );
    let nat = d.nat_ty();

    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let mut row_terms: Vec<ExprId> = Vec::with_capacity(rows);
    for r in 0..rows {
        let mut term = rq(d, p, entries[r * cols + (cols - 1)]);
        for c in (0..cols - 1).rev() {
            let entry = rq(d, p, entries[r * cols + c]);
            let idx = d.num(u32::try_from(c).expect("small"));
            let cond = NatOps::beq(d, j, idx);
            term = bool_select_rat(d, cond, entry, term);
        }
        row_terms.push(term);
    }
    let mut body = row_terms[rows - 1];
    for r in (0..rows - 1).rev() {
        let idx = d.num(u32::try_from(r).expect("small"));
        let cond = NatOps::beq(d, i, idx);
        body = bool_select_rat(d, cond, row_terms[r], body);
    }

    let with_j = d.lam_fv(j_fv, nat, body);
    d.lam_fv(i_fv, nat, with_j)
}

/// Assert `rankCols M rows cols` and `nullity M rows cols` reduce to
/// `want_rank` / `want_nullity`, and NOT to their neighbours.
///
/// The controls are what make this an evaluation test rather than a type
/// check: a `rankCols` that returned a constant satisfies one row of the table
/// and fails its neighbour, and an off-by-one is caught here rather than by a
/// later theorem that never runs the definition.
fn assert_rank_cols_and_nullity(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    rows: u32,
    cols: u32,
    want_rank: u32,
    want_nullity: u32,
    what: &str,
) {
    let rows_n = d.num(rows);
    let cols_n = d.num(cols);

    let rc = rrank_cols(d, p, m, rows_n, cols_n);
    let expected = d.num(want_rank);
    assert!(
        d.kernel().def_eq(rc, expected),
        "{what}: rankCols must be {want_rank}"
    );
    let above = d.num(want_rank + 1);
    assert!(
        !d.kernel().def_eq(rc, above),
        "{what}: rankCols must NOT also be {} -- it is not discriminating here",
        want_rank + 1
    );
    if want_rank > 0 {
        let below = d.num(want_rank - 1);
        assert!(
            !d.kernel().def_eq(rc, below),
            "{what}: rankCols must NOT also be {}",
            want_rank - 1
        );
    }

    let nl = rnullity(d, p, m, rows_n, cols_n);
    let expected_n = d.num(want_nullity);
    assert!(
        d.kernel().def_eq(nl, expected_n),
        "{what}: nullity must be {want_nullity}"
    );
    let above_n = d.num(want_nullity + 1);
    assert!(
        !d.kernel().def_eq(nl, above_n),
        "{what}: nullity must NOT also be {}",
        want_nullity + 1
    );
    if want_nullity > 0 {
        let below_n = d.num(want_nullity - 1);
        assert!(
            !d.kernel().def_eq(nl, below_n),
            "{what}: nullity must NOT also be {}",
            want_nullity - 1
        );
    }
}

/// The six matrices, as `(rows, cols, entries, rankCols, nullity)`.
///
/// One table, read by every test below, so the evaluation table, the
/// rank-nullity instantiation and the bridge check cannot drift apart.
const CASES: &[(usize, usize, &[i64], u32, u32, &str)] = &[
    (2, 2, &[1, 2, 3, 4], 2, 0, "[[1,2],[3,4]]"),
    (2, 2, &[1, 2, 2, 4], 1, 1, "[[1,2],[2,4]]"),
    (2, 2, &[0, 0, 0, 0], 0, 2, "the zero 2x2"),
    (
        3,
        3,
        &[1, 2, 3, 2, 4, 6, 1, 1, 1],
        2,
        1,
        "[[1,2,3],[2,4,6],[1,1,1]]",
    ),
    (3, 3, &[1, 0, 0, 0, 1, 0, 0, 0, 1], 3, 0, "the 3x3 identity"),
    (2, 3, &[1, 0, 2, 0, 1, 3], 2, 1, "the 2x3 [[1,0,2],[0,1,3]]"),
];

/// `Rat.rankCols` counts pivot columns and `Rat.nullity` counts the rest, at
/// six matrices whose answers are pairwise discriminating.
#[test]
fn rank_cols_and_nullity_count_the_pivot_columns_and_their_complement() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    for &(rows, cols, entries, want_rank, want_nullity, what) in CASES {
        let m = rect_matrix(&mut d, p, rows, cols, entries);
        assert_rank_cols_and_nullity(
            &mut d,
            p,
            m,
            u32::try_from(rows).expect("small"),
            u32::try_from(cols).expect("small"),
            want_rank,
            want_nullity,
            what,
        );
    }
}

/// `Rat.rank_nullity` is symbolic, so instantiate it: at every one of the six
/// matrices the two counts really do add to `cols`.
///
/// This is the retrospective check on the theorem — the statement is proved
/// for all `M`, `rows`, `cols`, and here the two sides are actually REDUCED so
/// that a definition pair which satisfied the theorem vacuously (both `0` and
/// `cols` is not one of them, but `rankCols := 0`, `nullity := cols` is) would
/// still be caught by the table above.
#[test]
fn rank_nullity_holds_by_reduction_at_every_concrete_matrix() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    for &(rows, cols, entries, _want_rank, _want_nullity, what) in CASES {
        let m = rect_matrix(&mut d, p, rows, cols, entries);
        let rows_n = d.num(u32::try_from(rows).expect("small"));
        let cols_n = d.num(u32::try_from(cols).expect("small"));

        let rc = rrank_cols(&mut d, p, m, rows_n, cols_n);
        let nl = rnullity(&mut d, p, m, rows_n, cols_n);
        let sum = d.add(rc, nl);
        assert!(
            d.kernel().def_eq(sum, cols_n),
            "{what}: rankCols + nullity must reduce to cols"
        );
        let wrong = d.num(u32::try_from(cols).expect("small") + 1);
        assert!(
            !d.kernel().def_eq(sum, wrong),
            "{what}: the sum must NOT also reduce to cols + 1"
        );
    }
}

/// The BRIDGE, checked where it is decidable: `rank M rows cols` and
/// `rankCols M rows cols` reduce to the same number at all six matrices.
///
/// The general statement is open — it needs `rowEchelon_isEchelon`, and
/// ADR-1558 records the stuck term. This is the decidable-fragment row of the
/// graded family, and it is a real check: nothing in either definition refers
/// to the other, so agreement at six matrices including a rectangular one is
/// evidence rather than restatement.
#[test]
fn rank_equals_rank_cols_at_every_concrete_matrix() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    for &(rows, cols, entries, want_rank, _want_nullity, what) in CASES {
        let m = rect_matrix(&mut d, p, rows, cols, entries);
        let rows_n = d.num(u32::try_from(rows).expect("small"));
        let cols_n = d.num(u32::try_from(cols).expect("small"));

        let row_form = rrank(&mut d, p, m, rows_n, cols_n);
        let col_form = rrank_cols(&mut d, p, m, rows_n, cols_n);
        let expected = d.num(want_rank);
        assert!(
            d.kernel().def_eq(row_form, expected),
            "{what}: rank (row form) must be {want_rank}"
        );
        assert!(
            d.kernel().def_eq(col_form, expected),
            "{what}: rankCols (column form) must be {want_rank}"
        );
    }
}

/// `Rat.isPivotColB` separates a pivot column from a free one on the SAME
/// matrix.
///
/// `[[1,2],[2,4]]` has echelon form `[[1,2],[0,0]]`: column `0` is a pivot
/// column, column `1` is not. A predicate that was constantly `true` or
/// constantly `false` passes exactly one of these two assertions.
#[test]
fn is_pivot_col_b_separates_a_pivot_column_from_a_free_one() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 2, 2, &[1, 2, 2, 4]);
    let two_n = d.num(2);
    let reduced = d.const_app(p.row_echelon, &[m, two_n, two_n]);

    let true_v = d.bool_true();
    let false_v = d.bool_false();

    let c0 = d.num(0);
    let col0 = ris_pivot_col_b(&mut d, p, reduced, two_n, two_n, c0);
    assert!(
        d.kernel().def_eq(col0, true_v),
        "column 0 of [[1,2],[0,0]] is a pivot column"
    );
    assert!(
        !d.kernel().def_eq(col0, false_v),
        "isPivotColB must not be constantly false"
    );

    let c1 = d.num(1);
    let col1 = ris_pivot_col_b(&mut d, p, reduced, two_n, two_n, c1);
    assert!(
        d.kernel().def_eq(col1, false_v),
        "column 1 of [[1,2],[0,0]] is free"
    );
    assert!(
        !d.kernel().def_eq(col1, true_v),
        "isPivotColB must not be constantly true"
    );
}

/// `Rat.isPivotColB` is `false` at a column index that is out of range, and at
/// every column when there are no rows.
///
/// The first is what keeps `rankCols ≤ cols` honest rather than accidental;
/// the second is the reduction behind `Rat.isPivotColB_zero_rows`, checked
/// here at a CONCRETE matrix as well as proved symbolically.
#[test]
fn is_pivot_col_b_is_false_out_of_range_and_with_no_rows() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 2, 2, &[1, 2, 3, 4]);
    let two_n = d.num(2);
    let reduced = d.const_app(p.row_echelon, &[m, two_n, two_n]);
    let false_v = d.bool_false();

    // Column 2 is out of range for a 2-column matrix: no row's leading index
    // can be 2 unless the row is zero, and a zero row's leading index is
    // `cols = 2` -- which is why this matrix, with no zero row, must say false.
    let c2 = d.num(2);
    let out = ris_pivot_col_b(&mut d, p, reduced, two_n, two_n, c2);
    assert!(
        d.kernel().def_eq(out, false_v),
        "column 2 is out of range for a 2-column matrix"
    );

    let zero_rows = d.num(0);
    let c0 = d.num(0);
    let none = ris_pivot_col_b(&mut d, p, reduced, zero_rows, two_n, c0);
    assert!(
        d.kernel().def_eq(none, false_v),
        "with no rows no column is a pivot column"
    );
    let true_v = d.bool_true();
    assert!(
        !d.kernel().def_eq(none, true_v),
        "the no-rows answer must not also be true"
    );
}

/// The degenerate dimensions, by reduction: `nullity M 0 cols = cols` and
/// `rankCols M 0 cols = 0` at a concrete `cols`.
///
/// `Rat.nullity_zero_rows` is the discriminating half — a `nullity` that
/// returned `0` would satisfy `rankCols_zero_rows` and fail this.
#[test]
fn with_no_rows_every_column_is_free() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 2, 3, &[1, 0, 2, 0, 1, 3]);
    let zero_rows = d.num(0);
    let three_n = d.num(3);

    let rc = rrank_cols(&mut d, p, m, zero_rows, three_n);
    let zero = d.num(0);
    assert!(
        d.kernel().def_eq(rc, zero),
        "with no rows there are no pivot columns"
    );

    let nl = rnullity(&mut d, p, m, zero_rows, three_n);
    assert!(
        d.kernel().def_eq(nl, three_n),
        "with no rows all three columns are free"
    );
    assert!(
        !d.kernel().def_eq(nl, zero),
        "nullity must NOT also be 0 -- the no-rows case is where a constant-0 nullity hides"
    );
}

/// Every declaration this module adds is axiom-free, read from the kernel.
///
/// The footprint is taken from [`Kernel::axiom_footprint`] and not from a
/// rendered name or a source comment — the rule this repository's guide states
/// as "read a trusted surface from the kernel".
#[test]
fn the_nullity_family_is_axiom_free() {
    let (kernel, p) = built();
    let names = [
        ("pivotColSearchAux", p.pivot_col_search_aux),
        ("isPivotColB", p.is_pivot_col_b),
        ("isPivotColB_eq_search", p.is_pivot_col_b_eq_search),
        ("isPivotColB_zero_rows", p.is_pivot_col_b_zero_rows),
        ("rankCols", p.rank_cols),
        ("rankCols_eq_countRange", p.rank_cols_eq_count_range),
        ("nullity", p.nullity),
        ("nullity_eq_countRange", p.nullity_eq_count_range),
        ("rank_nullity", p.rank_nullity),
        ("rankCols_le_cols", p.rank_cols_le_cols),
        ("nullity_le_cols", p.nullity_le_cols),
        ("rankCols_zero_cols", p.rank_cols_zero_cols),
        ("nullity_zero_cols", p.nullity_zero_cols),
        (
            "countRange_isPivotColB_zeroRows",
            p.count_range_is_pivot_col_b_zero_rows,
        ),
        ("rankCols_zero_rows", p.rank_cols_zero_rows),
        ("nullity_zero_rows", p.nullity_zero_rows),
    ];
    for (label, name) in names {
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "Rat.{label} must be axiom-free, found {} axiom(s)",
            footprint.len()
        );
    }
}
