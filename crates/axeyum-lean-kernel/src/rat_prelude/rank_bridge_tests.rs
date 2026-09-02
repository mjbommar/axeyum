//! Evaluation tests for [`super::rank_bridge`] — the two maps of the
//! `Rat.rank = Rat.rankCols` bridge, REDUCED at the six matrices the rank and
//! nullity lanes used.
//!
//! **The trusted gate cannot tell you a `Definition` is wrong.**
//! `Rat.pivotRowOfCol` has type `Mat → Nat → Nat → Nat → Nat` whether it
//! returns the first matching row, the last one, or `0`. So every test below
//! reads the value back by reduction and compares it against a table worked
//! out by hand, and the read-back is a SEARCH over the candidate answers
//! ([`nat_value`]) rather than an assertion against one — a definition that
//! reduced to a different number is reported as that number, not as an opaque
//! failure.
//!
//! ## What discriminates
//!
//! The six matrices are the nullity lane's, unchanged, so the tables cannot
//! drift apart. What they buy here:
//!
//! - `[[1,2],[2,4]]` has a ZERO ROW in its echelon form, whose leading index is
//!   `cols = 2`. So `pivotRowOfCol` at `j = 2` finds row `1` — the one place
//!   where a column index out of range is still "found", and the reason
//!   [`pivot_row_of_col_reads_the_leading_indices_back`] tabulates `j` up to
//!   `cols` inclusive rather than stopping at `cols - 1`.
//! - the 3×3 `[[1,2,3],[2,4,6],[1,1,1]]` needs the elimination AND a mid-run
//!   re-pivot: its echelon form is `[[1,2,3],[0,-1,-2],[0,0,0]]`, so
//!   `pivotRowOfCol` at `j = 1` must return row `1` (the row that was SWAPPED
//!   into place), not row `2` where the `-1` started.
//! - the rectangular 2×3 is the only case with `rows ≠ cols`, so it is the only
//!   one that can catch the two `Nat` arguments being read in the wrong order —
//!   and `pivotRowOfCol` takes both.
//! - the zero 2×2 is where "not found" must answer `rows`: every column below
//!   `cols` is absent, and `j = cols` finds row `0`.

use super::RatPrelude;
use super::nullity_tests::{CASES, rect_matrix};
use super::rank_bridge::{rpivot_col_of_row, rpivot_row_of_col};
use crate::env::Declaration;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{ExprId, Kernel, build_rat_prelude};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("the rational prelude must build");
    (kernel, prelude)
}

/// The natural number `term` reduces to, searched over `0..=limit`.
///
/// A plain `assert!(def_eq(term, expected))` reports only that the definition
/// is not the expected value; this reports what it IS, which is the difference
/// between a failing test that tells you the answer and one that does not. It
/// returns `None` when nothing in range matches, which is itself a finding — a
/// definition that ran away is not the same defect as one that is off by one.
fn nat_value(d: &mut IntDev<'_>, term: ExprId, limit: u32) -> Option<u32> {
    (0..=limit).find(|&candidate| {
        let numeral = d.num(candidate);
        d.kernel().def_eq(term, numeral)
    })
}

/// The row-echelon form of the `case` matrix, plus its dimensions as numerals.
fn echelon_of(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    rows: usize,
    cols: usize,
    entries: &[i64],
) -> (ExprId, ExprId, ExprId) {
    let m = rect_matrix(d, p, rows, cols, entries);
    let rows_n = d.num(u32::try_from(rows).expect("small"));
    let cols_n = d.num(u32::try_from(cols).expect("small"));
    let e = d.const_app(p.row_echelon, &[m, rows_n, cols_n]);
    (e, rows_n, cols_n)
}

/// The leading index of each row of each echelon form, by row index.
///
/// Indexed the same way as [`CASES`]. A zero row's entry is `cols`, which is
/// the convention `echelon.rs` fixed and `rank.rs` counts against.
const LEADING: &[&[u32]] = &[
    &[0, 1],    // [[1,2],[3,4]]   -> [[1,2],[0,-2]]
    &[0, 2],    // [[1,2],[2,4]]   -> [[1,2],[0,0]]
    &[2, 2],    // the zero 2x2    -> unchanged, both rows zero
    &[0, 1, 3], // the 3x3         -> [[1,2,3],[0,-1,-2],[0,0,0]]
    &[0, 1, 2], // the 3x3 identity
    &[0, 1],    // the 2x3 [[1,0,2],[0,1,3]]
];

/// `Rat.pivotColOfRow` is the leading index, at every row of every echelon
/// form.
///
/// It is a one-line `Definition`, so what this really checks is the ARGUMENT
/// ORDER: `pivotColOfRow E cols r` against `leadingIndex E r cols`, whose two
/// `Nat`s are swapped. Every square case is blind to that, which is why the
/// rectangular 2×3 is in the table — at `rows = 2, cols = 3` a swapped pair
/// gives a different answer.
#[test]
fn pivot_col_of_row_is_the_leading_index() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    for (idx, &(rows, cols, entries, _rc, _nl, what)) in CASES.iter().enumerate() {
        let (e, _rows_n, cols_n) = echelon_of(&mut d, p, rows, cols, entries);
        for (r, &want) in LEADING[idx].iter().enumerate() {
            let r_n = d.num(u32::try_from(r).expect("small"));
            let term = rpivot_col_of_row(&mut d, p, e, cols_n, r_n);
            let got = nat_value(&mut d, term, 8);
            assert_eq!(
                got,
                Some(want),
                "{what}: pivotColOfRow at row {r} must be the leading index {want}"
            );
        }
    }
}

/// `Rat.pivotRowOfCol` inverts the leading-index map: at every column `j` it
/// returns the FIRST row whose leading index is `j`, and `rows` when there is
/// none.
///
/// The expected value is DERIVED from [`LEADING`] rather than written out
/// again, so this test cannot agree with a hand-typed table that is itself
/// wrong — and it is a real inversion check because [`LEADING`] was verified
/// independently by [`pivot_col_of_row_is_the_leading_index`].
#[test]
fn pivot_row_of_col_reads_the_leading_indices_back() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    for (idx, &(rows, cols, entries, _rc, _nl, what)) in CASES.iter().enumerate() {
        let (e, rows_n, cols_n) = echelon_of(&mut d, p, rows, cols, entries);
        let leads = LEADING[idx];
        // `j` runs to `cols` INCLUSIVE: `cols` is a zero row's leading index,
        // so it is the one out-of-range column that can still be found.
        for j in 0..=u32::try_from(cols).expect("small") {
            let want = leads.iter().position(|&l| l == j).map_or_else(
                || u32::try_from(rows).expect("small"),
                |r| u32::try_from(r).expect("small"),
            );
            let j_n = d.num(j);
            let term = rpivot_row_of_col(&mut d, p, e, rows_n, cols_n, j_n);
            let got = nat_value(&mut d, term, 8);
            assert_eq!(
                got,
                Some(want),
                "{what}: pivotRowOfCol at column {j} must be row {want}"
            );
        }
    }
}

/// The residue hypothesis, checked where it IS decidable: on every echelon
/// form, `pivotRowOfCol (leadingIndex r) = r` at every NONZERO row.
///
/// This is the one hypothesis the bridge cannot discharge from the searches
/// alone (`rank_bridge.rs`'s module note). It is a decidable statement at a
/// concrete matrix, so it is checked at all six — the decidable-fragment row of
/// the graded family (ADR-0603), not a substitute for the general statement.
///
/// The test also asserts the hypothesis FAILS at the zero rows, which is what
/// makes the `nonzeroRowB` side condition load-bearing rather than decorative:
/// row `2` of the 3×3 and both rows of the zero 2×2 have leading index `cols`,
/// and `pivotRowOfCol` sends `cols` to the FIRST such row, not to each of them.
#[test]
fn the_section_hypothesis_holds_at_every_nonzero_row_and_fails_at_the_zero_ones() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let mut zero_rows_seen = 0usize;
    let mut nonzero_rows_seen = 0usize;

    for (idx, &(rows, cols, entries, _rc, _nl, what)) in CASES.iter().enumerate() {
        let (e, rows_n, cols_n) = echelon_of(&mut d, p, rows, cols, entries);
        let leads = LEADING[idx];
        let cols_u = u32::try_from(cols).expect("small");

        for (r, &lead) in leads.iter().enumerate() {
            let r_u = u32::try_from(r).expect("small");
            let lead_n = d.num(lead);
            let term = rpivot_row_of_col(&mut d, p, e, rows_n, cols_n, lead_n);
            let got = nat_value(&mut d, term, 8);
            if lead < cols_u {
                nonzero_rows_seen += 1;
                assert_eq!(
                    got,
                    Some(r_u),
                    "{what}: the section hypothesis must hold at nonzero row {r}"
                );
            } else {
                zero_rows_seen += 1;
                // A zero row is NOT recovered unless it happens to be the
                // first zero row; the side condition is what excludes it.
                let first_zero = leads
                    .iter()
                    .position(|&l| l >= cols_u)
                    .expect("this row is itself zero");
                assert_eq!(
                    got,
                    Some(u32::try_from(first_zero).expect("small")),
                    "{what}: pivotRowOfCol at cols must be the FIRST zero row"
                );
            }
        }
    }

    // Both populations must be non-empty, or one half of the test measured
    // nothing: an all-nonzero table would make the failure branch vacuous.
    assert!(
        nonzero_rows_seen >= 6,
        "the table must exercise the nonzero-row branch"
    );
    assert!(
        zero_rows_seen >= 3,
        "the table must exercise the zero-row branch"
    );
}

/// Every declaration this module adds is axiom-free, read from the kernel.
///
/// The footprint comes from [`Kernel::axiom_footprint`] and not from a rendered
/// name or a source comment.
///
/// **The existence check is not decoration.** `axiom_footprint` walks the
/// dependencies of whatever it is handed, and a name that was never declared
/// has none — so it returns the EMPTY footprint and this test would pass for a
/// declaration that does not exist. Asking the environment first is what makes
/// the assertion say something.
#[test]
fn the_rank_bridge_family_is_axiom_free() {
    let (kernel, p) = built();
    let names = [
        ("pivotColOfRow", p.pivot_col_of_row),
        (
            "pivotColOfRow_eq_leadingIndex",
            p.pivot_col_of_row_eq_leading_index,
        ),
        ("pivotRowSearchAux", p.pivot_row_search_aux),
        ("pivotRowOfCol", p.pivot_row_of_col),
        ("pivotRowOfCol_eq_search", p.pivot_row_of_col_eq_search),
    ];
    for (label, name) in names {
        assert!(
            kernel.environment().get(name).is_some(),
            "Rat.{label} must be declared -- an absent name has an EMPTY footprint"
        );
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "Rat.{label} must be axiom-free, found {} axiom(s)",
            footprint.len()
        );
    }
}

/// The section property is a REAL constraint on a matrix, not something every
/// matrix satisfies.
///
/// `Rat.rank_eq_rankCols_of_pivotSection` is a conditional theorem, so the
/// first question to ask of it is whether its hypothesis says anything at all:
/// a hypothesis satisfied by every matrix would make the bridge unconditional
/// and this lane's residue imaginary. It is not. At the matrix `[[1,0],[1,0]]`
/// — two nonzero rows sharing leading index `0`, which is exactly what echelon
/// form forbids — the section equation FAILS at row `1`: the scan finds row `0`
/// first and never reaches row `1`, while row `1` is nonzero and in range.
///
/// The matrix is used RAW here, not through `rowEchelon`, because that is the
/// point: the property is a fact about echelon forms, and the residue
/// `rowEchelon_isEchelon` is what would supply it.
#[test]
fn the_section_property_is_a_real_constraint() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let e = rect_matrix(&mut d, p, 2, 2, &[1, 0, 1, 0]);
    let two_n = d.num(2);
    let one_n = d.num(1);
    let zero_n = d.num(0);
    let true_v = d.bool_true();

    // Row 1 is in range and nonzero, so it is inside the hypothesis's scope.
    let nonzero = d.const_app(p.nonzero_row_b, &[e, two_n, one_n]);
    assert!(
        d.kernel().def_eq(nonzero, true_v),
        "row 1 of [[1,0],[1,0]] is nonzero, so the hypothesis would have to cover it"
    );

    // ... and its leading index is 0, the same as row 0's.
    let lead_one = rpivot_col_of_row(&mut d, p, e, two_n, one_n);
    assert_eq!(
        nat_value(&mut d, lead_one, 8),
        Some(0),
        "both rows lead in column 0 -- that is the shape echelon form forbids"
    );

    // So the section equation fails: the scan comes back with row 0, not row 1.
    let back = rpivot_row_of_col(&mut d, p, e, two_n, two_n, lead_one);
    assert_eq!(
        nat_value(&mut d, back, 8),
        Some(0),
        "the scan finds the FIRST such row"
    );
    assert!(
        !d.kernel().def_eq(back, one_n),
        "the section equation must FAIL here -- otherwise the bridge's hypothesis is vacuous"
    );

    // The positive control: at row 0 the same equation HOLDS, so the failure
    // above is about the repeated leading index and not about the matrix being
    // outside the definition's reach altogether.
    let lead_zero = rpivot_col_of_row(&mut d, p, e, two_n, zero_n);
    let back_zero = rpivot_row_of_col(&mut d, p, e, two_n, two_n, lead_zero);
    assert!(
        d.kernel().def_eq(back_zero, zero_n),
        "the section equation must still hold at row 0"
    );
}

/// The three headline statements, pinned by their RENDERED TYPE.
///
/// A name says nothing: `rank_le_cols_of_pivotSection` would still be called
/// that if its conclusion were `Le (rank …) rows`, which is free. Reading the
/// type out of the environment is what makes the pin a check on the theorem
/// rather than on the maintainer's memory.
///
/// The assertions are stated as required substrings plus one FORBIDDEN
/// substring each, because the full rendering of a four-binder matrix statement
/// is long enough that an exact pin would be maintained by copy-paste and would
/// stop being read.
#[test]
fn the_bridge_statements_say_what_they_claim() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };

    let bridge = rendered(&mut kernel, p.rank_eq_rank_cols_of_pivot_section);
    for needle in [
        "Rat.rank ",
        "Rat.rankCols ",
        "Rat.pivotRowOfCol",
        "Rat.pivotColOfRow",
        "Rat.nonzeroRowB",
        "Rat.rowEchelon",
    ] {
        assert!(
            bridge.contains(needle),
            "the bridge statement must mention {needle}: {bridge}"
        );
    }
    assert!(
        !bridge.contains("Rat.isEchelon"),
        "the bridge must NOT assume the full echelon predicate -- \
         its hypothesis is strictly weaker: {bridge}"
    );

    let bound = rendered(&mut kernel, p.rank_le_cols_of_pivot_section);
    assert!(
        bound.contains("Nat.le (Rat.rank x0 x1 x2) x2"),
        "the bound must be rank <= COLS, not rank <= rows: {bound}"
    );

    let rank_nullity = rendered(&mut kernel, p.rank_nullity_rows_of_pivot_section);
    assert!(
        rank_nullity.contains("Nat.add (Rat.rank x0 x1 x2) (Rat.nullity x0 x1 x2)"),
        "the row form must add rank and nullity: {rank_nullity}"
    );
    assert!(
        !rank_nullity.contains("Nat.add (Rat.rankCols"),
        "the row form must not be the column form under a new name: {rank_nullity}"
    );
}

/// Every theorem the bridge adds is axiom-free, read from the kernel.
///
/// The existence check is load-bearing for the same reason as in
/// [`the_rank_bridge_family_is_axiom_free`]: `axiom_footprint` of a name that
/// was never declared is EMPTY.
#[test]
fn the_bridge_theorems_are_axiom_free() {
    let (kernel, p) = built();
    let names = [
        ("pivotColSearchAux_eq_ble", p.pivot_col_search_aux_eq_ble),
        ("isPivotColB_eq_ble", p.is_pivot_col_b_eq_ble),
        ("pivotRowOfCol_lt_rows", p.pivot_row_of_col_lt_rows),
        (
            "pivotRowSearchAux_leadingIndex",
            p.pivot_row_search_aux_leading_index,
        ),
        (
            "leadingIndex_pivotRowOfCol",
            p.leading_index_pivot_row_of_col,
        ),
        (
            "rank_eq_rankCols_of_pivotSection",
            p.rank_eq_rank_cols_of_pivot_section,
        ),
        (
            "rank_le_cols_of_pivotSection",
            p.rank_le_cols_of_pivot_section,
        ),
        (
            "rank_nullity_rows_of_pivotSection",
            p.rank_nullity_rows_of_pivot_section,
        ),
    ];
    for (label, name) in names {
        assert!(
            kernel.environment().get(name).is_some(),
            "Rat.{label} must be declared -- an absent name has an EMPTY footprint"
        );
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "Rat.{label} must be axiom-free, found {} axiom(s)",
            footprint.len()
        );
    }
}

/// `Rat.isPivotColB_eq_ble` is not vacuous: it separates the two answers on the
/// SAME matrix.
///
/// The identity `isPivotColB E rows cols j = ble (succ (pivotRowOfCol …)) rows`
/// would hold trivially if `isPivotColB` were constantly `false` and
/// `pivotRowOfCol` constantly `rows`. `[[1,2],[2,4]]`'s echelon form
/// `[[1,2],[0,0]]` has column `0` a pivot column (so both sides are `true`) and
/// column `1` free (so both sides are `false`), which is what makes the
/// identity a statement about two agreeing searches rather than about two
/// constants.
#[test]
fn the_scan_identity_separates_a_pivot_column_from_a_free_one() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let (e, rows_n, cols_n) = echelon_of(&mut d, p, 2, 2, &[1, 2, 2, 4]);
    let true_v = d.bool_true();
    let false_v = d.bool_false();

    for (j, want_pivot, want_row) in [(0u32, true, 0u32), (1, false, 2)] {
        let j_n = d.num(j);
        let is_pivot = d.const_app(p.is_pivot_col_b, &[e, rows_n, cols_n, j_n]);
        let expected = if want_pivot { true_v } else { false_v };
        let other = if want_pivot { false_v } else { true_v };
        assert!(
            d.kernel().def_eq(is_pivot, expected),
            "isPivotColB at column {j} must be {want_pivot}"
        );
        assert!(
            !d.kernel().def_eq(is_pivot, other),
            "isPivotColB at column {j} must not be both"
        );

        let row = rpivot_row_of_col(&mut d, p, e, rows_n, cols_n, j_n);
        assert_eq!(
            nat_value(&mut d, row, 8),
            Some(want_row),
            "pivotRowOfCol at column {j} must be {want_row}"
        );
    }
}
