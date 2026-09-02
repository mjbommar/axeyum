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
