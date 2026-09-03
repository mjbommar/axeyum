//! Evidence for [`super::pivot_content`] — obligation 2's value half.
//!
//! A `Not (Eq Rat … Rat.zero)` theorem is a type, so unlike a `Definition` it
//! cannot be reduced against a wrong answer. What CAN be checked is that its
//! hypothesis is satisfiable and its conclusion is not trivially true, and that
//! is what the first test does: at one matrix the search comes in strictly
//! under the bound and the entry it lands on really is nonzero by reduction,
//! while from a start already past the bound the same search returns `rows` and
//! the hypothesis is unavailable.
//!
//! Without that, a theorem whose hypothesis were never satisfiable would look
//! exactly like this one.

use super::RatPrelude;
use super::matrix_det::rq;
use super::nullity_tests::rect_matrix;
use crate::env::Declaration;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{Kernel, build_rat_prelude};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("the rational prelude must build");
    (kernel, prelude)
}

/// The value half is not vacuous: the search's in-range hypothesis is
/// satisfiable, and where it holds the entry really is nonzero.
///
/// `[[0,1],[1,0]]` is the matrix `nullity_tests.rs` uses for the range half,
/// deliberately: column `0` is zero at row `0` and nonzero at row `1`, so the
/// scan from row `0` must SKIP a row before it succeeds. A `pivotSearch` that
/// returned `start` unconditionally would satisfy neither assertion here.
///
/// The second half is the control that makes the hypothesis load-bearing: from
/// a start already past the row count the answer is `rows` itself, `Lt rows
/// rows` is false, and the theorem says nothing — which matters because at that
/// index the matrix's entry is `0` (the constant-matrix fallback), so the
/// conclusion would be FALSE if the hypothesis were droppable.
#[test]
fn the_pivot_search_value_half_is_not_vacuous() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 2, 2, &[0, 1, 1, 0]);
    let zero_n = d.num(0);
    let one_n = d.num(1);
    let two_n = d.num(2);

    // From row 0 in column 0 the scan skips row 0 and lands on row 1.
    let found = d.const_app(p.pivot_search, &[m, zero_n, zero_n, two_n]);
    assert!(
        d.kernel().def_eq(found, one_n),
        "the scan must land on row 1, strictly under the bound"
    );
    assert!(
        !d.kernel().def_eq(found, two_n),
        "the scan must NOT return rows here -- the hypothesis would be unsatisfiable"
    );

    // ... and the entry there is nonzero, which is what the theorem asserts.
    let entry = d.apply(m, &[one_n, zero_n]);
    let rat_zero = rq(&mut d, p, 0);
    let rat_one = rq(&mut d, p, 1);
    assert!(d.kernel().def_eq(entry, rat_one), "M 1 0 must reduce to 1");
    assert!(
        !d.kernel().def_eq(entry, rat_zero),
        "M 1 0 must NOT also reduce to 0 -- the conclusion has to be observable"
    );

    // The control: at row 0 the same column IS zero, so a theorem that
    // concluded about the START row rather than the FOUND row would be false.
    let start_entry = d.apply(m, &[zero_n, zero_n]);
    assert!(
        d.kernel().def_eq(start_entry, rat_zero),
        "M 0 0 must be 0 -- otherwise the found-vs-start distinction is untested"
    );

    // From a start past the bound the answer is `rows`, so `Lt rows rows`
    // cannot be supplied and the theorem is silent.
    let exhausted = d.const_app(p.pivot_search, &[m, zero_n, two_n, two_n]);
    assert!(
        d.kernel().def_eq(exhausted, two_n),
        "an exhausted scan returns rows, where the hypothesis is unavailable"
    );
}

/// The value half says what it claims, pinned by its rendered type.
///
/// The forbidden substring is the point: a version concluding about the entry
/// at the START row (`x2`, the third binder) rather than at the row the search
/// FOUND would be false at `[[0,1],[1,0]]`, and the name would not change.
#[test]
fn the_value_half_is_about_the_row_the_search_found() {
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.pivot_search_ne_zero)
        .expect("Rat.pivotSearch_ne_zero must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem"),
    };
    let rendered = kernel
        .render_lean(ty)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");

    assert!(
        rendered.contains("AxNat.lt (Rat.pivotSearch x0 x1 x2 x3) x3"),
        "the hypothesis must be that the SEARCH landed under the row count: {rendered}"
    );
    assert!(
        rendered.contains("Not (Eq.{1} Rat (x0 (Rat.pivotSearch x0 x1 x2 x3) x1) Rat.zero)"),
        "the conclusion must be about the entry at the row the search FOUND, \
         in the column it searched: {rendered}"
    );
    assert!(
        !rendered.contains("Not (Eq.{1} Rat (x0 x2 x1) Rat.zero)"),
        "the conclusion must NOT be about the entry at the START row: {rendered}"
    );
}

/// Both halves of the value statement are axiom-free, read from the kernel.
///
/// The existence check first: `axiom_footprint` of a name that was never
/// declared is EMPTY, so without it this passes for a missing declaration.
#[test]
fn the_pivot_content_family_is_axiom_free() {
    let (kernel, p) = built();
    for (label, name) in [
        ("pivotSearchAux_ne_zero", p.pivot_search_aux_ne_zero),
        ("pivotSearch_ne_zero", p.pivot_search_ne_zero),
        ("pivotSearchAux_column_zero", p.pivot_search_aux_column_zero),
        ("pivotSearch_column_zero", p.pivot_search_column_zero),
    ] {
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

/// The exhaustion disjunct is not vacuous: there is a matrix where the scan
/// really does answer `rows`, and there the column really is zero at every row
/// the scan passed.
///
/// `[[0,1],[0,2]]` has column `0` zero at BOTH rows, so `pivotSearch` from row
/// `0` exhausts and returns `2`. The control is the same matrix's column `1`,
/// where the scan lands on row `0` and the hypothesis `Eq Nat … rows` is
/// unavailable — which matters because at that column the entries are `1` and
/// `2`, so the conclusion would be FALSE if the hypothesis were droppable.
#[test]
fn the_exhaustion_disjunct_is_not_vacuous() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 2, 2, &[0, 1, 0, 2]);
    let zero_n = d.num(0);
    let one_n = d.num(1);
    let two_n = d.num(2);
    let rat_zero = rq(&mut d, p, 0);

    // Column 0 is all zero, so the scan exhausts and answers `rows`.
    let exhausted = d.const_app(p.pivot_search, &[m, zero_n, zero_n, two_n]);
    assert!(
        d.kernel().def_eq(exhausted, two_n),
        "column 0 is all zero, so the scan must answer rows"
    );
    assert!(
        !d.kernel().def_eq(exhausted, zero_n),
        "the scan must NOT answer 0 -- the hypothesis would be unsatisfiable"
    );

    // ... and the conclusion holds at BOTH rows the scan passed, which is what
    // makes this a statement about the range and not about one index.
    for r in [zero_n, one_n] {
        let entry = d.apply(m, &[r, zero_n]);
        assert!(
            d.kernel().def_eq(entry, rat_zero),
            "every entry of column 0 must be 0"
        );
    }

    // The control: in column 1 the scan lands on row 0, the hypothesis is
    // unavailable, and the entries are NOT zero.
    let found = d.const_app(p.pivot_search, &[m, one_n, zero_n, two_n]);
    assert!(
        d.kernel().def_eq(found, zero_n),
        "column 1 has a pivot at row 0"
    );
    let live = d.apply(m, &[one_n, one_n]);
    assert!(
        !d.kernel().def_eq(live, rat_zero),
        "column 1 is nonzero, so the conclusion would be FALSE there"
    );
}

/// The exhaustion disjunct says what it claims, pinned by its rendered type.
///
/// Two forbidden shapes. A version concluding about the START row rather than
/// an arbitrary `q` in range would be strictly weaker and would not supply the
/// loop invariant; and a version without the `Eq Nat … rows` hypothesis would
/// be plainly false, so its presence is asserted rather than assumed.
#[test]
fn the_exhaustion_disjunct_is_about_every_row_the_scan_passed() {
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.pivot_search_column_zero)
        .expect("Rat.pivotSearch_column_zero must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem"),
    };
    let rendered = kernel
        .render_lean(ty)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");

    assert!(
        rendered.contains("AxNat.le x2 x4"),
        "the range must start at the scan's START row: {rendered}"
    );
    assert!(
        rendered.contains("AxNat.lt x4 x3"),
        "the range must stop at the row count: {rendered}"
    );
    assert!(
        rendered.contains("Eq.{1} AxNat (Rat.pivotSearch x0 x1 x2 x3) x3"),
        "the hypothesis must be that the scan EXHAUSTED: {rendered}"
    );
    assert!(
        rendered.contains("Eq.{1} Rat (x0 x4 x1) Rat.zero"),
        "the conclusion must be about the arbitrary in-range row x4, in the \
         column the scan searched: {rendered}"
    );
    assert!(
        !rendered.contains("Eq.{1} Rat (x0 x2 x1) Rat.zero"),
        "the conclusion must NOT be about the START row alone -- that is the \
         weaker statement the loop invariant cannot use: {rendered}"
    );
}
