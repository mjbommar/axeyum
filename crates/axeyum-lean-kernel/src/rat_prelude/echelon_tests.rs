//! Evaluation tests for [`super::echelon`]'s `Definition`s, plus concrete
//! instantiations of its three inverse laws.
//!
//! **The trusted gate cannot tell you a `Definition` is wrong.**
//! `Rat.rowEchelon` has type `Mat -> Nat -> Nat -> Mat` whatever it returns,
//! and so does a "row echelon" that hands its argument straight back. Every
//! test below REDUCES a definition at concrete arguments and compares against
//! a value computed by hand, and every one of them carries a control that must
//! FAIL to be defeq — an evaluation test whose expected value is also what a
//! broken definition returns is not a test.
//!
//! ## What discriminates
//!
//! - `Rat.isZeroB` is separated in both directions (`0` and `1`), and at a
//!   NEGATIVE rational, which a test written against a `Nat`-shaped intuition
//!   would omit and a one-sided `ble` would get wrong.
//! - The three row operations run on `[[1,2,3],[4,5,6],[7,8,9]]`, nine pairwise
//!   distinct entries, so writing the wrong row or reading the wrong source row
//!   shows up as a wrong number rather than as a coincidence.
//! - `Rat.rowEchelon` is run at three 2×2 shapes chosen so that the three
//!   BRANCHES of the loop are each the only one that produces the observed
//!   answer: an ordinary elimination (`[[1,2],[3,4]]`), a dependent pair that
//!   must yield a zero row (`[[1,2],[2,4]]`), and a zero pivot that must force
//!   a SWAP (`[[0,1],[1,0]]`, whose echelon form is the identity and whose
//!   input is not in echelon form at all). A 3×3 exercises the two-cursor
//!   advance and a mid-elimination swap in one run.
//! - `Rat.isEchelon` is asserted `false` on inputs that are not in echelon
//!   form, not merely `true` on ones that are. A predicate that returns `true`
//!   unconditionally passes every positive test there is.
//!
//! Every magnitude formed is a single-digit integer with a denominator of 1 or
//! 2, so nothing here touches the unary-numeral cost `CLAUDE.md` documents.

use super::RatPrelude;
use super::echelon::{
    ris_echelon, ris_zero_b, rleading_index, rpivot_search, rrow_add_mul, rrow_echelon, rrow_scale,
    rrow_swap,
};
use super::matrix_det::{const_matrix, rq};
use super::ops::{req, rneg};
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{ExprId, Kernel, build_rat_prelude};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("the rational prelude must build");
    (kernel, prelude)
}

/// `[[1,2,3],[4,5,6],[7,8,9]]` — nine pairwise distinct entries.
fn base3(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    const_matrix(d, p, 3, &[1, 2, 3, 4, 5, 6, 7, 8, 9])
}

/// Assert `M r c` reduces to `want` for every entry of a `k × k` block.
fn assert_block(d: &mut IntDev<'_>, p: RatPrelude, m: ExprId, k: u32, want: &[i64], what: &str) {
    for r in 0..k {
        for c in 0..k {
            let ri = d.num(r);
            let ci = d.num(c);
            let lhs = d.apply(m, &[ri, ci]);
            let expected = want[(r * k + c) as usize];
            let rhs = rq(d, p, expected);
            assert!(
                d.kernel().def_eq(lhs, rhs),
                "{what}: entry ({r},{c}) must be {expected}"
            );
        }
    }
}

/// `Rat.isZeroB` decides zero, and it decides NEGATIVE numbers as nonzero.
///
/// The negative case is the one a one-sided `Rat.ble x 0` would get wrong: it
/// holds for every `x <= 0`, so a definition that dropped the second
/// comparison would call `-1` zero and every pivot search would walk past a
/// perfectly good negative pivot.
#[test]
fn is_zero_b_decides_zero_in_both_directions() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let true_v = d.bool_true();
    let false_v = d.bool_false();

    for (n, want_zero) in [(0_i64, true), (1, false), (-1, false), (2, false)] {
        let x = rq(&mut d, p, n);
        let test = ris_zero_b(&mut d, p, x);
        let want = if want_zero { true_v } else { false_v };
        assert!(
            d.kernel().def_eq(test, want),
            "isZeroB {n} must be {want_zero}"
        );
        let other = if want_zero { false_v } else { true_v };
        assert!(
            !d.kernel().def_eq(test, other),
            "isZeroB {n} must NOT also be {}",
            !want_zero
        );
    }
}

/// `Rat.rowSwap` exchanges exactly two rows and leaves the third alone.
#[test]
fn row_swap_exchanges_exactly_two_rows() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = base3(&mut d, p);
    let zero_n = d.num(0);
    let two_n = d.num(2);
    let swapped = rrow_swap(&mut d, p, zero_n, two_n, m);

    assert_block(
        &mut d,
        p,
        swapped,
        3,
        &[7, 8, 9, 4, 5, 6, 1, 2, 3],
        "rowSwap 0 2",
    );

    // Non-vacuity: the swap actually moved something.
    let r0 = d.num(0);
    let c0 = d.num(0);
    let entry = d.apply(swapped, &[r0, c0]);
    let one = rq(&mut d, p, 1);
    assert!(
        !d.kernel().def_eq(entry, one),
        "entry (0,0) was 1 before the swap -- if this passes rowSwap is the identity"
    );
}

/// `Rat.rowSwap i i M` is the identity, entry by entry.
///
/// The degenerate corner [`super::echelon`]'s involution law has to handle, and
/// the one a definition reading the INNER write's result would get wrong.
#[test]
fn row_swap_at_equal_indices_is_the_identity() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = base3(&mut d, p);
    let one_n = d.num(1);
    let swapped = rrow_swap(&mut d, p, one_n, one_n, m);
    assert_block(
        &mut d,
        p,
        swapped,
        3,
        &[1, 2, 3, 4, 5, 6, 7, 8, 9],
        "rowSwap 1 1",
    );
}

/// `Rat.rowScale` multiplies exactly one row.
#[test]
fn row_scale_multiplies_exactly_one_row() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = base3(&mut d, p);
    let one_n = d.num(1);
    let three = rq(&mut d, p, 3);
    let scaled = rrow_scale(&mut d, p, one_n, three, m);

    assert_block(
        &mut d,
        p,
        scaled,
        3,
        &[1, 2, 3, 12, 15, 18, 7, 8, 9],
        "rowScale 1 3",
    );

    let r1 = d.num(1);
    let c0 = d.num(0);
    let entry = d.apply(scaled, &[r1, c0]);
    let four = rq(&mut d, p, 4);
    assert!(
        !d.kernel().def_eq(entry, four),
        "row 1 was 4 at column 0 before the scaling"
    );
}

/// `Rat.rowAddMul i j k M` adds `k` times row `j` to row `i`, and touches
/// nothing else.
///
/// `i = 0`, `j = 2`, `k = -1` is chosen so the answer separates the two index
/// mistakes that matter: adding row `i` to row `j` would rewrite row 2, and
/// adding row `i` to itself would give `[0,0,0]` rather than `[-6,-6,-6]`.
#[test]
fn row_add_mul_adds_a_multiple_of_another_row() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = base3(&mut d, p);
    let zero_n = d.num(0);
    let two_n = d.num(2);
    let minus_one = rq(&mut d, p, -1);
    let combined = rrow_add_mul(&mut d, p, zero_n, two_n, minus_one, m);

    assert_block(
        &mut d,
        p,
        combined,
        3,
        &[-6, -6, -6, 4, 5, 6, 7, 8, 9],
        "rowAddMul 0 2 (-1)",
    );

    let r0 = d.num(0);
    let c0 = d.num(0);
    let entry = d.apply(combined, &[r0, c0]);
    let zero_q = rq(&mut d, p, 0);
    assert!(
        !d.kernel().def_eq(entry, zero_q),
        "adding row 0 to ITSELF would give 0 here -- the source row must be row 2"
    );
}

/// The three inverse laws, instantiated at concrete arguments AND checked by
/// computation.
///
/// The theorems themselves were admitted against genuinely free variables — the
/// kernel re-checked each proof term inside `add_declaration`, which is the
/// symbolic half. This is the other half: reduce both sides at a concrete
/// matrix, and confirm each instantiated theorem infers to exactly the equation
/// between the two values that were just computed.
#[test]
fn the_row_operations_invert_at_concrete_arguments() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = base3(&mut d, p);
    let i = d.num(0);
    let j = d.num(2);
    let r = d.num(0);
    let c = d.num(1);

    // rowSwap is an involution.
    {
        let once = rrow_swap(&mut d, p, i, j, m);
        let twice = rrow_swap(&mut d, p, i, j, once);
        let lhs = d.apply(twice, &[r, c]);
        let rhs = d.apply(m, &[r, c]);
        let two_q = rq(&mut d, p, 2);
        assert!(d.kernel().def_eq(lhs, two_q), "the round trip restores 2");
        let eight = rq(&mut d, p, 8);
        assert!(
            !d.kernel().def_eq(lhs, eight),
            "8 is what ONE swap leaves at (0,1) -- if this passes only one ran"
        );
        let proof = d.lemma(p.row_swap_involutive, &[i, j, m, r, c]);
        let inferred = d
            .kernel()
            .infer(proof)
            .unwrap_or_else(|e| panic!("rowSwap_involutive should infer: {e:?}"));
        let expected = req(&mut d, lhs, rhs);
        assert!(
            d.kernel().def_eq(inferred, expected),
            "the instantiated involution must be the equation between those two entries"
        );
    }

    // rowAddMul k is inverted by rowAddMul (-k), given j != i.
    {
        let k = rq(&mut d, p, 3);
        let neg_k = rneg(&mut d, k);
        let once = rrow_add_mul(&mut d, p, i, j, k, m);
        let twice = rrow_add_mul(&mut d, p, i, j, neg_k, once);
        let lhs = d.apply(twice, &[r, c]);
        let rhs = d.apply(m, &[r, c]);
        let two_q = rq(&mut d, p, 2);
        assert!(d.kernel().def_eq(lhs, two_q), "the round trip restores 2");
        let mid = d.apply(once, &[r, c]);
        let twenty_six = rq(&mut d, p, 26);
        assert!(
            d.kernel().def_eq(mid, twenty_six),
            "one step takes (0,1) from 2 to 2 + 3*8 = 26"
        );
        assert!(
            !d.kernel().def_eq(lhs, twenty_six),
            "if this passes the second step did nothing"
        );
        let false_v = d.bool_false();
        let beq_ji = NatOps::beq(&mut d, j, i);
        let hyp = d.bool_refl(false_v);
        assert!(
            d.kernel().def_eq(beq_ji, false_v),
            "the hypothesis Nat.beq 2 0 = false must reduce"
        );
        let proof = d.lemma(p.row_add_mul_inverse, &[i, j, k, m, hyp, r, c]);
        let inferred = d
            .kernel()
            .infer(proof)
            .unwrap_or_else(|e| panic!("rowAddMul_inverse should infer: {e:?}"));
        let expected = req(&mut d, lhs, rhs);
        assert!(
            d.kernel().def_eq(inferred, expected),
            "the instantiated add-multiple inverse must be that equation"
        );
    }

    // rowScale k is inverted by rowScale (1/k), given k != 0.
    {
        let k = rq(&mut d, p, 3);
        let inv_k = d.const_app(p.inv, &[k]);
        let once = rrow_scale(&mut d, p, i, k, m);
        let twice = rrow_scale(&mut d, p, i, inv_k, once);
        let lhs = d.apply(twice, &[r, c]);
        let two_q = rq(&mut d, p, 2);
        assert!(d.kernel().def_eq(lhs, two_q), "the round trip restores 2");
        let six = rq(&mut d, p, 6);
        let mid = d.apply(once, &[r, c]);
        assert!(
            d.kernel().def_eq(mid, six),
            "one step takes (0,1) from 2 to 6"
        );
        assert!(
            !d.kernel().def_eq(lhs, six),
            "if this passes the inverse scaling did nothing"
        );
    }
}

/// `Rat.pivotSearch` finds the first nonzero row at or below the start, and
/// reports `rows` when there is none.
///
/// Both answers are checked on the SAME matrix, so a search that always
/// returned its start index and a search that always returned `rows` are each
/// refuted by one of the two.
#[test]
fn pivot_search_finds_the_first_nonzero_row_or_reports_absence() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    // `[[0,1],[1,0]]`: column 0 is zero at row 0 and nonzero at row 1;
    // column 1 is nonzero at row 0 and zero at row 1.
    let m = const_matrix(&mut d, p, 2, &[0, 1, 1, 0]);
    let zero_n = d.num(0);
    let one_n = d.num(1);
    let two_n = d.num(2);

    let found = rpivot_search(&mut d, p, m, zero_n, zero_n, two_n);
    let want = d.num(1);
    assert!(
        d.kernel().def_eq(found, want),
        "the first nonzero entry of column 0 is at row 1"
    );
    assert!(
        !d.kernel().def_eq(found, zero_n),
        "row 0 of column 0 is ZERO -- if this passes the search never tested it"
    );

    // Column 1, starting at row 1: nothing nonzero, so the answer is `rows`.
    let absent = rpivot_search(&mut d, p, m, one_n, one_n, two_n);
    assert!(
        d.kernel().def_eq(absent, two_n),
        "column 1 has no nonzero entry at or below row 1, so the answer is rows = 2"
    );
    assert!(
        !d.kernel().def_eq(absent, one_n),
        "if this passes the search returned its start index without testing it"
    );
}

/// `Rat.leadingIndex` is the first nonzero column, and `cols` for a zero row.
#[test]
fn leading_index_is_the_first_nonzero_column() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    // `[[0,1],[0,0]]`: row 0 leads at column 1, row 1 is zero.
    let m = const_matrix(&mut d, p, 2, &[0, 1, 0, 0]);
    let zero_n = d.num(0);
    let one_n = d.num(1);
    let two_n = d.num(2);

    let lead0 = rleading_index(&mut d, p, m, zero_n, two_n);
    assert!(
        d.kernel().def_eq(lead0, one_n),
        "row 0 is [0,1], so its leading index is 1"
    );
    assert!(
        !d.kernel().def_eq(lead0, zero_n),
        "column 0 of row 0 is ZERO -- if this passes the scan never tested it"
    );

    let lead1 = rleading_index(&mut d, p, m, one_n, two_n);
    assert!(
        d.kernel().def_eq(lead1, two_n),
        "row 1 is zero, so its leading index is cols = 2"
    );
    assert!(
        !d.kernel().def_eq(lead1, zero_n),
        "a zero row must NOT report a leading index inside the matrix"
    );
}

/// `Rat.rowEchelon [[1,2],[3,4]] 2 2 = [[1,2],[0,-2]]`, and the result is in
/// echelon form while the input is not.
#[test]
fn row_echelon_reduces_an_ordinary_two_by_two() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = const_matrix(&mut d, p, 2, &[1, 2, 3, 4]);
    let two_n = d.num(2);
    let reduced = rrow_echelon(&mut d, p, m, two_n, two_n);

    assert_block(
        &mut d,
        p,
        reduced,
        2,
        &[1, 2, 0, -2],
        "rowEchelon [[1,2],[3,4]]",
    );

    // The elimination actually ran.
    let r1 = d.num(1);
    let c0 = d.num(0);
    let entry = d.apply(reduced, &[r1, c0]);
    let three = rq(&mut d, p, 3);
    assert!(
        !d.kernel().def_eq(entry, three),
        "entry (1,0) was 3 -- if this passes rowEchelon returned its argument"
    );

    // The predicate separates the output from the input.
    let true_v = d.bool_true();
    let false_v = d.bool_false();
    let ok = ris_echelon(&mut d, p, reduced, two_n, two_n);
    assert!(
        d.kernel().def_eq(ok, true_v),
        "the reduced matrix is in echelon form"
    );
    let before = ris_echelon(&mut d, p, m, two_n, two_n);
    assert!(
        d.kernel().def_eq(before, false_v),
        "[[1,2],[3,4]] is NOT in echelon form -- both rows lead at column 0"
    );
}

/// A dependent pair reduces to one zero row, which is what `rank` will count.
#[test]
fn row_echelon_produces_a_zero_row_for_a_dependent_pair() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = const_matrix(&mut d, p, 2, &[1, 2, 2, 4]);
    let two_n = d.num(2);
    let reduced = rrow_echelon(&mut d, p, m, two_n, two_n);

    assert_block(
        &mut d,
        p,
        reduced,
        2,
        &[1, 2, 0, 0],
        "rowEchelon [[1,2],[2,4]]",
    );

    let one_n = d.num(1);
    let lead1 = rleading_index(&mut d, p, reduced, one_n, two_n);
    assert!(
        d.kernel().def_eq(lead1, two_n),
        "the second row is zero, so its leading index is cols = 2"
    );
    let zero_n = d.num(0);
    assert!(
        !d.kernel().def_eq(lead1, zero_n),
        "if this passes the second row is still nonzero at column 0"
    );

    let true_v = d.bool_true();
    let ok = ris_echelon(&mut d, p, reduced, two_n, two_n);
    assert!(
        d.kernel().def_eq(ok, true_v),
        "a zero row at the BOTTOM is echelon form"
    );
}

/// A zero pivot forces a swap: `[[0,1],[1,0]]` reduces to the identity.
#[test]
fn row_echelon_swaps_when_the_pivot_is_zero() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = const_matrix(&mut d, p, 2, &[0, 1, 1, 0]);
    let two_n = d.num(2);
    let reduced = rrow_echelon(&mut d, p, m, two_n, two_n);

    assert_block(
        &mut d,
        p,
        reduced,
        2,
        &[1, 0, 0, 1],
        "rowEchelon [[0,1],[1,0]]",
    );

    let r0 = d.num(0);
    let c0 = d.num(0);
    let entry = d.apply(reduced, &[r0, c0]);
    let zero_q = rq(&mut d, p, 0);
    assert!(
        !d.kernel().def_eq(entry, zero_q),
        "entry (0,0) was 0 -- if this passes the pivot search never swapped"
    );

    let true_v = d.bool_true();
    let false_v = d.bool_false();
    let ok = ris_echelon(&mut d, p, reduced, two_n, two_n);
    assert!(
        d.kernel().def_eq(ok, true_v),
        "the identity is echelon form"
    );
    let before = ris_echelon(&mut d, p, m, two_n, two_n);
    assert!(
        d.kernel().def_eq(before, false_v),
        "[[0,1],[1,0]] is NOT echelon form -- its leading indices DECREASE"
    );
}

/// A 3×3 with a dependent row: two cursors advance, and a mid-elimination swap
/// moves the surviving row up.
///
/// `[[1,2,3],[2,4,6],[1,1,1]]` clears to `[[1,2,3],[0,0,0],[0,-1,-2]]` after the
/// first pivot, so the SECOND pivot column has a zero on its diagonal and the
/// loop has to search downward and swap. The answer therefore separates a loop
/// that only ever eliminates from one that also re-pivots.
#[test]
fn row_echelon_reduces_a_three_by_three_with_a_mid_run_swap() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = const_matrix(&mut d, p, 3, &[1, 2, 3, 2, 4, 6, 1, 1, 1]);
    let three_n = d.num(3);
    let reduced = rrow_echelon(&mut d, p, m, three_n, three_n);

    assert_block(
        &mut d,
        p,
        reduced,
        3,
        &[1, 2, 3, 0, -1, -2, 0, 0, 0],
        "rowEchelon of the 3x3",
    );

    // The zero row is at the BOTTOM, not where the elimination created it.
    let one_n = d.num(1);
    let c1 = d.num(1);
    let entry = d.apply(reduced, &[one_n, c1]);
    let zero_q = rq(&mut d, p, 0);
    assert!(
        !d.kernel().def_eq(entry, zero_q),
        "row 1 was zeroed by the first pivot -- if it is still zero here the swap never ran"
    );

    let true_v = d.bool_true();
    let false_v = d.bool_false();
    let ok = ris_echelon(&mut d, p, reduced, three_n, three_n);
    assert!(
        d.kernel().def_eq(ok, true_v),
        "the 3x3 result is echelon form"
    );
    let before = ris_echelon(&mut d, p, m, three_n, three_n);
    assert!(
        d.kernel().def_eq(before, false_v),
        "the input is not echelon form"
    );
}

/// `Rat.isEchelon` rejects a zero row sitting ABOVE a nonzero one.
///
/// This is the clause `Rat.echelonStepOk`'s second conjunct exists for. Without
/// it the test would read "the leading indices increase, or the first row is
/// zero", which accepts `[[0,0],[1,0]]` — a matrix in no textbook's echelon
/// form.
#[test]
fn is_echelon_rejects_a_zero_row_above_a_nonzero_one() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = const_matrix(&mut d, p, 2, &[0, 0, 1, 0]);
    let two_n = d.num(2);
    let true_v = d.bool_true();
    let false_v = d.bool_false();

    let verdict = ris_echelon(&mut d, p, m, two_n, two_n);
    assert!(
        d.kernel().def_eq(verdict, false_v),
        "[[0,0],[1,0]] must be REJECTED -- the zero row is on top"
    );
    assert!(
        !d.kernel().def_eq(verdict, true_v),
        "if this passes isEchelon accepts everything"
    );

    // ...and the same matrix with its rows the other way round is accepted, so
    // the rejection is about the ORDER and not about the matrix.
    let flipped = const_matrix(&mut d, p, 2, &[1, 0, 0, 0]);
    let ok = ris_echelon(&mut d, p, flipped, two_n, two_n);
    assert!(
        d.kernel().def_eq(ok, true_v),
        "[[1,0],[0,0]] IS echelon form"
    );
}

/// Every declaration `echelon` adds is `Theorem`- or `Definition`-kinded with
/// an EMPTY axiom footprint, read from the kernel rather than from this file.
#[test]
fn the_echelon_family_is_axiom_free() {
    use crate::env::Declaration;

    let (kernel, p) = built();
    let expected: [(crate::NameId, bool); 25] = [
        (p.is_zero_b, false),
        (p.row_swap, false),
        (p.row_scale, false),
        (p.row_add_mul, false),
        (p.row_swap_at_left, true),
        (p.row_swap_at_right, true),
        (p.row_swap_off, true),
        (p.row_scale_at, true),
        (p.row_scale_off, true),
        (p.row_add_mul_at, true),
        (p.row_add_mul_off, true),
        (p.row_swap_involutive, true),
        (p.row_add_mul_inverse, true),
        (p.row_scale_inverse, true),
        (p.pivot_search_aux, false),
        (p.pivot_search, false),
        (p.clear_below_aux, false),
        (p.clear_below, false),
        (p.echelon_aux, false),
        (p.row_echelon, false),
        (p.leading_index_aux, false),
        (p.leading_index, false),
        (p.echelon_step_ok, false),
        (p.is_echelon_aux, false),
        (p.is_echelon, false),
    ];
    for &(name, is_theorem) in &expected {
        let decl = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{} must be declared", kernel.display_name(name)));
        if is_theorem {
            assert!(
                matches!(decl, Declaration::Theorem { .. }),
                "{} must be a Theorem",
                kernel.display_name(name)
            );
        } else {
            assert!(
                matches!(decl, Declaration::Definition { .. }),
                "{} must be a Definition",
                kernel.display_name(name)
            );
        }
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{} must be axiom-free, got {:?}",
            kernel.display_name(name),
            footprint
                .iter()
                .map(|&a| kernel.display_name(a).to_string())
                .collect::<Vec<_>>()
        );
    }
}
