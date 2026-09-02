//! Evidence for [`super::clear_below`] — ADR-1554's obligation 3.
//!
//! Three things are checked, and they catch disjoint defects.
//!
//! 1. **The sweep computes what the theorem says**, by reduction at a 2×2 and
//!    two 3×3 instances. `Rat.clearBelow` is a `Definition`, so the trusted
//!    gate cannot tell you it is wrong — every entry it produces is read back
//!    against a hand-computed value, and each check has a control that must
//!    NOT be `def_eq`.
//! 2. **The theorem applies at fully free arguments**, in an explicit
//!    `LocalContext`, with a control refusing the statement a proof that forgot
//!    to apply the sweep would have.
//! 3. **The arithmetic core's hypothesis is load-bearing.** At `b = 0` the
//!    identity `a + (-(a/b)) * b = 0` is FALSE by reduction — `Rat.inv 0` is
//!    `0`, so the whole correction term vanishes and the answer is `a`. Without
//!    that check a `Not (b = 0)` hypothesis could be pure decoration.
//!
//! Every magnitude formed is a single-digit integer, so nothing here touches
//! the unary-numeral cost `CLAUDE.md` documents.

use super::RatPrelude;
use super::echelon::{rclear_below, rdiv};
use super::matrix_det::{mat_ty, rq};
use super::nullity_tests::rect_matrix;
use super::ops::{radd, req, rmul, rneg, rzero};
use crate::env::Declaration;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{BinderInfo, ExprId, Kernel, LocalContext, LocalDecl, build_rat_prelude};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("the rational prelude must build");
    (kernel, prelude)
}

/// Assert `M r c` reduces to `want` for every entry of a `rows × cols` block,
/// and that it does NOT reduce to a neighbouring value.
fn assert_block(
    d: &mut IntDev<'_>,
    p: RatPrelude,
    m: ExprId,
    rows: u32,
    cols: u32,
    want: &[i64],
    what: &str,
) {
    for r in 0..rows {
        for c in 0..cols {
            let ri = d.num(r);
            let ci = d.num(c);
            let lhs = d.apply(m, &[ri, ci]);
            let expected = want[(r * cols + c) as usize];
            let rhs = rq(d, p, expected);
            assert!(
                d.kernel().def_eq(lhs, rhs),
                "{what}: entry ({r},{c}) must be {expected}"
            );
            let other = rq(d, p, expected + 1);
            assert!(
                !d.kernel().def_eq(lhs, other),
                "{what}: entry ({r},{c}) must NOT also be {}",
                expected + 1
            );
        }
    }
}

/// `[[2,1],[4,3]]` swept from pivot `(0,0)`: row 1 becomes
/// `row1 - 2*row0 = [0, 1]`, and row 0 is untouched.
///
/// The pivot is `2` rather than `1` on purpose: with a unit pivot the
/// multiplier is `-M r pc` and a definition that forgot to DIVIDE would produce
/// the same answer.
#[test]
fn clear_below_zeroes_the_pivot_column_at_two_by_two() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 2, 2, &[2, 1, 4, 3]);
    let zero_n = d.num(0);
    let two_n = d.num(2);
    let swept = rclear_below(&mut d, p, m, zero_n, zero_n, two_n);

    assert_block(
        &mut d,
        p,
        swept,
        2,
        2,
        &[2, 1, 0, 1],
        "clearBelow [[2,1],[4,3]] from (0,0)",
    );
}

/// `[[1,2,3],[2,5,7],[3,7,11]]` swept from pivot `(0,0)`: both rows below lose
/// their first entry, and the rest of each row moves.
///
/// Two rows below the pivot is the case that distinguishes a sweep from a
/// single row operation: the second one is cleared against a matrix the FIRST
/// one already rewrote, and a definition that recursed on the original matrix
/// would still get row 1 right and row 2 wrong.
#[test]
fn clear_below_zeroes_every_row_below_the_pivot_at_three_by_three() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 3, 3, &[1, 2, 3, 2, 5, 7, 3, 7, 11]);
    let zero_n = d.num(0);
    let three_n = d.num(3);
    let swept = rclear_below(&mut d, p, m, zero_n, zero_n, three_n);

    assert_block(
        &mut d,
        p,
        swept,
        3,
        3,
        &[1, 2, 3, 0, 1, 1, 0, 1, 2],
        "clearBelow [[1,2,3],[2,5,7],[3,7,11]] from (0,0)",
    );
}

/// The same 3×3 swept from the MIDDLE pivot `(1,1)`: only row 2 changes.
///
/// This is the half of obligation 3 that says rows at or above the pivot are
/// untouched (`Rat.clearBelow_off`). A sweep that started at `pr` rather than
/// `succ pr` would clear the pivot row against itself and turn row 1 into
/// zeroes; a sweep that started at `0` would rewrite row 0 as well.
#[test]
fn clear_below_from_a_middle_pivot_leaves_the_rows_above_alone() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 3, 3, &[1, 2, 3, 2, 5, 7, 3, 7, 11]);
    let one_n = d.num(1);
    let three_n = d.num(3);
    let swept = rclear_below(&mut d, p, m, one_n, one_n, three_n);

    // row2 := row2 - (7/5)*row1 = [3 - 14/5, 0, 11 - 49/5] — only the pivot
    // column is asserted as an exact integer; the two rows above must be
    // byte-for-byte the input.
    assert_block(
        &mut d,
        p,
        swept,
        2,
        3,
        &[1, 2, 3, 2, 5, 7],
        "clearBelow from (1,1) must not touch rows 0 and 1",
    );

    let two_n = d.num(2);
    let cleared = d.apply(swept, &[two_n, one_n]);
    let rat_zero = rzero(&mut d, p);
    assert!(
        d.kernel().def_eq(cleared, rat_zero),
        "entry (2,1) must be cleared to 0"
    );

    // The control: column 0 of row 2 is NOT cleared — the sweep touches one
    // column's worth of guarantee, not the whole row.
    let zero_n = d.num(0);
    let untouched_column = d.apply(swept, &[two_n, zero_n]);
    assert!(
        !d.kernel().def_eq(untouched_column, rat_zero),
        "entry (2,0) must NOT be zero -- the pivot column is (1), not (0)"
    );
}

/// The arithmetic core computes, and its `b ≠ 0` hypothesis is load-bearing.
///
/// At `(a, b) = (3, 2)` the expression reduces to `0`. At `b = 0` it reduces
/// to `3`: `Rat.inv 0` is `0`, so the correction term is `(-(3*0)) * 0 = 0` and
/// the identity is FALSE. A conditional theorem whose hypothesis every argument
/// satisfies is an unconditional theorem with a decoration, and this rules that
/// out by reduction rather than by assertion.
#[test]
fn the_arithmetic_core_computes_and_its_hypothesis_is_load_bearing() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let core = |d: &mut IntDev<'_>, a: i64, b: i64| -> ExprId {
        let av = rq(d, p, a);
        let bv = rq(d, p, b);
        let quotient = rdiv(d, p, av, bv);
        let factor = rneg(d, quotient);
        let scaled = rmul(d, factor, bv);
        radd(d, av, scaled)
    };

    let rat_zero = rzero(&mut d, p);

    let good = core(&mut d, 3, 2);
    assert!(
        d.kernel().def_eq(good, rat_zero),
        "3 + (-(3/2)) * 2 must reduce to 0"
    );

    let degenerate = core(&mut d, 3, 0);
    let three = rq(&mut d, p, 3);
    assert!(
        d.kernel().def_eq(degenerate, three),
        "at b = 0 the correction vanishes and the value is 3"
    );
    assert!(
        !d.kernel().def_eq(degenerate, rat_zero),
        "at b = 0 the identity is FALSE -- the hypothesis is load-bearing"
    );
}

/// `Rat.clearBelow_zero` applies at fully free arguments, and concludes about
/// the SWEPT matrix.
///
/// The control is the statement a proof that forgot to apply the sweep would
/// have — `M q pc = 0`, which is false for a general matrix and would make the
/// theorem say nothing about `clearBelow` at all.
#[test]
fn clear_below_zero_applies_at_free_variables_with_an_unswept_control() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let anon = d.anon_name();
    let nat = d.nat_ty();
    let mty = mat_ty(&mut d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let pr_fv = d.fresh_fvar();
    let pr = d.kernel().fvar(pr_fv);
    let pc_fv = d.fresh_fvar();
    let pc = d.kernel().fvar(pc_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let q_fv = d.fresh_fvar();
    let q = d.kernel().fvar(q_fv);

    let t1 = NatOps::lt(&mut d, pr, q);
    let t2 = NatOps::lt(&mut d, q, rows);
    let pivot = d.apply(m, &[pr, pc]);
    let rat_zero = rzero(&mut d, p);
    let pivot_eq = req(&mut d, pivot, rat_zero);
    let t3 = d.not(pivot_eq);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let h3_fv = d.fresh_fvar();
    let h3 = d.kernel().fvar(h3_fv);

    let mut ctx = LocalContext::new();
    for (fvar, ty) in [
        (m_fv, mty),
        (pr_fv, nat),
        (pc_fv, nat),
        (rows_fv, nat),
        (q_fv, nat),
        (h1_fv, t1),
        (h2_fv, t2),
        (h3_fv, t3),
    ] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }

    let applied = d.const_app(p.clear_below_zero, &[m, pr, pc, rows, q, h1, h2, h3]);
    let inferred = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("Rat.clearBelow_zero must apply at free variables");

    let swept = d.const_app(p.clear_below, &[m, pr, pc, rows]);
    let entry = d.apply(swept, &[q, pc]);
    let want = req(&mut d, entry, rat_zero);
    assert!(
        d.kernel().def_eq(inferred, want),
        "the conclusion must be about the SWEPT matrix at (q, pc)"
    );

    let unswept = d.apply(m, &[q, pc]);
    let control = req(&mut d, unswept, rat_zero);
    assert!(
        !d.kernel().def_eq(inferred, control),
        "negative control: the conclusion must NOT be about the original matrix"
    );
}

/// Every obligation-3 declaration rests on zero axioms.
#[test]
fn the_obligation_three_family_is_axiom_free() {
    let (kernel, p) = built();
    for name in [
        p.add_neg_div_mul_cancel,
        p.clear_below_aux_off,
        p.clear_below_off,
        p.clear_below_aux_zero,
        p.clear_below_zero,
    ] {
        assert!(
            kernel.axiom_footprint(name).is_empty(),
            "{} must rest on zero axioms",
            kernel.display_name(name)
        );
    }
}

/// The two headline statements say what obligation 3 asks for, pinned by their
/// rendered types.
///
/// The forbidden substrings matter more than the required ones. `clearBelow_off`
/// must NOT mention the pivot column in its conclusion (it holds at EVERY
/// column), and `clearBelow_zero` must NOT be stated with `Le pr q` — at
/// `pr = q` it would be false, because the pivot row is not cleared against
/// itself.
#[test]
fn the_obligation_three_statements_say_what_they_claim() {
    let (kernel, p) = built();
    let rendered = |name| {
        let ty = match kernel
            .environment()
            .get(name)
            .expect("the declaration must exist")
        {
            Declaration::Theorem { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };

    let off = rendered(p.clear_below_off);
    assert!(
        off.contains("AxNat.le x4 x1"),
        "clearBelow_off's hypothesis must be `Le q pr`: {off}"
    );
    assert!(
        off.contains("Eq.{1} Rat (Rat.clearBelow x0 x1 x2 x3 x4 x5) (x0 x4 x5)"),
        "clearBelow_off must equate the swept and original entries at (q, c): {off}"
    );
    assert!(
        !off.contains("AxNat.lt x4 x1"),
        "clearBelow_off's hypothesis is `Le q pr`, NOT `Lt q pr` -- the pivot \
         row itself is untouched: {off}"
    );

    let zero = rendered(p.clear_below_zero);
    assert!(
        zero.contains("AxNat.lt x1 x4"),
        "clearBelow_zero must require the target row strictly BELOW the pivot \
         row: {zero}"
    );
    assert!(
        zero.contains("AxNat.lt x4 x3"),
        "clearBelow_zero must require the target row inside the row count: {zero}"
    );
    assert!(
        zero.contains("Not (Eq.{1} Rat (x0 x1 x2) Rat.zero)"),
        "clearBelow_zero must require the pivot entry nonzero: {zero}"
    );
    assert!(
        zero.contains("Eq.{1} Rat (Rat.clearBelow x0 x1 x2 x3 x4 x2) Rat.zero"),
        "clearBelow_zero must conclude that the swept entry in the PIVOT \
         column is zero: {zero}"
    );
    assert!(
        !zero.contains("AxNat.le x1 x4"),
        "clearBelow_zero must NOT be stated with `Le pr q` -- at pr = q it is \
         false: {zero}"
    );
}
