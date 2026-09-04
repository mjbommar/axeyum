//! Evaluation tests for [`super::rank`], plus the invariance checks that ARE
//! available without `rowEchelon_isEchelon`.
//!
//! **The trusted gate cannot tell you a `Definition` is wrong.** `Rat.rank` has
//! type `Mat → Nat → Nat → Nat` whether it counts nonzero rows, counts every
//! row, or returns `0`. So every test below REDUCES `rank` at a concrete matrix
//! whose rank was worked out by hand, and carries a control that must FAIL to be
//! defeq.
//!
//! ## What discriminates
//!
//! The five matrices are chosen so that no single wrong definition passes them
//! all:
//!
//! - `[[1,2],[3,4]]` → `2` and `[[0,0],[0,0]]` → `0` together kill "return
//!   `rows`" and "return `0`".
//! - `[[1,2],[2,4]]` → `1` is the one that needs the zero row to be EXCLUDED:
//!   its echelon form is `[[1,2],[0,0]]`, so a count that ignored the leading
//!   index would say `2`.
//! - `[[1,2,3],[2,4,6],[1,1,1]]` → `2` at 3×3 needs the elimination's
//!   mid-run swap as well; a count over the INPUT rather than the echelon form
//!   would say `3`.
//! - the 3×3 identity → `3` is the only one that separates "count the nonzero
//!   rows" from "count the rows below the last pivot".
//!
//! ## Invariance
//!
//! Rank invariance under the three elementary row operations is NOT a theorem
//! in this tree, and `super::rank`'s module doc plus ADR-1555 say why. It is
//! still a decidable statement at a concrete matrix, so
//! [`rank_is_invariant_under_each_row_operation_at_two_by_two`] checks it by
//! reduction at 2×2 — for each of `rowSwap`, `rowScale` and `rowAddMul`,
//! against a control that the operated matrix genuinely differs from the
//! original. That is the decidable-fragment row of the graded family
//! (ADR-0603), not a substitute for the general statement.

use super::RatPrelude;
use super::echelon::{rleading_index, rrow_add_mul, rrow_echelon, rrow_scale, rrow_swap};
use super::matrix_det::{const_matrix, rq};
use super::rank::{rnonzero_row_b, rrank};
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{BinderInfo, ExprId, Kernel, LocalContext, LocalDecl, build_rat_prelude};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("the rational prelude must build");
    (kernel, prelude)
}

/// Assert `rank M k k` reduces to `want` and NOT to `want ± 1`.
///
/// The control is what makes this an evaluation test rather than a type check:
/// a `rank` that returned a constant would satisfy one row of the table and
/// fail its neighbour, and a `rank` off by one is caught here rather than by a
/// later theorem that never runs the definition.
fn assert_rank(d: &mut IntDev<'_>, p: RatPrelude, m: ExprId, k: u32, want: u32, what: &str) {
    let dim = d.num(k);
    let value = rrank(d, p, m, dim, dim);
    let expected = d.num(want);
    assert!(
        d.kernel().def_eq(value, expected),
        "{what}: rank must be {want}"
    );
    let neighbour = d.num(want + 1);
    assert!(
        !d.kernel().def_eq(value, neighbour),
        "{what}: rank must NOT also be {} -- rank is not discriminating here",
        want + 1
    );
    if want > 0 {
        let below = d.num(want - 1);
        assert!(
            !d.kernel().def_eq(value, below),
            "{what}: rank must NOT also be {}",
            want - 1
        );
    }
}

/// `Rat.rank` counts the nonzero rows of the echelon form, at five matrices
/// whose ranks are pairwise discriminating.
#[test]
fn rank_counts_the_nonzero_rows_of_the_echelon_form() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let full2 = const_matrix(&mut d, p, 2, &[1, 2, 3, 4]);
    assert_rank(&mut d, p, full2, 2, 2, "[[1,2],[3,4]]");

    let dependent2 = const_matrix(&mut d, p, 2, &[1, 2, 2, 4]);
    assert_rank(&mut d, p, dependent2, 2, 1, "[[1,2],[2,4]]");

    let zero2 = const_matrix(&mut d, p, 2, &[0, 0, 0, 0]);
    assert_rank(&mut d, p, zero2, 2, 0, "[[0,0],[0,0]]");

    let dependent3 = const_matrix(&mut d, p, 3, &[1, 2, 3, 2, 4, 6, 1, 1, 1]);
    assert_rank(&mut d, p, dependent3, 3, 2, "[[1,2,3],[2,4,6],[1,1,1]]");

    let id3 = const_matrix(&mut d, p, 3, &[1, 0, 0, 0, 1, 0, 0, 0, 1]);
    assert_rank(&mut d, p, id3, 3, 3, "the 3x3 identity");
}

/// `Rat.nonzeroRowB` separates a nonzero row from a zero one, on the SAME
/// echelon form.
///
/// `[[1,2],[2,4]]` reduces to `[[1,2],[0,0]]`, so row `0` is nonzero and row
/// `1` is not. A predicate that was constantly `true` or constantly `false`
/// passes exactly one of these two assertions.
#[test]
fn nonzero_row_b_separates_the_zero_row_from_the_nonzero_one() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = const_matrix(&mut d, p, 2, &[1, 2, 2, 4]);
    let two_n = d.num(2);
    let reduced = rrow_echelon(&mut d, p, m, two_n, two_n);

    let true_v = d.bool_true();
    let false_v = d.bool_false();

    let r0 = d.num(0);
    let row0 = rnonzero_row_b(&mut d, p, reduced, two_n, r0);
    assert!(
        d.kernel().def_eq(row0, true_v),
        "row 0 of [[1,2],[0,0]] is nonzero"
    );
    assert!(
        !d.kernel().def_eq(row0, false_v),
        "nonzeroRowB must not be constantly false"
    );

    let r1 = d.num(1);
    let row1 = rnonzero_row_b(&mut d, p, reduced, two_n, r1);
    assert!(
        d.kernel().def_eq(row1, false_v),
        "row 1 of [[1,2],[0,0]] is zero"
    );
    assert!(
        !d.kernel().def_eq(row1, true_v),
        "nonzeroRowB must not be constantly true"
    );

    // The leading index is the quantity being compared, and it is `cols` on the
    // zero row -- which is what makes the strict comparison the nonzero test.
    let lead1 = rleading_index(&mut d, p, reduced, r1, two_n);
    assert!(
        d.kernel().def_eq(lead1, two_n),
        "the zero row's leading index must be cols = 2"
    );
}

/// `Rat.nonzeroRowB E 0 r` is `false` at a SYMBOLIC matrix and row.
///
/// The `cols = 0` corner reduces without evaluating the leading index at all
/// (`Nat.ble (succ _) zero` is `false` by ι), which is what makes
/// `Rat.rank_zero_cols` a short induction rather than a fight with the
/// elimination.
#[test]
fn nonzero_row_b_is_false_with_no_columns_symbolically() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let nat = d.nat_ty();
    let mty = super::matrix_det::mat_ty(&mut d);
    let anon = d.anon_name();

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let zero_n = d.zero();
    let test = rnonzero_row_b(&mut d, p, e, zero_n, r);
    let false_v = d.bool_false();
    let true_v = d.bool_true();
    assert!(
        d.kernel().def_eq(test, false_v),
        "with no columns every row is zero, symbolically"
    );
    assert!(
        !d.kernel().def_eq(test, true_v),
        "if this passes Bool has collapsed and every Bool test here is vacuous"
    );

    // And the declared theorem says the same thing, at genuinely free variables.
    let proof = d.const_app(p.nonzero_row_b_zero_cols, &[e, r]);
    let expected = d.bool_eq(test, false_v);
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: e_fv,
        name: anon,
        ty: mty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: r_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let inferred = d
        .kernel()
        .infer_in(proof, &mut ctx)
        .expect("nonzeroRowB_zero_cols must apply at a free matrix and row");
    assert!(
        d.kernel().def_eq(inferred, expected),
        "nonzeroRowB_zero_cols must prove nonzeroRowB E 0 r = false"
    );
}

/// `Rat.rank_le_rows` applies concretely and at genuinely free arguments.
#[test]
fn rank_le_rows_applies_concretely_and_symbolically() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = const_matrix(&mut d, p, 2, &[1, 2, 2, 4]);
    let two_n = d.num(2);
    let proof = d.const_app(p.rank_le_rows, &[m, two_n, two_n]);
    let value = rrank(&mut d, p, m, two_n, two_n);
    let expected = NatOps::le(&mut d, value, two_n);
    let inferred = d
        .kernel()
        .infer(proof)
        .expect("rank_le_rows must type-check at a concrete matrix");
    assert!(
        d.kernel().def_eq(inferred, expected),
        "rank_le_rows must prove Le (rank M 2 2) 2"
    );
    // Not vacuous: the bound is strict here, so this is not `Le 2 2`.
    let one_n = d.num(1);
    assert!(
        d.kernel().def_eq(value, one_n),
        "[[1,2],[2,4]] has rank 1, so the bound Le 1 2 is strict"
    );

    let nat = d.nat_ty();
    let mty = super::matrix_det::mat_ty(&mut d);
    let anon = d.anon_name();
    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);

    let sym_proof = d.const_app(p.rank_le_rows, &[a, rows, cols]);
    let sym_rank = rrank(&mut d, p, a, rows, cols);
    let sym_expected = NatOps::le(&mut d, sym_rank, rows);
    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: a_fv,
        name: anon,
        ty: mty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: rows_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: cols_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });
    let sym_inferred = d
        .kernel()
        .infer_in(sym_proof, &mut ctx)
        .expect("rank_le_rows must apply at a free matrix and free dimensions");
    assert!(
        d.kernel().def_eq(sym_inferred, sym_expected),
        "rank_le_rows must hold symbolically"
    );
}

/// The two degenerate dimensions, symbolically in the matrix.
///
/// `rank_zero_cols` is the only place `rank ≤ cols` is available at all, and
/// there it is an EQUALITY. A definition that counted rows without consulting
/// the leading index would satisfy `rank_le_rows` and fail this.
#[test]
fn rank_is_zero_at_both_degenerate_dimensions() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let nat = d.nat_ty();
    let mty = super::matrix_det::mat_ty(&mut d);
    let anon = d.anon_name();

    let a_fv = d.fresh_fvar();
    let a = d.kernel().fvar(a_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let zero_n = d.zero();

    let mut ctx = LocalContext::new();
    ctx.push(LocalDecl {
        fvar: a_fv,
        name: anon,
        ty: mty,
        info: BinderInfo::Default,
    });
    ctx.push(LocalDecl {
        fvar: n_fv,
        name: anon,
        ty: nat,
        info: BinderInfo::Default,
    });

    // No rows.
    let no_rows = rrank(&mut d, p, a, zero_n, n);
    let want_zero = d.zero();
    let expect_rows = d.eq(no_rows, want_zero);
    let proof_rows = d.const_app(p.rank_zero_rows, &[a, n]);
    let inferred_rows = d
        .kernel()
        .infer_in(proof_rows, &mut ctx)
        .expect("rank_zero_rows must apply at a free matrix and free column count");
    assert!(
        d.kernel().def_eq(inferred_rows, expect_rows),
        "rank_zero_rows must prove rank A 0 cols = 0"
    );

    // No columns -- the case that needs the induction.
    let no_cols = rrank(&mut d, p, a, n, zero_n);
    let expect_cols = d.eq(no_cols, want_zero);
    let proof_cols = d.const_app(p.rank_zero_cols, &[a, n]);
    let inferred_cols = d
        .kernel()
        .infer_in(proof_cols, &mut ctx)
        .expect("rank_zero_cols must apply at a free matrix and free row count");
    assert!(
        d.kernel().def_eq(inferred_cols, expect_cols),
        "rank_zero_cols must prove rank A rows 0 = 0"
    );

    // Non-vacuity: at a nonzero column count the same matrix shape is NOT
    // forced to rank 0, so neither statement is true for trivial reasons.
    let m = const_matrix(&mut d, p, 2, &[1, 2, 3, 4]);
    let two_n = d.num(2);
    let real_rank = rrank(&mut d, p, m, two_n, two_n);
    let zero_r = d.zero();
    assert!(
        !d.kernel().def_eq(real_rank, zero_r),
        "if this passes rank is constantly 0 and both degenerate laws are vacuous"
    );
}

/// Rank is unchanged by each of the three elementary row operations, at 2×2,
/// **by reduction**.
///
/// This is the decidable-fragment form (ADR-0603 row 3). The general statement
/// is not available: `echelon.rs`'s inverse laws are POINTWISE equalities and
/// this kernel has no `funext`, so they cannot be transported under `rank` —
/// ADR-1555. Each case carries a control that the operation actually changed
/// the matrix, so "the operation is the identity" cannot pass.
///
/// Every magnitude formed is a single digit, so this is not the unary-numeral
/// cliff `CLAUDE.md` documents. Like `det_mul_tests.rs`'s
/// `mat_subst_rows_replaces_the_window_by_relative_index`, the abort is the
/// test's OWN bulk — two matrices, each run through three row operations and
/// a `rank` reduction, all with locals live for the rest of an unoptimized
/// function body — on top of a `rat` prelude build pinned with zero debug
/// margin (`artifacts/kernel-stack-envelope.tsv`). Measured 2026-09-03: aborts
/// at the default 2,097,152, passes at 4,194,304. Runs on
/// [`crate::on_a_deep_stack`] for the same reason.
#[test]
fn rank_is_invariant_under_each_row_operation_at_two_by_two() {
    crate::on_a_deep_stack(rank_is_invariant_under_each_row_operation_at_two_by_two_body);
}

fn rank_is_invariant_under_each_row_operation_at_two_by_two_body() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let zero_n = d.num(0);
    let one_n = d.num(1);

    // A rank-2 matrix and a rank-1 one, so an operation that collapsed the
    // matrix and one that inflated it are both visible.
    for (entries, want) in [([1_i64, 2, 3, 4], 2_u32), ([1, 2, 2, 4], 1)] {
        let base = const_matrix(&mut d, p, 2, &entries);
        assert_rank(&mut d, p, base, 2, want, "the base matrix");

        // rowSwap 0 1.
        let swapped = rrow_swap(&mut d, p, zero_n, one_n, base);
        assert_rank(&mut d, p, swapped, 2, want, "rowSwap 0 1");
        let moved = d.apply(swapped, &[zero_n, zero_n]);
        let was = rq(&mut d, p, entries[0]);
        assert!(
            !d.kernel().def_eq(moved, was),
            "rowSwap left entry (0,0) alone -- the invariance check is vacuous"
        );

        // rowScale 0 3.
        let three_q = rq(&mut d, p, 3);
        let scaled = rrow_scale(&mut d, p, zero_n, three_q, base);
        assert_rank(&mut d, p, scaled, 2, want, "rowScale 0 3");
        let scaled_entry = d.apply(scaled, &[zero_n, zero_n]);
        let was0 = rq(&mut d, p, entries[0]);
        assert!(
            !d.kernel().def_eq(scaled_entry, was0),
            "rowScale left entry (0,0) alone -- the invariance check is vacuous"
        );

        // rowAddMul 1 0 2 -- row 1 += 2 * row 0.
        let two_q = rq(&mut d, p, 2);
        let combined = rrow_add_mul(&mut d, p, one_n, zero_n, two_q, base);
        assert_rank(&mut d, p, combined, 2, want, "rowAddMul 1 0 2");
        let combined_entry = d.apply(combined, &[one_n, zero_n]);
        let was2 = rq(&mut d, p, entries[2]);
        assert!(
            !d.kernel().def_eq(combined_entry, was2),
            "rowAddMul left entry (1,0) alone -- the invariance check is vacuous"
        );
    }

    // The scaling factor 0 is NOT rank-preserving, and the test says so: this
    // is the boundary the `k ≠ 0` hypothesis of `rowScale_inverse` marks.
    let base = const_matrix(&mut d, p, 2, &[1, 2, 3, 4]);
    let zero_q = rq(&mut d, p, 0);
    let killed = rrow_scale(&mut d, p, zero_n, zero_q, base);
    assert_rank(&mut d, p, killed, 2, 1, "rowScale 0 0 -- rank DROPS");
}

/// Every declaration `rank` adds is `Theorem`- or `Definition`-kinded with an
/// EMPTY axiom footprint, read from the kernel rather than from this file.
#[test]
fn the_rank_family_is_axiom_free() {
    use crate::env::Declaration;

    let (kernel, p) = built();
    let expected: [(crate::NameId, bool); 9] = [
        (p.nonzero_row_b, false),
        (p.nonzero_row_b_eq_ble, true),
        (p.nonzero_row_b_zero_cols, true),
        (p.rank, false),
        (p.rank_eq_count_range, true),
        (p.rank_le_rows, true),
        (p.rank_zero_rows, true),
        (p.count_range_nonzero_row_b_zero, true),
        (p.rank_zero_cols, true),
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
