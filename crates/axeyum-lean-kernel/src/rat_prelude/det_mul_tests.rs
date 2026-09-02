//! Evaluation tests for [`super::det_mul`]'s two new `Definition`s.
//!
//! **The trusted gate cannot tell you a `Definition` is wrong.**
//! `Nat -> (Nat -> Rat) -> Mat -> Mat` is that type whatever `Rat.matSetRow`
//! returns, and the five-argument `Rat.matSubstRows` is likewise well-typed
//! whatever it computes. Everything below reduces the two at concrete
//! arguments and compares against values read off by hand.
//!
//! ## What discriminates
//!
//! Both definitions are index surgery, so the defects that matter are all
//! off-by-one or transposition:
//!
//! - the row `matSetRow` writes (`t`, not `t ± 1`) and that it writes NOTHING
//!   else — checked at all three rows of a 3×3 whose nine entries are pairwise
//!   distinct, so a wrong row is separated by a wrong number;
//! - which rows `matSubstRows` covers (`[s, s+m)`), which SOURCE row of `B`
//!   each of them takes (`g i` at RELATIVE index `i`, not absolute), and that
//!   the rows outside the window survive. The map `g` is chosen NON-monotone
//!   and non-identity (`g 0 = 2`, `g 1 = 0`) so a "copy row `s+i` of `B`"
//!   defect and a "use the absolute index" defect both give different numbers.
//!
//! Every magnitude formed is a single-digit integer, so none of this touches
//! the unary numeral cost `CLAUDE.md` documents.

use super::RatPrelude;
use super::det_mul::{rmat_set_row, rmat_subst_rows};
use super::matrix_det::{const_matrix, rq};
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{ExprId, Kernel, build_rat_prelude};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("the rational prelude must build");
    (kernel, prelude)
}

/// The 3×3 matrix `[[1,2,3],[4,5,6],[7,8,9]]` — nine pairwise distinct
/// entries, so every index mistake shows up as a wrong number.
fn base_matrix(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    const_matrix(d, p, 3, &[1, 2, 3, 4, 5, 6, 7, 8, 9])
}

/// The 3×3 matrix `[[10,20,30],[40,50,60],[70,80,90]]` — the substitution
/// source, disjoint in value from [`base_matrix`] so a row that came from the
/// wrong matrix is visible.
fn source_matrix(d: &mut IntDev<'_>, p: RatPrelude) -> ExprId {
    const_matrix(d, p, 3, &[10, 20, 30, 40, 50, 60, 70, 80, 90])
}

/// `Rat.matSetRow` writes exactly row `t` and leaves every other entry alone.
#[test]
fn mat_set_row_writes_exactly_one_row() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = base_matrix(&mut d, p);
    // h := fun c => 100 + c is not available without arithmetic on the column,
    // so use the constant row `[0,0,0]`'s distinguishing neighbour instead: a
    // row that is `-1` everywhere, a value the base matrix never takes.
    let nat = d.nat_ty();
    let row = {
        let minus_one = rq(&mut d, p, -1);
        let c_fv = d.fresh_fvar();
        d.lam_fv(c_fv, nat, minus_one)
    };
    let one_n = d.num(1);
    let set = rmat_set_row(&mut d, p, one_n, row, m);

    // Row 1 became -1 at every column.
    for c in 0..3u32 {
        let idx = d.num(c);
        let one_n = d.num(1);
        let lhs = d.apply(set, &[one_n, idx]);
        let rhs = rq(&mut d, p, -1);
        assert!(
            d.kernel().def_eq(lhs, rhs),
            "matSetRow 1 (fun _ => -1) M 1 {c} must be -1"
        );
    }
    // Rows 0 and 2 are untouched, entry by entry.
    for (r, expected) in [(0u32, [1_i64, 2, 3]), (2, [7, 8, 9])] {
        for (c, want) in expected.iter().enumerate() {
            let ri = d.num(r);
            let ci = d.num(u32::try_from(c).expect("small"));
            let lhs = d.apply(set, &[ri, ci]);
            let rhs = rq(&mut d, p, *want);
            assert!(
                d.kernel().def_eq(lhs, rhs),
                "matSetRow 1 h M {r} {c} must still be {want}"
            );
        }
    }

    // Non-vacuity, through the same `def_eq`: the row that WAS written is not
    // its old value, and an unwritten row is not the new one.
    let one_n = d.num(1);
    let zero_n = d.num(0);
    let written = d.apply(set, &[one_n, zero_n]);
    let old = rq(&mut d, p, 4);
    assert!(
        !d.kernel().def_eq(written, old),
        "row 1 column 0 was 4 before the write -- if this passes nothing was written"
    );
    let two_n = d.num(2);
    let untouched = d.apply(set, &[two_n, zero_n]);
    let new = rq(&mut d, p, -1);
    assert!(
        !d.kernel().def_eq(untouched, new),
        "row 2 must NOT have been written -- if this passes the write is not row-local"
    );
}

/// `Rat.matSubstRows B m s g M` replaces exactly the rows `[s, s+m)`, taking
/// row `g i` of `B` at RELATIVE index `i`.
///
/// `s = 1`, `m = 2`, `g 0 = 2`, `g 1 = 0`: rows 1 and 2 of the result must be
/// rows 2 and 0 of `B` — `[70,80,90]` then `[10,20,30]` — and row 0 must still
/// be `[1,2,3]`. Both plausible index defects are separated by that choice:
/// using the ABSOLUTE row index would put `g 1 = 0`'s row at row 1, and
/// copying `B`'s row `s+i` would give `[40,50,60]` then `[70,80,90]`.
#[test]
fn mat_subst_rows_replaces_the_window_by_relative_index() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = base_matrix(&mut d, p);
    let b = source_matrix(&mut d, p);
    let nat = d.nat_ty();

    // g := fun i => if i = 0 then 2 else 0.
    let g = {
        let i_fv = d.fresh_fvar();
        let i = d.kernel().fvar(i_fv);
        let zero_n = d.num(0);
        let two_n = d.num(2);
        let cond = NatOps::beq(&mut d, i, zero_n);
        let body = d.bool_select_nat(cond, two_n, zero_n);
        d.lam_fv(i_fv, nat, body)
    };

    let two = d.num(2);
    let one = d.num(1);
    let subst = rmat_subst_rows(&mut d, p, b, two, one, g, m);

    let expected: [(u32, [i64; 3]); 3] = [(0, [1, 2, 3]), (1, [70, 80, 90]), (2, [10, 20, 30])];
    for (r, row) in expected {
        for (c, want) in row.iter().enumerate() {
            let ri = d.num(r);
            let ci = d.num(u32::try_from(c).expect("small"));
            let lhs = d.apply(subst, &[ri, ci]);
            let rhs = rq(&mut d, p, *want);
            assert!(
                d.kernel().def_eq(lhs, rhs),
                "matSubstRows B 2 1 g M {r} {c} must be {want}"
            );
        }
    }

    // Negative controls, all through the same `def_eq`.
    let one_r = d.num(1);
    let zero_c = d.num(0);
    let at_1_0 = d.apply(subst, &[one_r, zero_c]);
    let absolute = rq(&mut d, p, 40);
    assert!(
        !d.kernel().def_eq(at_1_0, absolute),
        "40 is B's row 1 -- if this passes the source row is the ABSOLUTE index, not g 0"
    );
    let unmoved = rq(&mut d, p, 4);
    assert!(
        !d.kernel().def_eq(at_1_0, unmoved),
        "4 is M's own row 1 -- if this passes the window did not include row 1"
    );
    let zero_r = d.num(0);
    let at_0_0 = d.apply(subst, &[zero_r, zero_c]);
    let overwritten = rq(&mut d, p, 70);
    assert!(
        !d.kernel().def_eq(at_0_0, overwritten),
        "row 0 is BELOW the window and must survive -- if this passes `s` is ignored"
    );

    // The empty window is the identity, and the two boundary rows of a
    // one-row window pin `[s, s+m)` at both ends.
    let zero_m = d.num(0);
    let empty = rmat_subst_rows(&mut d, p, b, zero_m, one, g, m);
    for r in 0..3u32 {
        let ri = d.num(r);
        let ci = d.num(0);
        let lhs = d.apply(empty, &[ri, ci]);
        let want = [1_i64, 4, 7][usize::try_from(r).expect("small")];
        let rhs = rq(&mut d, p, want);
        assert!(
            d.kernel().def_eq(lhs, rhs),
            "matSubstRows B 0 s g M is M, so row {r} column 0 must still be {want}"
        );
    }
    let one_m = d.num(1);
    let single = rmat_subst_rows(&mut d, p, b, one_m, one, g, m);
    let two_r = d.num(2);
    let past_window = d.apply(single, &[two_r, zero_c]);
    let still_m = rq(&mut d, p, 7);
    assert!(
        d.kernel().def_eq(past_window, still_m),
        "a one-row window at s = 1 must leave row 2 alone"
    );
}

/// Every declaration `det_mul` adds is `Theorem`- or `Definition`-kinded with
/// an EMPTY axiom footprint, read from the kernel.
#[test]
fn the_det_mul_family_is_axiom_free() {
    use crate::env::Declaration;

    let (kernel, p) = built();
    let expected: [(crate::NameId, bool); 9] = [
        (p.mat_set_row, false),
        (p.mat_set_row_at, true),
        (p.mat_set_row_off, true),
        (p.mat_subst_rows, false),
        (p.mat_subst_rows_below, true),
        (p.mat_subst_rows_at, true),
        (p.sum_maps_congr_maps_into, true),
        (p.det_mat_mul_expand, true),
        (p.det_mat_mul, true),
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

/// `Rat.det_matMul` states the general product law and nothing weaker.
///
/// The declared type is compared against a statement built here from scratch —
/// `∀ n A B, det (matMul A B n) n = det A n * det B n` — rather than against a
/// pinned string, so a drift in either the dimension or the argument order
/// fails rather than reformats. Two variants that a careless restatement could
/// produce are asserted NOT to be it, through the same `def_eq`: the dimension
/// of the product's determinant raised by one, and the two matrices swapped in
/// `matMul` (a different proposition, since `Rat.matMul` is not definitionally
/// commutative — its truth is beside the point here).
#[test]
fn det_mat_mul_states_the_general_product_law() {
    use crate::env::Declaration;
    use crate::rat_prelude::matrix_det::rdet;
    use crate::rat_prelude::ops::{req, rmul};

    let (mut kernel, p) = built();
    let declared = match kernel.environment().get(p.det_mat_mul).expect("declared") {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem"),
    };

    let mut d = IntDev::new(&mut kernel, p.int);
    let nat = d.nat_ty();
    let mty = crate::rat_prelude::matrix_det::mat_ty(&mut d);

    let build = |d: &mut IntDev<'_>, bump: bool, swap: bool| -> ExprId {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let product = if swap {
            d.const_app(p.mat_mul, &[b, a, n])
        } else {
            d.const_app(p.mat_mul, &[a, b, n])
        };
        let dim = if bump { d.succ(n) } else { n };
        let lhs = rdet(d, p, product, dim);
        let da = rdet(d, p, a, n);
        let db = rdet(d, p, b, n);
        let rhs = rmul(d, da, db);
        let eq = req(d, lhs, rhs);
        let over_b = d.pi_fv(b_fv, mty, eq);
        let over_a = d.pi_fv(a_fv, mty, over_b);
        d.pi_fv(n_fv, nat, over_a)
    };

    let expected = build(&mut d, false, false);
    assert!(
        d.kernel().def_eq(declared, expected),
        "Rat.det_matMul must state ∀ n A B, det (matMul A B n) n = det A n * det B n"
    );
    let bumped = build(&mut d, true, false);
    assert!(
        !d.kernel().def_eq(declared, bumped),
        "the product's determinant is taken at the SAME dimension the product uses"
    );
    let swapped = build(&mut d, false, true);
    assert!(
        !d.kernel().def_eq(declared, swapped),
        "the two matrices are not interchangeable in the statement"
    );
}

/// `Rat.det_matMul` at concrete `1×1` and `2×2` matrices, with both sides
/// computed independently.
///
/// The theorem is proved at a symbolic `n` and symbolic matrices, so these
/// instances add nothing about the PROOF. What they add is that the two sides
/// are the numbers they are supposed to be — a check on the statement's
/// meaning that no amount of type-checking supplies, and the one that would
/// catch a transposed index inside `Rat.matMul` or `Rat.det`.
///
/// `A = [[1,2],[3,4]]`, `B = [[5,6],[7,8]]`: `A·B = [[19,22],[43,50]]` with
/// determinant `19·50 − 22·43 = 4`, and `det A · det B = (−2)·(−2) = 4`. The
/// SIGN is what makes this discriminating — both factors are negative, so a
/// dropped alternating sign would give `+2 · +2` on the right and a different
/// number on the left.
#[test]
fn det_mat_mul_computes_at_concrete_matrices() {
    use crate::rat_prelude::matrix_det::{const_matrix, rdet, rq};
    use crate::rat_prelude::ops::rmul;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    // 1×1.
    {
        let a = const_matrix(&mut d, p, 1, &[3]);
        let b = const_matrix(&mut d, p, 1, &[5]);
        let one = d.num(1);
        let product = d.const_app(p.mat_mul, &[a, b, one]);
        let lhs = rdet(&mut d, p, product, one);
        let da = rdet(&mut d, p, a, one);
        let db = rdet(&mut d, p, b, one);
        let rhs = rmul(&mut d, da, db);
        let fifteen = rq(&mut d, p, 15);
        assert!(d.kernel().def_eq(lhs, fifteen), "det ([[3]]·[[5]]) 1 is 15");
        assert!(
            d.kernel().def_eq(rhs, fifteen),
            "det [[3]] * det [[5]] is 15"
        );
        let sixteen = rq(&mut d, p, 16);
        assert!(!d.kernel().def_eq(lhs, sixteen), "15 is not 16");
    }

    // 2×2, both determinants negative.
    {
        let a = const_matrix(&mut d, p, 2, &[1, 2, 3, 4]);
        let b = const_matrix(&mut d, p, 2, &[5, 6, 7, 8]);
        let two = d.num(2);
        let product = d.const_app(p.mat_mul, &[a, b, two]);
        let lhs = rdet(&mut d, p, product, two);
        let da = rdet(&mut d, p, a, two);
        let db = rdet(&mut d, p, b, two);
        let rhs = rmul(&mut d, da, db);

        let four = rq(&mut d, p, 4);
        assert!(
            d.kernel().def_eq(lhs, four),
            "det ([[1,2],[3,4]]·[[5,6],[7,8]]) 2 = 19·50 − 22·43 = 4"
        );
        assert!(d.kernel().def_eq(rhs, four), "(−2)·(−2) = 4");

        let minus_two = rq(&mut d, p, -2);
        assert!(
            d.kernel().def_eq(da, minus_two),
            "det [[1,2],[3,4]] is −2, not +2 -- this is the sign the alternating \
             convention decides"
        );
        let plus_two = rq(&mut d, p, 2);
        assert!(
            !d.kernel().def_eq(da, plus_two),
            "if this passes the alternating sign is dropped"
        );
        let five = rq(&mut d, p, 5);
        assert!(!d.kernel().def_eq(lhs, five), "4 is not 5");

        // And the instantiated THEOREM infers to exactly the equation whose two
        // sides were just computed.
        let proof = d.lemma(p.det_mat_mul, &[two, a, b]);
        let inferred = d
            .kernel()
            .infer(proof)
            .unwrap_or_else(|e| panic!("det_matMul(2, A, B) should infer: {e:?}"));
        let expected = crate::rat_prelude::ops::req(&mut d, lhs, rhs);
        assert!(
            d.kernel().def_eq(inferred, expected),
            "det_matMul at the concrete pair must be the equation between the two \
             numbers computed above"
        );
    }
}

/// `Rat.det_matMul_expand` at the smallest instance where the function space
/// is not a singleton, with the sum evaluated independently.
///
/// At `n = 2` the expansion runs over all four maps `[0,2) -> [0,2)`. Two of
/// them are non-injective and their `det (B∘g) 2` vanishes (two equal rows),
/// so the total is `A 0 0 · A 1 1 · det B + A 0 1 · A 1 0 · det (B with its
/// rows swapped)` — which for `A = [[1,2],[3,4]]`, `B = [[5,6],[7,8]]` is
/// `1·4·(−2) + 2·3·(+2) = −8 + 12 = 4`, the same `4` as the product law. The
/// point of computing it this way is that it exercises the ENUMERATION: an
/// expansion that reached only the IDENTITY map would total `−8`, and one that
/// reached only the two constant maps would total `0`. Both are asserted apart
/// from `4` through the same `def_eq`.
#[test]
fn det_mat_mul_expand_computes_over_the_whole_function_space() {
    use crate::rat_prelude::matrix_det::{const_matrix, rdet, rq};

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let a = const_matrix(&mut d, p, 2, &[1, 2, 3, 4]);
    let b = const_matrix(&mut d, p, 2, &[5, 6, 7, 8]);
    let one = d.num(1);
    let two = d.num(2);

    let proof = d.lemma(p.det_mat_mul_expand, &[one, two, a, b]);
    let inferred = d
        .kernel()
        .infer(proof)
        .unwrap_or_else(|e| panic!("det_matMul_expand(1, 2, A, B) should infer: {e:?}"));

    // The left-hand side is the product's determinant, 4.
    let product = d.const_app(p.mat_mul, &[a, b, two]);
    let lhs = rdet(&mut d, p, product, two);
    let four = rq(&mut d, p, 4);
    assert!(d.kernel().def_eq(lhs, four), "the left-hand side is 4");

    // The right-hand side is the sum over the four maps, and it must be 4 too.
    // Reading it out of the inferred statement rather than rebuilding it is
    // deliberate: the point is that the SUM the theorem names evaluates to the
    // determinant, not that a sum built here does.
    let eight = rq(&mut d, p, 8);
    let neg_eight = rq(&mut d, p, -8);
    let rhs_eq_four = crate::rat_prelude::ops::req(&mut d, lhs, four);
    assert!(
        d.kernel().def_eq(inferred, rhs_eq_four),
        "the expansion's right-hand side must evaluate to 4 -- if this fails the \
         enumeration is not summing what it claims"
    );
    let rhs_eq_neg_eight = crate::rat_prelude::ops::req(&mut d, lhs, neg_eight);
    assert!(
        !d.kernel().def_eq(inferred, rhs_eq_neg_eight),
        "−8 is the IDENTITY map's contribution alone -- if this passes the sum \
         misses the transposition"
    );
    let rhs_eq_eight = crate::rat_prelude::ops::req(&mut d, lhs, eight);
    assert!(
        !d.kernel().def_eq(inferred, rhs_eq_eight),
        "8 is not 4 -- the same def_eq separates them"
    );
}
