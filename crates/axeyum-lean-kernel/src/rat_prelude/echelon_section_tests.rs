//! Evidence for [`super::echelon_section`] — the pivot section, and the
//! ADR-1562 bridge unconditional.
//!
//! Four things are checked, and they catch disjoint defects.
//!
//! 1. **`rank`, `rankCols` and `nullity` compute the right numbers**, at a
//!    rank-deficient matrix and a full-rank one, each read back against a
//!    hand-computed value with a control that must NOT be `def_eq`. The three
//!    unconditional theorems are equations between `Definition`s, and the
//!    trusted gate cannot tell you a `Definition` is wrong.
//! 2. **The three theorems apply at fully free arguments with NO hypothesis** —
//!    which is the whole point of the change, since their `_of_pivotSection`
//!    predecessors each took one.
//! 3. **`Rat.rank_nullity_rows` is checked at the numbers**, not only
//!    symbolically: `rank + nullity` reduces to `cols` at both matrices.
//! 4. **The pivot-section hypothesis is NOT satisfied by every matrix.**
//!    ADR-1562 §2 exhibits `[[1,0],[1,0]]` — two nonzero rows sharing leading
//!    index `0` — where the section equation is false at row 1. This file
//!    checks the corresponding fact about the antecedent: `Rat.isEchelon` says
//!    `false` there, so `Rat.pivotSection_of_isEchelon` is a real implication
//!    and not a hypothesis every matrix meets.
//!
//! Every magnitude formed is a single-digit integer, so nothing here touches
//! the unary-numeral cost `CLAUDE.md` documents.

use super::RatPrelude;
use super::echelon::ris_echelon;
use super::matrix_det::mat_ty;
use super::nullity_tests::rect_matrix;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{BinderInfo, Kernel, LocalContext, LocalDecl, build_rat_prelude};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("the rational prelude must build");
    (kernel, prelude)
}

/// `rank`, `rankCols` and `nullity` at a rank-deficient 2×2 and a full-rank
/// one, every value read back against a hand-computed numeral.
///
/// `[[1,2],[2,4]]` reduces to `[[1,2],[0,0]]`, so its rank is 1 and its nullity
/// is 1; `[[0,1],[2,3]]` needs the pivot swap and has rank 2, nullity 0. The
/// pair is chosen so a `rank` that always answered `rows`, or always `0`, fails
/// one of them.
#[test]
fn rank_and_nullity_compute_at_two_concrete_matrices() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    for (entries, want_rank, label) in [
        (vec![1i64, 2, 2, 4], 1u32, "[[1,2],[2,4]]"),
        (vec![0, 1, 2, 3], 2, "[[0,1],[2,3]]"),
    ] {
        let m = rect_matrix(&mut d, p, 2, 2, &entries);
        let two_n = d.num(2);
        let want = d.num(want_rank);
        let want_nullity = d.num(2 - want_rank);

        let rk = d.const_app(p.rank, &[m, two_n, two_n]);
        assert!(
            d.kernel().def_eq(rk, want),
            "{label}: rank must be {want_rank}"
        );
        let other = d.num(want_rank + 1);
        assert!(
            !d.kernel().def_eq(rk, other),
            "{label}: rank must NOT also be {}",
            want_rank + 1
        );

        let rkc = d.const_app(p.rank_cols, &[m, two_n, two_n]);
        assert!(
            d.kernel().def_eq(rkc, want),
            "{label}: rankCols must agree with rank at {want_rank}"
        );

        let nl = d.const_app(p.nullity, &[m, two_n, two_n]);
        assert!(
            d.kernel().def_eq(nl, want_nullity),
            "{label}: nullity must be {}",
            2 - want_rank
        );

        // Rank-nullity, at the numbers.
        let sum = NatOps::add(&mut d, rk, nl);
        assert!(
            d.kernel().def_eq(sum, two_n),
            "{label}: rank + nullity must be the column count"
        );
    }
}

/// The three bridge results apply at fully free arguments and take **no**
/// hypothesis, which is what distinguishes them from their
/// `_of_pivotSection` predecessors.
#[test]
fn the_three_bridge_results_apply_with_no_hypothesis() {
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

    let rk = d.const_app(p.rank, &[m, rows, cols]);
    let rkc = d.const_app(p.rank_cols, &[m, rows, cols]);
    let nl = d.const_app(p.nullity, &[m, rows, cols]);

    let bridge = d.const_app(p.rank_eq_rank_cols, &[m, rows, cols]);
    let got = d
        .kernel()
        .infer_in(bridge, &mut ctx)
        .expect("Rat.rank_eq_rankCols must apply with no hypothesis");
    let want = d.eq(rk, rkc);
    assert!(
        d.kernel().def_eq(got, want),
        "the bridge equates rank and rankCols"
    );

    let bound = d.const_app(p.rank_le_cols, &[m, rows, cols]);
    let got = d
        .kernel()
        .infer_in(bound, &mut ctx)
        .expect("Rat.rank_le_cols must apply with no hypothesis");
    let want = NatOps::le(&mut d, rk, cols);
    assert!(
        d.kernel().def_eq(got, want),
        "the bound is on rank, against the column count"
    );
    // The control: it is NOT the free bound against the ROW count, which
    // `Rat.rank_le_rows` already gave and which ADR-1555 says is the easy one.
    let control = NatOps::le(&mut d, rk, rows);
    assert!(
        !d.kernel().def_eq(got, control),
        "negative control: this is the COLUMN bound, not the row bound"
    );

    let law = d.const_app(p.rank_nullity_rows, &[m, rows, cols]);
    let got = d
        .kernel()
        .infer_in(law, &mut ctx)
        .expect("Rat.rank_nullity_rows must apply with no hypothesis");
    let sum = NatOps::add(&mut d, rk, nl);
    let want = d.eq(sum, cols);
    assert!(
        d.kernel().def_eq(got, want),
        "rank-nullity in the ROW form: rank + nullity = cols"
    );
    // The control: the column form `rankCols + nullity = cols` is a different
    // theorem and was already free.
    let col_sum = NatOps::add(&mut d, rkc, nl);
    let control = d.eq(col_sum, cols);
    assert!(
        !d.kernel().def_eq(got, control),
        "negative control: the left summand is `rank`, not `rankCols`"
    );
}

/// The antecedent of `Rat.pivotSection_of_isEchelon` is not met by every
/// matrix.
///
/// ADR-1562 §2 exhibits `[[1,0],[1,0]]` — two nonzero rows sharing leading
/// index `0` — as the shape where the pivot-section equation is FALSE. Its
/// `Rat.isEchelon` must therefore be `false`, or the implication would be
/// deriving a false conclusion from a satisfied hypothesis. The positive
/// control is the same matrix reduced, which IS in echelon form.
#[test]
fn the_echelon_hypothesis_is_not_met_by_every_matrix() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 2, 2, &[1, 0, 1, 0]);
    let two_n = d.num(2);
    let true_v = d.bool_true();
    let false_v = d.bool_false();

    let raw = ris_echelon(&mut d, p, m, two_n, two_n);
    assert!(
        d.kernel().def_eq(raw, false_v),
        "ADR-1562's counterexample matrix is NOT in echelon form"
    );

    let reduced = d.const_app(p.row_echelon, &[m, two_n, two_n]);
    let ok = ris_echelon(&mut d, p, reduced, two_n, two_n);
    assert!(
        d.kernel().def_eq(ok, true_v),
        "positive control: reducing it does put it in echelon form"
    );

    // ... and its rank really is 1, so the two rows were dependent.
    let one_n = d.num(1);
    let rk = d.const_app(p.rank, &[m, two_n, two_n]);
    assert!(
        d.kernel().def_eq(rk, one_n),
        "the two rows are dependent, so the rank is 1"
    );
}

/// `Rat.pivotSection_of_isEchelon` applies at fully free arguments and its
/// conclusion is the equation ADR-1562 §2 named.
#[test]
fn pivot_section_of_is_echelon_applies_at_free_variables() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let anon = d.anon_name();
    let nat = d.nat_ty();
    let mty = mat_ty(&mut d);

    let e_fv = d.fresh_fvar();
    let e = d.kernel().fvar(e_fv);
    let rows_fv = d.fresh_fvar();
    let rows = d.kernel().fvar(rows_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);

    let scanned = d.const_app(p.is_echelon, &[e, rows, cols]);
    let true_v = d.bool_true();
    let hyp_ty = d.bool_eq(scanned, true_v);
    let hyp_fv = d.fresh_fvar();
    let hyp = d.kernel().fvar(hyp_fv);

    let bound_ty = NatOps::lt(&mut d, r, rows);
    let nz = d.const_app(p.nonzero_row_b, &[e, cols, r]);
    let sel_ty = d.bool_eq(nz, true_v);
    let hb_fv = d.fresh_fvar();
    let hb = d.kernel().fvar(hb_fv);
    let hs_fv = d.fresh_fvar();
    let hs = d.kernel().fvar(hs_fv);

    let mut ctx = LocalContext::new();
    for (fvar, ty) in [
        (e_fv, mty),
        (rows_fv, nat),
        (cols_fv, nat),
        (hyp_fv, hyp_ty),
        (r_fv, nat),
        (hb_fv, bound_ty),
        (hs_fv, sel_ty),
    ] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }

    let applied = d.const_app(
        p.pivot_section_of_is_echelon,
        &[e, rows, cols, hyp, r, hb, hs],
    );
    let got = d
        .kernel()
        .infer_in(applied, &mut ctx)
        .expect("Rat.pivotSection_of_isEchelon must apply at free variables");

    let col = d.const_app(p.pivot_col_of_row, &[e, cols, r]);
    let back = d.const_app(p.pivot_row_of_col, &[e, rows, cols, col]);
    let want = d.eq(back, r);
    assert!(
        d.kernel().def_eq(got, want),
        "the conclusion is ADR-1562's section equation"
    );

    // The control: the equation goes FROM the round trip TO `r`, not from `r`
    // to the leading index — confusing the two would make it trivial.
    let lead = d.const_app(p.leading_index, &[e, r, cols]);
    let control = d.eq(lead, r);
    assert!(
        !d.kernel().def_eq(got, control),
        "negative control: the section is about the round trip, not the leading index"
    );
}
