//! Evidence for [`super::leading_index`] — what `Rat.leadingIndex` answers.
//!
//! The two theorems are characterizations, so the honest evidence has two
//! halves that catch different defects.
//!
//! - **The scan really computes what they claim**, checked by reduction at a
//!   3-column matrix carrying a leading `1` at column `0`, a leading entry at
//!   column `2`, and an all-zero row whose answer must be `cols`. A
//!   characterization theorem that agreed with a WRONG scan would be useless,
//!   and only reduction can tell you which one you have.
//! - **The theorems apply at fully free arguments**, in a `LocalContext`,
//!   with controls refusing the two statements a mis-stated version would
//!   have: a first-nonzero lemma concluding `Lt` instead of `Eq`, and a
//!   zero-row lemma concluding `0` (the answer a scan that reported "no
//!   leading entry" as index zero would give) instead of `cols`.

use super::RatPrelude;
use super::matrix_det::{mat_ty, rq};
use super::nullity_tests::rect_matrix;
use super::ops::{req, rzero};
use crate::env::Declaration;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{BinderInfo, ExprId, Kernel, LocalContext, LocalDecl, build_rat_prelude};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("the rational prelude must build");
    (kernel, prelude)
}

/// The scan agrees with the characterizations at three shapes that between
/// them exercise every branch: a leading entry at column `0`, one at the LAST
/// column (so the scan skips two zeroes first), and an all-zero row, whose
/// answer must be `cols` and not `0`.
#[test]
fn leading_index_computes_the_first_nonzero_column_and_cols_for_a_zero_row() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let m = rect_matrix(&mut d, p, 3, 3, &[1, 2, 3, 0, 0, 5, 0, 0, 0]);
    let three_n = d.num(3);

    for (row, want) in [(0_u32, 0_u32), (1, 2), (2, 3)] {
        let r = d.num(row);
        let scanned = d.const_app(p.leading_index, &[m, r, three_n]);
        let expected = d.num(want);
        assert!(
            d.kernel().def_eq(scanned, expected),
            "leadingIndex of row {row} must be {want}"
        );
        let other = d.num(want + 1);
        assert!(
            !d.kernel().def_eq(scanned, other),
            "leadingIndex of row {row} must NOT also be {}",
            want + 1
        );
    }

    // The control that makes the zero row's answer meaningful: `cols` and `0`
    // are different answers, and a scan reporting "nothing here" as `0` would
    // make the zero row indistinguishable from row 0.
    let two_n = d.num(2);
    let zero_n = d.num(0);
    let zero_row = d.const_app(p.leading_index, &[m, two_n, three_n]);
    assert!(
        !d.kernel().def_eq(zero_row, zero_n),
        "the zero row's leading index must be cols, NOT 0"
    );

    // ... and the entries the theorems' hypotheses talk about really are what
    // the names say.
    let rat_zero = rzero(&mut d, p);
    let five = rq(&mut d, p, 5);
    let one_n = d.num(1);
    let skipped = d.apply(m, &[one_n, zero_n]);
    assert!(
        d.kernel().def_eq(skipped, rat_zero),
        "row 1 must be zero at column 0"
    );
    let landed = d.apply(m, &[one_n, two_n]);
    assert!(
        d.kernel().def_eq(landed, five),
        "row 1 must be 5 at column 2"
    );
}

/// Both characterizations apply at fully free arguments, and neither concludes
/// the statement a mis-stated version would.
#[test]
fn both_characterizations_apply_at_free_variables_with_mis_stated_controls() {
    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.int);

    let anon = d.anon_name();
    let nat = d.nat_ty();
    let mty = mat_ty(&mut d);

    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let r_fv = d.fresh_fvar();
    let r = d.kernel().fvar(r_fv);
    let cols_fv = d.fresh_fvar();
    let cols = d.kernel().fvar(cols_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);

    let zero_range = |d: &mut IntDev<'_>, hi: ExprId| -> ExprId {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let upper = NatOps::lt(d, k, hi);
        let entry = d.apply(m, &[r, k]);
        let rat_zero = rzero(d, p);
        let concl = req(d, entry, rat_zero);
        let body = d.arrow(upper, concl);
        d.pi_fv(k_fv, nat, body)
    };

    let t1 = NatOps::lt(&mut d, j, cols);
    let t2 = zero_range(&mut d, j);
    let entry_j = d.apply(m, &[r, j]);
    let rat_zero = rzero(&mut d, p);
    let eq_j = req(&mut d, entry_j, rat_zero);
    let t3 = d.not(eq_j);
    let t4 = zero_range(&mut d, cols);

    let h1_fv = d.fresh_fvar();
    let h1 = d.kernel().fvar(h1_fv);
    let h2_fv = d.fresh_fvar();
    let h2 = d.kernel().fvar(h2_fv);
    let h3_fv = d.fresh_fvar();
    let h3 = d.kernel().fvar(h3_fv);
    let h4_fv = d.fresh_fvar();
    let h4 = d.kernel().fvar(h4_fv);

    let mut ctx = LocalContext::new();
    for (fvar, ty) in [
        (m_fv, mty),
        (r_fv, nat),
        (cols_fv, nat),
        (j_fv, nat),
        (h1_fv, t1),
        (h2_fv, t2),
        (h3_fv, t3),
        (h4_fv, t4),
    ] {
        ctx.push(LocalDecl {
            fvar,
            name: anon,
            ty,
            info: BinderInfo::Default,
        });
    }

    let scanned = d.const_app(p.leading_index, &[m, r, cols]);

    let first = d.const_app(
        p.leading_index_eq_of_first_nonzero,
        &[m, r, cols, j, h1, h2, h3],
    );
    let first_ty = d
        .kernel()
        .infer_in(first, &mut ctx)
        .expect("leadingIndex_eq_of_first_nonzero must apply at free variables");
    let want_first = d.eq(scanned, j);
    assert!(
        d.kernel().def_eq(first_ty, want_first),
        "the first-nonzero lemma must conclude leadingIndex = j"
    );
    let weaker = NatOps::le(&mut d, scanned, j);
    assert!(
        !d.kernel().def_eq(first_ty, weaker),
        "negative control: the conclusion is an EQUATION, not a bound -- a \
         bound would not pin the pivot column"
    );

    let zero_row = d.const_app(p.leading_index_eq_cols_of_zero_row, &[m, r, cols, h4]);
    let zero_ty = d
        .kernel()
        .infer_in(zero_row, &mut ctx)
        .expect("leadingIndex_eq_cols_of_zero_row must apply at free variables");
    let want_zero = d.eq(scanned, cols);
    assert!(
        d.kernel().def_eq(zero_ty, want_zero),
        "the zero-row lemma must conclude leadingIndex = cols"
    );
    let zero_n = d.zero();
    let mis_stated = d.eq(scanned, zero_n);
    assert!(
        !d.kernel().def_eq(zero_ty, mis_stated),
        "negative control: a zero row's leading index is `cols`, NOT 0 -- \
         ADR-1554 §3 is the reason"
    );
}

/// Every declaration in the family rests on zero axioms.
#[test]
fn the_leading_index_family_is_axiom_free() {
    let (kernel, p) = built();
    for (label, name) in [
        (
            "leadingIndexAux_eq_of_first_nonzero",
            p.leading_index_aux_eq_of_first_nonzero,
        ),
        (
            "leadingIndex_eq_of_first_nonzero",
            p.leading_index_eq_of_first_nonzero,
        ),
        (
            "leadingIndexAux_eq_cols_of_zero",
            p.leading_index_aux_eq_cols_of_zero,
        ),
        (
            "leadingIndex_eq_cols_of_zero_row",
            p.leading_index_eq_cols_of_zero_row,
        ),
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

/// The two headline statements say what they claim, pinned by their rendered
/// types.
#[test]
fn the_leading_index_statements_say_what_they_claim() {
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

    let first = rendered(p.leading_index_eq_of_first_nonzero);
    assert!(
        first.contains("AxNat.lt x3 x2"),
        "the target column must be inside the column count: {first}"
    );
    assert!(
        first.contains("Not (Eq.{1} Rat (x0 x1 x3) Rat.zero)"),
        "the entry at the target column must be required NONZERO: {first}"
    );
    assert!(
        first.contains("Eq.{1} AxNat (Rat.leadingIndex x0 x1 x2) x3"),
        "the conclusion must be that the scan returns exactly the target \
         column: {first}"
    );

    let zero_row = rendered(p.leading_index_eq_cols_of_zero_row);
    assert!(
        zero_row.contains("Eq.{1} AxNat (Rat.leadingIndex x0 x1 x2) x2"),
        "the zero row's leading index must be `cols`: {zero_row}"
    );
    assert!(
        !zero_row.contains("Not (Eq.{1} Rat"),
        "the zero-row lemma must NOT carry a nonzero hypothesis -- it is about \
         a row with none: {zero_row}"
    );
}
