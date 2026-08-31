//! Tests for [`super::matrix_invertible`] — `Rat.matInv2` and both-sided 2×2
//! invertibility stated through the general `matMul`/`matId` encoding.

use super::{RatPrelude, build_rat_prelude};
use crate::expr::ExprId;
use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use crate::{Declaration, Kernel};

fn built() -> (Kernel, RatPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_rat_prelude(&mut kernel).expect("Rat prelude must build");
    (kernel, prelude)
}

/// Every declaration `matrix_invertible::declare_matrix_invertible` adds is a
/// **checked** definition or theorem with an empty axiom footprint, read out
/// of the kernel rather than off the diff — same discipline as
/// `rat_prelude_tests::the_matrix_transpose_toolkit_is_axiom_free`.
#[test]
fn the_matrix_invertibility_toolkit_is_axiom_free() {
    let (kernel, p) = built();
    let expected = [
        ("matInv2", p.mat_inv2, false),
        ("matInv2_matMul_top_left", p.matinv2_matmul_top_left, true),
        ("matInv2_matMul_top_right", p.matinv2_matmul_top_right, true),
        (
            "matInv2_matMul_bottom_left",
            p.matinv2_matmul_bottom_left,
            true,
        ),
        (
            "matInv2_matMul_bottom_right",
            p.matinv2_matmul_bottom_right,
            true,
        ),
        ("matMul_matInv2_top_left", p.matmul_matinv2_top_left, true),
        ("matMul_matInv2_top_right", p.matmul_matinv2_top_right, true),
        (
            "matMul_matInv2_bottom_left",
            p.matmul_matinv2_bottom_left,
            true,
        ),
        (
            "matMul_matInv2_bottom_right",
            p.matmul_matinv2_bottom_right,
            true,
        ),
        ("matInv2_eval_example", p.mat_inv2_eval_example, true),
        ("matInv2_example", p.mat_inv2_example, true),
    ];
    for (label, name, is_theorem) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("Rat.{label} was interned but never declared"));
        if is_theorem {
            assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "Rat.{label} must be a checked Theorem, found a different kind"
            );
        } else {
            assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "Rat.{label} must be a Definition, found a different kind"
            );
        }
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "Rat.{label} rests on {footprint:?}");
    }
}

/// `Rat.matMul_matInv2_top_left`'s statement, asserted verbatim — an empty
/// axiom footprint on a theorem *named* this way says nothing about which
/// statement it proves (`CLAUDE.md`'s standing discipline; same check
/// `rat_prelude_tests::inv2_top_left_is_the_stated_entry_of_a_inverse_a`
/// applies to `super::matrix`'s own inverse family). Confirms the conclusion
/// is genuinely `matMul A (matInv2 A) 2 0 0 = matId 0 0` — the general
/// `matMul`/`matId` encoding, not a restatement in raw scalars.
#[test]
fn matmul_matinv2_top_left_is_the_stated_a_times_a_inverse_entry() {
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.matmul_matinv2_top_left)
        .expect("declared")
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
        rendered.contains("Rat.matMul x0 (Rat.matInv2 x0)"),
        "matMul_matInv2_top_left must state A · matInv2(A), got: {rendered}"
    );
    assert!(
        rendered.contains("Rat.matId"),
        "matMul_matInv2_top_left must conclude at Rat.matId, got: {rendered}"
    );
    assert!(
        rendered.contains("Not"),
        "matMul_matInv2_top_left must carry the det ≠ 0 hypothesis, got: {rendered}"
    );
}

/// `Rat.matInv2 A 0 0` at the concrete `A := [[2,3],[5,7]]` (`det = -1`)
/// REDUCES (`Eq.refl`) to `-7`, and the WRONG candidate a swapped-diagonal
/// (no-swap) formula would compute — `invD * A 0 0 = (-1)*2 = -2` — is
/// refused, so this is a discriminating check on the VALUE, not a tool that
/// cannot fail (same discipline as
/// `rat_prelude_tests::cramer2_solves_needs_its_hypothesis_the_unrestricted_claim_is_false_at_d_zero`).
#[test]
fn mat_inv2_eval_example_discriminates_a_swapped_diagonal() {
    use crate::rat_prelude::ops::{req, rmul, rrefl};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    // A wrong (no-swap) top-left candidate: invD * A 0 0, not invD * A 1 1.
    let literal = |d: &mut IntDev<'_>, k: i64| -> ExprId {
        let n = if k >= 0 {
            let nat = d.num(u32::try_from(k).expect("non-negative"));
            d.of_nat(nat)
        } else {
            let nat = d.num(u32::try_from(-k - 1).expect("negative"));
            d.neg_succ(nat)
        };
        d.const_app(p.of_int, &[n])
    };
    let a00 = literal(&mut d, 2);
    let a01 = literal(&mut d, 3);
    let a10 = literal(&mut d, 5);
    let a11 = literal(&mut d, 7);
    let _ = a11;
    let det = d.const_app(p.det2, &[a00, a01, a10, a11]);
    let inv_d = d.const_app(p.inv, &[det]);
    let wrong_top_left = rmul(&mut d, inv_d, a00); // no-swap mistake: invD * A 0 0
    let neg2 = literal(&mut d, -2);
    let claim = req(&mut d, wrong_top_left, neg2);
    let proof = rrefl(&mut d, neg2);
    let name = d
        .kernel()
        .name_str(anon, "Check.wrong_top_left_reduces_to_neg2");
    let accepted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: claim,
        value: proof,
    });
    assert!(
        accepted.is_ok(),
        "sanity: the WRONG (no-swap) candidate must reduce to -2, not -7: {accepted:?}"
    );

    let neg7 = literal(&mut d, -7);
    let claim_wrong_is_right = req(&mut d, wrong_top_left, neg7);
    let proof_wrong_is_right = rrefl(&mut d, neg7);
    let name2 = d
        .kernel()
        .name_str(anon, "Check.wrong_top_left_equals_neg7");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name: name2,
        uparams: vec![],
        ty: claim_wrong_is_right,
        value: proof_wrong_is_right,
    });
    assert!(
        refused.is_err(),
        "the WRONG (no-swap) candidate must NOT reduce to -7, or this control cannot \
         discriminate: {refused:?}"
    );
}

/// The negative control [`the_matrix_invertibility_toolkit_is_axiom_free`]
/// needs: at a SINGULAR instance (`det = 0`), the unrestricted claim `matMul
/// A (matInv2 A) 2 0 0 = matId 0 0` is not merely unprovable, it is FALSE —
/// `Rat.inv 0 = 0` (totality), so every `matInv2` entry is `0` there, and
/// `matMul A (matInv2 A) 2 0 0` reduces to `Rat.zero`, not `Rat.one`. Checked
/// both ways, same discipline as
/// `rat_prelude_tests::cramer2_solves_needs_its_hypothesis_the_unrestricted_claim_is_false_at_d_zero`.
#[test]
fn matmul_matinv2_needs_its_hypothesis_the_unrestricted_claim_is_false_at_det_zero() {
    use crate::rat_prelude::ops::{rat_ty, req, rrefl, rzero};

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.int);

    // A := [[1,1],[1,1]], det2 1 1 1 1 = 0.
    let literal = |d: &mut IntDev<'_>, k: u32| -> ExprId {
        let numerator = d.num(k);
        let index = d.num(0);
        d.const_app(p.nat_div_succ, &[numerator, index])
    };
    let one_q = literal(&mut d, 1);

    let nat = d.nat_ty();
    let zero_n = d.zero();
    let i_fv = d.fresh_fvar();
    let i = d.kernel().fvar(i_fv);
    let j_fv = d.fresh_fvar();
    let j = d.kernel().fvar(j_fv);
    let _ = rat_ty(&mut d);
    let cond_j = NatOps::beq(&mut d, j, zero_n);
    let row = crate::rat_prelude::probability::bool_select_rat(&mut d, cond_j, one_q, one_q);
    let cond_i = NatOps::beq(&mut d, i, zero_n);
    let body = crate::rat_prelude::probability::bool_select_rat(&mut d, cond_i, row, row);
    let a_mat = {
        let with_j = d.lam_fv(j_fv, nat, body);
        d.lam_fv(i_fv, nat, with_j)
    };

    let ainv = d.const_app(p.mat_inv2, &[a_mat]);
    let two_n = d.num(2);
    let zero_idx = d.num(0);
    let lhs = d.const_app(p.mat_mul, &[a_mat, ainv, two_n, zero_idx, zero_idx]);

    let zero_r = rzero(&mut d, p);
    let claim_true = req(&mut d, lhs, zero_r);
    let proof_true = rrefl(&mut d, zero_r);
    let name_true = d
        .kernel()
        .name_str(anon, "Check.matinv2_at_det_zero_is_zero");
    let accepted_true = d.kernel().add_declaration(Declaration::Theorem {
        name: name_true,
        uparams: vec![],
        ty: claim_true,
        value: proof_true,
    });
    assert!(
        accepted_true.is_ok(),
        "at det=0, matMul A (matInv2 A) 2 0 0 must REDUCE to 0 (Rat.inv 0 = 0): {accepted_true:?}"
    );

    let one_r = {
        use crate::rat_prelude::ops::rone;
        rone(&mut d, p)
    };
    let claim_false = req(&mut d, lhs, one_r);
    let proof_false = rrefl(&mut d, one_r);
    let name_false = d
        .kernel()
        .name_str(anon, "Check.matinv2_at_det_zero_equals_one");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name: name_false,
        uparams: vec![],
        ty: claim_false,
        value: proof_false,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted matMul A (matInv2 A) 2 0 0 = matId 0 0 at det=0 (0 = 1), so \
         dropping the det ≠ 0 hypothesis would not merely be unprovable, it would be FALSE, \
         and this reduction check caught neither: {refused:?}"
    );
}
