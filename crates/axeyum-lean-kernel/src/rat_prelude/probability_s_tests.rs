//! ADR-1616: what the generic layer is worth, measured.
//!
//! Two questions, and this file answers both with the kernel rather than
//! with prose.
//!
//! 1. **Is `AlgS.OrderedRing.sumRange` at `ℚ` the SAME construct as
//!    `Rat.sumRange`, or merely an analogue?** The definitions tests below
//!    demand definitional equality of the two closed terms — not of their
//!    types — so a generic definition that computed something else would
//!    fail even though it type-checks.
//!
//! 2. **How many of the existing `Rat.*` probability theorems BECOME
//!    instances of a generic statement, and how many need reproof?** Each
//!    instance test builds a proof term for the `ℚ` theorem's own declared
//!    type out of the generic theorem alone, infers its type, and requires
//!    that type to be definitionally equal to the `ℚ` theorem's. That is
//!    the deciding number the roadmap asked for, and it is counted by
//!    [`instance_count_is_pinned`], which derives the list from this
//!    module's own table rather than from a literal.
//!
//! Every positive test is paired with a discriminating negative one that
//! differs in a SMALL term, so a test that could not fail would be visible.

use super::*;
use crate::Kernel;
use crate::build_rat_prelude;
use crate::expr::ExprNode;
use crate::name::NameId;

/// The domain and (still-bound) codomain of a `Pi`, after weak-head
/// normalisation. `Kernel` exposes no such accessor, so each consumer would
/// otherwise re-match `ExprNode::Pi` by hand.
fn pi_parts(k: &mut Kernel, ty: ExprId) -> Option<(ExprId, ExprId)> {
    let w = k.whnf(ty);
    match k.expr_node(w) {
        ExprNode::Pi(_, dom, body, _) => Some((*dom, *body)),
        _ => None,
    }
}

/// Build the rational prelude and return it with a fresh kernel.
fn prelude() -> (Kernel, RatPrelude) {
    let mut k = Kernel::new();
    let p = build_rat_prelude(&mut k).expect("rat prelude must build");
    (k, p)
}

/// `AlgS.Rat.orderedRingS`, the `AlgS.OrderedRing` value at `ℚ`
/// (`AlgS.OrderedRing.ofAlg Rat.orderedRing`, so its `equiv` field is
/// `@Eq Rat` — which is why a generic `equiv` conclusion lands on the `ℚ`
/// theorems' own `Eq` statements).
fn rat_s(k: &mut Kernel, p: &RatPrelude) -> ExprId {
    k.const_(p.ordered_ring_ext_s.rat_ordered_ring_s, vec![])
}

fn rat_carrier(k: &mut Kernel, p: &RatPrelude) -> ExprId {
    k.const_(p.int.rat, vec![])
}

// ---------------------------------------------------------------------------
// 1. The definitions ARE the `ℚ` ones.
// ---------------------------------------------------------------------------

/// `AlgS.OrderedRing.sumRange AlgS.Rat.orderedRingS` is definitionally
/// `Rat.sumRange`.
#[test]
fn generic_sum_range_is_rat_sum_range() {
    const F_FV: u64 = 61_000;
    const N_FV: u64 = 61_001;
    let (mut k, p) = prelude();
    let r = rat_s(&mut k, &p);
    let carrier = rat_carrier(&mut k, &p);
    let nat = k.const_(p.int.nat.nat, vec![]);
    let fn_ty = crate::nat_prelude::structures::arrow(&mut k, nat, carrier);
    let f = k.fvar(F_FV);
    let n = k.fvar(N_FV);

    let generic = {
        let c = k.const_(p.probability_s.sum_range, vec![]);
        let e1 = k.app(c, r);
        let e2 = k.app(e1, f);
        let applied = k.app(e2, n);
        let v = crate::nat_prelude::structures::lam_over(&mut k, N_FV, nat, applied);
        crate::nat_prelude::structures::lam_over(&mut k, F_FV, fn_ty, v)
    };
    let hand = k.const_(p.sum_range, vec![]);
    assert!(
        k.def_eq(generic, hand),
        "AlgS.OrderedRing.sumRange at AlgS.Rat.orderedRingS must BE Rat.sumRange"
    );
}

/// **Negative control** for [`generic_sum_range_is_rat_sum_range`], one
/// `Nat.succ` apart: summing to `n+1` is not summing to `n`.
#[test]
fn generic_sum_range_at_succ_is_not_rat_sum_range() {
    const F_FV: u64 = 61_010;
    const N_FV: u64 = 61_011;
    let (mut k, p) = prelude();
    let r = rat_s(&mut k, &p);
    let carrier = rat_carrier(&mut k, &p);
    let nat = k.const_(p.int.nat.nat, vec![]);
    let fn_ty = crate::nat_prelude::structures::arrow(&mut k, nat, carrier);
    let f = k.fvar(F_FV);
    let n = k.fvar(N_FV);
    let succ = k.const_(p.int.nat.succ, vec![]);
    let sn = k.app(succ, n);

    let generic = {
        let c = k.const_(p.probability_s.sum_range, vec![]);
        let e1 = k.app(c, r);
        let e2 = k.app(e1, f);
        let applied = k.app(e2, sn);
        let v = crate::nat_prelude::structures::lam_over(&mut k, N_FV, nat, applied);
        crate::nat_prelude::structures::lam_over(&mut k, F_FV, fn_ty, v)
    };
    let hand = k.const_(p.sum_range, vec![]);
    assert!(
        !k.def_eq(generic, hand),
        "the generic sum to n+1 must NOT be Rat.sumRange to n"
    );
}

/// The generic `sumRange` **evaluates**: `sumRange RatS (fun _ => 1) 2`
/// reduces to `((0 + 1) + 1)`.
#[test]
fn generic_sum_range_evaluates_at_two() {
    const K_FV: u64 = 61_020;
    let (mut k, p) = prelude();
    let r = rat_s(&mut k, &p);
    let _carrier = rat_carrier(&mut k, &p);
    let nat = k.const_(p.int.nat.nat, vec![]);
    let one = k.const_(p.one, vec![]);
    let zero = k.const_(p.zero, vec![]);
    let add = k.const_(p.int.rat_add, vec![]);
    let ones = crate::nat_prelude::structures::lam_over(&mut k, K_FV, nat, one);

    let two = {
        let z = k.const_(p.int.nat.zero, vec![]);
        let succ = k.const_(p.int.nat.succ, vec![]);
        let s1 = k.app(succ, z);
        k.app(succ, s1)
    };
    let applied = {
        let c = k.const_(p.probability_s.sum_range, vec![]);
        let e1 = k.app(c, r);
        let e2 = k.app(e1, ones);
        k.app(e2, two)
    };
    let expected = {
        let a1 = crate::nat_prelude::structures::app2(&mut k, add, zero, one);
        crate::nat_prelude::structures::app2(&mut k, add, a1, one)
    };
    assert!(
        k.def_eq(applied, expected),
        "sumRange RatS (fun _ => 1) 2 must reduce to (0 + 1) + 1"
    );
    let three_terms = {
        let a1 = crate::nat_prelude::structures::app2(&mut k, add, zero, one);
        let a2 = crate::nat_prelude::structures::app2(&mut k, add, a1, one);
        crate::nat_prelude::structures::app2(&mut k, add, a2, one)
    };
    assert!(
        !k.def_eq(applied, three_terms),
        "sumRange RatS (fun _ => 1) 2 must NOT reduce to a THREE-term sum"
    );
}

/// `AlgS.OrderedRing.expectation` at `ℚ` is `Rat.expectation`.
#[test]
fn generic_expectation_is_rat_expectation() {
    const X_FV: u64 = 61_030;
    const P_FV: u64 = 61_031;
    const N_FV: u64 = 61_032;
    let (mut k, p) = prelude();
    let r = rat_s(&mut k, &p);
    let carrier = rat_carrier(&mut k, &p);
    let nat = k.const_(p.int.nat.nat, vec![]);
    let fn_ty = crate::nat_prelude::structures::arrow(&mut k, nat, carrier);
    let x = k.fvar(X_FV);
    let pf = k.fvar(P_FV);
    let n = k.fvar(N_FV);

    let generic = {
        let c = k.const_(p.probability_s.expectation, vec![]);
        let e1 = k.app(c, r);
        let e2 = k.app(e1, x);
        let e3 = k.app(e2, pf);
        let applied = k.app(e3, n);
        let v = crate::nat_prelude::structures::lam_over(&mut k, N_FV, nat, applied);
        let v = crate::nat_prelude::structures::lam_over(&mut k, P_FV, fn_ty, v);
        crate::nat_prelude::structures::lam_over(&mut k, X_FV, fn_ty, v)
    };
    let hand = k.const_(p.expectation, vec![]);
    assert!(
        k.def_eq(generic, hand),
        "AlgS.OrderedRing.expectation at ℚ must BE Rat.expectation"
    );
}

/// **Negative control**: the weights and the variable are not
/// interchangeable — `E[p; X]` is not `E[X; p]`. (`Rat.expectation X p n`
/// sums `X k * p k`; swapping the two arguments sums `p k * X k`, and `ℚ`'s
/// `mul` does not reduce those to one another without `mul_comm`.)
#[test]
fn generic_expectation_with_swapped_arguments_is_not_rat_expectation() {
    const X_FV: u64 = 61_040;
    const P_FV: u64 = 61_041;
    const N_FV: u64 = 61_042;
    let (mut k, p) = prelude();
    let r = rat_s(&mut k, &p);
    let carrier = rat_carrier(&mut k, &p);
    let nat = k.const_(p.int.nat.nat, vec![]);
    let fn_ty = crate::nat_prelude::structures::arrow(&mut k, nat, carrier);
    let x = k.fvar(X_FV);
    let pf = k.fvar(P_FV);
    let n = k.fvar(N_FV);

    let generic = {
        let c = k.const_(p.probability_s.expectation, vec![]);
        let e1 = k.app(c, r);
        let e2 = k.app(e1, pf);
        let e3 = k.app(e2, x);
        let applied = k.app(e3, n);
        let v = crate::nat_prelude::structures::lam_over(&mut k, N_FV, nat, applied);
        let v = crate::nat_prelude::structures::lam_over(&mut k, P_FV, fn_ty, v);
        crate::nat_prelude::structures::lam_over(&mut k, X_FV, fn_ty, v)
    };
    let hand = k.const_(p.expectation, vec![]);
    assert!(
        !k.def_eq(generic, hand),
        "expectation with its variable and weights swapped must NOT be Rat.expectation"
    );
}

/// `AlgS.OrderedRing.IsDistribution`, `variance` and `covariance` at `ℚ`
/// are the `ℚ` constants, all three by definitional equality of the closed
/// terms.
#[test]
fn generic_is_distribution_variance_covariance_are_the_rat_ones() {
    const A_FV: u64 = 61_050;
    const B_FV: u64 = 61_051;
    const C_FV: u64 = 61_052;
    const D_FV: u64 = 61_053;
    let (mut k, p) = prelude();
    let carrier = rat_carrier(&mut k, &p);
    let nat = k.const_(p.int.nat.nat, vec![]);
    let fn_ty = crate::nat_prelude::structures::arrow(&mut k, nat, carrier);

    // IsDistribution: two arguments.
    {
        let r = rat_s(&mut k, &p);
        let pf = k.fvar(A_FV);
        let n = k.fvar(B_FV);
        let c = k.const_(p.probability_s.is_distribution, vec![]);
        let e1 = k.app(c, r);
        let e2 = k.app(e1, pf);
        let applied = k.app(e2, n);
        let v = crate::nat_prelude::structures::lam_over(&mut k, B_FV, nat, applied);
        let generic = crate::nat_prelude::structures::lam_over(&mut k, A_FV, fn_ty, v);
        let hand = k.const_(p.is_distribution, vec![]);
        assert!(
            k.def_eq(generic, hand),
            "generic IsDistribution at ℚ must BE Rat.IsDistribution"
        );
    }
    // variance: three arguments.
    {
        let r = rat_s(&mut k, &p);
        let x = k.fvar(A_FV);
        let pf = k.fvar(B_FV);
        let n = k.fvar(C_FV);
        let c = k.const_(p.probability_s.variance, vec![]);
        let e1 = k.app(c, r);
        let e2 = k.app(e1, x);
        let e3 = k.app(e2, pf);
        let applied = k.app(e3, n);
        let v = crate::nat_prelude::structures::lam_over(&mut k, C_FV, nat, applied);
        let v = crate::nat_prelude::structures::lam_over(&mut k, B_FV, fn_ty, v);
        let generic = crate::nat_prelude::structures::lam_over(&mut k, A_FV, fn_ty, v);
        let hand = k.const_(p.variance, vec![]);
        assert!(
            k.def_eq(generic, hand),
            "generic variance at ℚ must BE Rat.variance"
        );
    }
    // covariance: four arguments.
    {
        let r = rat_s(&mut k, &p);
        let x = k.fvar(A_FV);
        let y = k.fvar(B_FV);
        let pf = k.fvar(C_FV);
        let n = k.fvar(D_FV);
        let c = k.const_(p.probability_s.covariance, vec![]);
        let e1 = k.app(c, r);
        let e2 = k.app(e1, x);
        let e3 = k.app(e2, y);
        let e4 = k.app(e3, pf);
        let applied = k.app(e4, n);
        let v = crate::nat_prelude::structures::lam_over(&mut k, D_FV, nat, applied);
        let v = crate::nat_prelude::structures::lam_over(&mut k, C_FV, fn_ty, v);
        let v = crate::nat_prelude::structures::lam_over(&mut k, B_FV, fn_ty, v);
        let generic = crate::nat_prelude::structures::lam_over(&mut k, A_FV, fn_ty, v);
        let hand = k.const_(p.covariance, vec![]);
        assert!(
            k.def_eq(generic, hand),
            "generic covariance at ℚ must BE Rat.covariance"
        );
    }
}

// ---------------------------------------------------------------------------
// 2. The instance count.
// ---------------------------------------------------------------------------

/// One row of the instance table: the generic theorem, the `ℚ` theorem it
/// is claimed to subsume, and how many leading `∀`-arguments (after the
/// record) the two share.
struct Row {
    generic: NameId,
    hand: NameId,
    /// Number of arguments to apply to BOTH sides before comparing types.
    /// A `0` compares the closed constants' types directly.
    args: usize,
    label: &'static str,
}

/// Apply `head` to `count` fresh free variables whose types are read off
/// its own `Pi` telescope, then close the application back over them.
///
/// The telescope is walked with [`pi_parts`] rather than by inferring the
/// partially-applied term: `Kernel::infer` needs every free variable's type,
/// and an open instance term does not carry them.
fn apply_and_close(k: &mut Kernel, head: ExprId, count: usize, base_fv: u64) -> ExprId {
    let mut ty = k.infer(head).expect("instance head must type-check");
    let mut term = head;
    let mut bound: Vec<(u64, ExprId)> = Vec::new();
    for i in 0..count {
        let (dom, body) = pi_parts(k, ty).expect("instance head must be a Pi");
        let fv = base_fv + i as u64;
        let v = k.fvar(fv);
        term = k.app(term, v);
        ty = k.instantiate(body, &[v]);
        bound.push((fv, dom));
    }
    close_over(k, term, &bound)
}

fn close_over(k: &mut Kernel, mut term: ExprId, bound: &[(u64, ExprId)]) -> ExprId {
    for (fv, ty) in bound.iter().rev() {
        term = crate::nat_prelude::structures::lam_over(k, *fv, *ty, term);
    }
    term
}

/// The instance table: nine `ℚ` theorems whose statements the generic layer
/// reproduces EXACTLY, so the `ℚ` proof is redundant.
fn instance_rows(p: &RatPrelude) -> Vec<Row> {
    let g = &p.probability_s;
    vec![
        Row {
            generic: g.sum_range_congr,
            hand: p.sum_range_congr_lt,
            args: 4,
            label: "sumRange_congr_lt",
        },
        Row {
            generic: g.sum_range_add,
            hand: p.sum_range_add,
            args: 3,
            label: "sumRange_add",
        },
        Row {
            generic: g.sum_range_le,
            hand: p.sum_range_le,
            args: 4,
            label: "sumRange_le",
        },
        Row {
            generic: g.sum_range_nonneg,
            hand: p.sum_range_nonneg,
            args: 3,
            label: "sumRange_nonneg",
        },
        Row {
            generic: g.expectation_add,
            hand: p.expectation_add,
            args: 4,
            label: "expectation_add",
        },
        Row {
            generic: g.expectation_smul,
            hand: p.expectation_smul,
            args: 4,
            label: "expectation_smul",
        },
        Row {
            generic: g.expectation_const,
            hand: p.expectation_const,
            args: 4,
            label: "expectation_const",
        },
        Row {
            generic: g.expectation_nonneg,
            hand: p.expectation_nonneg,
            args: 5,
            label: "expectation_nonneg",
        },
        Row {
            generic: g.expectation_le,
            hand: p.expectation_le,
            args: 6,
            label: "expectation_le",
        },
    ]
}

/// **The deciding number.** Every row of [`instance_rows`] must type-check
/// as an instance: the generic theorem applied at `AlgS.Rat.orderedRingS`
/// and closed over the shared arguments has a type definitionally equal to
/// the `ℚ` theorem's own.
///
/// Derived from the table, not from a literal — so adding a row makes this
/// test do more work, and removing the generic theorem makes it fail.
#[test]
fn every_instance_row_type_checks_against_its_rat_theorem() {
    let (mut k, p) = prelude();
    for row in instance_rows(&p) {
        let r = rat_s(&mut k, &p);
        let g = k.const_(row.generic, vec![]);
        let g = k.app(g, r);
        let closed = apply_and_close(&mut k, g, row.args, 62_000);
        let generic_ty = k
            .infer(closed)
            .unwrap_or_else(|e| panic!("{} instance must type-check: {e:?}", row.label));
        let hand = k.const_(row.hand, vec![]);
        let hand_ty = k
            .infer(hand)
            .unwrap_or_else(|e| panic!("Rat.{} must exist: {e:?}", row.label));
        assert!(
            k.def_eq(generic_ty, hand_ty),
            "{}: the generic statement at AlgS.Rat.orderedRingS must have the SAME \
             type as the ℚ theorem",
            row.label
        );
    }
}

/// **Negative control** for the instance table: the row count is what the
/// table says, and every row names a DISTINCT generic theorem. A table
/// whose rows silently collapsed to one entry would still make the test
/// above pass.
#[test]
fn instance_count_is_pinned() {
    let (_k, p) = prelude();
    let rows = instance_rows(&p);
    assert_eq!(
        rows.len(),
        9,
        "the measured instance count is 9 ℚ theorems; update the ADR if this moves"
    );
    let mut names: Vec<NameId> = rows.iter().map(|r| r.generic).collect();
    names.sort_unstable();
    names.dedup();
    assert_eq!(
        names.len(),
        9,
        "every instance row must name a distinct theorem"
    );
}

/// **Negative control** proving the instance test can fail:
/// `AlgS.OrderedRing.expectation_add` is NOT an instance of
/// `Rat.expectation_smul`. Without this, a `def_eq` that always returned
/// `true` would be invisible.
#[test]
fn a_wrong_pairing_is_rejected() {
    let (mut k, p) = prelude();
    let r = rat_s(&mut k, &p);
    let g = k.const_(p.probability_s.expectation_add, vec![]);
    let g = k.app(g, r);
    let closed = apply_and_close(&mut k, g, 4, 63_000);
    let generic_ty = k.infer(closed).expect("expectation_add must type-check");
    let hand = k.const_(p.expectation_smul, vec![]);
    let hand_ty = k.infer(hand).expect("Rat.expectation_smul must exist");
    assert!(
        !k.def_eq(generic_ty, hand_ty),
        "expectation_add must NOT match Rat.expectation_smul"
    );
}

/// `Rat.markov_inequality` is an instance of the generic Markov inequality
/// **after discarding two hypotheses the argument never uses** — `lt zero
/// a` and pointwise `le zero (X k)`. This is the one row where the generic
/// statement is strictly STRONGER than the `ℚ` one, so it is measured
/// separately rather than in the table.
#[test]
fn rat_markov_is_an_instance_after_dropping_two_unused_hypotheses() {
    let (mut k, p) = prelude();
    let hand = k.const_(p.markov_inequality, vec![]);
    let hand_ty = k.infer(hand).expect("Rat.markov_inequality must exist");

    // Walk `Rat.markov_inequality`'s own telescope, binding each argument,
    // and feed the generic theorem only the arguments it takes: the record,
    // `a`, `X`, `ind`, `p`, `n`, the distribution hypothesis (index 5) and
    // the pointwise bound (index 8). Indices 6 and 7 are the two unused
    // hypotheses.
    let mut ty = hand_ty;
    let mut bound: Vec<(u64, ExprId)> = Vec::new();
    for i in 0..9u64 {
        let (dom, cod) = pi_parts(&mut k, ty).expect("markov telescope must be a Pi");
        let fv = 64_000 + i;
        let v = k.fvar(fv);
        ty = k.instantiate(cod, &[v]);
        bound.push((fv, dom));
    }
    let r = rat_s(&mut k, &p);
    let g = k.const_(p.probability_s.markov_inequality, vec![]);
    let mut applied = k.app(g, r);
    for idx in [0usize, 1, 2, 3, 4, 5, 8] {
        let v = k.fvar(bound[idx].0);
        applied = k.app(applied, v);
    }
    let closed = close_over(&mut k, applied, &bound);
    let generic_ty = k
        .infer(closed)
        .expect("generic Markov must type-check under ℚ's telescope");
    assert!(
        k.def_eq(generic_ty, hand_ty),
        "Rat.markov_inequality must be the generic Markov with two hypotheses ignored"
    );
}

/// `Rat.variance_nonneg` is an instance of the generic one **only once
/// `Rat.sq_nonneg` is supplied** for the hypothesis `∀ a, le zero (a*a)`
/// that `AlgS.OrderedRing` cannot discharge — the record has no trichotomy,
/// so a square's nonnegativity is not a consequence of its seven order
/// fields.
#[test]
fn rat_variance_nonneg_is_an_instance_once_sq_nonneg_is_supplied() {
    let (mut k, p) = prelude();
    let hand = k.const_(p.variance_nonneg, vec![]);
    let hand_ty = k.infer(hand).expect("Rat.variance_nonneg must exist");

    let mut ty = hand_ty;
    let mut bound: Vec<(u64, ExprId)> = Vec::new();
    for i in 0..4u64 {
        let (dom, cod) = pi_parts(&mut k, ty).expect("variance_nonneg telescope must be a Pi");
        let fv = 65_000 + i;
        let v = k.fvar(fv);
        ty = k.instantiate(cod, &[v]);
        bound.push((fv, dom));
    }
    let r = rat_s(&mut k, &p);
    let sq = k.const_(p.sq_nonneg, vec![]);
    let g = k.const_(p.probability_s.variance_nonneg, vec![]);
    let mut applied = k.app(g, r);
    for idx in [0usize, 1, 2] {
        let v = k.fvar(bound[idx].0);
        applied = k.app(applied, v);
    }
    applied = k.app(applied, sq);
    {
        let v = k.fvar(bound[3].0);
        applied = k.app(applied, v);
    }
    let closed = close_over(&mut k, applied, &bound);
    let generic_ty = k
        .infer(closed)
        .expect("generic variance_nonneg at ℚ with Rat.sq_nonneg must type-check");
    assert!(
        k.def_eq(generic_ty, hand_ty),
        "Rat.variance_nonneg must be the generic one with Rat.sq_nonneg supplied"
    );
}

// ---------------------------------------------------------------------------
// 3. Axiom-freedom.
// ---------------------------------------------------------------------------

/// Every name this module declares has an EMPTY axiom footprint, read from
/// the kernel rather than from a comment.
#[test]
fn probability_s_declarations_are_axiom_free() {
    let (k, p) = prelude();
    let g = p.probability_s;
    let names = [
        g.to_ring_s,
        g.to_group_s,
        g.zero_mul,
        g.neg_mul,
        g.sub_nonneg_of_le,
        g.mul_le_mul_of_nonneg_right,
        g.sum_range,
        g.sum_range_map,
        g.expectation_map,
        g.sum_range_zero,
        g.sum_range_succ,
        g.sum_range_congr,
        g.sum_range_add,
        g.mul_sum_range,
        g.sum_range_le,
        g.sum_range_nonneg,
        g.is_distribution,
        g.expectation,
        g.expectation_add,
        g.expectation_smul,
        g.expectation_const,
        g.expectation_nonneg,
        g.expectation_le,
        g.markov_inequality,
        g.variance,
        g.variance_nonneg,
        g.covariance,
        g.independent,
        g.uncorrelated_of_independent,
    ];
    for name in names {
        assert!(
            k.axiom_footprint(name).is_empty(),
            "every AlgS.OrderedRing probability declaration must be axiom-free"
        );
    }
    assert_eq!(
        names.len(),
        29,
        "the generic layer declares 29 names; update the ADR if this moves"
    );
}

// ---------------------------------------------------------------------------
// 4. W2-15: independence.
// ---------------------------------------------------------------------------

/// **Why there is no "`Independent` unfolds to the ℚ product rule" test
/// here.** It was written and then withdrawn, because it does not terminate
/// in a usable time: comparing the generic `Prop` with the hand-built `Eq`
/// makes the kernel unfold `Rat.expectation` (delta height 36) and the
/// generic `expectation` (height 4) against each other under a symbolic
/// bound, and the two heights drive the unfolder the wrong way round. The
/// claim it was meant to make is covered, and covered more strongly, by
/// [`independence_discharges_the_uncorrelated_hypothesis_of_the_rat_theorem`]
/// below, which requires the kernel to accept the generic definition where
/// the `ℚ` theorem demands its own — and by
/// [`a_dependent_pair_is_not_independent`], which decides the definition at
/// concrete arguments in both directions.

/// **The negative control W2-15 needs: a DEPENDENT pair of events does not
/// satisfy the definition.**
///
/// Two points, uniform weights, and `A = B` the event `{0}` — as dependent
/// as a pair can be. `P(A ∩ A) = P(A) = 1/2` but `P(A)·P(A) = 1/4`, so the
/// two sides of `Independent` are unequal *by computation*, and the kernel
/// says so.
#[test]
fn a_dependent_pair_is_not_independent() {
    const K_FV: u64 = 66_100;
    const J_FV: u64 = 66_101;
    const I_FV: u64 = 66_102;
    let (mut k, p) = prelude();
    let r = rat_s(&mut k, &p);
    let carrier = rat_carrier(&mut k, &p);
    let nat = k.const_(p.int.nat.nat, vec![]);
    let one_r = k.const_(p.one, vec![]);
    let zero_r = k.const_(p.zero, vec![]);

    // A := fun k => Nat.rec (fun _ => Rat) 1 (fun _ _ => 0) k, the indicator
    // of `{0}`: `A 0 = 1`, `A (succ _) = 0`.
    let event = {
        let anon = k.anon();
        let motive = k.lam(anon, nat, carrier, crate::BinderInfo::Default);
        let step = {
            let inner = crate::nat_prelude::structures::lam_over(&mut k, I_FV, carrier, zero_r);
            crate::nat_prelude::structures::lam_over(&mut k, J_FV, nat, inner)
        };
        let lz2 = k.level_zero();
        let lvl = k.level_succ(lz2);
        let rec = k.const_(p.int.nat.rec, vec![lvl]);
        let kv = k.fvar(K_FV);
        let e1 = k.app(rec, motive);
        let e2 = k.app(e1, one_r);
        let e3 = k.app(e2, step);
        let body = k.app(e3, kv);
        crate::nat_prelude::structures::lam_over(&mut k, K_FV, nat, body)
    };
    let two = {
        let z = k.const_(p.int.nat.zero, vec![]);
        let succ = k.const_(p.int.nat.succ, vec![]);
        let s1 = k.app(succ, z);
        k.app(succ, s1)
    };
    let weights = {
        let u = k.const_(p.uniform, vec![]);
        k.app(u, two)
    };

    let exp_of = |k: &mut Kernel, f: ExprId| -> ExprId {
        let e = k.const_(p.expectation, vec![]);
        let e1 = k.app(e, f);
        let e2 = k.app(e1, weights);
        k.app(e2, two)
    };
    let product = {
        const M_FV: u64 = 66_110;
        let kv = k.fvar(M_FV);
        let ak = k.app(event, kv);
        let mul = k.const_(p.int.rat_mul, vec![]);
        let prod = crate::nat_prelude::structures::app2(&mut k, mul, ak, ak);
        crate::nat_prelude::structures::lam_over(&mut k, M_FV, nat, prod)
    };
    let lhs = exp_of(&mut k, product);
    let ea = exp_of(&mut k, event);
    let mul = k.const_(p.int.rat_mul, vec![]);
    let rhs = crate::nat_prelude::structures::app2(&mut k, mul, ea, ea);

    assert!(
        !k.def_eq(lhs, rhs),
        "P(A ∩ A) = 1/2 and P(A)·P(A) = 1/4 must NOT be definitionally equal — \
         a dependent pair must fail the independence definition"
    );

    // Positive control on the SAME machinery, so the negative above cannot
    // be an artefact of a stuck reduction: the two sides ARE equal when the
    // pointwise product is compared with itself.
    let lhs_again = exp_of(&mut k, product);
    assert!(
        k.def_eq(lhs, lhs_again),
        "the same expectation must be definitionally equal to itself — if this \
         fails, the negative control above proves nothing"
    );

    // An INDEPENDENT pair on the same two points, so the negative above is
    // discriminating rather than an artefact of the setup: `A` against the
    // SURE event. `P(A ∩ Ω) = P(A) = 1/2` and `P(A)·P(Ω) = 1/2 · 1`, and the
    // kernel decides that they agree.
    let sure = {
        const S_FV: u64 = 66_120;
        crate::nat_prelude::structures::lam_over(&mut k, S_FV, nat, one_r)
    };
    let a_and_sure = {
        const T_FV: u64 = 66_121;
        let kv = k.fvar(T_FV);
        let ak = k.app(event, kv);
        let sk = k.app(sure, kv);
        let prod = crate::nat_prelude::structures::app2(&mut k, mul, ak, sk);
        crate::nat_prelude::structures::lam_over(&mut k, T_FV, nat, prod)
    };
    let joint = exp_of(&mut k, a_and_sure);
    let e_sure = exp_of(&mut k, sure);
    let factored = crate::nat_prelude::structures::app2(&mut k, mul, ea, e_sure);
    assert!(
        k.def_eq(joint, factored),
        "an event and the sure event ARE independent — if this fails, the \
         dependent-pair control above proves nothing about the definition"
    );

    // And the same generic term at `AlgS.Rat.orderedRingS` computes to the
    // same `ℚ` value, so the two really are the same construct here.
    let generic_lhs = {
        let e = k.const_(p.probability_s.expectation, vec![]);
        let e1 = k.app(e, r);
        let e2 = k.app(e1, product);
        let e3 = k.app(e2, weights);
        k.app(e3, two)
    };
    assert!(
        k.def_eq(generic_lhs, lhs),
        "the generic expectation must compute to the ℚ one at concrete arguments"
    );
}

/// **The payoff W2-15 exists for.** `Rat.variance_add_of_uncorrelated`
/// carries the hypothesis `covariance X Y p n = zero`; independence in its
/// product form now discharges it, and the composite term type-checks.
///
/// This is the whole claim "the existing pairwise-uncorrelated hypotheses
/// are recognizable to a reader from the field", stated as something the
/// kernel either accepts or does not.
#[test]
fn independence_discharges_the_uncorrelated_hypothesis_of_the_rat_theorem() {
    let (mut k, p) = prelude();
    let hand = k.const_(p.variance_add_of_uncorrelated, vec![]);
    let hand_ty = k
        .infer(hand)
        .expect("Rat.variance_add_of_uncorrelated must exist");

    // Walk its telescope: X, Y, p, n, IsDistribution, covariance = 0.
    let mut ty = hand_ty;
    let mut bound: Vec<(u64, ExprId)> = Vec::new();
    for i in 0..5u64 {
        let (dom, cod) = pi_parts(&mut k, ty).expect("telescope must be a Pi");
        let fv = 67_000 + i;
        let v = k.fvar(fv);
        ty = k.instantiate(cod, &[v]);
        bound.push((fv, dom));
    }
    // Replace the sixth binder (`covariance X Y p n = zero`) by an
    // independence hypothesis, and derive the sixth from it.
    let r = rat_s(&mut k, &p);
    let indep_ty = {
        let c = k.const_(p.probability_s.independent, vec![]);
        let mut e = k.app(c, r);
        for idx in [0usize, 1, 2, 3] {
            let v = k.fvar(bound[idx].0);
            e = k.app(e, v);
        }
        e
    };
    let h_fv = 67_100u64;
    let h = k.fvar(h_fv);
    let derived = {
        let c = k.const_(p.probability_s.uncorrelated_of_independent, vec![]);
        let mut e = k.app(c, r);
        for idx in [0usize, 1, 2, 3] {
            let v = k.fvar(bound[idx].0);
            e = k.app(e, v);
        }
        k.app(e, h)
    };
    let mut applied = hand;
    for idx in [0usize, 1, 2, 3, 4] {
        let v = k.fvar(bound[idx].0);
        applied = k.app(applied, v);
    }
    applied = k.app(applied, derived);
    let closed = {
        let mut t = crate::nat_prelude::structures::lam_over(&mut k, h_fv, indep_ty, applied);
        for (fv, bty) in bound.iter().rev() {
            t = crate::nat_prelude::structures::lam_over(&mut k, *fv, *bty, t);
        }
        t
    };
    k.infer(closed).expect(
        "Rat.variance_add_of_uncorrelated must accept a covariance-zero proof derived \
         from the generic independence definition",
    );
}
