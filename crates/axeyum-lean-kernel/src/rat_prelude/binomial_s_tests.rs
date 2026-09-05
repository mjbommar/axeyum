//! ADR-1631: what the constructed Bernoulli model is worth, measured.
//!
//! Three questions, each answered by the kernel rather than by prose.
//!
//! 1. **Do the two `Definition`s compute the right values?** A `Definition`
//!    type-checks whatever it computes, so every one gets an evaluation test
//!    at concrete, small, DISCRIMINATING arguments — `bernoulliMass R q 0`
//!    and `bernoulliMass R q 1` are different rationals at `q = 1/3`, and the
//!    tests demand exactly that.
//!
//! 2. **Do the generic theorems become `ℚ` facts by instantiation?** Each
//!    theorem is instantiated at `AlgS.Rat.orderedRingS` with `q = 1/2` and
//!    `q = 1/3`, and the *value* of the expectation and the variance is
//!    compared against the hand-built rational by `def_eq` — a computation
//!    the proof term takes no part in, so a wrong proof of a right statement
//!    and a right proof of a wrong statement are both caught.
//!
//! 3. **Is `q = 1/2` enough?** No, and that is why `q = 1/3` is here.
//!    `Var[X] = q(1−q)` and the plausible wrong answer `q·q` AGREE at
//!    `q = 1/2` (both `1/4`). At `q = 1/3` they are `2/9` and `1/9`. Every
//!    variance test therefore carries its `1/3` twin, and the negative
//!    control [`bernoulli_variance_at_a_third_is_not_q_squared`] is the one
//!    that can actually die.

use super::*;
use crate::Kernel;
use crate::build_rat_prelude;

/// Build the rational prelude and return it with a fresh kernel.
fn prelude() -> (Kernel, RatPrelude) {
    let mut k = Kernel::new();
    let p = build_rat_prelude(&mut k).expect("rat prelude must build");
    (k, p)
}

/// `AlgS.Rat.orderedRingS`, the `AlgS.OrderedRing` value at `ℚ`.
fn rat_s(k: &mut Kernel, p: &RatPrelude) -> ExprId {
    k.const_(p.ordered_ring_ext_s.rat_ordered_ring_s, vec![])
}

/// The `Nat` numeral `n`, unary.
fn nat_num(k: &mut Kernel, p: &RatPrelude, n: u32) -> ExprId {
    let mut e = k.const_(p.int.nat.zero, vec![]);
    let succ = k.const_(p.int.nat.succ, vec![]);
    for _ in 0..n {
        e = k.app(succ, e);
    }
    e
}

/// The rational `num / (den_pred + 1)`, i.e. `Rat.natDivSucc num den_pred`.
fn frac(k: &mut Kernel, p: &RatPrelude, num: u32, den_pred: u32) -> ExprId {
    let n = nat_num(k, p, num);
    let d = nat_num(k, p, den_pred);
    let c = k.const_(p.nat_div_succ, vec![]);
    let e1 = k.app(c, n);
    k.app(e1, d)
}

/// `AlgS.OrderedRing.bernoulliVar RatS k`.
fn bvar_at(k: &mut Kernel, p: &RatPrelude, idx: ExprId) -> ExprId {
    let r = rat_s(k, p);
    let c = k.const_(p.binomial_s.bernoulli_var, vec![]);
    let e1 = k.app(c, r);
    k.app(e1, idx)
}

/// `AlgS.OrderedRing.bernoulliMass RatS q`, the partial application.
fn bmass_fn(k: &mut Kernel, p: &RatPrelude, q: ExprId) -> ExprId {
    let r = rat_s(k, p);
    let c = k.const_(p.binomial_s.bernoulli_mass, vec![]);
    let e1 = k.app(c, r);
    k.app(e1, q)
}

/// `AlgS.OrderedRing.expectation RatS (bernoulliVar RatS) (bernoulliMass
/// RatS q) 2`, the two-outcome mean as a closed `ℚ` term.
fn bernoulli_mean(k: &mut Kernel, p: &RatPrelude, q: ExprId) -> ExprId {
    let r = rat_s(k, p);
    let var = {
        let c = k.const_(p.binomial_s.bernoulli_var, vec![]);
        k.app(c, r)
    };
    let mass = bmass_fn(k, p, q);
    let two = nat_num(k, p, 2);
    let c = k.const_(p.probability_s.expectation, vec![]);
    let e1 = k.app(c, r);
    let e2 = k.app(e1, var);
    let e3 = k.app(e2, mass);
    k.app(e3, two)
}

/// `AlgS.OrderedRing.variance RatS (bernoulliVar RatS) (bernoulliMass RatS
/// q) 2`, the two-outcome variance as a closed `ℚ` term.
fn bernoulli_var_value(k: &mut Kernel, p: &RatPrelude, q: ExprId) -> ExprId {
    let r = rat_s(k, p);
    let var = {
        let c = k.const_(p.binomial_s.bernoulli_var, vec![]);
        k.app(c, r)
    };
    let mass = bmass_fn(k, p, q);
    let two = nat_num(k, p, 2);
    let c = k.const_(p.probability_s.variance, vec![]);
    let e1 = k.app(c, r);
    let e2 = k.app(e1, var);
    let e3 = k.app(e2, mass);
    k.app(e3, two)
}

// ---------------------------------------------------------------------------
// 1. The definitions compute.
// ---------------------------------------------------------------------------

/// `bernoulliVar RatS` is the two-point success indicator: `0 ↦ 0`,
/// `1 ↦ 1`, `2 ↦ 1`.
#[test]
fn bernoulli_var_evaluates_at_zero_and_one() {
    let (mut k, p) = prelude();
    let zero_r = k.const_(p.zero, vec![]);
    let one_r = k.const_(p.one, vec![]);

    for (idx, want) in [(0u32, zero_r), (1, one_r), (2, one_r)] {
        let i = nat_num(&mut k, &p, idx);
        let got = bvar_at(&mut k, &p, i);
        assert!(
            k.def_eq(got, want),
            "bernoulliVar RatS {idx} must compute to the expected ℚ value"
        );
    }

    // **Negative control, one value apart**: the failure outcome is not the
    // success outcome. Without this the loop above would pass for the
    // constant-`one` function.
    let zero_idx = nat_num(&mut k, &p, 0);
    let at_zero = bvar_at(&mut k, &p, zero_idx);
    assert!(
        !k.def_eq(at_zero, one_r),
        "bernoulliVar RatS 0 must NOT be Rat.one — the variable would be constant"
    );
}

/// `bernoulliMass RatS q` is `0 ↦ 1 − q`, `1 ↦ q`, at `q = 1/2` and — the
/// discriminating one — at `q = 1/3`, where `1 − q = 2/3 ≠ q`.
#[test]
fn bernoulli_mass_evaluates_at_a_half_and_a_third() {
    let (mut k, p) = prelude();

    let half = frac(&mut k, &p, 1, 1);
    let third = frac(&mut k, &p, 1, 2);
    let two_thirds = frac(&mut k, &p, 2, 2);

    let zero_idx = nat_num(&mut k, &p, 0);
    let one_idx = nat_num(&mut k, &p, 1);

    // q = 1/2 : both outcomes weigh 1/2.
    let m_half = bmass_fn(&mut k, &p, half);
    let m_half_0 = k.app(m_half, zero_idx);
    let m_half_1 = k.app(m_half, one_idx);
    assert!(
        k.def_eq(m_half_0, half),
        "bernoulliMass RatS (1/2) 0 must be 1/2"
    );
    assert!(
        k.def_eq(m_half_1, half),
        "bernoulliMass RatS (1/2) 1 must be 1/2"
    );

    // q = 1/3 : the two outcomes DIFFER, so this is the discriminating case.
    let m_third = bmass_fn(&mut k, &p, third);
    let m_third_0 = k.app(m_third, zero_idx);
    let m_third_1 = k.app(m_third, one_idx);
    assert!(
        k.def_eq(m_third_0, two_thirds),
        "bernoulliMass RatS (1/3) 0 must be 2/3"
    );
    assert!(
        k.def_eq(m_third_1, third),
        "bernoulliMass RatS (1/3) 1 must be 1/3"
    );

    // **Negative control**: the failure weight is not the success weight at
    // `q = 1/3`. A mass function that returned `q` at both outcomes would
    // pass every assertion above except this one.
    assert!(
        !k.def_eq(m_third_0, third),
        "bernoulliMass RatS (1/3) 0 must NOT be 1/3 — the two outcomes differ"
    );
}

// ---------------------------------------------------------------------------
// 2. The generic theorems, instantiated at ℚ.
// ---------------------------------------------------------------------------

/// `E[X] = q` at `q = 1/2` and `q = 1/3` — the VALUE, computed by the
/// kernel, not the proof term's word for it.
#[test]
fn bernoulli_expectation_computes_to_the_parameter() {
    let (mut k, p) = prelude();

    let half = frac(&mut k, &p, 1, 1);
    let mean_half = bernoulli_mean(&mut k, &p, half);
    assert!(
        k.def_eq(mean_half, half),
        "the Bernoulli(1/2) mean must compute to 1/2"
    );

    let third = frac(&mut k, &p, 1, 2);
    let mean_third = bernoulli_mean(&mut k, &p, third);
    assert!(
        k.def_eq(mean_third, third),
        "the Bernoulli(1/3) mean must compute to 1/3"
    );

    // **Negative control**: the Bernoulli(1/3) mean is not 1/2. Without it a
    // `def_eq` that had degenerated into "any two rationals are equal" would
    // be invisible.
    assert!(
        !k.def_eq(mean_third, half),
        "the Bernoulli(1/3) mean must NOT compute to 1/2"
    );
}

/// The instantiated `bernoulli_expectation` proof term type-checks at `ℚ`
/// and its type is the `ℚ` statement — the theorem, not just the value.
#[test]
fn bernoulli_expectation_instance_type_checks_at_rat() {
    let (mut k, p) = prelude();
    assert!(
        k.environment().contains(p.binomial_s.bernoulli_expectation),
        "AlgS.OrderedRing.bernoulli_expectation must be declared — an absent \
         name type-checks nothing and reports no error"
    );

    let r = rat_s(&mut k, &p);
    let third = frac(&mut k, &p, 1, 2);
    let head = k.const_(p.binomial_s.bernoulli_expectation, vec![]);
    let e1 = k.app(head, r);
    let instance = k.app(e1, third);
    let got = k
        .infer(instance)
        .expect("the ℚ instance of bernoulli_expectation must type-check");

    let mean = bernoulli_mean(&mut k, &p, third);
    let want = {
        let rat = k.const_(p.int.rat, vec![]);
        let l1 = {
            let z = k.level_zero();
            k.level_succ(z)
        };
        let eq = k.const_(p.int.nat.logic.eq, vec![l1]);
        let e1 = k.app(eq, rat);
        let e2 = k.app(e1, mean);
        k.app(e2, third)
    };
    assert!(
        k.def_eq(got, want),
        "the instance's type must be the ℚ statement `E[Bernoulli(1/3)] = 1/3`"
    );

    // **Negative control**: it is not the statement with 1/2 on the right.
    let half = frac(&mut k, &p, 1, 1);
    let wrong = {
        let rat = k.const_(p.int.rat, vec![]);
        let l1 = {
            let z = k.level_zero();
            k.level_succ(z)
        };
        let eq = k.const_(p.int.nat.logic.eq, vec![l1]);
        let e1 = k.app(eq, rat);
        let e2 = k.app(e1, mean);
        k.app(e2, half)
    };
    assert!(
        !k.def_eq(got, wrong),
        "the instance must NOT prove `E[Bernoulli(1/3)] = 1/2`"
    );
}

/// `Var[X] = q(1−q)`: `1/4` at `q = 1/2`, and `2/9` at `q = 1/3`.
#[test]
fn bernoulli_variance_computes_to_q_times_one_minus_q() {
    let (mut k, p) = prelude();

    let half = frac(&mut k, &p, 1, 1);
    let quarter = frac(&mut k, &p, 1, 3);
    let var_half = bernoulli_var_value(&mut k, &p, half);
    assert!(
        k.def_eq(var_half, quarter),
        "the Bernoulli(1/2) variance must compute to 1/4"
    );

    let third = frac(&mut k, &p, 1, 2);
    let two_ninths = frac(&mut k, &p, 2, 8);
    let var_third = bernoulli_var_value(&mut k, &p, third);
    assert!(
        k.def_eq(var_third, two_ninths),
        "the Bernoulli(1/3) variance must compute to 2/9"
    );
}

/// **The negative control the `p·p` mutant needs.** At `q = 1/2` the true
/// variance `q(1−q)` and the wrong one `q·q` are BOTH `1/4`, so a test at
/// `1/2` alone cannot distinguish them. At `q = 1/3` they are `2/9` and
/// `1/9`, and this test demands the second is wrong.
#[test]
fn bernoulli_variance_at_a_third_is_not_q_squared() {
    let (mut k, p) = prelude();
    let third = frac(&mut k, &p, 1, 2);
    let ninth = frac(&mut k, &p, 1, 8);
    let var_third = bernoulli_var_value(&mut k, &p, third);
    assert!(
        !k.def_eq(var_third, ninth),
        "the Bernoulli(1/3) variance must NOT be q·q = 1/9"
    );

    // Positive control on the same machinery: 1/9 is a real rational the
    // kernel can compare, so the negative above is a decision and not a
    // stuck reduction.
    let ninth_again = frac(&mut k, &p, 1, 8);
    assert!(
        k.def_eq(ninth, ninth_again),
        "1/9 must be definitionally equal to itself — if this fails, the \
         negative control above proves nothing"
    );

    // And at `q = 1/2` the two DO agree, which is the measurement that says
    // why the `1/3` instance is mandatory rather than decorative.
    let half = frac(&mut k, &p, 1, 1);
    let quarter = frac(&mut k, &p, 1, 3);
    let var_half = bernoulli_var_value(&mut k, &p, half);
    assert!(
        k.def_eq(var_half, quarter),
        "at q = 1/2 the true variance and q·q coincide at 1/4 — this is the \
         reason the 1/3 instance exists"
    );
}

/// The instantiated `bernoulli_isDistribution` needs `0 ≤ q` and `q ≤ 1`,
/// and at `q = 1/3` both are decided by `Rat.ble`, so the whole
/// `IsDistribution` is discharged with no assumption at all.
#[test]
fn bernoulli_is_distribution_instance_type_checks_at_rat() {
    let (mut k, p) = prelude();
    assert!(
        k.environment()
            .contains(p.binomial_s.bernoulli_is_distribution),
        "AlgS.OrderedRing.bernoulli_isDistribution must be declared"
    );

    let r = rat_s(&mut k, &p);
    let third = frac(&mut k, &p, 1, 2);
    let zero_r = k.const_(p.zero, vec![]);
    let one_r = k.const_(p.one, vec![]);

    let true_b = k.const_(p.int.nat.logic.bool_true, vec![]);
    let refl_true = {
        let bool_ty = k.const_(p.int.nat.logic.bool_, vec![]);
        let l1 = {
            let z = k.level_zero();
            k.level_succ(z)
        };
        let refl = k.const_(p.int.nat.logic.eq_refl, vec![l1]);
        let e1 = k.app(refl, bool_ty);
        k.app(e1, true_b)
    };
    let le_of_ble = |k: &mut Kernel, a: ExprId, b: ExprId| -> ExprId {
        let c = k.const_(p.le_of_ble_eq_true, vec![]);
        let e1 = k.app(c, a);
        let e2 = k.app(e1, b);
        k.app(e2, refl_true)
    };
    let h0 = le_of_ble(&mut k, zero_r, third);
    let h1 = le_of_ble(&mut k, third, one_r);

    let head = k.const_(p.binomial_s.bernoulli_is_distribution, vec![]);
    let e1 = k.app(head, r);
    let e2 = k.app(e1, third);
    let e3 = k.app(e2, h0);
    let instance = k.app(e3, h1);
    let got = k
        .infer(instance)
        .expect("the ℚ instance of bernoulli_isDistribution must type-check");

    let want = {
        let mass = bmass_fn(&mut k, &p, third);
        let two = nat_num(&mut k, &p, 2);
        let c = k.const_(p.probability_s.is_distribution, vec![]);
        let a1 = k.app(c, r);
        let a2 = k.app(a1, mass);
        k.app(a2, two)
    };
    assert!(
        k.def_eq(got, want),
        "the instance must prove `IsDistribution RatS (bernoulliMass RatS 1/3) 2`"
    );
}

// ---------------------------------------------------------------------------
// 3. The trusted base.
// ---------------------------------------------------------------------------

/// Every declaration this module adds is axiom-free — asserted only AFTER
/// the environment is asked whether the name exists, because
/// `axiom_footprint` of a name that was never declared is also empty.
#[test]
fn binomial_s_declarations_are_axiom_free() {
    let (k, p) = prelude();
    let g = p.binomial_s;
    let names = [
        g.mul_neg,
        g.zero_add,
        g.bernoulli_var,
        g.bernoulli_mass,
        g.bernoulli_mass_nonneg,
        g.bernoulli_is_distribution,
        g.bernoulli_expectation,
        g.bernoulli_variance,
    ];
    for name in names {
        assert!(
            k.environment().contains(name),
            "the name must be DECLARED before its footprint means anything — \
             an absent name has an empty footprint too"
        );
        assert!(
            k.axiom_footprint(name).is_empty(),
            "every ADR-1631 declaration must be axiom-free"
        );
    }
    assert_eq!(
        names.len(),
        8,
        "ADR-1631 declares 8 names; update the ADR if this moves"
    );
}

/// The two new generic ring lemmas are the ones the spine did NOT have, and
/// they are genuinely different statements: `neg_mul` and `mul_neg` disagree
/// on which factor is negated, so neither can stand in for the other in a
/// ring without `mulComm`.
#[test]
fn mul_neg_is_not_neg_mul() {
    let (mut k, p) = prelude();
    assert!(
        k.environment().contains(p.binomial_s.mul_neg),
        "AlgS.OrderedRing.mul_neg must be declared"
    );
    let mul_neg_c = k.const_(p.binomial_s.mul_neg, vec![]);
    let mul_neg_ty = k.infer(mul_neg_c).expect("mul_neg must type-check");
    let neg_mul_c = k.const_(p.probability_s.neg_mul, vec![]);
    let neg_mul_ty = k.infer(neg_mul_c).expect("neg_mul must type-check");
    assert!(
        !k.def_eq(mul_neg_ty, neg_mul_ty),
        "a·(−b) ≃ −(a·b) and (−a)·b ≃ −(a·b) are different statements without \
         mulComm — if the kernel calls them equal this test measures nothing"
    );
    assert!(
        k.def_eq(mul_neg_ty, mul_neg_ty),
        "positive control: mul_neg's type is definitionally itself"
    );
}
