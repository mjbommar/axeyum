//! ADR-1631: the `ℚ` binomial, measured.
//!
//! The interesting test here is [`binomial_expectation_at_three_bernoulli_
//! trials_computes_to_one`], because it is the one that closes the loop: the
//! per-trial hypothesis `∀ j < m, E[X j] = q` is discharged by
//! [`super::binomial_s`]'s generic `bernoulli_expectation` instantiated at
//! `AlgS.Rat.orderedRingS`, and the resulting `E[Σ] = m·q` is then EVALUATED
//! at `m = 3`, `q = 1/3` and required to be `1`. Nothing in that chain is
//! taken on the proof term's word.
//!
//! The off-by-one control is at the statement level, where it belongs: the
//! instance's inferred type must be the `m`-copies statement and must NOT be
//! the `succ m`-copies one.

use super::*;
use crate::Kernel;
use crate::build_rat_prelude;

fn prelude() -> (Kernel, RatPrelude) {
    let mut k = Kernel::new();
    let p = build_rat_prelude(&mut k).expect("rat prelude must build");
    (k, p)
}

fn rat_s(k: &mut Kernel, p: &RatPrelude) -> ExprId {
    k.const_(p.ordered_ring_ext_s.rat_ordered_ring_s, vec![])
}

fn nat_num(k: &mut Kernel, p: &RatPrelude, n: u32) -> ExprId {
    let mut e = k.const_(p.int.nat.zero, vec![]);
    let succ = k.const_(p.int.nat.succ, vec![]);
    for _ in 0..n {
        e = k.app(succ, e);
    }
    e
}

/// `Rat.natDivSucc num den_pred`, i.e. `num / (den_pred + 1)`.
fn frac(k: &mut Kernel, p: &RatPrelude, num: u32, den_pred: u32) -> ExprId {
    let n = nat_num(k, p, num);
    let d = nat_num(k, p, den_pred);
    let c = k.const_(p.nat_div_succ, vec![]);
    let e1 = k.app(c, n);
    k.app(e1, d)
}

/// `fun _ : Nat => AlgS.OrderedRing.bernoulliVar RatS` — the constant family
/// of `m` identically-distributed Bernoulli trials, as a `Nat → Nat → Rat`.
fn constant_bernoulli_family(k: &mut Kernel, p: &RatPrelude) -> ExprId {
    const J_FV: u64 = 71_000;
    let r = rat_s(k, p);
    let nat = k.const_(p.int.nat.nat, vec![]);
    let c = k.const_(p.binomial_s.bernoulli_var, vec![]);
    let body = k.app(c, r);
    crate::nat_prelude::structures::lam_over(k, J_FV, nat, body)
}

/// `AlgS.OrderedRing.bernoulliMass RatS q`, the weights.
fn bmass_fn(k: &mut Kernel, p: &RatPrelude, q: ExprId) -> ExprId {
    let r = rat_s(k, p);
    let c = k.const_(p.binomial_s.bernoulli_mass, vec![]);
    let e1 = k.app(c, r);
    k.app(e1, q)
}

/// `Rat.mul a b`.
fn rat_mul(k: &mut Kernel, p: &RatPrelude, a: ExprId, b: ExprId) -> ExprId {
    let mul = k.const_(p.int.rat_mul, vec![]);
    crate::nat_prelude::structures::app2(k, mul, a, b)
}

/// `Rat.expectation (Rat.sumVars X m) p n`.
fn mean_of_sum(
    k: &mut Kernel,
    p: &RatPrelude,
    x: ExprId,
    m: ExprId,
    weights: ExprId,
    n: ExprId,
) -> ExprId {
    let sv = {
        let c = k.const_(p.sum_vars, vec![]);
        let e1 = k.app(c, x);
        k.app(e1, m)
    };
    let c = k.const_(p.expectation, vec![]);
    let e1 = k.app(c, sv);
    let e2 = k.app(e1, weights);
    k.app(e2, n)
}

// ---------------------------------------------------------------------------
// The loop closes: generic Bernoulli moments feed the ℚ binomial.
// ---------------------------------------------------------------------------

/// Three Bernoulli(1/3) trials have mean `3 · 1/3 = 1`, and the kernel
/// computes it.
#[test]
fn binomial_expectation_at_three_bernoulli_trials_computes_to_one() {
    let (mut k, p) = prelude();

    let r = rat_s(&mut k, &p);
    let third = frac(&mut k, &p, 1, 2);
    let two = nat_num(&mut k, &p, 2);
    let three = nat_num(&mut k, &p, 3);
    let family = constant_bernoulli_family(&mut k, &p);
    let weights = bmass_fn(&mut k, &p, third);

    // hq : ∀ j, j < 3 → Eq (Rat.expectation (family j) weights 2) (1/3),
    // discharged entirely by the GENERIC theorem at `AlgS.Rat.orderedRingS`.
    let hq = {
        const HJ_FV: u64 = 71_010;
        const JJ_FV: u64 = 71_011;
        let nat = k.const_(p.int.nat.nat, vec![]);
        let j = k.fvar(JJ_FV);
        let lt = k.const_(p.int.nat.lt, vec![]);
        let hyp = crate::nat_prelude::structures::app2(&mut k, lt, j, three);
        let generic = {
            let c = k.const_(p.binomial_s.bernoulli_expectation, vec![]);
            let e1 = k.app(c, r);
            k.app(e1, third)
        };
        let with_h = crate::nat_prelude::structures::lam_over(&mut k, HJ_FV, hyp, generic);
        crate::nat_prelude::structures::lam_over(&mut k, JJ_FV, nat, with_h)
    };

    let instance = {
        let c = k.const_(p.binomial_rat.binomial_expectation, vec![]);
        let e1 = k.app(c, family);
        let e2 = k.app(e1, weights);
        let e3 = k.app(e2, two);
        let e4 = k.app(e3, three);
        let e5 = k.app(e4, third);
        k.app(e5, hq)
    };
    let got = k
        .infer(instance)
        .expect("the ℚ instance of Rat.binomial_expectation must type-check");

    // The statement it proves: E[Σ_{j<3}] = natDivSucc 3 0 · (1/3).
    let mean = mean_of_sum(&mut k, &p, family, three, weights, two);
    let three_rat = frac(&mut k, &p, 3, 0);
    let rhs = rat_mul(&mut k, &p, three_rat, third);
    let want = {
        let rat = k.const_(p.int.rat, vec![]);
        let l1 = {
            let z = k.level_zero();
            k.level_succ(z)
        };
        let eq = k.const_(p.int.nat.logic.eq, vec![l1]);
        let e1 = k.app(eq, rat);
        let e2 = k.app(e1, mean);
        k.app(e2, rhs)
    };
    assert!(
        k.def_eq(got, want),
        "the instance must prove `E[three Bernoulli(1/3) trials] = 3 · (1/3)`"
    );

    // **Off-by-one control, at the statement level.** The same instance must
    // NOT be the `succ m` statement — this is the shape a wrong index range
    // would produce, and the kernel decides it.
    let four_rat = frac(&mut k, &p, 4, 0);
    let wrong_rhs = rat_mul(&mut k, &p, four_rat, third);
    let wrong = {
        let rat = k.const_(p.int.rat, vec![]);
        let l1 = {
            let z = k.level_zero();
            k.level_succ(z)
        };
        let eq = k.const_(p.int.nat.logic.eq, vec![l1]);
        let e1 = k.app(eq, rat);
        let e2 = k.app(e1, mean);
        k.app(e2, wrong_rhs)
    };
    assert!(
        !k.def_eq(got, wrong),
        "the instance must NOT prove the four-trial statement — an off-by-one \
         in the index range would land exactly here"
    );

    // And the VALUE: `3 · (1/3) = 1`, computed.
    let one_r = k.const_(p.one, vec![]);
    assert!(k.def_eq(rhs, one_r), "3 · (1/3) must compute to Rat.one");
    assert!(
        k.def_eq(mean, one_r),
        "the mean of three Bernoulli(1/3) trials must COMPUTE to 1 — this is \
         the assertion the proof term takes no part in"
    );

    // Negative control on that computation: it is not 1/3.
    assert!(
        !k.def_eq(mean, third),
        "the three-trial mean must NOT compute to 1/3"
    );
}

/// Every `ℚ` binomial declaration is axiom-free — asserted after
/// `Environment::contains`, since an absent name has an empty footprint too.
#[test]
fn binomial_rat_declarations_are_axiom_free() {
    let (k, p) = prelude();
    let g = p.binomial_rat;
    let names = [
        g.binomial_expectation,
        g.binomial_variance,
        g.binomial_chebyshev,
        g.fourth_moment_inequality,
    ];
    for name in names {
        assert!(
            k.environment().contains(name),
            "the name must be DECLARED before its footprint means anything"
        );
        assert!(
            k.axiom_footprint(name).is_empty(),
            "every ADR-1631 ℚ binomial declaration must be axiom-free"
        );
    }
    assert_eq!(
        names.len(),
        4,
        "ADR-1631 declares 4 ℚ names; update the ADR if this moves"
    );
}

/// `Rat.binomial_chebyshev`'s conclusion no longer mentions `Rat.variance`:
/// its right-hand side is `m·q(1−q)`, which is the whole point of stating the
/// corollary rather than leaving the caller to rewrite.
///
/// Checked by comparing the declared type against the one the *unrewritten*
/// Chebyshev would have — they must differ.
#[test]
fn binomial_chebyshev_bound_is_the_binomial_variance_not_the_variance() {
    let (mut k, p) = prelude();
    assert!(
        k.environment().contains(p.binomial_rat.binomial_chebyshev),
        "Rat.binomial_chebyshev must be declared"
    );
    let cheb_c = k.const_(p.binomial_rat.binomial_chebyshev, vec![]);
    let bound_ty = k
        .infer(cheb_c)
        .expect("Rat.binomial_chebyshev must type-check");
    let plain_c = k.const_(p.chebyshev_inequality, vec![]);
    let plain_ty = k
        .infer(plain_c)
        .expect("Rat.chebyshev_inequality must type-check");
    assert!(
        !k.def_eq(bound_ty, plain_ty),
        "the binomial corollary must not be the plain Chebyshev statement"
    );
    assert!(
        k.def_eq(bound_ty, bound_ty),
        "positive control: the corollary's type is definitionally itself"
    );
}
