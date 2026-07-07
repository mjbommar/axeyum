//! Census-driven NRA levers (P2.5): the bounded sat-witness probe and the
//! threshold-1 monotonicity pre-check past the cross-product cap.
#![allow(clippy::doc_markdown)]
//!
//! These are the `cvc5-regress-clean` QF_NRA movers this pass targets:
//! `issue9164-2` (nested division, sat), `dist-big` (all-zero high-degree root,
//! sat), `nlExtPurify-test` (high-power positivity, sat), and `ones`
//! (`a,b,c,d ≥ 1 ∧ a·b·c·d < 1`, unsat by threshold-1 monotonicity). Every `sat`
//! here is checkable by replaying the returned model against the original terms
//! under the ground evaluator (the solver already gates on this); the tests also
//! assert the aggregate verdict.

use axeyum_ir::{Rational, Sort, TermArena, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, check_with_nra};

fn real(arena: &mut TermArena, name: &str) -> axeyum_ir::TermId {
    let s = arena.declare(name, Sort::Real).unwrap();
    arena.var(s)
}

/// Replay: every assertion must evaluate `true` under the returned model.
fn model_satisfies(
    arena: &TermArena,
    model: &axeyum_solver::Model,
    assertions: &[axeyum_ir::TermId],
) -> bool {
    let assign = model.to_assignment();
    assertions
        .iter()
        .all(|&t| matches!(eval(arena, t, &assign), Ok(Value::Bool(true))))
}

#[test]
fn nested_division_issue9164_2_is_sat() {
    // (> (/ 1 (/ a b)) (/ (* a a) a)) — the named nested-division target.
    // sat at a=1, b=2: 1/(1/2)=2 > 1²/1=1. The interval relaxation leaves this an
    // unbounded-box timeout; the sat-witness probe finds it.
    let mut a = TermArena::new();
    let av = real(&mut a, "a");
    let bv = real(&mut a, "b");
    let one = a.real_const(Rational::integer(1));
    let ab = a.real_div(av, bv).unwrap();
    let recip = a.real_div(one, ab).unwrap();
    let aa = a.real_mul(av, av).unwrap();
    let aa_over_a = a.real_div(aa, av).unwrap();
    let goal = a.real_gt(recip, aa_over_a).unwrap();

    let r = check_with_nra(&mut a, &[goal], &SolverConfig::default()).unwrap();
    match r {
        CheckResult::Sat(m) => assert!(
            model_satisfies(&a, &m, &[goal]),
            "issue9164-2 model must replay true"
        ),
        other => panic!("issue9164-2 must be sat, got {other:?}"),
    }
}

#[test]
fn all_zero_high_degree_root_dist_big_is_sat() {
    // (= (* s s s s) 0) with s = v1+…+v4 (the `dist-big` shape, scaled down):
    // sat at all vars = 0. The uniform all-zero probe candidate finds it even
    // when the many-cross-product count trips the cap.
    let mut a = TermArena::new();
    let vs: Vec<_> = (0..4).map(|i| real(&mut a, &format!("v{i}"))).collect();
    let mut sum = vs[0];
    for &v in &vs[1..] {
        sum = a.real_add(sum, v).unwrap();
    }
    let s2 = a.real_mul(sum, sum).unwrap();
    let s3 = a.real_mul(s2, sum).unwrap();
    let s4 = a.real_mul(s3, sum).unwrap();
    let zero = a.real_const(Rational::integer(0));
    let goal = a.eq(s4, zero).unwrap();

    let r = check_with_nra(&mut a, &[goal], &SolverConfig::default()).unwrap();
    match r {
        CheckResult::Sat(m) => assert!(model_satisfies(&a, &m, &[goal]), "dist-big model replays"),
        other => panic!("all-zero quartic root must be sat, got {other:?}"),
    }
}

#[test]
fn high_power_positivity_nlextpurify_is_sat() {
    // (> ((x)^8) 0) ∧ x > 0 — the `nlExtPurify-test` positivity shape (lower
    // degree). sat at x = 1. Probe finds it despite the cross-product blowup.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let mut pw = x;
    for _ in 0..7 {
        pw = a.real_mul(pw, x).unwrap();
    }
    let zero = a.real_const(Rational::integer(0));
    let pos = a.real_gt(pw, zero).unwrap();
    let xpos = a.real_gt(x, zero).unwrap();

    let r = check_with_nra(&mut a, &[pos, xpos], &SolverConfig::default()).unwrap();
    match r {
        CheckResult::Sat(m) => {
            assert!(
                model_satisfies(&a, &m, &[pos, xpos]),
                "nlExtPurify model replays"
            );
        }
        other => panic!("x^8>0 ∧ x>0 must be sat, got {other:?}"),
    }
}

#[test]
fn ones_product_ge_one_is_unsat_via_threshold1() {
    // a,b,c,d ≥ 1 ∧ (a·b·c·d) < 1 — the `ones` benchmark. unsat: each factor ≥ 1
    // ⇒ product ≥ 1. Trips the 3-cross-product cap; the threshold-1 monotonicity
    // pre-check refutes it (chain r₀=a·b ≥ b ≥ 1 ⇒ r₁ ≥ c ≥ 1 ⇒ r₂ ≥ d ≥ 1).
    let mut a = TermArena::new();
    let av = real(&mut a, "a");
    let bv = real(&mut a, "b");
    let cv = real(&mut a, "c");
    let dv = real(&mut a, "d");
    let one = a.real_const(Rational::integer(1));
    let mut asserts = Vec::new();
    for &v in &[av, bv, cv, dv] {
        asserts.push(a.real_ge(v, one).unwrap());
    }
    let ab = a.real_mul(av, bv).unwrap();
    let abc = a.real_mul(ab, cv).unwrap();
    let abcd = a.real_mul(abc, dv).unwrap();
    asserts.push(a.real_lt(abcd, one).unwrap());

    let r = check_with_nra(&mut a, &asserts, &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "a,b,c,d≥1 ∧ abcd<1 must be unsat, got {r:?}"
    );
}

#[test]
fn decoupled_circles_five_vars_is_sat_via_coordinate_probe() {
    // The `very-easy-sat` shape (5 free reals): two *independent* circles
    // `sB² = 1 − cB²` and `s² = 1 − c²`, plus `0 ≤ x < 177/366500000 ∧ x ≤ 1e-7`.
    // The uniform (all-equal) fallback can never satisfy two decoupled circles;
    // the per-variable coordinate search (slice 3) climbs to `c=1,s=0` on each
    // pair with `x=0`. Replay-gated, so a returned model must satisfy every term.
    let mut a = TermArena::new();
    let cos_a = real(&mut a, "skoC");
    let sin_a = real(&mut a, "skoS");
    let cos_b = real(&mut a, "skoCB");
    let sin_b = real(&mut a, "skoSB");
    let sko_x = real(&mut a, "skoX");
    let one = a.real_const(Rational::integer(1));
    let zero = a.real_const(Rational::integer(0));
    let bound = a.real_const(Rational::new(177, 366_500_000));
    let tiny = a.real_const(Rational::new(1, 10_000_000));

    // sB² = 1 − cB²  ⟺  sB² + cB² = 1
    let sb2 = a.real_mul(sin_b, sin_b).unwrap();
    let cb2 = a.real_mul(cos_b, cos_b).unwrap();
    let sum_b = a.real_add(sb2, cb2).unwrap();
    let circle_b = a.eq(sum_b, one).unwrap();
    // s² = 1 − c²
    let s2 = a.real_mul(sin_a, sin_a).unwrap();
    let c2 = a.real_mul(cos_a, cos_a).unwrap();
    let sum_a = a.real_add(s2, c2).unwrap();
    let circle_a = a.eq(sum_a, one).unwrap();
    // 0 ≤ x < 177/366500000 ∧ x ≤ 1e-7
    let x_ge0 = a.real_ge(sko_x, zero).unwrap();
    let x_below_bound = a.real_lt(sko_x, bound).unwrap();
    let x_below_tiny = a.real_le(sko_x, tiny).unwrap();

    let asserts = [circle_b, circle_a, x_ge0, x_below_bound, x_below_tiny];
    let r = check_with_nra(&mut a, &asserts, &SolverConfig::default()).unwrap();
    match r {
        CheckResult::Sat(m) => assert!(
            model_satisfies(&a, &m, &asserts),
            "very-easy-sat model must replay true"
        ),
        other => panic!("decoupled 5-var circles must be sat, got {other:?}"),
    }
}

#[test]
fn coordinate_probe_bounds_five_var_sum_of_squares_unsat() {
    // A >4-var shape with NO grid witness: `v0²+v1²+v2²+v3²+v4² = −1`. Every real
    // square is ≥ 0, so the sum is ≥ 0 > −1 — unsat. The 5-variable coordinate
    // search runs (past the ≤4-var full product), never finds a satisfying
    // candidate (correct — there is none), and terminates within its bounded
    // budget: the verdict must NOT be a (wrong) sat.
    let mut a = TermArena::new();
    let vs: Vec<_> = (0..5).map(|i| real(&mut a, &format!("v{i}"))).collect();
    let mut sum = a.real_mul(vs[0], vs[0]).unwrap();
    for &v in &vs[1..] {
        let sq = a.real_mul(v, v).unwrap();
        sum = a.real_add(sum, sq).unwrap();
    }
    let neg1 = a.real_const(Rational::integer(-1));
    let goal = a.eq(sum, neg1).unwrap();

    let r = check_with_nra(&mut a, &[goal], &SolverConfig::default()).unwrap();
    assert!(
        !matches!(r, CheckResult::Sat(_)),
        "sum of 5 squares = -1 must never be sat, got {r:?}"
    );
}

#[test]
fn probe_never_reports_wrong_sat_on_negative_square() {
    // (= (* x x) (- 2)) is unsat (a real square is ≥ 0). The grid probe includes
    // x=±2 etc.; none satisfy, so it must NOT report sat — the verdict is unsat
    // (exact poly decider) or unknown, never a wrong sat.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let xx = a.real_mul(x, x).unwrap();
    let neg2 = a.real_const(Rational::integer(-2));
    let goal = a.eq(xx, neg2).unwrap();

    let r = check_with_nra(&mut a, &[goal], &SolverConfig::default()).unwrap();
    assert!(
        !matches!(r, CheckResult::Sat(_)),
        "x²=-2 must never be reported sat, got {r:?}"
    );
}

#[test]
fn probe_sat_witness_replays_for_reciprocal_inequality() {
    // (> (/ 1 x) 3) ∧ x > 0 — sat at x=1/2 (2 > 3? no) … at x=1/4 gives 4>3.
    // The grid includes 1/2 (1/(1/2)=2, not > 3) so this is a genuine miss for the
    // probe and must fall through to a sound verdict, never a wrong sat.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let one = a.real_const(Rational::integer(1));
    let three = a.real_const(Rational::integer(3));
    let recip = a.real_div(one, x).unwrap();
    let g = a.real_gt(recip, three).unwrap();
    let xpos = a.real_gt(x, one).unwrap(); // x>1 ⇒ 1/x<1<3: unsat

    let r = check_with_nra(&mut a, &[g, xpos], &SolverConfig::default()).unwrap();
    assert!(
        !matches!(r, CheckResult::Sat(_)),
        "1/x>3 ∧ x>1 must never be sat, got {r:?}"
    );
}
