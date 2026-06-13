//! Quantifier refutation by enumerative ground instantiation — handles
//! infinite-domain (`Int`/`Real`) universals that finite-domain expansion
//! cannot (ADR-0016 / E-matching family).

use std::time::Duration;

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{
    CheckResult, SolverConfig, prove_unsat_by_ematching, prove_unsat_by_instantiation,
};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn solve(arena: &mut TermArena, assertions: &[axeyum_ir::TermId]) -> CheckResult {
    prove_unsat_by_instantiation(arena, assertions, &config())
        .expect("instantiation decides or returns unknown without error")
}

#[test]
fn integer_universal_instantiation_is_bounded_unknown() {
    // (forall x:Int. x < 10) is false; instantiating x:=10 gives 10 < 10 (false),
    // so the instantiation is unsatisfiable. But integers go through *bounded*
    // bit-blasting, whose `unsat` is only "no model in range" → reported
    // `unknown` (ADR-0014). So integer-universal refutation degrades to
    // `unknown`, unlike the exact real case below.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let ten = arena.int_const(10);
    let body = arena.int_lt(x, ten).unwrap();
    let all = arena.forall(x_sym, body).unwrap();
    let c = arena.declare("c", Sort::Int).unwrap();
    let cv = arena.var(c);
    let c_is_10 = arena.eq(cv, ten).unwrap();

    assert!(matches!(
        solve(&mut arena, &[all, c_is_10]),
        CheckResult::Unknown(_)
    ));
}

#[test]
fn quantifier_free_query_decides_exactly() {
    // No universal to instantiate: the result is exact (sat).
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let two = arena.int_const(2);
    let five = arena.int_const(5);
    let sum = arena.int_add(x, two).unwrap();
    let eq = arena.eq(sum, five).unwrap();
    assert!(matches!(solve(&mut arena, &[eq]), CheckResult::Sat(_)));
}

#[test]
fn satisfiable_instantiation_is_inconclusive() {
    // (forall x:Int. x >= 0) instantiated only with the constant 3 gives 3 >= 0
    // = true; the instantiation is satisfiable but the universal is actually
    // false (e.g. x = -1), so the honest answer is `unknown`, not `sat`.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Int).unwrap();
    let x = arena.var(x_sym);
    let zero = arena.int_const(0);
    let three = arena.int_const(3);
    let body = arena.int_ge(x, zero).unwrap();
    let all = arena.forall(x_sym, body).unwrap();
    let y = arena.declare("y", Sort::Int).unwrap();
    let yv = arena.var(y);
    let y_is_3 = arena.eq(yv, three).unwrap();

    assert!(matches!(
        solve(&mut arena, &[all, y_is_3]),
        CheckResult::Unknown(_)
    ));
}

#[test]
fn real_universal_refuted_by_instantiation() {
    // (forall r:Real. r < 1) refuted by the ground term 1 (1 < 1 is false).
    let mut arena = TermArena::new();
    let r_sym = arena.declare("r", Sort::Real).unwrap();
    let r = arena.var(r_sym);
    let one = arena.real_ratio(1, 1);
    let body = arena.real_lt(r, one).unwrap();
    let all = arena.forall(r_sym, body).unwrap();
    let s = arena.declare("s", Sort::Real).unwrap();
    let sv = arena.var(s);
    let s_is_1 = arena.eq(sv, one).unwrap();

    assert_eq!(solve(&mut arena, &[all, s_is_1]), CheckResult::Unsat);
}

#[test]
fn nested_universal_chain_is_refuted_by_instantiation() {
    // forall x:Real. forall y:Real. x + y >= 0   plus   a < 0.
    // A *nested* universal chain — previously skipped entirely (→ unknown). The
    // chain is now peeled and instantiated over the cartesian product of ground
    // terms {0, a}; the instance x:=a, y:=a gives 2a >= 0, which with a < 0 is
    // unsatisfiable, so the universal is refuted.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let y_sym = arena.declare("y", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let zero = arena.real_ratio(0, 1);
    let sum = arena.real_add(x, y).unwrap();
    let body = arena.real_ge(sum, zero).unwrap();
    let inner = arena.forall(y_sym, body).unwrap();
    let outer = arena.forall(x_sym, inner).unwrap();

    let a = arena.real_var("a").unwrap();
    let a_neg = arena.real_lt(a, zero).unwrap();

    assert_eq!(
        solve(&mut arena, &[outer, a_neg]),
        CheckResult::Unsat,
        "the nested universal is refuted by the x:=a, y:=a instance"
    );
}

#[test]
fn true_nested_universal_is_inconclusive() {
    // forall x:Real. forall y:Real. x + y == y + x is valid, so no instance is
    // false; the (satisfiable) instantiation is honestly reported `unknown`.
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::Real).unwrap();
    let y_sym = arena.declare("y", Sort::Real).unwrap();
    let x = arena.var(x_sym);
    let y = arena.var(y_sym);
    let xy = arena.real_add(x, y).unwrap();
    let yx = arena.real_add(y, x).unwrap();
    let body = arena.eq(xy, yx).unwrap();
    let inner = arena.forall(y_sym, body).unwrap();
    let outer = arena.forall(x_sym, inner).unwrap();
    let a = arena.real_var("a").unwrap();
    let zero = arena.real_ratio(0, 1);
    let a_pos = arena.real_gt(a, zero).unwrap();

    assert!(matches!(
        solve(&mut arena, &[outer, a_pos]),
        CheckResult::Unknown(_)
    ));
}

#[test]
fn ematching_refutes_a_compound_instance_enumeration_misses() {
    // forall x:BV16. g(x) == 0   plus   g(f(a)) != 0.
    // BV16 is too wide for finite expansion, so this exercises instantiation.
    // The refuting instance needs x := f(a) — a *compound* ground term that
    // leaves-only enumeration never tries. So enumerative instantiation cannot
    // refute (it stays `unknown`), but trigger-based E-matching (trigger g(x)
    // matches the ground term g(f(a))) instantiates g(f(a)) == 0 and refutes.
    let build = |arena: &mut TermArena| {
        let bv16 = Sort::BitVec(16);
        let g = arena.declare_fun("g", &[bv16], bv16).unwrap();
        let f = arena.declare_fun("f", &[bv16], bv16).unwrap();
        let a = arena.bv_var("a", 16).unwrap();
        let zero = arena.bv_const(16, 0).unwrap();
        let x_sym = arena.declare("x", bv16).unwrap();
        let x = arena.var(x_sym);
        let gx = arena.apply(g, &[x]).unwrap();
        let body = arena.eq(gx, zero).unwrap();
        let all = arena.forall(x_sym, body).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let gfa = arena.apply(g, &[fa]).unwrap();
        let gfa_eq0 = arena.eq(gfa, zero).unwrap();
        let gfa_ne0 = arena.not(gfa_eq0).unwrap();
        vec![all, gfa_ne0]
    };

    // Leaves-only enumeration cannot reach x := f(a): inconclusive.
    let mut arena_enum = TermArena::new();
    let enum_assertions = build(&mut arena_enum);
    assert!(
        matches!(
            prove_unsat_by_instantiation(&mut arena_enum, &enum_assertions, &config()).unwrap(),
            CheckResult::Unknown(_)
        ),
        "leaves-only enumeration should not refute the compound case"
    );

    // E-matching binds x := f(a) via the trigger g(x) and refutes exactly.
    let mut arena_em = TermArena::new();
    let em_assertions = build(&mut arena_em);
    assert_eq!(
        prove_unsat_by_ematching(&mut arena_em, &em_assertions, &config()).unwrap(),
        CheckResult::Unsat,
        "E-matching should refute via the compound binding x := f(a)"
    );
}
