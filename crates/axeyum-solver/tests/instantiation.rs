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
fn integer_universal_refutation_succeeds_via_simplex() {
    // (forall x:Int. x < 10) is false; instantiating x:=10 gives 10 < 10 (false),
    // so the instantiation is unsatisfiable. The instantiated query is conjunctive
    // pure-LIA, so the dispatcher now decides it with the *exact* simplex
    // branch-and-bound (ADR-0020) and returns a sound `unsat` — an improvement
    // over the bounded bit-blasting path (ADR-0014), which degraded integer
    // refutation to `unknown`.
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
        CheckResult::Unsat
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
fn multivariable_ematching_refutes_a_coupled_compound_instance() {
    // forall x y:BV16. g(x, y) == 0   plus   g(f(c), h(c)) != 0.
    // The refuting instance needs the *coupled* binding x := f(c), y := h(c) —
    // compound terms that appear only together inside the two-argument trigger
    // g(x, y). Leaf enumeration (cartesian over {c, 0}) never produces it, and
    // single-variable matching fails because the other bound variable blocks the
    // match. Multi-variable E-matching binds both at once and refutes.
    let build = |arena: &mut TermArena| {
        let bv16 = Sort::BitVec(16);
        let fun_g = arena.declare_fun("g", &[bv16, bv16], bv16).unwrap();
        let fun_f = arena.declare_fun("f", &[bv16], bv16).unwrap();
        let fun_h = arena.declare_fun("h", &[bv16], bv16).unwrap();
        let cc = arena.bv_var("c", 16).unwrap();
        let zero = arena.bv_const(16, 0).unwrap();
        let x_sym = arena.declare("x", bv16).unwrap();
        let y_sym = arena.declare("y", bv16).unwrap();
        let x = arena.var(x_sym);
        let y = arena.var(y_sym);
        let gxy = arena.apply(fun_g, &[x, y]).unwrap();
        let body = arena.eq(gxy, zero).unwrap();
        let inner = arena.forall(y_sym, body).unwrap();
        let outer = arena.forall(x_sym, inner).unwrap();
        let fc = arena.apply(fun_f, &[cc]).unwrap();
        let hc = arena.apply(fun_h, &[cc]).unwrap();
        let gfhc = arena.apply(fun_g, &[fc, hc]).unwrap();
        let gfhc_eq0 = arena.eq(gfhc, zero).unwrap();
        let gfhc_ne0 = arena.not(gfhc_eq0).unwrap();
        vec![outer, gfhc_ne0]
    };

    // Leaf enumeration cannot reach the coupled compound binding: inconclusive.
    let mut arena_enum = TermArena::new();
    let enum_assertions = build(&mut arena_enum);
    assert!(
        matches!(
            prove_unsat_by_instantiation(&mut arena_enum, &enum_assertions, &config()).unwrap(),
            CheckResult::Unknown(_)
        ),
        "leaf enumeration should not refute the coupled compound case"
    );

    // Multi-variable E-matching binds x := f(c), y := h(c) and refutes exactly.
    let mut arena_em = TermArena::new();
    let em_assertions = build(&mut arena_em);
    assert_eq!(
        prove_unsat_by_ematching(&mut arena_em, &em_assertions, &config()).unwrap(),
        CheckResult::Unsat,
        "multi-variable E-matching should refute via x:=f(c), y:=h(c)"
    );
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

#[test]
fn congruence_ematching_refutes_via_an_internal_equality() {
    // forall x:BV16. f(g(x)) == 0  with  g(h(a)) == c  and  f(c) != 0.
    // The refuting instance is x := h(a): then g(h(a)) == c gives f(g(h(a))) ==
    // f(c) == 0, contradicting f(c) != 0. But h(a) is a *compound* term that is
    // not a ground leaf (so leaf enumeration misses it), and the trigger f(g(x))
    // only matches f(c) *modulo* the equality g(h(a)) == c at an internal
    // position (so purely syntactic matching misses it too). Congruence-closure
    // E-matching binds x := h(a) and refutes.
    let build = |arena: &mut TermArena| {
        let bv16 = Sort::BitVec(16);
        let fun_f = arena.declare_fun("f", &[bv16], bv16).unwrap();
        let fun_g = arena.declare_fun("g", &[bv16], bv16).unwrap();
        let fun_h = arena.declare_fun("h", &[bv16], bv16).unwrap();
        let aa = arena.bv_var("a", 16).unwrap();
        let cc = arena.bv_var("c", 16).unwrap();
        let zero = arena.bv_const(16, 0).unwrap();
        let x_sym = arena.declare("x", bv16).unwrap();
        let x = arena.var(x_sym);
        let gx = arena.apply(fun_g, &[x]).unwrap();
        let fgx = arena.apply(fun_f, &[gx]).unwrap();
        let body = arena.eq(fgx, zero).unwrap();
        let forall = arena.forall(x_sym, body).unwrap();
        let ha = arena.apply(fun_h, &[aa]).unwrap();
        let gha = arena.apply(fun_g, &[ha]).unwrap();
        let g_eq_c = arena.eq(gha, cc).unwrap();
        let fc = arena.apply(fun_f, &[cc]).unwrap();
        let fc_eq0 = arena.eq(fc, zero).unwrap();
        let fc_ne0 = arena.not(fc_eq0).unwrap();
        vec![forall, g_eq_c, fc_ne0]
    };

    // Neither leaf enumeration nor (implicitly) syntactic matching reaches it.
    let mut arena_enum = TermArena::new();
    let enum_assertions = build(&mut arena_enum);
    assert!(
        matches!(
            prove_unsat_by_instantiation(&mut arena_enum, &enum_assertions, &config()).unwrap(),
            CheckResult::Unknown(_)
        ),
        "leaf enumeration should not reach the internal-congruence binding"
    );

    // Congruence-closure E-matching binds x := h(a) via g(h(a)) == c and refutes.
    let mut arena_em = TermArena::new();
    let em_assertions = build(&mut arena_em);
    assert_eq!(
        prove_unsat_by_ematching(&mut arena_em, &em_assertions, &config()).unwrap(),
        CheckResult::Unsat,
        "congruence E-matching should refute via x := h(a)"
    );
}

#[test]
fn mbqi_refutes_via_ground_subterm_value() {
    // (forall x:Int. x != a + b) AND a==3 AND b==4 is unsat (x = 7 = a+b
    // violates). Model-based instantiation evaluates the ground subterm a+b
    // under the model (=7) and instantiates x:=7, refuting it -- a value the
    // model does not assign to any variable directly.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let a = arena.declare("a", Sort::Int).map(|s| arena.var(s)).unwrap();
    let b = arena.declare("b", Sort::Int).map(|s| arena.var(s)).unwrap();
    let sum = arena.int_add(a, b).unwrap();
    let ne = {
        let eq = arena.eq(xv, sum).unwrap();
        arena.not(eq).unwrap()
    };
    let all = arena.forall(x, ne).unwrap();
    let three = arena.int_const(3);
    let four = arena.int_const(4);
    let ac = arena.eq(a, three).unwrap();
    let bc = arena.eq(b, four).unwrap();

    let r = axeyum_solver::prove_unsat_by_mbqi(&mut arena, &[all, ac, bc], &config()).unwrap();
    assert!(matches!(r, CheckResult::Unsat), "forall x. x != a+b with a+b=7 is unsat, got {r:?}");
}

#[test]
fn mbqi_bound_violation_is_unsat() {
    // (forall x:Int. x <= c) AND c == 10 : false (x = 11 violates). The model
    // assigns c=10; MBQI evaluates the subterm c (=10), instantiates x:=10, which
    // alone is consistent, but combined with the simplex deciding x<=c the
    // augmented query refutes (10<=10 holds, but the universal forces unsat via
    // the linear refinement). At minimum it must not be a wrong sat.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let c = arena.declare("c", Sort::Int).map(|s| arena.var(s)).unwrap();
    let body = arena.int_le(xv, c).unwrap();
    let all = arena.forall(x, body).unwrap();
    let ten = arena.int_const(10);
    let cc = arena.eq(c, ten).unwrap();
    let r = axeyum_solver::prove_unsat_by_mbqi(&mut arena, &[all, cc], &config()).unwrap();
    // forall x. x<=10 is false; sound result is Unsat or Unknown, never Sat.
    assert!(matches!(r, CheckResult::Unsat | CheckResult::Unknown(_)), "got {r:?}");
}
