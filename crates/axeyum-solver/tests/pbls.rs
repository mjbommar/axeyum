//! Tests for the word-level local-search (PBLS) portfolio engine (P1.7).
//!
//! Soundness contract: `solve_local_search` returns `Sat` only with a model the
//! evaluator confirms, never `Unsat` (it cannot refute), and `Unknown` when it
//! gives up or the query is out of scope. The differential check confirms it
//! never contradicts the complete eager backend.

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SatBvBackend, SolverBackend, SolverConfig, solve_local_search};

fn cfg() -> SolverConfig {
    SolverConfig::default().with_timeout(Duration::from_secs(5))
}

fn model_satisfies(arena: &TermArena, model: &axeyum_solver::Model, assertions: &[TermId]) {
    let asg = model.to_assignment();
    for &a in assertions {
        assert_eq!(
            eval(arena, a, &asg).unwrap(),
            Value::Bool(true),
            "local-search model must satisfy assertion #{}",
            a.index()
        );
    }
}

#[test]
fn finds_a_model_for_a_satisfiable_bv_formula() {
    // x + y == 10 ∧ x <u 5 over 8-bit BV — satisfiable (e.g. x=4, y=6).
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let y = arena.declare("y", Sort::BitVec(8)).unwrap();
    let (xv, yv) = (arena.var(x), arena.var(y));
    let sum = arena.bv_add(xv, yv).unwrap();
    let ten = arena.bv_const(8, 10).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let a1 = arena.eq(sum, ten).unwrap();
    let a2 = arena.bv_ult(xv, five).unwrap();

    let out = solve_local_search(&arena, &[a1, a2], &cfg()).unwrap();
    let CheckResult::Sat(model) = out.result else {
        panic!("local search should find a model, got {:?}", out.result);
    };
    model_satisfies(&arena, &model, &[a1, a2]);
}

#[test]
fn solves_a_boolean_formula() {
    // (p ∨ q) ∧ ¬q  ⇒  p true, q false.
    let mut arena = TermArena::new();
    let p = arena.declare("p", Sort::Bool).unwrap();
    let q = arena.declare("q", Sort::Bool).unwrap();
    let (pv, qv) = (arena.var(p), arena.var(q));
    let por = arena.or(pv, qv).unwrap();
    let nq = arena.not(qv).unwrap();

    let out = solve_local_search(&arena, &[por, nq], &cfg()).unwrap();
    let CheckResult::Sat(model) = out.result else {
        panic!("expected sat, got {:?}", out.result);
    };
    model_satisfies(&arena, &model, &[por, nq]);
}

#[test]
fn never_reports_unsat_on_an_unsatisfiable_formula() {
    // x <u 3 ∧ x >u 10 is unsatisfiable; local search must return Unknown, never
    // a (wrong) Sat and never Unsat (it cannot refute).
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let xv = arena.var(x);
    let three = arena.bv_const(8, 3).unwrap();
    let ten = arena.bv_const(8, 10).unwrap();
    let a1 = arena.bv_ult(xv, three).unwrap();
    let a2 = arena.bv_ugt(xv, ten).unwrap();

    let out = solve_local_search(&arena, &[a1, a2], &cfg()).unwrap();
    assert!(
        matches!(out.result, CheckResult::Unknown(_)),
        "must be Unknown (never Sat or Unsat), got {:?}",
        out.result
    );
}

#[test]
fn returns_unknown_for_an_unsupported_sort() {
    // An integer variable is outside the engine's Bool/BV scope.
    let mut arena = TermArena::new();
    let n = arena.declare("n", Sort::Int).unwrap();
    let nv = arena.var(n);
    let zero = arena.int_const(0);
    let a1 = arena.eq(nv, zero).unwrap();

    let out = solve_local_search(&arena, &[a1], &cfg()).unwrap();
    assert!(
        matches!(out.result, CheckResult::Unknown(_)),
        "unsupported sort must yield Unknown, got {:?}",
        out.result
    );
}

fn xorshift(state: &mut u64) -> u64 {
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *state = x;
    x
}

fn pick(state: &mut u64, n: usize) -> usize {
    usize::try_from(xorshift(state)).unwrap_or(0) % n
}

#[test]
#[ignore = "differential sweep (seconds); run with --ignored"]
fn local_search_never_contradicts_the_eager_backend() {
    // A tight per-formula budget: local search burns the whole timeout on the
    // unsatisfiable instances it cannot refute, so keep it short for the sweep.
    let cfg = || SolverConfig::default().with_timeout(Duration::from_millis(800));
    // Random small (width-4) BV formulas: whenever local search returns Sat its
    // model must replay AND the complete eager backend must agree it is sat; local
    // search must never return Unsat. (No completeness is required — Unknown is
    // always acceptable.) A sanity floor ensures it actually solves a useful share.
    let mut state = 0x7AB1_C0DE_2468_1357u64;
    let mut pbls_solved = 0usize;
    let mut eager_sat = 0usize;
    let trials = 150;
    for _ in 0..trials {
        let mut arena = TermArena::new();
        let n_vars = 2 + pick(&mut state, 2); // 2..=3
        let vars: Vec<TermId> = (0..n_vars)
            .map(|i| {
                let s = arena.declare(&format!("v{i}"), Sort::BitVec(4)).unwrap();
                arena.var(s)
            })
            .collect();
        let mut pool = vars.clone();
        for _ in 0..3 {
            let a = pool[pick(&mut state, pool.len())];
            let b = pool[pick(&mut state, pool.len())];
            let t = match xorshift(&mut state) % 5 {
                0 => arena.bv_add(a, b).unwrap(),
                1 => arena.bv_sub(a, b).unwrap(),
                2 => arena.bv_xor(a, b).unwrap(),
                3 => arena.bv_and(a, b).unwrap(),
                _ => arena.bv_or(a, b).unwrap(),
            };
            pool.push(t);
        }
        let n_clauses = 1 + pick(&mut state, 3); // 1..=3 (kept small ⇒ often sat)
        let mut assertions = Vec::new();
        for _ in 0..n_clauses {
            let s = pool[pick(&mut state, pool.len())];
            let t = pool[pick(&mut state, pool.len())];
            let atom = match xorshift(&mut state) % 3 {
                0 => arena.eq(s, t).unwrap(),
                1 => arena.bv_ult(s, t).unwrap(),
                _ => arena.bv_ule(s, t).unwrap(),
            };
            assertions.push(atom);
        }

        let pbls = solve_local_search(&arena, &assertions, &cfg()).unwrap();
        let eager = SatBvBackend::new()
            .check(&arena, &assertions, &cfg())
            .unwrap();
        assert!(
            !matches!(pbls.result, CheckResult::Unsat),
            "local search must never report Unsat"
        );
        if let CheckResult::Sat(model) = &pbls.result {
            model_satisfies(&arena, model, &assertions);
            assert!(
                matches!(eager, CheckResult::Sat(_)),
                "local search found a model the eager backend calls unsat: {eager:?}"
            );
            pbls_solved += 1;
        }
        if matches!(eager, CheckResult::Sat(_)) {
            eager_sat += 1;
        }
    }
    // Sanity: it should crack a meaningful share of the satisfiable instances.
    assert!(
        pbls_solved * 2 >= eager_sat,
        "local search solved only {pbls_solved}/{eager_sat} eager-sat instances (engine likely broken)"
    );
}
