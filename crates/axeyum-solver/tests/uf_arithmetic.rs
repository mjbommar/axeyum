//! EUF + linear-arithmetic combination (`QF_UFLIA` / `QF_UFLRA`) via the
//! functional-consistency CEGAR over the arithmetic dispatcher
//! ([`axeyum_solver::check_with_uf_arithmetic`], P1.6). The arithmetic solver and the
//! congruence closure exchange equalities through the shared abstraction: arithmetic
//! forces argument equalities; a functional-consistency lemma then forces the
//! results equal.
#![allow(clippy::many_single_char_names)]

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{CheckResult, SolverConfig, check_with_uf_arithmetic};

/// `f(a) ≠ f(b) ∧ a ≤ b ∧ b ≤ a` is UNSAT: LIA forces `a = b`, congruence forces
/// `f(a) = f(b)`, contradicting the disequality. The textbook Nelson–Oppen case.
#[test]
fn uflia_squeeze_forces_congruence_unsat() {
    let mut a = TermArena::new();
    let x = decl_int(&mut a, "x");
    let y = decl_int(&mut a, "y");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fx = a.apply(f, &[x]).unwrap();
    let fy = a.apply(f, &[y]).unwrap();
    let ne = {
        let e = a.eq(fx, fy).unwrap();
        a.not(e).unwrap()
    };
    let le1 = a.int_le(x, y).unwrap();
    let le2 = a.int_le(y, x).unwrap();
    assert!(matches!(
        check_with_uf_arithmetic(&mut a, &[ne, le1, le2], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// Regression for the nested-UF projection CRASH found by the `QF_UFLIA` differential
/// fuzz: `g(f(-3), 0) ≥ 0` (a nested arithmetic-sorted application as an argument to
/// another) panicked in `project_model` (`functions.rs:159` — the inner fresh symbol
/// is unassigned in the base model). The "never crash, graceful Unknown" hard rule:
/// the projection now declines (`Err`) instead of `.expect`-panicking, and the caller
/// maps that to a sound `Unknown`. The instance is satisfiable, so the only
/// requirement is it does NOT panic and is NOT wrongly `Unsat`.
#[test]
fn nested_arith_uf_application_does_not_crash() {
    let mut a = TermArena::new();
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let g = a.declare_fun("g", &[Sort::Int, Sort::Int], Sort::Int).unwrap();
    let m3 = a.int_const(-3);
    let fm3 = a.apply(f, &[m3]).unwrap();
    let zero = a.int_const(0);
    let gfm3 = a.apply(g, &[fm3, zero]).unwrap();
    let zero2 = a.int_const(0);
    let atom = a.int_ge(gfm3, zero2).unwrap(); // g(f(-3), 0) >= 0  (satisfiable)

    // Must not panic; must not be a wrong Unsat (the system is Sat).
    let r = check_with_uf_arithmetic(&mut a, &[atom], &SolverConfig::default()).unwrap();
    assert!(
        !matches!(r, CheckResult::Unsat),
        "g(f(-3),0)>=0 is satisfiable — never Unsat; got {r:?}"
    );
}

/// `f(a) ≠ f(b) ∧ a ≤ b` is satisfiable, so it is **never refuted**. (The witnessing
/// model for an arithmetic-sorted UF is not yet built — `project_model` keys function
/// tables by scalar codes — so this returns a sound `Unknown` rather than `Sat`; the
/// point is it is not a wrong `Unsat`.)
#[test]
fn uflia_loose_bound_is_not_refuted() {
    let mut a = TermArena::new();
    let x = decl_int(&mut a, "x");
    let y = decl_int(&mut a, "y");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fx = a.apply(f, &[x]).unwrap();
    let fy = a.apply(f, &[y]).unwrap();
    let ne = {
        let e = a.eq(fx, fy).unwrap();
        a.not(e).unwrap()
    };
    let le1 = a.int_le(x, y).unwrap();
    assert!(!matches!(
        check_with_uf_arithmetic(&mut a, &[ne, le1], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// `QF_UFLRA`: the same squeeze over the reals (`g(p) ≠ g(q) ∧ p ≤ q ∧ q ≤ p`).
#[test]
fn uflra_squeeze_forces_congruence_unsat() {
    let mut a = TermArena::new();
    let p = a.real_var("p").unwrap();
    let q = a.real_var("q").unwrap();
    let g = a.declare_fun("g", &[Sort::Real], Sort::Real).unwrap();
    let gp = a.apply(g, &[p]).unwrap();
    let gq = a.apply(g, &[q]).unwrap();
    let ne = {
        let e = a.eq(gp, gq).unwrap();
        a.not(e).unwrap()
    };
    let le1 = a.real_le(p, q).unwrap();
    let le2 = a.real_le(q, p).unwrap();
    assert!(matches!(
        check_with_uf_arithmetic(&mut a, &[ne, le1, le2], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

fn decl_int(a: &mut TermArena, name: &str) -> axeyum_ir::TermId {
    let s = a.declare(name, Sort::Int).unwrap();
    a.var(s)
}

/// The dispatcher (`solve`) routes `QF_UFLIA` automatically: the squeeze refutation
/// is decided without naming the combination procedure explicitly.
#[test]
fn solve_dispatches_uflia_combination() {
    use axeyum_solver::solve;
    let mut a = TermArena::new();
    let x = decl_int(&mut a, "x");
    let y = decl_int(&mut a, "y");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fx = a.apply(f, &[x]).unwrap();
    let fy = a.apply(f, &[y]).unwrap();
    let ne = {
        let e = a.eq(fx, fy).unwrap();
        a.not(e).unwrap()
    };
    let le1 = a.int_le(x, y).unwrap();
    let le2 = a.int_le(y, x).unwrap();
    assert!(matches!(
        solve(&mut a, &[ne, le1, le2], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// Congruence over an arithmetic argument term: `f(x+0) ≠ f(x)` is UNSAT because
/// `x+0 = x`, so `f(x+0) = f(x)`. The eager Ackermann constraint `(x+0 = x) ⇒
/// (f(x+0) = f(x))` over the arithmetic solver decides it (no unbound-intermediate
/// issue the lazy refinement would have).
#[test]
fn uflia_congruence_over_arith_argument_unsat() {
    let mut a = TermArena::new();
    let x = decl_int(&mut a, "x");
    let zero = a.int_const(0);
    let xp0 = a.int_add(x, zero).unwrap();
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let f1 = a.apply(f, &[xp0]).unwrap();
    let f2 = a.apply(f, &[x]).unwrap();
    let ne = {
        let e = a.eq(f1, f2).unwrap();
        a.not(e).unwrap()
    };
    assert!(matches!(
        check_with_uf_arithmetic(&mut a, &[ne], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// The UF result feeding arithmetic: `f(a) + 1 = f(b) ∧ a = b` is UNSAT — `a = b`
/// forces `f(a) = f(b)` by congruence, so `f(a) + 1 = f(a)`, i.e. `1 = 0`.
#[test]
fn uflia_result_in_arithmetic_unsat() {
    let mut a = TermArena::new();
    let p = decl_int(&mut a, "p");
    let q = decl_int(&mut a, "q");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fp = a.apply(f, &[p]).unwrap();
    let fq = a.apply(f, &[q]).unwrap();
    let one = a.int_const(1);
    let fp1 = a.int_add(fp, one).unwrap();
    let eq1 = a.eq(fp1, fq).unwrap(); // f(p) + 1 = f(q)
    let eq2 = a.eq(p, q).unwrap(); // p = q
    assert!(matches!(
        check_with_uf_arithmetic(&mut a, &[eq1, eq2], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// Nested UF over Int: `f(g(a)) ≠ f(g(b)) ∧ a = b` is UNSAT — `a=b` ⇒ `g(a)=g(b)`
/// ⇒ `f(g(a))=f(g(b))` (two rounds of functional-consistency refinement).
#[test]
fn uflia_nested_congruence_unsat() {
    let mut a = TermArena::new();
    let s = decl_int(&mut a, "s");
    let t = decl_int(&mut a, "t");
    let g = a.declare_fun("g", &[Sort::Int], Sort::Int).unwrap();
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let gs = a.apply(g, &[s]).unwrap();
    let gt = a.apply(g, &[t]).unwrap();
    let fgs = a.apply(f, &[gs]).unwrap();
    let fgt = a.apply(f, &[gt]).unwrap();
    let ne = {
        let e = a.eq(fgs, fgt).unwrap();
        a.not(e).unwrap()
    };
    let eq = a.eq(s, t).unwrap();
    assert!(matches!(
        check_with_uf_arithmetic(&mut a, &[ne, eq], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// Regression: `solve` on a quantified UF+LIA query must not crash. `∀x:Int. f(x)=0`
/// instantiated at `f(5)` contradicts `f(5)≠0`, and the combined path used to panic
/// (`scalar_code` on an Int in function-model projection) — now it decides UNSAT.
#[test]
fn quantified_uf_lia_solve_decides_without_crashing() {
    use axeyum_solver::solve;
    let mut a = TermArena::new();
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let xsym = a.declare("x", Sort::Int).unwrap();
    let xv = a.var(xsym);
    let fx = a.apply(f, &[xv]).unwrap();
    let zero = a.int_const(0);
    let body = a.eq(fx, zero).unwrap();
    let forall = a.forall(xsym, body).unwrap();
    let five = a.int_const(5);
    let f5 = a.apply(f, &[five]).unwrap();
    let ne = {
        let e = a.eq(f5, zero).unwrap();
        a.not(e).unwrap()
    };
    let r = solve(&mut a, &[forall, ne], &SolverConfig::default()).unwrap();
    assert!(
        matches!(r, CheckResult::Unsat),
        "instantiate x=5: f(5)=0 ∧ f(5)≠0; got {r:?}"
    );
}

/// Value conflict via congruence: `f(a) = 1 ∧ f(b) = 2 ∧ a = b` is UNSAT —
/// `a = b` ⇒ `f(a) = f(b)`, so `1 = 2`.
#[test]
fn uflia_value_conflict_via_congruence_unsat() {
    let mut a = TermArena::new();
    let u = decl_int(&mut a, "u");
    let v = decl_int(&mut a, "v");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fu = a.apply(f, &[u]).unwrap();
    let fv = a.apply(f, &[v]).unwrap();
    let one = a.int_const(1);
    let two = a.int_const(2);
    let e1 = a.eq(fu, one).unwrap();
    let e2 = a.eq(fv, two).unwrap();
    let e3 = a.eq(u, v).unwrap();
    assert!(matches!(
        check_with_uf_arithmetic(&mut a, &[e1, e2, e3], &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    ));
}

/// Regression (graceful): `solve` on a *satisfiable* Int-domain quantifier
/// `∀x:Int. f(x)=0` must return `Ok` (a sound `Unknown` — arith-UF sat model
/// unsupported), never an error or panic.
#[test]
fn sat_int_domain_quantifier_is_graceful() {
    use axeyum_solver::solve;
    let mut a = TermArena::new();
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let xsym = a.declare("x", Sort::Int).unwrap();
    let xv = a.var(xsym);
    let fx = a.apply(f, &[xv]).unwrap();
    let zero = a.int_const(0);
    let body = a.eq(fx, zero).unwrap();
    let forall = a.forall(xsym, body).unwrap();
    let r = solve(&mut a, &[forall], &SolverConfig::default());
    assert!(
        r.is_ok(),
        "sat Int-domain quantifier must be graceful, got {r:?}"
    );
    assert!(
        !matches!(r, Ok(CheckResult::Unsat)),
        "satisfiable: must not claim unsat"
    );
}

// ---------------------------------------------------------------------------
// QF_UFLIA / QF_UFLRA satisfiable cases: a replay-checked witnessing model is
// now built by projecting the eager-Ackermann arithmetic model back to a
// full-`Value`-keyed UF interpretation. SOUNDNESS: every returned `Sat` model
// is replayed through the ground evaluator against the *original* assertions;
// a wrong projection can only fail replay (→ decline), never a wrong `sat`.
// ---------------------------------------------------------------------------

/// Replays every original `assertion` under `model` through the ground
/// evaluator (which consults the projected UF interpretation for `Op::Apply`);
/// asserts each evaluates to `Bool(true)` — the level-1 evidence check.
fn assert_model_replays(
    arena: &axeyum_ir::TermArena,
    assertions: &[axeyum_ir::TermId],
    model: &axeyum_solver::Model,
) {
    use axeyum_ir::{Value, eval};
    let assignment = model.to_assignment();
    for &t in assertions {
        assert_eq!(
            eval(arena, t, &assignment).unwrap(),
            Value::Bool(true),
            "original assertion must replay to true under the projected model"
        );
    }
}

/// `f(x) = 1 ∧ x = 2` over `Int` is SAT (`x = 2`, `f(2) = 1`); the projected
/// UF interpretation replays against the original query.
#[test]
fn uflia_simple_sat_model_replays() {
    let mut a = TermArena::new();
    let x = decl_int(&mut a, "x");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fx = a.apply(f, &[x]).unwrap();
    let one = a.int_const(1);
    let two = a.int_const(2);
    let e1 = a.eq(fx, one).unwrap();
    let e2 = a.eq(x, two).unwrap();
    let originals = [e1, e2];
    let result = check_with_uf_arithmetic(&mut a, &originals, &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected SAT for f(x)=1 ∧ x=2, got {result:?}");
    };
    assert_model_replays(&a, &originals, &model);
}

/// `f(a) = f(b) ∧ a = b + 1` over `Int` is SAT (e.g. `b = 0`, `a = 1`, `f`
/// constant); the projected interpretation replays.
#[test]
fn uflia_congruent_results_sat_model_replays() {
    let mut a = TermArena::new();
    let av = decl_int(&mut a, "a");
    let bv = decl_int(&mut a, "b");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fa = a.apply(f, &[av]).unwrap();
    let fb = a.apply(f, &[bv]).unwrap();
    let one = a.int_const(1);
    let bp1 = a.int_add(bv, one).unwrap();
    let e1 = a.eq(fa, fb).unwrap(); // f(a) = f(b)
    let e2 = a.eq(av, bp1).unwrap(); // a = b + 1
    let originals = [e1, e2];
    let result = check_with_uf_arithmetic(&mut a, &originals, &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected SAT for f(a)=f(b) ∧ a=b+1, got {result:?}");
    };
    assert_model_replays(&a, &originals, &model);
}

/// `solve` (the public dispatcher) returns a replay-checked `Sat` for a
/// satisfiable `QF_UFLIA` query — the capability is reachable end-to-end.
#[test]
fn solve_returns_replay_checked_uflia_sat() {
    use axeyum_solver::solve;
    let mut a = TermArena::new();
    let x = decl_int(&mut a, "x");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fx = a.apply(f, &[x]).unwrap();
    let seven = a.int_const(7);
    let three = a.int_const(3);
    let e1 = a.eq(fx, seven).unwrap();
    let e2 = a.eq(x, three).unwrap();
    let originals = [e1, e2];
    let result = solve(&mut a, &originals, &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected SAT via solve, got {result:?}");
    };
    assert_model_replays(&a, &originals, &model);
}

/// `QF_UFLRA` satisfiable: `g(p) = 1 ∧ p = q ∧ g(q) = 1` over `Real`. Congruence
/// is consistent (`p = q ⇒ g(p) = g(q)`, both `1`); the projected real-keyed
/// interpretation replays.
#[test]
fn uflra_simple_sat_model_replays() {
    let mut a = TermArena::new();
    let p = a.real_var("p").unwrap();
    let q = a.real_var("q").unwrap();
    let g = a.declare_fun("g", &[Sort::Real], Sort::Real).unwrap();
    let gp = a.apply(g, &[p]).unwrap();
    let gq = a.apply(g, &[q]).unwrap();
    let one = a.real_const(axeyum_ir::Rational::new(1, 1));
    let e1 = a.eq(gp, one).unwrap();
    let e2 = a.eq(p, q).unwrap();
    let e3 = a.eq(gq, one).unwrap();
    let originals = [e1, e2, e3];
    let result = check_with_uf_arithmetic(&mut a, &originals, &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected SAT for the QF_UFLRA case, got {result:?}");
    };
    assert_model_replays(&a, &originals, &model);
}

/// Two distinct constrained points: `f(a) = 1 ∧ f(b) = 2 ∧ a = b + 1` is SAT
/// (the args differ, so no congruence conflict); the projected interpretation
/// must carry *both* entries `f(arg_a)=1` and `f(arg_b)=2` and replay.
#[test]
fn uflia_two_point_interp_sat_model_replays() {
    let mut a = TermArena::new();
    let av = decl_int(&mut a, "a");
    let bv = decl_int(&mut a, "b");
    let f = a.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let fa = a.apply(f, &[av]).unwrap();
    let fb = a.apply(f, &[bv]).unwrap();
    let one = a.int_const(1);
    let two = a.int_const(2);
    let bp1 = a.int_add(bv, one).unwrap();
    let e1 = a.eq(fa, one).unwrap();
    let e2 = a.eq(fb, two).unwrap();
    let e3 = a.eq(av, bp1).unwrap();
    let originals = [e1, e2, e3];
    let result = check_with_uf_arithmetic(&mut a, &originals, &SolverConfig::default()).unwrap();
    let CheckResult::Sat(model) = result else {
        panic!("expected SAT for the two-point case, got {result:?}");
    };
    assert_model_replays(&a, &originals, &model);
}
