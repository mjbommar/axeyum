//! The warm `Solver` façade: state reuse, real scopes, and the scope-leak
//! negative control (roadmap item 1.1b).
//!
//! `corpus/incremental/` — the prerequisite item 1.1b was blocked on — is
//! **entirely `QF_LIA`** (12 of 12 files declare `(set-logic QF_LIA)`), and the
//! warm engine this item routes to is a bit-vector engine. So that corpus
//! cannot fail on a warm-façade scope leak no matter how the leak is
//! introduced: every one of its assertions is refused by the fragment screen
//! and decided cold. The scoped scripts below are the bit-vector counterparts
//! that *can* fail, `warm_scope_leak_is_caught` first among them.
//!
//! Every verdict expectation here is oracle-free. The differential test decides
//! each scoped script twice — once on the warm route, once on the pre-existing
//! cold route with the warm route refused by configuration — and requires them
//! to agree at every `check`; the leak catchers additionally pin the verdict a
//! human can read off the constraints.
#![cfg(feature = "full")]

use axeyum_ir::{ArraySortKey, Assignment, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SatBvBackend, Solver, SolverConfig, SolverError};

/// A configuration the warm route must refuse, used as the cold control.
///
/// `cnf_vivify` defaults to `true` and the warm engine never reads it (no
/// occurrence of the name in `incremental.rs`), so flipping it off is exactly a
/// lever `warm_config_is_honored` rejects. It is a SAT inprocessing switch, so
/// the cold route it forces decides the same queries the same way.
fn cold_only_config() -> SolverConfig {
    let mut config = SolverConfig::default();
    config.cnf_vivify = false;
    config
}

fn bv(arena: &mut TermArena, name: &str, width: u32) -> (SymbolId, TermId) {
    let symbol = arena.declare(name, Sort::BitVec(width)).unwrap();
    let term = arena.var(symbol);
    (symbol, term)
}

fn label(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

/// Replays a model against the terms it is supposed to satisfy, using the IR's
/// ground evaluator and nothing the solver produced.
fn model_satisfies(arena: &TermArena, result: &CheckResult, terms: &[TermId]) -> bool {
    let CheckResult::Sat(model) = result else {
        return true;
    };
    let mut assignment = Assignment::new();
    for (symbol, value) in model.iter() {
        assignment.set(symbol, value);
    }
    terms
        .iter()
        .all(|&t| matches!(eval(arena, t, &assignment), Ok(Value::Bool(true))))
}

// ---------------------------------------------------------------------------
// The positive: state actually survives between checks
// ---------------------------------------------------------------------------

/// The façade reuses one engine across checks instead of restarting cold.
///
/// The assertion is on a **count**, not a clock: `n` checks over a stack that
/// grows by one assertion each time encode `n` assertions in total when state
/// is retained, and `n * (n + 1) / 2` when every check re-submits the active
/// set. A monotone clause total could not tell those apart — a fresh engine at
/// round `n` encodes the whole larger working set and its counts are monotone
/// too, which is why item 1.1a's original criterion was replaced.
#[test]
fn warm_facade_reuses_state_across_checks() {
    const N: u64 = 8;

    let mut arena = TermArena::new();
    let (_, x) = bv(&mut arena, "x", 8);
    let mut solver = Solver::new(SatBvBackend::new());

    let mut asserted = Vec::new();
    for i in 0..N {
        let c = arena.bv_const(8, u128::from(i)).unwrap();
        let ne = {
            let eq = arena.eq(x, c).unwrap();
            arena.not(eq).unwrap()
        };
        solver.assert(ne);
        asserted.push(ne);
        let result = solver.check(&arena).unwrap();
        assert_eq!(
            label(&result),
            "sat",
            "x != 0..{i} is satisfiable in 8 bits"
        );
        assert!(
            model_satisfies(&arena, &result, &asserted),
            "the warm model must replay against the ORIGINAL assertions"
        );
    }

    let stats = solver.warm_facade_stats();
    assert!(solver.warm_engine_live(), "the engine must still be live");
    assert_eq!(stats.warm_checks, N, "every check took the warm route");
    assert_eq!(stats.cold_checks, 0, "no check fell back");
    assert_eq!(
        stats.cold_restarts, 1,
        "exactly one engine was built for {N} checks"
    );
    assert_eq!(
        stats.assertions_encoded,
        N,
        "each assertion is encoded ONCE across {N} checks; a cold restart per \
         check would encode {} of them",
        N * (N + 1) / 2
    );

    // The control that makes the counters above discriminating: the same script
    // on a configuration the warm route refuses builds no engine at all.
    let mut cold = Solver::with_config(SatBvBackend::new(), cold_only_config());
    for &term in &asserted {
        cold.assert(term);
        assert_eq!(label(&cold.check(&arena).unwrap()), "sat");
    }
    let cold_stats = cold.warm_facade_stats();
    assert!(!cold.warm_engine_live());
    assert_eq!(cold_stats.warm_checks, 0);
    assert_eq!(cold_stats.cold_checks, N);
    assert_eq!(cold_stats.cold_restarts, 0);
    assert_eq!(cold_stats.assertions_encoded, 0);
}

/// `push`/`pop` open and close real engine scopes, not just façade watermarks.
#[test]
fn warm_facade_opens_real_engine_scopes() {
    let mut arena = TermArena::new();
    let (_, x) = bv(&mut arena, "x", 8);
    let one = arena.bv_const(8, 1).unwrap();
    let x_is_one = arena.eq(x, one).unwrap();

    let mut solver = Solver::new(SatBvBackend::new());
    assert_eq!(label(&solver.check(&arena).unwrap()), "sat");
    solver.push();
    solver.assert(x_is_one);
    assert_eq!(label(&solver.check(&arena).unwrap()), "sat");
    solver.pop();
    assert_eq!(label(&solver.check(&arena).unwrap()), "sat");

    let stats = solver.warm_facade_stats();
    assert_eq!(stats.scope_pushes, 1, "one engine scope was opened");
    assert_eq!(stats.scope_pops, 1, "and closed by the matching pop");
    assert_eq!(stats.cold_restarts, 1, "without rebuilding the engine");
    assert_eq!(stats.warm_checks, 3);
}

// ---------------------------------------------------------------------------
// The negative control: scope leakage
// ---------------------------------------------------------------------------

/// THE LEAK CATCHER, in bit-vectors. The `QF_BV` counterpart of
/// `corpus/incremental/04-leak-catcher.smt2`, which the warm engine cannot see.
///
/// An unconstrained baseline is `sat`; a contradictory pair under one `push` is
/// `unsat`; popping must restore the `sat` verdict. A façade that fails to drop
/// the scope's assertions answers the last check `unsat` — a wrong `unsat`, the
/// most serious thing this routing can produce.
#[test]
fn warm_scope_leak_is_caught() {
    let mut arena = TermArena::new();
    let (_, x) = bv(&mut arena, "x", 8);
    let zero = arena.bv_const(8, 0).unwrap();
    let x_is_zero = arena.eq(x, zero).unwrap();
    let x_gt_zero = arena.bv_ult(zero, x).unwrap();

    let mut solver = Solver::new(SatBvBackend::new());
    assert_eq!(
        label(&solver.check(&arena).unwrap()),
        "sat",
        "check #1: unconstrained"
    );

    solver.push();
    solver.assert(x_is_zero);
    solver.assert(x_gt_zero);
    assert_eq!(
        label(&solver.check(&arena).unwrap()),
        "unsat",
        "check #2: x = 0 and 0 <u x under one scope"
    );

    solver.pop();
    let after = solver.check(&arena).unwrap();
    assert_eq!(
        label(&after),
        "sat",
        "check #3: the popped scope's assertions must NOT survive the pop"
    );
    assert!(
        model_satisfies(&arena, &after, &[]),
        "the post-pop model replays against the (empty) active set"
    );
    assert!(solver.warm_engine_live(), "decided on the warm route");
    assert_eq!(solver.warm_facade_stats().warm_checks, 3);
    assert_eq!(solver.warm_facade_stats().cold_checks, 0);
}

/// The leak the *depth comparison* alone cannot see, and it produces a wrong
/// `unsat`.
///
/// `pop` then `push` returns to the same depth with the same frame index, so an
/// engine whose frames are only reconciled at check time keeps the discarded
/// scope's assertion and treats the new scope's first assertion as already
/// encoded. The second scope holds two assertions, so the stale frame ends up
/// carrying the *discarded* `x = 1` alongside the new `x = 2` — a conjunction
/// that is unsatisfiable, while the query actually posed (`x <u 8` and `x = 2`)
/// is plainly satisfiable.
///
/// This is the shape that forces `Solver::pop` to close the engine frame
/// eagerly, and the reason a depth check alone is not enough.
#[test]
fn warm_pop_then_push_does_not_reuse_the_discarded_scope() {
    let mut arena = TermArena::new();
    let (_, x) = bv(&mut arena, "x", 8);
    let one = arena.bv_const(8, 1).unwrap();
    let two = arena.bv_const(8, 2).unwrap();
    let eight = arena.bv_const(8, 8).unwrap();
    let x_is_one = arena.eq(x, one).unwrap();
    let x_is_two = arena.eq(x, two).unwrap();
    let x_lt_eight = arena.bv_ult(x, eight).unwrap();

    let mut solver = Solver::new(SatBvBackend::new());

    solver.push();
    solver.assert(x_is_one);
    assert_eq!(label(&solver.check(&arena).unwrap()), "sat", "x = 1");
    solver.pop();

    solver.push();
    solver.assert(x_lt_eight);
    solver.assert(x_is_two);
    let result = solver.check(&arena).unwrap();
    assert_eq!(
        label(&result),
        "sat",
        "x <u 8 and x = 2 is satisfiable; an `unsat` here is the discarded \
         `x = 1` frame being reused at the same depth — a WRONG UNSAT"
    );
    assert!(
        model_satisfies(&arena, &result, &[x_lt_eight, x_is_two]),
        "and the model must satisfy the assertions actually posed"
    );
    assert!(solver.warm_engine_live());
    assert_eq!(solver.warm_facade_stats().cold_checks, 0);
}

/// Nested scopes: an inner `pop` must not take the enclosing scope with it, and
/// the outer `pop` must still discard everything.
#[test]
fn warm_nested_scopes_pop_exactly_one_level() {
    let mut arena = TermArena::new();
    let (_, x) = bv(&mut arena, "x", 8);
    let three = arena.bv_const(8, 3).unwrap();
    let four = arena.bv_const(8, 4).unwrap();
    let five = arena.bv_const(8, 5).unwrap();
    let x_is_three = arena.eq(x, three).unwrap();
    let x_is_four = arena.eq(x, four).unwrap();
    let x_lt_five = arena.bv_ult(x, five).unwrap();

    let mut solver = Solver::new(SatBvBackend::new());
    solver.assert(x_lt_five);

    solver.push();
    solver.assert(x_is_three);
    solver.push();
    solver.assert(x_is_four);
    assert_eq!(
        label(&solver.check(&arena).unwrap()),
        "unsat",
        "x = 3 and x = 4 together"
    );
    solver.pop();
    let outer = solver.check(&arena).unwrap();
    assert_eq!(
        label(&outer),
        "sat",
        "the inner pop drops x = 4 and keeps x = 3"
    );
    assert!(model_satisfies(&arena, &outer, &[x_lt_five, x_is_three]));

    solver.pop();
    let base = solver.check(&arena).unwrap();
    assert_eq!(label(&base), "sat", "the outer pop drops x = 3 too");
    assert!(model_satisfies(&arena, &base, &[x_lt_five]));
    assert_eq!(solver.warm_facade_stats().cold_checks, 0);
    assert_eq!(solver.warm_facade_stats().scope_pops, 2);
}

/// `check_assuming` assumptions are one-shot on the warm route as well: an
/// assumption that refutes the stack must not survive into the next check.
#[test]
fn warm_assumptions_are_not_retained() {
    let mut arena = TermArena::new();
    let (_, x) = bv(&mut arena, "x", 8);
    let six = arena.bv_const(8, 6).unwrap();
    let seven = arena.bv_const(8, 7).unwrap();
    let x_is_six = arena.eq(x, six).unwrap();
    let x_is_seven = arena.eq(x, seven).unwrap();

    let mut solver = Solver::new(SatBvBackend::new());
    solver.assert(x_is_six);
    assert_eq!(label(&solver.check(&arena).unwrap()), "sat");
    assert_eq!(
        label(&solver.check_assuming(&arena, &[x_is_seven]).unwrap()),
        "unsat",
        "x = 6 with x = 7 assumed"
    );
    let after = solver.check(&arena).unwrap();
    assert_eq!(
        label(&after),
        "sat",
        "the assumption must not persist past its check"
    );
    assert!(model_satisfies(&arena, &after, &[x_is_six]));
    assert_eq!(solver.warm_facade_stats().cold_checks, 0);
}

// ---------------------------------------------------------------------------
// The differential: warm route vs the pre-existing cold route
// ---------------------------------------------------------------------------

/// One step of a scoped script.
#[derive(Debug, Clone, Copy)]
enum Step {
    Assert(TermId),
    Push,
    Pop,
    Check,
    CheckAssuming(TermId),
}

fn run_script(config: SolverConfig, arena: &TermArena, script: &[Step]) -> (Vec<String>, u64, u64) {
    let mut solver = Solver::with_config(SatBvBackend::new(), config);
    let mut verdicts = Vec::new();
    for step in script {
        match *step {
            Step::Assert(t) => solver.assert(t),
            Step::Push => solver.push(),
            Step::Pop => {
                solver.pop();
            }
            Step::Check => {
                let result = solver.check(arena).unwrap();
                assert!(
                    model_satisfies(arena, &result, solver.assertions()),
                    "a `sat` model must replay against the active assertions"
                );
                verdicts.push(label(&result).to_owned());
            }
            Step::CheckAssuming(a) => {
                let result = solver.check_assuming(arena, &[a]).unwrap();
                let mut with = solver.assertions().to_vec();
                with.push(a);
                assert!(model_satisfies(arena, &result, &with));
                verdicts.push(label(&result).to_owned());
            }
        }
    }
    let stats = solver.warm_facade_stats();
    (verdicts, stats.warm_checks, stats.cold_checks)
}

/// Every scoped script decides identically on the warm route and on the
/// pre-existing route, at every `check`.
///
/// The cold run is the reference: it is the code that shipped before item 1.1b,
/// reached by setting one configuration lever the warm route refuses. No
/// external oracle is involved, and a verdict that moves fails here.
#[test]
fn warm_and_cold_routes_agree_on_scoped_scripts() {
    let mut arena = TermArena::new();
    let (_, x) = bv(&mut arena, "x", 4);
    let (_, y) = bv(&mut arena, "y", 4);

    // A pool of small `QF_BV` atoms with plenty of shared structure, so scripts
    // are frequently contradictory rather than trivially satisfiable.
    let mut atoms = Vec::new();
    for k in 0..8u128 {
        let c = arena.bv_const(4, k).unwrap();
        atoms.push(arena.eq(x, c).unwrap());
        atoms.push(arena.bv_ult(x, c).unwrap());
        let sum = arena.bv_add(x, y).unwrap();
        atoms.push(arena.eq(sum, c).unwrap());
        let xor = arena.bv_xor(x, y).unwrap();
        atoms.push(arena.bv_ult(c, xor).unwrap());
    }

    // A deterministic xorshift; the seed and the schedule are the whole state,
    // so a failure here reproduces exactly.
    let mut state: u64 = 0x2026_0909_1b1b_0001;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };

    let mut scripts = 0usize;
    let mut checks = 0usize;
    for _ in 0..200 {
        let mut script = Vec::new();
        let mut depth = 0usize;
        for _ in 0..24 {
            match next() % 10 {
                0..=3 => script.push(Step::Assert(atoms[(next() % 32) as usize])),
                4..=5 => {
                    script.push(Step::Push);
                    depth += 1;
                }
                6 => {
                    if depth > 0 {
                        script.push(Step::Pop);
                        depth -= 1;
                    }
                }
                7 => script.push(Step::CheckAssuming(atoms[(next() % 32) as usize])),
                _ => script.push(Step::Check),
            }
        }
        script.push(Step::Check);

        let (warm, warm_checks, warm_cold) = run_script(SolverConfig::default(), &arena, &script);
        let (cold, cold_warm, _) = run_script(cold_only_config(), &arena, &script);
        assert_eq!(
            warm, cold,
            "warm and cold routes disagreed on script {scripts}: {script:?}"
        );
        assert_eq!(cold_warm, 0, "the control must never take the warm route");
        assert!(
            warm_checks > 0,
            "script {scripts} never reached the warm route (warm={warm_checks}, \
             cold={warm_cold}) — this test would be vacuous"
        );
        scripts += 1;
        checks += warm.len();
    }

    assert!(
        checks >= 1000,
        "expected a substantial sweep, got {checks} check-sat verdicts over \
         {scripts} scripts"
    );
    eprintln!("warm_and_cold_routes_agree_on_scoped_scripts: {scripts} scripts | {checks} checks");
}

// ---------------------------------------------------------------------------
// The route is refused where it must be
// ---------------------------------------------------------------------------

/// A query outside the scalar `QF_BV` fragment is decided cold, with the
/// backend's own error — not the warm engine's different one.
#[test]
fn warm_route_declines_outside_the_bv_fragment() {
    // Integers: the whole of `corpus/incremental/` is `QF_LIA`, so this is the
    // shape that corpus actually exercises.
    let mut arena = TermArena::new();
    let i = {
        let s = arena.declare("i", Sort::Int).unwrap();
        arena.var(s)
    };
    let zero = arena.int_const(0);
    let positive = arena.int_ge(i, zero).unwrap();

    let mut solver = Solver::new(SatBvBackend::new());
    solver.assert(positive);
    let error = solver.check(&arena).unwrap_err();
    assert!(
        matches!(error, SolverError::Unsupported(_)),
        "an integer query still reaches the backend and its refusal: {error:?}"
    );
    assert_eq!(solver.warm_facade_stats().cold_checks, 1);
    assert_eq!(solver.warm_facade_stats().warm_checks, 0);
    assert!(!solver.warm_engine_live());

    // Arrays: rejected by the same screen, before anything is encoded.
    let mut arena = TermArena::new();
    let a = {
        let s = arena
            .declare(
                "a",
                Sort::Array {
                    index: ArraySortKey::BitVec(4),
                    element: ArraySortKey::BitVec(4),
                },
            )
            .unwrap();
        arena.var(s)
    };
    let idx = arena.bv_const(4, 1).unwrap();
    let read = arena.select(a, idx).unwrap();
    let read_is_idx = arena.eq(read, idx).unwrap();

    let mut solver = Solver::new(SatBvBackend::new());
    solver.assert(read_is_idx);
    let error = solver.check(&arena).unwrap_err();
    assert!(
        matches!(error, SolverError::Unsupported(_)),
        "an array query still reaches the backend and its refusal: {error:?}"
    );
    assert_eq!(solver.warm_facade_stats().warm_checks, 0);
}

/// A configuration lever the warm engine does not read forces the cold route.
///
/// `prove_unsat` is the one that matters most: the warm engine has no
/// occurrence of the field, so routing a proof-producing query through it would
/// silently return an `unsat` with no DRAT proof behind it.
#[test]
fn warm_route_declines_a_config_it_cannot_honor() {
    let mut arena = TermArena::new();
    let (_, x) = bv(&mut arena, "x", 8);
    let one = arena.bv_const(8, 1).unwrap();
    let two = arena.bv_const(8, 2).unwrap();
    let a = arena.eq(x, one).unwrap();
    let b = arena.eq(x, two).unwrap();

    for config in [
        {
            let mut c = SolverConfig::default();
            c.prove_unsat = true;
            c
        },
        {
            let mut c = SolverConfig::default();
            c.node_budget = Some(1_000_000);
            c
        },
        {
            let mut c = SolverConfig::default();
            c.lazy_bv = true;
            c
        },
        cold_only_config(),
    ] {
        let mut solver = Solver::with_config(SatBvBackend::new(), config);
        solver.assert(a);
        solver.assert(b);
        assert_eq!(label(&solver.check(&arena).unwrap()), "unsat");
        let stats = solver.warm_facade_stats();
        assert_eq!(stats.warm_checks, 0, "a lever the warm engine ignores");
        assert_eq!(stats.cold_checks, 1);
        assert_eq!(stats.cold_restarts, 0, "no engine was even built");
    }

    // ...and the default configuration DOES take the warm route, so the four
    // refusals above are about the levers and not about this test's shape.
    let mut solver = Solver::new(SatBvBackend::new());
    solver.assert(a);
    solver.assert(b);
    assert_eq!(label(&solver.check(&arena).unwrap()), "unsat");
    assert_eq!(solver.warm_facade_stats().warm_checks, 1);
}

/// `set_config` discards the retained engine rather than carrying an engine
/// built for the old budgets into the new ones.
#[test]
fn set_config_retires_the_warm_engine() {
    let mut arena = TermArena::new();
    let (_, x) = bv(&mut arena, "x", 8);
    let one = arena.bv_const(8, 1).unwrap();
    let x_is_one = arena.eq(x, one).unwrap();

    let mut solver = Solver::new(SatBvBackend::new());
    solver.assert(x_is_one);
    assert_eq!(label(&solver.check(&arena).unwrap()), "sat");
    assert_eq!(solver.warm_facade_stats().cold_restarts, 1);

    solver.set_config(SolverConfig::default());
    assert!(!solver.warm_engine_live(), "the old engine was dropped");
    assert_eq!(label(&solver.check(&arena).unwrap()), "sat");
    let stats = solver.warm_facade_stats();
    assert_eq!(stats.cold_restarts, 2, "a fresh engine was built");
    assert_eq!(
        stats.assertions_encoded, 2,
        "and it re-encoded the active assertion from scratch"
    );
}
