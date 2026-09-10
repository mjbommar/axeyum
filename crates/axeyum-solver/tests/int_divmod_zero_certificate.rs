//! Roadmap 2.10 — the int-linear routes solve the `div`/`mod`-**eliminated**
//! form and return that verdict *and that model* for the **original** query.
//!
//! `eliminate_int_divmod` replaces each `div a 0` / `mod a 0` with a fresh
//! unconstrained `!divmod_k`, because SMT-LIB leaves those values
//! underspecified. The ground evaluator does not: it pins `div a 0 = 0` and
//! `mod a 0 = a`. `Model` has no integer division-at-zero component — the way
//! it has `real_div_zero` for the real case — so a route that chooses
//! `!divmod_0 = 5` for `(div x 0)` cannot put that choice in the certificate,
//! and the caller's replay falls back to the evaluator's convention.
//!
//! Measured before the guard existed (both through `check_auto` and through the
//! public `solve_smtlib` front door):
//!
//! ```text
//! (assert (= x 3)) (assert (= (div x 0) 5))
//!   -> Sat, model = ["x=Int(3)", "!divmod_0=Int(5)"]
//!   -> replay of assertion #1 against that model: Ok(Bool(false))
//! ```
//!
//! `sat` was the correct VERDICT and the certificate was wrong — the SOUND-1
//! shape (`c41dd4264`) one theory over. The verdicts were never wrong: the two
//! shapes that must be `unsat` by congruence were `unsat` before the guard and
//! are `unsat` after it, and both are pinned below so a future fix here cannot
//! buy replayability by weakening the congruence lemmas.
//!
//! Each test below names the mutation it dies on. Measured, not asserted —
//! `auto.rs` was mutated five ways and the suite re-run each time:
//!
//! | mutation | tests that died |
//! | --- | --- |
//! | delete the replay loop in `replay_int_linear_sat` | 5 |
//! | delete the internal-symbol strip | 1 |
//! | revert the guard at the `lia-simplex` call site | 4 |
//! | revert the guard at the `lia-dpll` call site | 1 |
//! | revert the guard at the fused-group call site | 1 |
//!
//! The last three rows are the ones that matter. `replay_int_linear_sat` is one
//! shared helper called from three places, which is exactly the shape that let
//! six of seven guards in another suite be deleted with everything still green.
//! On the first honest run of this table, reverting the `lia-dpll` and
//! fused-group call sites killed **zero** tests: every div-at-zero shape then in
//! the file was answered by `lia-simplex` and neither of the other two sites was
//! reached by anything. The two route tests below exist because of that
//! measurement, not because the sites looked like they needed covering.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, IntLinearPortfolioWorkersGuard, SolverConfig, check_auto, portfolio_groups_run,
    solve_smtlib_with_model,
};

fn ivar(a: &mut TermArena, name: &str) -> TermId {
    let s = a.declare(name, Sort::Int).unwrap();
    a.var(s)
}

fn cfg() -> SolverConfig {
    SolverConfig::default().with_timeout(Duration::from_secs(10))
}

/// `(= x 3) ∧ (= (div x 0) 5)` — the witness. Built with a **literal** zero
/// divisor deliberately: the wrong-unsat of `a946f925` shipped because the
/// differential fuzz only ever emitted *variable* divisors and structurally
/// could not generate this shape.
fn div_at_zero_witness(a: &mut TermArena) -> [TermId; 2] {
    let x = ivar(a, "x");
    let z = a.int_const(0);
    let three = a.int_const(3);
    let five = a.int_const(5);
    let d = a.int_div(x, z).unwrap();
    [a.eq(x, three).unwrap(), a.eq(d, five).unwrap()]
}

/// `(= x 3) ∧ ¬(= (div x 0) 0)` — the same defect behind Boolean structure
/// `lia-simplex` will not take, so the ladder falls through to `lia-dpll` and
/// (with more than one worker) to the fused group.
fn negated_div_at_zero_witness(a: &mut TermArena) -> [TermId; 2] {
    let x = ivar(a, "x");
    let z = a.int_const(0);
    let three = a.int_const(3);
    let zero = a.int_const(0);
    let d = a.int_div(x, z).unwrap();
    let is_zero = a.eq(d, zero).unwrap();
    [a.eq(x, three).unwrap(), a.not(is_zero).unwrap()]
}

/// Asserts the contract, which is deliberately **not** "the answer is
/// `unknown`": a `sat` is welcome, as long as its model is a model of what was
/// asked. Written this way so that giving `Model` an integer
/// division-at-zero component later turns this into a passing `sat` case
/// rather than a test to edit.
fn assert_sat_is_replayable(
    label: &str,
    arena: &TermArena,
    assertions: &[TermId],
    r: &CheckResult,
) {
    let CheckResult::Sat(model) = r else {
        return;
    };
    let assignment = model.to_assignment();
    for (i, &assertion) in assertions.iter().enumerate() {
        let value = eval(arena, assertion, &assignment);
        assert!(
            matches!(value, Ok(Value::Bool(true))),
            "{label}: emitted `sat` whose model is not a model of the original query — \
             assertion #{i} replays as {value:?} under the model the caller receives"
        );
    }
}

/// DIES ON: deleting the replay loop in `replay_int_linear_sat`.
#[test]
fn div_at_zero_sat_is_never_emitted_with_a_model_that_does_not_replay() {
    let mut arena = TermArena::new();
    let assertions = div_at_zero_witness(&mut arena);
    let result = check_auto(&mut arena, &assertions, &cfg()).expect("check_auto must not error");
    assert_sat_is_replayable("div-at-zero via check_auto", &arena, &assertions, &result);
}

/// The same shape through `mod`, whose evaluator convention is `mod a 0 = a`
/// rather than a constant — so it fails the replay for a different arithmetic
/// reason than `div` does.
///
/// DIES ON: deleting the replay loop in `replay_int_linear_sat`.
#[test]
fn mod_at_zero_sat_is_never_emitted_with_a_model_that_does_not_replay() {
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let z = arena.int_const(0);
    let three = arena.int_const(3);
    let five = arena.int_const(5);
    let m = arena.int_mod(x, z).unwrap();
    let assertions = [arena.eq(x, three).unwrap(), arena.eq(m, five).unwrap()];
    let result = check_auto(&mut arena, &assertions, &cfg()).expect("check_auto must not error");
    assert_sat_is_replayable("mod-at-zero via check_auto", &arena, &assertions, &result);
}

/// The **public front door**, which is how this reached a caller. `check_auto`
/// and `solve_smtlib` are different entry points and only one of them is the
/// shipped API.
///
/// DIES ON: deleting the replay loop in `replay_int_linear_sat`.
#[test]
fn front_door_div_at_zero_sat_is_never_emitted_with_a_model_that_does_not_replay() {
    let text = "(set-logic QF_LIA)\n\
                (declare-fun x () Int)\n\
                (assert (= x 3))\n\
                (assert (= (div x 0) 5))\n\
                (check-sat)\n";
    let solved = solve_smtlib_with_model(text, &cfg()).expect("solve_smtlib must not error");
    assert_sat_is_replayable(
        "div-at-zero via solve_smtlib_with_model",
        &solved.script.arena,
        &solved.assertions,
        &solved.outcome.result,
    );
}

/// A div-at-zero term under a **negation**, which `lia-simplex` declines as
/// `Unsupported` (it decides conjunctions of linear atoms). The ladder then
/// falls through to `lia-dpll` — a *different* call site of the guard, in a
/// different function.
///
/// Measured, because it is not obvious from the shape: every conjunctive
/// div-at-zero query above is answered by `lia-simplex` and never reaches this
/// site. Reverting the guard at the `lia-dpll` call site alone killed **zero**
/// tests until this one existed.
///
/// DIES ON: reverting the guard at the `lia-dpll` call site.
#[test]
fn div_at_zero_is_guarded_on_the_lia_dpll_route_too() {
    let mut arena = TermArena::new();
    let assertions = negated_div_at_zero_witness(&mut arena);
    let result = check_auto(&mut arena, &assertions, &cfg()).expect("check_auto must not error");
    assert_sat_is_replayable("div-at-zero via lia-dpll", &arena, &assertions, &result);
}

/// The fused group is the third call site, in `run_int_linear_group`, on its own
/// arena clone and its own clock. At the default one worker the group is not
/// constructed at all, so without the worker override this site is unreachable —
/// and the query must additionally be one `lia-simplex` declines, or the ladder
/// returns before the group is built.
///
/// `portfolio_groups_run` is the control: without it this test would silently
/// degrade into a second copy of the `lia-dpll` test the moment the override or
/// the group wiring stopped working, and would keep passing.
///
/// DIES ON: reverting the guard at the fused-group call site.
#[test]
fn div_at_zero_is_guarded_on_the_fused_group_route_too() {
    let before = portfolio_groups_run();
    let result = {
        let _workers = IntLinearPortfolioWorkersGuard::set(2);
        let mut arena = TermArena::new();
        let assertions = negated_div_at_zero_witness(&mut arena);
        let result =
            check_auto(&mut arena, &assertions, &cfg()).expect("check_auto must not error");
        assert_sat_is_replayable("div-at-zero via fused group", &arena, &assertions, &result);
        result
    };
    assert!(
        portfolio_groups_run() > before,
        "this query never went through a fused group, so it did not exercise the \
         group's call site — it is a duplicate of the sequential test. Got {result:?}"
    );
}

/// The elimination's fresh symbols are internal scratch state. Emitting one is
/// a leak in its own right — the caller receives a binding for a symbol it
/// never declared — and it is a separate defect from the non-replaying model:
/// this query is genuinely `sat`, its model *does* replay, and it still leaked
/// `!divmod_0` before the strip existed.
///
/// DIES ON: deleting the internal-symbol strip in `replay_int_linear_sat`.
#[test]
fn a_replaying_div_sat_does_not_leak_the_eliminations_fresh_symbols() {
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let four = arena.int_const(4);
    let three = arena.int_const(3);
    let d = arena.int_div(x, four).unwrap();
    let assertions = [arena.eq(d, three).unwrap()];
    let result = check_auto(&mut arena, &assertions, &cfg()).expect("check_auto must not error");
    let CheckResult::Sat(model) = &result else {
        panic!("`(= (div x 4) 3)` is satisfiable (x in 12..=15); got {result:?}");
    };
    // Derived from the arena, not from a literal name list: the elimination owns
    // its own naming and a test that pins `!divmod_0` measures this file's
    // memory of it rather than the emitted model.
    let leaked: Vec<&str> = model
        .iter()
        .filter_map(|(sym, _)| {
            arena
                .symbols()
                .find(|(s, _, _)| *s == sym)
                .map(|(_, name, _)| name)
        })
        .filter(|name| name.starts_with('!'))
        .collect();
    assert!(
        leaked.is_empty(),
        "emitted model leaks the elimination's internal symbols: {leaked:?}"
    );
    // And it is still a certificate.
    assert_sat_is_replayable("div-by-4", &arena, &assertions, &result);
}

/// The verdicts this guard must not buy its replayability with. `div(·, 0)` is
/// underspecified but it is still a **function of the dividend**, so both of
/// these are `unsat` and were `unsat` before the guard existed.
///
/// DIES ON: weakening `eliminate_int_divmod`'s zero-divisor congruence lemmas
/// (not on any mutation of `replay_int_linear_sat`) — which is the point: it is
/// the control that says the fix above did not move the verdict.
#[test]
fn div_at_zero_verdicts_are_unchanged_and_still_unsat_by_congruence() {
    // Same term, two values.
    {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let z = arena.int_const(0);
        let five = arena.int_const(5);
        let seven = arena.int_const(7);
        let d = arena.int_div(x, z).unwrap();
        let assertions = [arena.eq(d, five).unwrap(), arena.eq(d, seven).unwrap()];
        assert!(
            matches!(
                check_auto(&mut arena, &assertions, &cfg()).unwrap(),
                CheckResult::Unsat
            ),
            "`(div x 0) = 5 ∧ (div x 0) = 7` must stay unsat"
        );
    }
    // Provably equal dividends, two values.
    {
        let mut arena = TermArena::new();
        let x = ivar(&mut arena, "x");
        let y = ivar(&mut arena, "y");
        let z = arena.int_const(0);
        let five = arena.int_const(5);
        let seven = arena.int_const(7);
        let dx = arena.int_div(x, z).unwrap();
        let dy = arena.int_div(y, z).unwrap();
        let assertions = [
            arena.eq(x, y).unwrap(),
            arena.eq(dx, five).unwrap(),
            arena.eq(dy, seven).unwrap(),
        ];
        assert!(
            matches!(
                check_auto(&mut arena, &assertions, &cfg()).unwrap(),
                CheckResult::Unsat
            ),
            "`x = y ∧ (div x 0) = 5 ∧ (div y 0) = 7` must stay unsat"
        );
    }
}

/// The guard must not touch a query the elimination never fired on. Without
/// this, "return `Unknown` unconditionally" would be a passing implementation
/// of every test above.
#[test]
fn ordinary_integer_queries_are_untouched() {
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let y = ivar(&mut arena, "y");
    let sum = arena.int_add(x, y).unwrap();
    let ten = arena.int_const(10);
    let three = arena.int_const(3);
    let assertions = [arena.eq(sum, ten).unwrap(), arena.int_gt(x, three).unwrap()];
    let result = check_auto(&mut arena, &assertions, &cfg()).expect("check_auto must not error");
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "a plain linear integer query must still be decided `sat`; got {result:?}"
    );
    assert_sat_is_replayable("plain LIA", &arena, &assertions, &result);
}
