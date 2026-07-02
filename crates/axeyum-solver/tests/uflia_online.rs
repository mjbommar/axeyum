//! Integration tests for the online (model-based) `Nelson–Oppen` combination of
//! `EUF` + linear integer arithmetic — `check_qf_uflia_online`.
//!
//! The load-bearing test is the **differential fuzz** against the trusted offline
//! decider `check_with_uf_arithmetic` (eager Ackermann): over many deterministic
//! random `QF_UFLIA` conjunctions the online combination must AGREE (sat / unsat)
//! with the offline decider on every jointly-decided instance — zero disagreements —
//! and every `sat` model must replay against the original assertions with **integer**
//! values. A graceful `Unknown` on a hard case is fine; a wrong sat / unsat is
//! unacceptable.

use std::time::Duration;

use axeyum_ir::{Assignment, Sort, TermArena, TermId, Value, eval};
use axeyum_solver::{
    CheckResult, IncrementalDecisionLia, SolverConfig, UnknownKind,
    check_qf_uflia_boolean_prop_metrics, check_qf_uflia_boolean_with_metrics,
    check_qf_uflia_online, check_with_uf_arithmetic, combined_incremental_lia_structure,
    combined_incremental_lia_vs_check, combined_theory_lia_propagations,
};

fn iconst(arena: &mut TermArena, n: i128) -> TermId {
    arena.int_const(n)
}

fn ivar(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::Int).expect("declare int");
    arena.var(s)
}

/// `Some(true)` for SAT, `Some(false)` for UNSAT, `None` for Unknown.
fn verdict(result: &CheckResult) -> Option<bool> {
    match result {
        CheckResult::Sat(_) => Some(true),
        CheckResult::Unsat => Some(false),
        CheckResult::Unknown(_) => None,
    }
}

/// Replays a `sat` model against the assertions through the ground evaluator, checking
/// every model symbol value is an integer.
fn model_replays(arena: &TermArena, assertions: &[TermId], result: &CheckResult) {
    if let CheckResult::Sat(model) = result {
        let mut assignment = Assignment::new();
        for (symbol, value) in model.iter() {
            assert!(
                matches!(value, Value::Int(_)),
                "sat model symbol value must be an integer, got {value:?}"
            );
            assignment.set(symbol, value);
        }
        for (func, interp) in model.functions() {
            assignment.set_function(func, interp.clone());
        }
        for &a in assertions {
            assert_eq!(
                eval(arena, a, &assignment),
                Ok(Value::Bool(true)),
                "sat model must replay every assertion to true"
            );
        }
    }
}

#[test]
fn boolean_combination_zero_timeout_is_timeout_unknown() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let y = ivar(&mut arena, "y");
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let eq = arena.eq(fx, fy).unwrap();
    let lt = arena.int_lt(x, y).unwrap();
    let assertion = arena.or(eq, lt).unwrap();

    let config = SolverConfig::default().with_timeout(Duration::ZERO);
    let result = check_qf_uflia_online(&mut arena, &[assertion], &config).unwrap();
    assert!(
        matches!(&result, CheckResult::Unknown(reason) if reason.kind == UnknownKind::Timeout),
        "expected timeout unknown, got {result:?}"
    );
}

#[test]
fn boolean_equality_over_lia_atoms_is_encoded_as_boolean_structure() {
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let zero = iconst(&mut arena, 0);
    let one = iconst(&mut arena, 1);
    let x_le_zero = arena.int_le(x, zero).unwrap();
    let x_ge_one = arena.int_ge(x, one).unwrap();
    let same_truth = arena.eq(x_le_zero, x_ge_one).unwrap();

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &[same_truth], &config).unwrap();
    assert_eq!(
        online,
        CheckResult::Unsat,
        "Boolean equality over LIA atoms should be handled by the Boolean layer"
    );
}

#[test]
fn opaque_int_app_order_conflict_is_lia_unsat() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let zero = iconst(&mut arena, 0);
    let one = iconst(&mut arena, 1);
    let fx_le_zero = arena.int_le(fx, zero).unwrap();
    let fx_ge_one = arena.int_ge(fx, one).unwrap();

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &[fx_le_zero, fx_ge_one], &config).unwrap();
    assert_eq!(
        online,
        CheckResult::Unsat,
        "Int-valued UF applications in order atoms should be opaque LIA variables for UNSAT"
    );
}

#[test]
fn opaque_int_app_boolean_path_zero_timeout_is_timeout_unknown() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let zero = iconst(&mut arena, 0);
    let one = iconst(&mut arena, 1);
    let fx_le_zero = arena.int_le(fx, zero).unwrap();
    let fx_ge_one = arena.int_ge(fx, one).unwrap();
    let assertion = arena.or(fx_le_zero, fx_ge_one).unwrap();

    let config = SolverConfig::default().with_timeout(Duration::ZERO);
    let online = check_qf_uflia_online(&mut arena, &[assertion], &config).unwrap();
    assert!(
        matches!(
            &online,
            CheckResult::Unknown(reason)
                if reason.kind == UnknownKind::Timeout
                    && reason.detail.contains("timeout in the online combination boolean layer")
        ),
        "Boolean-structured opaque-app UFLIA should honor zero timeout before theory work, got {online:?}"
    );
}

#[test]
fn opaque_int_app_equality_only_sat_still_replays() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let one = iconst(&mut arena, 1);
    let fx_eq_one = arena.eq(fx, one).unwrap();

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &[fx_eq_one], &config).unwrap();
    assert_eq!(
        verdict(&online),
        Some(true),
        "pure EUF equality over an Int UF result should not be forced through opaque LIA"
    );
    model_replays(&arena, &[fx_eq_one], &online);
}

#[test]
fn large_opaque_int_app_online_skeleton_declines_before_search() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let mut assertions = Vec::new();
    for i in 0..129 {
        let offset = iconst(&mut arena, i);
        let arg = arena.int_add(x, offset).unwrap();
        let app = arena.apply(f, &[arg]).unwrap();
        let bound = iconst(&mut arena, i + 1);
        assertions.push(arena.int_le(app, bound).unwrap());
    }

    let config = SolverConfig::default().with_timeout(Duration::from_millis(1));
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert!(
        matches!(
            &online,
            CheckResult::Unknown(reason)
                if reason.detail.contains("too many theory atoms for opaque-app online UFLIA")
        ),
        "large opaque-app online skeleton should decline before search, got {online:?}"
    );
}

#[test]
fn large_total_atom_skeleton_with_small_opaque_subset_is_admitted() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let app = arena.apply(f, &[x]).unwrap();
    let zero = iconst(&mut arena, 0);
    let mut assertion = arena.int_le(app, zero).unwrap();

    for i in 0..129 {
        let y = ivar(&mut arena, &format!("y{i}"));
        let bound = iconst(&mut arena, i);
        let pure = arena.int_ge(y, bound).unwrap();
        assertion = arena.or(assertion, pure).unwrap();
    }

    let config = SolverConfig::default().with_timeout(Duration::from_millis(100));
    let online = check_qf_uflia_online(&mut arena, &[assertion], &config).unwrap();
    assert!(
        !matches!(
            &online,
            CheckResult::Unknown(reason)
                if reason.detail.contains("too many theory atoms for opaque-app online UFLIA")
        ),
        "only the opaque-app subset should drive the opaque guard, got {online:?}"
    );
}

#[test]
fn opaque_app_interface_overflow_declines_without_enumerative_fallback() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let zero = iconst(&mut arena, 0);
    let fx = arena.apply(f, &[x]).unwrap();
    let mut assertion = arena.int_le(fx, zero).unwrap();

    for i in 0..12 {
        let y = ivar(&mut arena, &format!("y{i}"));
        let z = ivar(&mut arena, &format!("z{i}"));
        let fy = arena.apply(f, &[y]).unwrap();
        let eq = arena.eq(fy, z).unwrap();
        assertion = arena.or(assertion, eq).unwrap();
    }

    let config = SolverConfig::default().with_timeout(Duration::from_millis(100));
    let online = check_qf_uflia_online(&mut arena, &[assertion], &config).unwrap();
    assert!(
        matches!(
            &online,
            CheckResult::Unknown(reason)
                if reason
                    .detail
                    .contains("opaque-app online UFLIA incremental combined state could not be built safely")
        ),
        "opaque-app layouts that exceed the incremental interface split should not restart the unsafe enumerative fallback, got {online:?}"
    );
}

#[test]
fn interface_equality_forces_euf_contradiction_unsat() {
    // f(x) != f(y)  AND  x <= y  AND  y <= x.
    // LIA forces x = y; EUF then needs f(x) = f(y) by congruence, contradicting the
    // asserted f(x) != f(y) ⇒ UNSAT. The interface equality (x, y) is load-bearing.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let y = ivar(&mut arena, "y");
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let fx_ne_fy = {
        let eq = arena.eq(fx, fy).unwrap();
        arena.not(eq).unwrap()
    };
    let x_le_y = arena.int_le(x, y).unwrap();
    let y_le_x = arena.int_le(y, x).unwrap();
    let assertions = [fx_ne_fy, x_le_y, y_le_x];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(online, CheckResult::Unsat, "combination must refute");

    // Agree with the trusted offline decider.
    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(false));
}

#[test]
fn interface_equality_sat_companion() {
    // f(x) != f(y)  AND  x <= y. Here x can be strictly below y, so f(x), f(y) may
    // differ ⇒ SAT. The combination must build an integer f-interpretation that replays.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let y = ivar(&mut arena, "y");
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let fx_ne_fy = {
        let eq = arena.eq(fx, fy).unwrap();
        arena.not(eq).unwrap()
    };
    let x_le_y = arena.int_le(x, y).unwrap();
    let assertions = [fx_ne_fy, x_le_y];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&online), Some(true), "expected SAT, got {online:?}");
    model_replays(&arena, &assertions, &online);

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(true));
}

/// Replays a `sat` model that may carry Bool symbol values (e.g. an injected
/// skeleton-only Bool) against the assertions, asserting each evaluates to `true`.
fn replays_with_bool(arena: &TermArena, assertions: &[TermId], result: &CheckResult) {
    let CheckResult::Sat(model) = result else {
        panic!("expected a sat model, got {result:?}");
    };
    let mut assignment = Assignment::new();
    for (symbol, value) in model.iter() {
        assignment.set(symbol, value);
    }
    for (func, interp) in model.functions() {
        assignment.set_function(func, interp.clone());
    }
    for &a in assertions {
        assert_eq!(
            eval(arena, a, &assignment),
            Ok(Value::Bool(true)),
            "sat model must replay every assertion to true"
        );
    }
}

/// A free Bool symbol living *only* in the propositional skeleton (never as a theory
/// atom) must land in the returned `sat` model with the skeleton's committed truth
/// value — otherwise the witness fails to replay against the original assertions. Here
/// `¬(x < 0)` forces the disjunct `b` true, so a model that omits `b` (or defaults it
/// to `false`) does not satisfy `(b ∨ x < 0)`.
#[test]
fn skeleton_only_bool_symbol_is_injected_into_sat_model() {
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let zero = iconst(&mut arena, 0);
    let b_sym = arena.declare("b", Sort::Bool).expect("declare bool");
    let b = arena.var(b_sym);
    let x_lt_0 = arena.int_lt(x, zero).unwrap();
    let disj = arena.or(b, x_lt_0).unwrap();
    let not_lt = arena.not(x_lt_0).unwrap();
    let assertions = [disj, not_lt];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(
        verdict(&online),
        Some(true),
        "instance is SAT with b = true"
    );
    replays_with_bool(&arena, &assertions, &online);
}

#[test]
fn integer_tightening_interface_unsat() {
    // 0 < x  AND  x < 2  AND  f(x) != f(1).
    // Over ℤ, 0 < x < 2 forces x = 1, so the interface equality x = 1 holds, hence
    // f(x) = f(1) by congruence, contradicting f(x) != f(1) ⇒ UNSAT. This bites only
    // because LIA is *integer*-tight (rationally x could be 0.5 and avoid the
    // equality). The shared interface term is the constant 1.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let zero = iconst(&mut arena, 0);
    let one = iconst(&mut arena, 1);
    let two = iconst(&mut arena, 2);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();
    let fx_ne_f1 = {
        let eq = arena.eq(fx, f1).unwrap();
        arena.not(eq).unwrap()
    };
    let zero_lt_x = arena.int_lt(zero, x).unwrap();
    let x_lt_two = arena.int_lt(x, two).unwrap();
    let assertions = [zero_lt_x, x_lt_two, fx_ne_f1];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(
        online,
        CheckResult::Unsat,
        "integer tightening must force x = 1 and refute"
    );

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(false));
}

#[test]
fn integer_tightening_interface_sat_companion() {
    // 0 < x  AND  x < 3  AND  f(x) != f(1).
    // Over ℤ, x can be 2 (≠ 1), so f(x) and f(1) may differ ⇒ SAT.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let zero = iconst(&mut arena, 0);
    let one = iconst(&mut arena, 1);
    let three = iconst(&mut arena, 3);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();
    let fx_ne_f1 = {
        let eq = arena.eq(fx, f1).unwrap();
        arena.not(eq).unwrap()
    };
    let zero_lt_x = arena.int_lt(zero, x).unwrap();
    let x_lt_three = arena.int_lt(x, three).unwrap();
    let assertions = [zero_lt_x, x_lt_three, fx_ne_f1];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&online), Some(true), "expected SAT, got {online:?}");
    model_replays(&arena, &assertions, &online);

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(true));
}

#[test]
fn pure_lia_decides() {
    // (x < y) AND (y < x): pure LIA, no UF ⇒ UNSAT.
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let y = ivar(&mut arena, "y");
    let xy = arena.int_lt(x, y).unwrap();
    let yx = arena.int_lt(y, x).unwrap();
    let config = SolverConfig::default();
    let result = check_qf_uflia_online(&mut arena, &[xy, yx], &config).unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn pure_lia_strict_tightening_unsat() {
    // 0 < x AND x < 1: pure LIA, integer-UNSAT (rationally SAT) — the LIA point.
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let zero = iconst(&mut arena, 0);
    let one = iconst(&mut arena, 1);
    let gt = arena.int_gt(x, zero).unwrap();
    let lt = arena.int_lt(x, one).unwrap();
    let config = SolverConfig::default();
    let result = check_qf_uflia_online(&mut arena, &[gt, lt], &config).unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn pure_lia_sat_replays() {
    // x <= y AND x >= 0: pure LIA, satisfiable.
    let mut arena = TermArena::new();
    let x = ivar(&mut arena, "x");
    let y = ivar(&mut arena, "y");
    let zero = iconst(&mut arena, 0);
    let x_le_y = arena.int_le(x, y).unwrap();
    let x_ge_0 = arena.int_ge(x, zero).unwrap();
    let assertions = [x_le_y, x_ge_0];
    let config = SolverConfig::default();
    let result = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&result), Some(true));
    model_replays(&arena, &assertions, &result);
}

#[test]
fn pure_euf_decides() {
    // f(a) = b AND f(a) != b (degenerate EUF): UNSAT, no LIA atoms.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let a = ivar(&mut arena, "a");
    let b = ivar(&mut arena, "b");
    let fa = arena.apply(f, &[a]).unwrap();
    let eq = arena.eq(fa, b).unwrap();
    let ne = {
        let e = arena.eq(fa, b).unwrap();
        arena.not(e).unwrap()
    };
    let config = SolverConfig::default();
    let result = check_qf_uflia_online(&mut arena, &[eq, ne], &config).unwrap();
    assert_eq!(result, CheckResult::Unsat);
}

#[test]
fn nested_congruence_unsat() {
    // f(f(a)) != f(f(b)) AND a <= b AND b <= a. a=b ⇒ f(a)=f(b) ⇒ f(f(a))=f(f(b)).
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let a = ivar(&mut arena, "a");
    let b = ivar(&mut arena, "b");
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let ffa = arena.apply(f, &[fa]).unwrap();
    let ffb = arena.apply(f, &[fb]).unwrap();
    let ne = {
        let e = arena.eq(ffa, ffb).unwrap();
        arena.not(e).unwrap()
    };
    let a_le_b = arena.int_le(a, b).unwrap();
    let b_le_a = arena.int_le(b, a).unwrap();
    let assertions = [ne, a_le_b, b_le_a];
    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(online, CheckResult::Unsat);

    // The offline eager-Ackermann decider may *decline* (Unknown) on a nested-UF case;
    // when it does decide, it must agree (never SAT).
    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_ne!(verdict(&offline), Some(true), "offline must not claim SAT");
}

#[test]
fn non_uflia_atom_declines_gracefully() {
    // A bit-vector equality atom is outside QF_UFLIA ⇒ graceful Unknown, never panic.
    let mut arena = TermArena::new();
    let bv = arena.declare("v", Sort::BitVec(8)).unwrap();
    let v = arena.var(bv);
    let k = arena.bv_const(8, 5).unwrap();
    let eq = arena.eq(v, k).unwrap();
    let config = SolverConfig::default();
    let result = check_qf_uflia_online(&mut arena, &[eq], &config).unwrap();
    assert!(
        matches!(result, CheckResult::Unknown(_)),
        "expected a graceful Unknown, got {result:?}"
    );
}

#[test]
#[allow(clippy::similar_names)]
fn disjunctive_sat_replays() {
    // (x <= 0 OR f(x) = f(1)) AND x >= 1 AND x <= 1.
    // x >= 1 AND x <= 1 ⇒ x = 1, refuting x <= 0, so the disjunction is satisfied by
    // f(x) = f(1), which holds by congruence (x = 1) ⇒ SAT.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let one = iconst(&mut arena, 1);
    let zero = iconst(&mut arena, 0);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();

    let x_le_0 = arena.int_le(x, zero).unwrap();
    let fx_eq_f1 = arena.eq(fx, f1).unwrap();
    let disjunction = arena.or(x_le_0, fx_eq_f1).unwrap();
    let x_ge_1 = arena.int_ge(x, one).unwrap();
    let x_le_1 = arena.int_le(x, one).unwrap();
    let assertions = [disjunction, x_ge_1, x_le_1];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&online), Some(true), "expected SAT, got {online:?}");
    model_replays(&arena, &assertions, &online);

    // Re-check the verdict test-side against the trusted offline decider.
    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(true));
}

#[test]
#[allow(clippy::similar_names)]
fn disjunctive_unsat() {
    // (x <= 0 OR f(x) = f(1)) AND x >= 1 AND x <= 1 AND f(x) != f(1).
    // x = 1 refutes x <= 0, forcing f(x) = f(1), contradicting f(x) != f(1) ⇒ UNSAT.
    // The old conjunctive path declined this (a disjunction in the skeleton).
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let one = iconst(&mut arena, 1);
    let zero = iconst(&mut arena, 0);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();

    let x_le_0 = arena.int_le(x, zero).unwrap();
    let fx_eq_f1 = arena.eq(fx, f1).unwrap();
    let disjunction = arena.or(x_le_0, fx_eq_f1).unwrap();
    let x_ge_1 = arena.int_ge(x, one).unwrap();
    let x_le_1 = arena.int_le(x, one).unwrap();
    let fx_ne_f1 = arena.not(fx_eq_f1).unwrap();
    let assertions = [disjunction, x_ge_1, x_le_1, fx_ne_f1];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(online, CheckResult::Unsat, "combination must refute");

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(false));
}

#[test]
#[allow(clippy::similar_names)]
fn ite_over_uflia_sat_replays() {
    // ite(x >= 1, f(x) = f(1), x <= 0) AND x >= 1 AND x <= 1 AND nothing forbidding
    // f(x) = f(1). The guard x >= 1 holds (x = 1), selecting the then-branch
    // f(x) = f(1), which is consistent (x = 1 ⇒ f(x) = f(1) by congruence) ⇒ SAT.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let one = iconst(&mut arena, 1);
    let zero = iconst(&mut arena, 0);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();

    let guard = arena.int_ge(x, one).unwrap();
    let then_b = arena.eq(fx, f1).unwrap();
    let else_b = arena.int_le(x, zero).unwrap();
    let ite = arena.ite(guard, then_b, else_b).unwrap();
    let x_ge_1 = arena.int_ge(x, one).unwrap();
    let x_le_1 = arena.int_le(x, one).unwrap();
    let assertions = [ite, x_ge_1, x_le_1];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&online), Some(true), "expected SAT, got {online:?}");
    model_replays(&arena, &assertions, &online);

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(true));
}

#[test]
#[allow(clippy::similar_names)]
fn ite_over_uflia_unsat() {
    // ite(x >= 1, f(x) = f(1), x <= 0) AND x >= 1 AND x <= 1 AND f(x) != f(1).
    // The guard holds, selecting f(x) = f(1); with f(x) != f(1) asserted ⇒ UNSAT.
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(&mut arena, "x");
    let one = iconst(&mut arena, 1);
    let zero = iconst(&mut arena, 0);
    let fx = arena.apply(f, &[x]).unwrap();
    let f1 = arena.apply(f, &[one]).unwrap();

    let guard = arena.int_ge(x, one).unwrap();
    let then_b = arena.eq(fx, f1).unwrap();
    let else_b = arena.int_le(x, zero).unwrap();
    let ite = arena.ite(guard, then_b, else_b).unwrap();
    let x_ge_1 = arena.int_ge(x, one).unwrap();
    let x_le_1 = arena.int_le(x, one).unwrap();
    let fx_ne_f1 = arena.not(then_b).unwrap();
    let assertions = [ite, x_ge_1, x_le_1, fx_ne_f1];

    let config = SolverConfig::default();
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).unwrap();
    assert_eq!(online, CheckResult::Unsat);

    let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).unwrap();
    assert_eq!(verdict(&offline), Some(false));
}

/// Advances a 64-bit LCG and returns a 32-bit draw (no `rand` crate, no clock).
fn next_rand(state: &mut u64) -> u32 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    (*state >> 33) as u32
}

/// Builds one deterministic-random small `QF_UFLIA` conjunction over a few integer vars
/// and a unary integer function `f`: a conjunction of LIA order atoms and
/// `f`-application equalities / disequalities.
#[allow(clippy::many_single_char_names)]
fn build_case(arena: &mut TermArena, state: &mut u64) -> Vec<TermId> {
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(arena, "x");
    let y = ivar(arena, "y");
    let z = ivar(arena, "z");

    // A small pool of integer terms: vars, a couple of small constants, and f-apps.
    let mut pool: Vec<TermId> = vec![x, y, z];
    for _ in 0..2 {
        let n = i128::from(next_rand(state) % 5);
        pool.push(iconst(arena, n));
    }
    // A few f-applications over pool members (and one nested application).
    for _ in 0..3 {
        let pick = pool[(next_rand(state) as usize) % pool.len()];
        let app = arena.apply(f, &[pick]).unwrap();
        pool.push(app);
    }

    // 2..4 atoms combined as a conjunction (this slice decides conjunctions).
    let atom_count = 2 + (next_rand(state) % 3) as usize;
    let mut atoms: Vec<TermId> = Vec::with_capacity(atom_count);
    for _ in 0..atom_count {
        let lhs = pool[(next_rand(state) as usize) % pool.len()];
        let rhs = pool[(next_rand(state) as usize) % pool.len()];
        let atom = match next_rand(state) % 5 {
            0 => arena.int_lt(lhs, rhs).unwrap(),
            1 => arena.int_le(lhs, rhs).unwrap(),
            2 => arena.eq(lhs, rhs).unwrap(),
            3 => {
                let e = arena.eq(lhs, rhs).unwrap();
                arena.not(e).unwrap()
            }
            _ => arena.int_ge(lhs, rhs).unwrap(),
        };
        atoms.push(atom);
    }
    atoms
}

#[test]
fn differential_fuzz_agrees_with_offline_ackermann() {
    let config = SolverConfig::default();
    let mut jointly_decided = 0usize;
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;
    let mut online_decided = 0usize;

    let mut state: u64 = 0x1234_5678_9abc_def0;

    for _case in 0..600usize {
        let mut arena = TermArena::new();
        let assertions = build_case(&mut arena, &mut state);

        let online = check_qf_uflia_online(&mut arena, &assertions, &config).expect("online check");
        let offline =
            check_with_uf_arithmetic(&mut arena, &assertions, &config).expect("offline check");

        // Every online `sat` must replay against the originals with integer values —
        // the trust anchor.
        model_replays(&arena, &assertions, &online);

        if verdict(&online).is_some() {
            online_decided += 1;
        }

        if let (Some(on), Some(off)) = (verdict(&online), verdict(&offline)) {
            assert_eq!(
                on, off,
                "online/offline DISAGREE on a jointly-decided case \
                 (online={online:?}, offline={offline:?}); assertions: {assertions:?}"
            );
            jointly_decided += 1;
            if on {
                sat_count += 1;
            } else {
                unsat_count += 1;
            }
        }
    }

    assert!(
        jointly_decided > 0,
        "expected some jointly-decided cases, got none"
    );
    assert!(
        online_decided > 0,
        "online decider should decide some cases (not all Unknown)"
    );
    assert!(sat_count > 0, "expected non-zero SAT coverage, got none");
    assert!(
        unsat_count > 0,
        "expected non-zero UNSAT coverage, got none"
    );
}

/// Builds a small deterministic-random pool of `QF_UFLIA` atoms over a few integer vars
/// and a unary integer `f`: order atoms and `f`-application equalities.
#[allow(clippy::many_single_char_names)]
fn build_atom_pool(arena: &mut TermArena, state: &mut u64) -> Vec<TermId> {
    let f = arena
        .declare_fun("f", &[Sort::Int], Sort::Int)
        .expect("declare f");
    let x = ivar(arena, "x");
    let y = ivar(arena, "y");
    let z = ivar(arena, "z");

    let mut terms: Vec<TermId> = vec![x, y, z];
    for _ in 0..2 {
        let n = i128::from(next_rand(state) % 4);
        terms.push(iconst(arena, n));
    }
    for _ in 0..3 {
        let pick = terms[(next_rand(state) as usize) % terms.len()];
        terms.push(arena.apply(f, &[pick]).unwrap());
    }

    let mut atoms: Vec<TermId> = Vec::new();
    for _ in 0..6 {
        let lhs = terms[(next_rand(state) as usize) % terms.len()];
        let rhs = terms[(next_rand(state) as usize) % terms.len()];
        let atom = match next_rand(state) % 4 {
            0 => arena.int_lt(lhs, rhs).unwrap(),
            1 => arena.int_le(lhs, rhs).unwrap(),
            2 => arena.int_ge(lhs, rhs).unwrap(),
            _ => arena.eq(lhs, rhs).unwrap(),
        };
        atoms.push(atom);
    }
    atoms
}

/// Builds a random `and`/`or`/`not` tree (depth-bounded) over the atom pool.
fn build_bool_tree(arena: &mut TermArena, pool: &[TermId], state: &mut u64, depth: u32) -> TermId {
    if depth == 0 || next_rand(state).is_multiple_of(3) {
        return pool[(next_rand(state) as usize) % pool.len()];
    }
    match next_rand(state) % 3 {
        0 => {
            let inner = build_bool_tree(arena, pool, state, depth - 1);
            arena.not(inner).unwrap()
        }
        1 => {
            let a = build_bool_tree(arena, pool, state, depth - 1);
            let b = build_bool_tree(arena, pool, state, depth - 1);
            arena.and(a, b).unwrap()
        }
        _ => {
            let a = build_bool_tree(arena, pool, state, depth - 1);
            let b = build_bool_tree(arena, pool, state, depth - 1);
            arena.or(a, b).unwrap()
        }
    }
}

#[test]
fn boolean_structured_differential_fuzz_agrees_with_offline_ackermann() {
    // The load-bearing gate for the Boolean (DPLL(T)) layer: random and/or/not trees
    // over a pool of UFLIA atoms must AGREE with the trusted offline decider on every
    // jointly-decided instance, every sat model replayed, zero disagreements.
    let config = SolverConfig::default();
    let mut jointly_decided = 0usize;
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;
    let mut online_decided = 0usize;

    let mut state: u64 = 0x0bad_f00d_dead_beef;

    for _case in 0..600usize {
        let mut arena = TermArena::new();
        let pool = build_atom_pool(&mut arena, &mut state);
        // 2..3 top-level Boolean assertions over the pool.
        let assertion_count = 2 + (next_rand(&mut state) % 2) as usize;
        let assertions: Vec<TermId> = (0..assertion_count)
            .map(|_| build_bool_tree(&mut arena, &pool, &mut state, 3))
            .collect();

        let online = check_qf_uflia_online(&mut arena, &assertions, &config).expect("online check");
        let offline =
            check_with_uf_arithmetic(&mut arena, &assertions, &config).expect("offline check");

        // Every online `sat` must replay against the originals with integer values —
        // the trust anchor.
        model_replays(&arena, &assertions, &online);

        if verdict(&online).is_some() {
            online_decided += 1;
        }

        if let (Some(on), Some(off)) = (verdict(&online), verdict(&offline)) {
            assert_eq!(
                on, off,
                "online/offline DISAGREE on a jointly-decided boolean-structured case \
                 (online={online:?}, offline={offline:?}); assertions: {assertions:?}"
            );
            jointly_decided += 1;
            if on {
                sat_count += 1;
            } else {
                unsat_count += 1;
            }
        }
    }

    assert!(
        jointly_decided > 0,
        "expected some jointly-decided boolean-structured cases, got none"
    );
    assert!(
        online_decided > 0,
        "online decider should decide some boolean-structured cases (not all Unknown)"
    );
    assert!(
        sat_count > 0,
        "expected non-zero SAT coverage on boolean-structured cases, got none"
    );
    assert!(
        unsat_count > 0,
        "expected non-zero UNSAT coverage on boolean-structured cases, got none"
    );
}

/// Builds a Boolean-structured UNSAT `QF_UFLIA` query whose *early* (low-index) theory
/// atoms already conflict, while many independent downstream atoms remain free —
/// exactly the shape early partial-assignment pruning is meant to short-circuit.
///
/// Atoms 0 and 1 are `x < y` and `y < x` (jointly LIA-UNSAT), each unit-asserted so
/// `BCP` fixes them before any decision. Then `n_free` independent disjunctions
/// `(or (u_k < v_k) (v_k < u_k))` over fresh variables force a branching factor that,
/// WITHOUT pruning, explodes the number of total propositional models enumerated
/// before the conflict on atoms {0,1} is finally seen at a leaf. WITH pruning the
/// conflict is caught on the 2-atom partial assignment and the query is `UNSAT` at once.
fn build_early_conflict_query(arena: &mut TermArena, n_free: usize) -> Vec<TermId> {
    let x = ivar(arena, "x");
    let y = ivar(arena, "y");
    let x_lt_y = arena.int_lt(x, y).unwrap();
    let y_lt_x = arena.int_lt(y, x).unwrap();
    let mut assertions = vec![x_lt_y, y_lt_x];
    for k in 0..n_free {
        let u = ivar(arena, &format!("u{k}"));
        let v = ivar(arena, &format!("v{k}"));
        let u_lt_v = arena.int_lt(u, v).unwrap();
        let v_lt_u = arena.int_lt(v, u).unwrap();
        assertions.push(arena.or(u_lt_v, v_lt_u).unwrap());
    }
    assertions
}

#[test]
fn early_theory_prune_fires_and_reduces_enumeration() {
    // Prove early theory-conflict detection (i) engages and (ii) strictly reduces the
    // number of total propositional models enumerated — without changing the verdict.
    let config = SolverConfig::default();
    let mut arena = TermArena::new();
    let assertions = build_early_conflict_query(&mut arena, 8);

    // Public path (pruning on by default) must agree with the offline decider: UNSAT.
    let online = check_qf_uflia_online(&mut arena, &assertions, &config).expect("online check");
    let offline =
        check_with_uf_arithmetic(&mut arena, &assertions, &config).expect("offline check");
    assert_eq!(
        verdict(&online),
        Some(false),
        "early-conflict query is UNSAT"
    );
    assert_eq!(
        verdict(&online),
        verdict(&offline),
        "online/offline must agree on the early-conflict query"
    );

    // Verdict invariant across the pruning toggle, plus the metric contrast.
    let (with_prune, prunes_fired, models_with) =
        check_qf_uflia_boolean_with_metrics(&mut arena, &assertions, &config, true);
    let (without_prune, prunes_off, models_without) =
        check_qf_uflia_boolean_with_metrics(&mut arena, &assertions, &config, false);

    assert_eq!(verdict(&with_prune), Some(false), "pruned run is UNSAT");
    assert_eq!(
        verdict(&without_prune),
        Some(false),
        "baseline run is UNSAT"
    );
    assert_eq!(prunes_off, 0, "pruning disabled must fire zero prunes");
    assert!(
        prunes_fired > 0,
        "early pruning must engage (prunes_fired > 0), got {prunes_fired}"
    );
    assert!(
        models_with < models_without,
        "pruning must reduce enumerated total models: with={models_with} \
         (prunes_fired={prunes_fired}) vs baseline={models_without}"
    );
}

/// **Slice-1 parallel-run equivalence gate (load-bearing).** The warm equality-sharing
/// `CombinedTheoryLia` oracle must return the **identical** verdict (Sat / Unsat /
/// Unknown) to the trusted cold from-scratch `decide_conjunction` on every conjunctive
/// instance — zero disagreements. A divergence is exactly the bug slice 1 must not
/// introduce: the warm path only changes the theory solver's lifetime, never the
/// decision. Driven over both fuzz corpora's conjunctions (the `build_case` conjunctions
/// and any `build_bool_tree` assertion that happens to flatten to a conjunction of theory
/// atoms).
#[test]
fn combined_theory_lia_matches_cold_decide_conjunction() {
    let mut compared = 0usize;

    // Corpus A: the `build_case` conjunctions (the conjunctive fast-path's own corpus).
    let mut state: u64 = 0x1234_5678_9abc_def0;
    for _case in 0..600usize {
        let mut arena = TermArena::new();
        let assertions = build_case(&mut arena, &mut state);
        if let Some((cold, warm)) =
            axeyum_solver::combined_lia_vs_cold_conjunction(&mut arena, &assertions)
        {
            assert_eq!(
                cold, warm,
                "warm CombinedTheoryLia DIVERGES from cold decide_conjunction \
                 (cold={cold}, warm={warm}); assertions: {assertions:?}"
            );
            compared += 1;
        }
    }

    // Corpus B: the Boolean-tree corpus — many of its assertions flatten to a conjunction
    // of theory atoms, exercising the warm oracle on a different atom distribution.
    let mut state: u64 = 0x0bad_f00d_dead_beef;
    for _case in 0..600usize {
        let mut arena = TermArena::new();
        let pool = build_atom_pool(&mut arena, &mut state);
        let assertion_count = 2 + (next_rand(&mut state) % 2) as usize;
        let assertions: Vec<TermId> = (0..assertion_count)
            .map(|_| build_bool_tree(&mut arena, &pool, &mut state, 3))
            .collect();
        if let Some((cold, warm)) =
            axeyum_solver::combined_lia_vs_cold_conjunction(&mut arena, &assertions)
        {
            assert_eq!(
                cold, warm,
                "warm CombinedTheoryLia DIVERGES from cold decide_conjunction on a \
                 boolean-corpus conjunction (cold={cold}, warm={warm}); assertions: {assertions:?}"
            );
            compared += 1;
        }
    }

    assert!(
        compared > 0,
        "the parallel-run equivalence gate compared no conjunctive instances"
    );
}

/// `Some(true)`/`Some(false)` for the offline decider's sat/unsat verdict on a
/// conjunction, `None` on Unknown — the trusted reference for the slice-2 entailment
/// check.
fn offline_verdict(arena: &mut TermArena, assertions: &[TermId]) -> Option<bool> {
    let config = SolverConfig::default();
    verdict(&check_with_uf_arithmetic(arena, assertions, &config).expect("offline check"))
}

/// The witness term refuting a propagated literal `(atom, value)`: `not(atom)` when the
/// literal is entailed true (so `asserted ∧ ¬atom` must be UNSAT), `atom` itself when
/// entailed false.
fn refuting_witness(arena: &mut TermArena, atom: TermId, value: bool) -> TermId {
    if value {
        arena.not(atom).expect("negate atom")
    } else {
        atom
    }
}

/// **Slice-2 propagation soundness + fires gate (load-bearing).** Each literal the warm
/// `CombinedTheoryLia::propagate` reports must be GENUINELY entailed by the asserted
/// state — `asserted ∧ ¬entailed` is offline-UNSAT — and its reason asserted-only. A
/// counter proves propagation FIRES. The integer mirror of `uflra_online`'s
/// `combined_theory_propagation_is_sound_and_fires`.
#[test]
fn combined_theory_propagation_is_sound_and_fires() {
    let mut state: u64 = 0x51a2_b3c4_d5e6_f700;
    let mut fired = 0usize;
    let mut confirmed = 0usize;

    for _ in 0..1500usize {
        let mut arena = TermArena::new();
        let pool = build_atom_pool(&mut arena, &mut state);

        let mut asserted: Vec<(TermId, bool)> = Vec::new();
        for &atom in &pool {
            if next_rand(&mut state).is_multiple_of(2) {
                asserted.push((atom, true));
            }
        }
        if asserted.is_empty() {
            continue;
        }

        let asserted_terms: Vec<TermId> = asserted.iter().map(|&(t, _)| t).collect();
        if offline_verdict(&mut arena, &asserted_terms) == Some(false) {
            continue; // skip an already-UNSAT conjunction (vacuous entailment)
        }

        let Some(props) = combined_theory_lia_propagations(&mut arena, &pool, &asserted) else {
            continue;
        };

        for (atom, value, reason) in props {
            fired += 1;

            // (1) Genuine entailment: asserted ∧ ¬entailed must be offline-UNSAT.
            let witness = refuting_witness(&mut arena, atom, value);
            let mut full = asserted_terms.clone();
            full.push(witness);
            if let Some(sat) = offline_verdict(&mut arena, &full) {
                assert!(
                    !sat,
                    "UNSOUND COMBINED PROPAGATION: asserted ∧ ¬entailed is SAT \
                     (atom={atom:?}, value={value}); asserted: {asserted_terms:?}"
                );
                confirmed += 1;
            }

            // (2) Asserted-only reason.
            for (r_atom, r_value) in &reason {
                assert!(
                    *r_value,
                    "reason literal must be asserted-true here (got false), atom {r_atom:?}"
                );
                assert!(
                    asserted.contains(&(*r_atom, true)),
                    "reason names a NON-asserted atom {r_atom:?} — unsound explanation"
                );
            }
        }
    }

    eprintln!(
        "combined-theory-lia-propagation gate: fired={fired} propagations, \
         {confirmed} entailments offline-confirmed, 0 unsound"
    );
    assert!(
        fired > 20,
        "combined theory propagation never meaningfully fired ({fired}) — slice 2 not exercised"
    );
    assert!(
        confirmed > 10,
        "too few combined propagations offline-confirmed ({confirmed})"
    );
}

/// **Slice-2 propagation fires through the integrated `BoolSearch` path.** Combined
/// theory propagation must engage in the joint fixpoint (`props_fired > 0`), and the
/// verdict must still agree with the offline decider (verdict-invariant).
#[test]
fn combined_theory_propagation_fires_in_boolean_search() {
    let config = SolverConfig::default();
    let mut state: u64 = 0x2468_ace0_1357_9bdf;
    let mut total_props = 0usize;
    let mut decided = 0usize;

    for _ in 0..400usize {
        let mut arena = TermArena::new();
        let pool = build_atom_pool(&mut arena, &mut state);
        let assertion_count = 2 + (next_rand(&mut state) % 2) as usize;
        let assertions: Vec<TermId> = (0..assertion_count)
            .map(|_| build_bool_tree(&mut arena, &pool, &mut state, 3))
            .collect();

        let (result, props_fired) =
            check_qf_uflia_boolean_prop_metrics(&mut arena, &assertions, &config);
        total_props += props_fired;

        model_replays(&arena, &assertions, &result);
        let offline = check_with_uf_arithmetic(&mut arena, &assertions, &config).expect("offline");
        if let (Some(on), Some(off)) = (verdict(&result), verdict(&offline)) {
            assert_eq!(
                on, off,
                "theory propagation changed the verdict (online={result:?}, offline={offline:?}); \
                 assertions: {assertions:?}"
            );
            decided += 1;
        }
    }

    assert!(decided > 0, "expected some jointly-decided cases, got none");
    assert!(
        total_props > 0,
        "combined theory propagation never fired through BoolSearch ({total_props}) — \
         the slice-2 wiring is not engaging"
    );
}

/// **Slice-3b-lia incremental-vs-`check` validation gate (load-bearing).** Driving the
/// `CombinedIncrementalLia` surface to a fixpoint (as the slice-3c-lia `Dpll` will: `push`,
/// `assert` each literal to a propagation fixpoint) must AGREE with the trusted reference
/// `check` on every case it decides on its own, with **zero disagreements**, and never
/// refute a genuinely-SAT conjunction over ℤ:
///
/// - `Inconsistent` ⇒ `check` must NOT be SAT, AND the **offline Ackermann** decider (a
///   complete reference) must NOT call it SAT (the soundness anchor: the incremental
///   surface must never refute a satisfiable conjunction).
/// - `Consistent` (no `Undetermined` interface pair) ⇒ `check` must NOT be UNSAT.
/// - `Deferred` (an `Undetermined` pair only the slice-3c case-split resolves) imposes no
///   constraint.
///
/// The integer mirror of `uflra_online`'s `combined_incremental_surface_matches_check`.
#[test]
fn combined_incremental_lia_surface_matches_check() {
    // verdict codes: 0 = Unsat, 1 = Sat, 2 = Unknown.
    let mut handled = 0usize;
    let mut deferred = 0usize;
    let mut consistent = 0usize;
    let mut inconsistent = 0usize;
    let config = SolverConfig::default();

    let mut run = |assertions: &[TermId], arena: &mut TermArena| {
        let Some((decision, check)) = combined_incremental_lia_vs_check(arena, assertions) else {
            return;
        };
        // The trusted soundness anchor: the offline Ackermann verdict.
        let offline =
            verdict(&check_with_uf_arithmetic(arena, assertions, &config).expect("offline"));
        match decision {
            IncrementalDecisionLia::Inconsistent => {
                assert_ne!(
                    offline,
                    Some(true),
                    "UNSOUND: incremental Inconsistent on an offline-SAT case; \
                     assertions: {assertions:?}"
                );
                assert_ne!(
                    check, 1,
                    "incremental Inconsistent but check is SAT (check={check}); \
                     assertions: {assertions:?}"
                );
                handled += 1;
                inconsistent += 1;
            }
            IncrementalDecisionLia::Consistent => {
                assert_ne!(
                    check, 0,
                    "incremental Consistent (no undetermined pair) but check is UNSAT; \
                     assertions: {assertions:?}"
                );
                handled += 1;
                consistent += 1;
            }
            IncrementalDecisionLia::Deferred => deferred += 1,
        }
    };

    // Corpus A: the `build_case` conjunctions.
    let mut state: u64 = 0x1234_5678_9abc_def0;
    for _case in 0..600usize {
        let mut arena = TermArena::new();
        let assertions = build_case(&mut arena, &mut state);
        run(&assertions, &mut arena);
    }

    // Corpus B: the Boolean-tree corpus's conjunctive assertions.
    let mut state: u64 = 0x0bad_f00d_dead_beef;
    for _case in 0..600usize {
        let mut arena = TermArena::new();
        let pool = build_atom_pool(&mut arena, &mut state);
        let assertion_count = 2 + (next_rand(&mut state) % 2) as usize;
        let assertions: Vec<TermId> = (0..assertion_count)
            .map(|_| build_bool_tree(&mut arena, &pool, &mut state, 3))
            .collect();
        run(&assertions, &mut arena);
    }

    eprintln!(
        "slice-3b-lia incremental-vs-check: handled={handled} (consistent={consistent}, \
         inconsistent={inconsistent}), deferred={deferred}, 0 unsound disagreements"
    );
    assert!(
        handled > 0,
        "the incremental surface decided no case on its own — gate not exercised"
    );
    assert!(
        inconsistent > 0,
        "the incremental surface never detected a conflict — the Inconsistent path is untested"
    );
    assert!(
        consistent > 0,
        "the incremental surface never confirmed a consistent case — Consistent path untested"
    );
}

/// **Slice-3b-lia interface-variable registration structure (slice-3c-lia hand-off
/// check).** The `CombinedIncrementalLia` must register its interface variables FRESH —
/// beyond the original atom count — three per shared pair (`eq` / `lt` / `gt`), all
/// distinct, and its structural clauses (`eq ∨ lt ∨ gt`, the three pairwise exclusions)
/// must reference only those registered variables.
#[test]
fn combined_incremental_lia_registers_fresh_interface_vars() {
    let mut state: u64 = 0xfeed_face_0000_1111;
    let mut saw_pairs = 0usize;

    for _ in 0..400usize {
        let mut arena = TermArena::new();
        let pool = build_atom_pool(&mut arena, &mut state);
        let assertion_count = 2 + (next_rand(&mut state) % 2) as usize;
        let assertions: Vec<TermId> = (0..assertion_count)
            .map(|_| build_bool_tree(&mut arena, &pool, &mut state, 3))
            .collect();

        let Some((original_count, pairs, clauses)) =
            combined_incremental_lia_structure(&mut arena, &assertions)
        else {
            continue;
        };

        let mut all_vars = std::collections::BTreeSet::new();
        for (i, &(eq, lt, gt)) in pairs.iter().enumerate() {
            // Fresh: every interface variable is beyond the original atom numbering.
            for v in [eq, lt, gt] {
                assert!(
                    v >= original_count,
                    "interface var {v} not fresh (original_count={original_count})"
                );
                assert!(all_vars.insert(v), "interface var {v} registered twice");
            }
            // Three vars per pair, contiguous in registration order.
            assert_eq!(eq, original_count + i * 3);
            assert_eq!(lt, original_count + i * 3 + 1);
            assert_eq!(gt, original_count + i * 3 + 2);
        }

        // Exactly four structural clauses per pair, over registered variables only.
        assert_eq!(clauses.len(), pairs.len() * 4);
        for clause in &clauses {
            for &(v, _) in clause {
                assert!(
                    all_vars.contains(&v),
                    "structural clause references unregistered var {v}"
                );
            }
        }
        if !pairs.is_empty() {
            saw_pairs += 1;
        }
    }

    assert!(
        saw_pairs > 0,
        "no case registered an interface pair — the structure gate is not exercised"
    );
}
