//! MBQI model-finding for the almost-uninterpreted fragment (P2.6 T2.6.5).
//!
//! The MBQI loop in `auto.rs` can *refute* a top-level universal over an
//! infinite domain but, before this work, could never confirm one `sat`: a
//! satisfiable ground-plus-instances model is not, on its own, a model of the
//! original `∀x. body`. These tests pin the new `sat` direction — a candidate
//! model is certified a **genuine** model when the bound variable is `Int`/`Real`
//! and occurs only as a direct argument of an uninterpreted function (the
//! almost-uninterpreted fragment), where an exhaustive finite check over the
//! model's finite UF tables + defaults decides `∀x. body` over the whole domain.
//!
//! ADR-0357 closes the public evidence boundary: every accepted model carries a
//! source-bound finite-profile certificate and passes canonical `check_model`
//! plus `Evidence::check`. Soundness is tested both ways:
//!
//! - every `sat` this returns is checked against the exact quantified source by
//!   the small finite-profile checker, then additionally sampled over a wide
//!   concrete sweep as differential defense in depth; and
//! - the soundness negatives: a genuinely UNSAT quantified query — including
//!   ones whose violation lives at a UF *table entry* rather than the default —
//!   must NOT be reported `sat` (it must stay `unsat`), and an out-of-fragment
//!   universal must not be fabricated `sat`.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{
    Assignment, FuncId, FuncValue, Rational, Sort, SymbolId, TermArena, TermId, Value, eval,
};
use axeyum_solver::{
    CheckResult, Evidence, Model, QUANTIFIED_UF_BINDER_CAP, QUANTIFIED_UF_PROFILE_CAP,
    QuantifiedUfModelSatCertificate, SolverConfig, check_model, check_quantified_uf_model_sat,
    produce_evidence, solve,
};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(60))
}

fn check(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    solve(arena, assertions, &config()).expect("solve decides or returns unknown without error")
}

fn int_fn(arena: &mut TermArena, name: &str) -> FuncId {
    arena.declare_fun(name, &[Sort::Int], Sort::Int).unwrap()
}

fn int_bound(arena: &mut TermArena, name: &str) -> (SymbolId, TermId) {
    let s = arena.declare(name, Sort::Int).unwrap();
    let v = arena.var(s);
    (s, v)
}

/// Independent re-validation of a returned `sat` model: every ground assertion
/// must evaluate `true`, and the universal `∀sym. body` must evaluate `true` at a
/// wide sweep of concrete `sym`-values (this test's own check, not the finder's).
///
/// Substitution `body[sym := n]` is done by binding the bound variable's symbol
/// to `n` in the evaluator assignment (a free-symbol lookup), so no rewrite
/// machinery is needed.
fn replay_ground_and_universal(
    arena: &TermArena,
    model: &Model,
    ground: &[TermId],
    universal: Option<(SymbolId, TermId)>,
    int_sweep: &[i128],
) {
    let assignment: Assignment = model.to_assignment();
    for &g in ground {
        assert_eq!(
            eval(arena, g, &assignment),
            Ok(Value::Bool(true)),
            "returned sat model must satisfy every ground assertion"
        );
    }
    if let Some((sym, body)) = universal {
        for &n in int_sweep {
            let mut probe = assignment.clone();
            probe.set(sym, Value::Int(n));
            assert_eq!(
                eval(arena, body, &probe),
                Ok(Value::Bool(true)),
                "returned sat model must satisfy the universal body at x = {n}"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// SAT — genuine models the finder now certifies.
// ---------------------------------------------------------------------------

#[test]
fn forall_uf_nonneg_is_sat_and_model_replays() {
    // ∀x:Int. f(x) ≥ 0  ∧  f(5) = 3.
    // Genuine model: f ≡ 3 (or any all-nonneg interpretation with f(5)=3).
    let mut arena = TermArena::new();
    let f = int_fn(&mut arena, "f");
    let (x_sym, x) = int_bound(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let zero = arena.int_const(0);
    let body = arena.int_ge(fx, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();

    let five = arena.int_const(5);
    let f5 = arena.apply(f, &[five]).unwrap();
    let three = arena.int_const(3);
    let f5_is_3 = arena.eq(f5, three).unwrap();

    let assertions = [forall, f5_is_3];
    let CheckResult::Sat(model) = check(&mut arena, &assertions) else {
        panic!("∀x. f(x) ≥ 0 ∧ f(5) = 3 is genuinely satisfiable");
    };
    assert!(
        check_model(&arena, &assertions, &model).unwrap(),
        "the public model checker must accept the exact quantified source"
    );
    assert!(
        Evidence::Sat(model.clone())
            .check(&arena, &assertions)
            .unwrap(),
        "SAT evidence must use and accept the same checked model"
    );
    let report = produce_evidence(&mut arena, &assertions, &config()).unwrap();
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&arena, &assertions).unwrap());
    let sweep: Vec<i128> = (-50..=50).chain([5, 1000, -1000]).collect();
    replay_ground_and_universal(&arena, &model, &[f5_is_3], Some((x_sym, body)), &sweep);
}

#[test]
fn forall_predicate_of_uf_is_sat() {
    // ∀x:Int. P(f(x))  ∧  P(f(7)).  Genuine: f ≡ 0, P(0) = true.
    let mut arena = TermArena::new();
    let f = int_fn(&mut arena, "f");
    let p = arena.declare_fun("P", &[Sort::Int], Sort::Bool).unwrap();
    let (x_sym, x) = int_bound(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let body = arena.apply(p, &[fx]).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();

    let seven = arena.int_const(7);
    let f7 = arena.apply(f, &[seven]).unwrap();
    let pf7 = arena.apply(p, &[f7]).unwrap();

    let assertions = [forall, pf7];
    let CheckResult::Sat(model) = check(&mut arena, &assertions) else {
        panic!("∀x. P(f(x)) ∧ P(f(7)) is genuinely satisfiable");
    };
    assert!(check_model(&arena, &assertions, &model).unwrap());
    let sweep: Vec<i128> = (-30..=30).collect();
    replay_ground_and_universal(&arena, &model, &[pf7], Some((x_sym, body)), &sweep);
}

#[test]
fn forall_two_ufs_sum_nonneg_is_sat() {
    // ∀x:Int. f(x) + g(x) ≥ 0  ∧  f(1) = 2  ∧  g(1) = 4.  x flows only into UFs.
    let mut arena = TermArena::new();
    let f = int_fn(&mut arena, "f");
    let g = int_fn(&mut arena, "g");
    let (x_sym, x) = int_bound(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let gx = arena.apply(g, &[x]).unwrap();
    let sum = arena.int_add(fx, gx).unwrap();
    let zero = arena.int_const(0);
    let body = arena.int_ge(sum, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();

    let one = arena.int_const(1);
    let f1 = arena.apply(f, &[one]).unwrap();
    let two = arena.int_const(2);
    let f1_is_2 = arena.eq(f1, two).unwrap();
    let g1 = arena.apply(g, &[one]).unwrap();
    let four = arena.int_const(4);
    let g1_is_4 = arena.eq(g1, four).unwrap();

    let assertions = [forall, f1_is_2, g1_is_4];
    let CheckResult::Sat(model) = check(&mut arena, &assertions) else {
        panic!("∀x. f(x)+g(x) ≥ 0 ∧ f(1)=2 ∧ g(1)=4 is satisfiable");
    };
    assert!(check_model(&arena, &assertions, &model).unwrap());
    let sweep: Vec<i128> = (-40..=40).collect();
    replay_ground_and_universal(
        &arena,
        &model,
        &[f1_is_2, g1_is_4],
        Some((x_sym, body)),
        &sweep,
    );
}

#[test]
fn forall_real_uf_nonneg_is_sat() {
    // ∀r:Real. f(r) ≥ 0  ∧  f(2.5) = 1.  Real analogue of the fragment.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let s = arena.declare("r", Sort::Real).unwrap();
    let r = arena.var(s);
    let fr = arena.apply(f, &[r]).unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let body = arena.real_ge(fr, zero).unwrap();
    let forall = arena.forall(s, body).unwrap();

    let two_half = arena.real_const(Rational::new(5, 2));
    let f_val = arena.apply(f, &[two_half]).unwrap();
    let one = arena.real_const(Rational::integer(1));
    let f_is_1 = arena.eq(f_val, one).unwrap();

    let assertions = [forall, f_is_1];
    let CheckResult::Sat(model) = check(&mut arena, &assertions) else {
        panic!("∀r:Real. f(r) ≥ 0 ∧ f(2.5) = 1 is satisfiable");
    };
    assert!(check_model(&arena, &assertions, &model).unwrap());
}

#[test]
fn default_repair_synthesizes_two_missing_int_functions() {
    // With no ground assertions the first QF candidate has no f/g
    // interpretations. A constant completion f=0,g=0 satisfies the exact
    // source; only canonical finite-profile replay may accept it.
    let mut arena = TermArena::new();
    let f = int_fn(&mut arena, "f");
    let g = int_fn(&mut arena, "g");
    let (binder, x) = int_bound(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let gx = arena.apply(g, &[x]).unwrap();
    let minus_two = arena.int_const(-2);
    let scaled = arena.int_mul(minus_two, fx).unwrap();
    let minus_eight = arena.int_const(-8);
    let lower = arena.int_add(minus_eight, scaled).unwrap();
    let body = arena.int_ge(gx, lower).unwrap();
    let forall = arena.forall(binder, body).unwrap();

    let CheckResult::Sat(model) = check(&mut arena, &[forall]) else {
        panic!("bounded default completion must find the checked constant model");
    };
    assert!(model.function(f).is_some());
    assert!(model.function(g).is_some());
    assert!(check_model(&arena, &[forall], &model).unwrap());
}

#[test]
fn default_repair_preserves_int_table_entry_for_strict_universal() {
    // The ground point f(5)=3 must remain exact while the unobserved default is
    // moved above zero. Rewriting the table point would invalidate replay.
    let mut arena = TermArena::new();
    let f = int_fn(&mut arena, "f");
    let (binder, x) = int_bound(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let zero = arena.int_const(0);
    let body = arena.int_gt(fx, zero).unwrap();
    let forall = arena.forall(binder, body).unwrap();
    let five = arena.int_const(5);
    let f5 = arena.apply(f, &[five]).unwrap();
    let three = arena.int_const(3);
    let point = arena.eq(f5, three).unwrap();
    let assertions = [forall, point];

    let CheckResult::Sat(model) = check(&mut arena, &assertions) else {
        panic!("strict integer default repair must find a checked model");
    };
    let interpretation = model.function(f).expect("repaired f interpretation");
    assert_eq!(interpretation.apply_value(&[Value::Int(5)]), Value::Int(3));
    assert!(matches!(
        interpretation.apply_value(&[Value::Int(6)]),
        Value::Int(value) if value > 0
    ));
    assert!(check_model(&arena, &assertions, &model).unwrap());
}

#[test]
fn default_repair_uses_checked_real_successor() {
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Real], Sort::Real).unwrap();
    let binder = arena.declare("r", Sort::Real).unwrap();
    let r = arena.var(binder);
    let fr = arena.apply(f, &[r]).unwrap();
    let zero = arena.real_const(Rational::zero());
    let body = arena.real_gt(fr, zero).unwrap();
    let forall = arena.forall(binder, body).unwrap();

    let CheckResult::Sat(model) = check(&mut arena, &[forall]) else {
        panic!("strict real default repair must find a checked model");
    };
    let interpretation = model.function(f).expect("repaired f interpretation");
    let Value::Real(default) = interpretation.default_value() else {
        panic!("real-result function must carry a real default");
    };
    assert!(matches!(
        default.checked_cmp(&Rational::zero()),
        Some(core::cmp::Ordering::Greater)
    ));
    assert!(check_model(&arena, &[forall], &model).unwrap());
}

#[test]
fn free_int_completion_preserves_explicit_function_point() {
    // The ground candidate sees only f(5)=3, so its absent/default y assignment
    // cannot make `f` constantly equal to y while preserving that table point.
    // ADR-0360 fixes y=3 only for candidate generation; the returned model must
    // then satisfy the exact unfixed source and preserve f(5)=3.
    let mut arena = TermArena::new();
    let function = int_fn(&mut arena, "f");
    let (binder, variable) = int_bound(&mut arena, "x");
    let free = arena.declare("y", Sort::Int).unwrap();
    let application = arena.apply(function, &[variable]).unwrap();
    let free_variable = arena.var(free);
    let body = arena.eq(application, free_variable).unwrap();
    let forall = arena.forall(binder, body).unwrap();
    let five = arena.int_const(5);
    let at_five = arena.apply(function, &[five]).unwrap();
    let three = arena.int_const(3);
    let point = arena.eq(at_five, three).unwrap();
    let assertions = [forall, point];

    let CheckResult::Sat(model) = check(&mut arena, &assertions) else {
        panic!("bounded free-Int completion must find the exact checked model");
    };
    assert_eq!(model.get(free), Some(Value::Int(3)));
    assert_eq!(
        model
            .function(function)
            .expect("completed function")
            .apply_value(&[Value::Int(5)]),
        Value::Int(3)
    );
    assert!(check_model(&arena, &assertions, &model).unwrap());
    assert!(Evidence::Sat(model).check(&arena, &assertions).unwrap());
}

#[test]
fn two_free_int_completion_searches_complete_cartesian_product() {
    // Neither free scalar occurs in the QF ground slice. The source requires
    // f(x)=y+z and f(5)=3, so candidate generation must search both scalars and
    // the final exact replay must establish y+z=3 without retaining fixings.
    let mut arena = TermArena::new();
    let function = int_fn(&mut arena, "f");
    let (binder, variable) = int_bound(&mut arena, "x");
    let first = arena.declare("y", Sort::Int).unwrap();
    let second = arena.declare("z", Sort::Int).unwrap();
    let first_variable = arena.var(first);
    let second_variable = arena.var(second);
    let sum = arena.int_add(first_variable, second_variable).unwrap();
    let application = arena.apply(function, &[variable]).unwrap();
    let body = arena.eq(application, sum).unwrap();
    let forall = arena.forall(binder, body).unwrap();
    let five = arena.int_const(5);
    let at_five = arena.apply(function, &[five]).unwrap();
    let three = arena.int_const(3);
    let point = arena.eq(at_five, three).unwrap();
    let assertions = [forall, point];

    let CheckResult::Sat(model) = check(&mut arena, &assertions) else {
        panic!("bounded two-free-Int completion must find the exact checked model");
    };
    let Value::Int(first_value) = model.get(first).expect("first completed scalar") else {
        panic!("first scalar must be Int");
    };
    let Value::Int(second_value) = model.get(second).expect("second completed scalar") else {
        panic!("second scalar must be Int");
    };
    assert_eq!(first_value.checked_add(second_value), Some(3));
    assert_eq!(
        model
            .function(function)
            .expect("completed function")
            .apply_value(&[Value::Int(5)]),
        Value::Int(3)
    );
    assert!(check_model(&arena, &assertions, &model).unwrap());
    assert!(Evidence::Sat(model).check(&arena, &assertions).unwrap());
}

#[test]
fn free_real_completion_remains_outside_the_preregistered_search() {
    let mut arena = TermArena::new();
    let function = arena.declare_fun("f", &[Sort::Int], Sort::Real).unwrap();
    let (binder, variable) = int_bound(&mut arena, "x");
    let free = arena.declare("r", Sort::Real).unwrap();
    let application = arena.apply(function, &[variable]).unwrap();
    let free_variable = arena.var(free);
    let body = arena.eq(application, free_variable).unwrap();
    let forall = arena.forall(binder, body).unwrap();
    let five = arena.int_const(5);
    let at_five = arena.apply(function, &[five]).unwrap();
    let three_halves = arena.real_const(Rational::new(3, 2));
    let point = arena.eq(at_five, three_halves).unwrap();

    assert!(matches!(
        check(&mut arena, &[forall, point]),
        CheckResult::Unknown(_)
    ));
}

#[test]
fn three_free_ints_remain_outside_the_preregistered_search() {
    let mut arena = TermArena::new();
    let function = int_fn(&mut arena, "f");
    let (binder, variable) = int_bound(&mut arena, "x");
    let first = arena.declare("a", Sort::Int).unwrap();
    let second = arena.declare("b", Sort::Int).unwrap();
    let third = arena.declare("c", Sort::Int).unwrap();
    let first_variable = arena.var(first);
    let second_variable = arena.var(second);
    let third_variable = arena.var(third);
    let first_sum = arena.int_add(first_variable, second_variable).unwrap();
    let sum = arena.int_add(first_sum, third_variable).unwrap();
    let application = arena.apply(function, &[variable]).unwrap();
    let body = arena.eq(application, sum).unwrap();
    let forall = arena.forall(binder, body).unwrap();
    let five = arena.int_const(5);
    let at_five = arena.apply(function, &[five]).unwrap();
    let three = arena.int_const(3);
    let point = arena.eq(at_five, three).unwrap();

    assert!(matches!(
        check(&mut arena, &[forall, point]),
        CheckResult::Unknown(_)
    ));
}

#[test]
fn two_binder_uf_nonneg_is_sat_and_model_replays() {
    // ∀x y:Int. f(x,y) ≥ 0  ∧  f(1,2) = 3.
    let mut arena = TermArena::new();
    let function = arena
        .declare_fun("f", &[Sort::Int, Sort::Int], Sort::Int)
        .unwrap();
    let (x_binder, x) = int_bound(&mut arena, "x");
    let (y_binder, y) = int_bound(&mut arena, "y");
    let application = arena.apply(function, &[x, y]).unwrap();
    let zero = arena.int_const(0);
    let body = arena.int_ge(application, zero).unwrap();
    let inner = arena.forall(y_binder, body).unwrap();
    let forall = arena.forall(x_binder, inner).unwrap();

    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let at_point = arena.apply(function, &[one, two]).unwrap();
    let three = arena.int_const(3);
    let point = arena.eq(at_point, three).unwrap();
    let assertions = [forall, point];

    let CheckResult::Sat(model) = check(&mut arena, &assertions) else {
        panic!("the bounded two-binder finite-profile model must be found");
    };
    assert!(model.quantified_uf_model_sat_certificate(forall).is_some());
    assert!(check_model(&arena, &assertions, &model).unwrap());
    assert!(Evidence::Sat(model).check(&arena, &assertions).unwrap());
}

#[test]
fn mixed_two_binder_uf_nonneg_is_sat_and_model_replays() {
    let mut arena = TermArena::new();
    let function = arena
        .declare_fun("f", &[Sort::Int, Sort::Real], Sort::Real)
        .unwrap();
    let (x_binder, x) = int_bound(&mut arena, "x");
    let r_binder = arena.declare("r", Sort::Real).unwrap();
    let r = arena.var(r_binder);
    let application = arena.apply(function, &[x, r]).unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let body = arena.real_ge(application, zero).unwrap();
    let inner = arena.forall(r_binder, body).unwrap();
    let forall = arena.forall(x_binder, inner).unwrap();

    let four = arena.int_const(4);
    let half = arena.real_const(Rational::new(1, 2));
    let at_point = arena.apply(function, &[four, half]).unwrap();
    let three = arena.real_const(Rational::integer(3));
    let point = arena.eq(at_point, three).unwrap();
    let assertions = [forall, point];

    let CheckResult::Sat(model) = check(&mut arena, &assertions) else {
        panic!("the mixed-sort Cartesian finite-profile model must be found");
    };
    assert!(check_model(&arena, &assertions, &model).unwrap());
    assert!(Evidence::Sat(model).check(&arena, &assertions).unwrap());
}

#[test]
fn two_binder_conflicting_point_falls_back_to_unsat_refutation() {
    let mut arena = TermArena::new();
    let function = arena
        .declare_fun("f", &[Sort::Int, Sort::Int], Sort::Int)
        .unwrap();
    let (x_binder, x) = int_bound(&mut arena, "x");
    let (y_binder, y) = int_bound(&mut arena, "y");
    let application = arena.apply(function, &[x, y]).unwrap();
    let zero = arena.int_const(0);
    let body = arena.int_ge(application, zero).unwrap();
    let inner = arena.forall(y_binder, body).unwrap();
    let forall = arena.forall(x_binder, inner).unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let at_point = arena.apply(function, &[one, two]).unwrap();
    let negative = arena.int_const(-1);
    let point = arena.eq(at_point, negative).unwrap();

    assert!(matches!(
        check(&mut arena, &[forall, point]),
        CheckResult::Unsat
    ));
}

// ---------------------------------------------------------------------------
// SOUNDNESS NEGATIVES — genuinely UNSAT must stay unsat, never fabricated sat.
// ---------------------------------------------------------------------------

#[test]
fn forall_uf_nonneg_conflicting_point_is_unsat_not_sat() {
    // ∀x:Int. f(x) ≥ 0  ∧  f(5) = -1.  The universal forces f(5) ≥ 0, so unsat.
    let mut arena = TermArena::new();
    let f = int_fn(&mut arena, "f");
    let (x_sym, x) = int_bound(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let zero = arena.int_const(0);
    let body = arena.int_ge(fx, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();

    let five = arena.int_const(5);
    let f5 = arena.apply(f, &[five]).unwrap();
    let neg1 = arena.int_const(-1);
    let f5_is_neg1 = arena.eq(f5, neg1).unwrap();

    let result = check(&mut arena, &[forall, f5_is_neg1]);
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "unsound: ∀x. f(x) ≥ 0 ∧ f(5) = -1 is UNSAT, must never be reported sat"
    );
    assert!(
        matches!(result, CheckResult::Unsat),
        "the refutation direction must still decide this unsat"
    );
}

#[test]
fn forall_uf_violation_at_table_entry_is_unsat_not_sat() {
    // ∀x:Int. f(x) ≥ 0  ∧  f(2) = 5  ∧  f(4) = -3.  The violation sits at a UF
    // *table entry* (x = 4), exercising the key-component path (not the default).
    let mut arena = TermArena::new();
    let f = int_fn(&mut arena, "f");
    let (x_sym, x) = int_bound(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let zero = arena.int_const(0);
    let body = arena.int_ge(fx, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();

    let two = arena.int_const(2);
    let f2 = arena.apply(f, &[two]).unwrap();
    let five = arena.int_const(5);
    let f2_is_5 = arena.eq(f2, five).unwrap();
    let fourc = arena.int_const(4);
    let f4 = arena.apply(f, &[fourc]).unwrap();
    let neg3 = arena.int_const(-3);
    let f4_is_neg3 = arena.eq(f4, neg3).unwrap();

    let result = check(&mut arena, &[forall, f2_is_5, f4_is_neg3]);
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "unsound: violation at f(4) = -3 must never be reported sat"
    );
    assert!(
        matches!(result, CheckResult::Unsat),
        "the refutation direction must decide this unsat"
    );
}

#[test]
fn forall_predicate_conflict_is_unsat_not_sat() {
    // ∀x:Int. P(f(x))  ∧  ¬P(f(7)).  P(f(7)) is both forced true and asserted
    // false ⇒ unsat.
    let mut arena = TermArena::new();
    let f = int_fn(&mut arena, "f");
    let p = arena.declare_fun("P", &[Sort::Int], Sort::Bool).unwrap();
    let (x_sym, x) = int_bound(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let body = arena.apply(p, &[fx]).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();

    let seven = arena.int_const(7);
    let f7 = arena.apply(f, &[seven]).unwrap();
    let pf7 = arena.apply(p, &[f7]).unwrap();
    let not_pf7 = arena.not(pf7).unwrap();

    let result = check(&mut arena, &[forall, not_pf7]);
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "unsound: ∀x. P(f(x)) ∧ ¬P(f(7)) is UNSAT, must never be reported sat"
    );
    assert!(
        matches!(result, CheckResult::Unsat),
        "the refutation direction must decide this unsat"
    );
}

// ---------------------------------------------------------------------------
// OUT OF FRAGMENT — x occurs in an interpreted position; the finder must decline
// (never fabricate `sat` from a non-exhaustive check).
// ---------------------------------------------------------------------------

#[test]
fn out_of_fragment_arith_occurrence_is_not_fabricated_sat() {
    // ∀x:Int. f(x) + x ≥ 0  ∧  f(0) = 0.  `x` appears directly under `+` (an
    // interpreted op), so the finite UF-profile check is NOT exhaustive; the
    // finder must decline. (The query is not decided here — the point is only
    // that no fabricated `sat` is produced from the incomplete check.) The result
    // must be `unknown` (declined), never a certified `sat`.
    let mut arena = TermArena::new();
    let f = int_fn(&mut arena, "f");
    let (x_sym, x) = int_bound(&mut arena, "x");
    let fx = arena.apply(f, &[x]).unwrap();
    let sum = arena.int_add(fx, x).unwrap();
    let zero = arena.int_const(0);
    let body = arena.int_ge(sum, zero).unwrap();
    let forall = arena.forall(x_sym, body).unwrap();

    let f0 = arena.apply(f, &[zero]).unwrap();
    let zero2 = arena.int_const(0);
    let f0_is_0 = arena.eq(f0, zero2).unwrap();

    // The finder declines the out-of-fragment universal, so no `sat` is certified.
    assert!(
        !matches!(check(&mut arena, &[forall, f0_is_0]), CheckResult::Sat(_)),
        "the finder must not certify a `sat` from a non-exhaustive out-of-fragment check"
    );
}

#[test]
fn certificate_and_model_tampering_fail_closed() {
    let mut arena = TermArena::new();
    let function = int_fn(&mut arena, "f");
    let (binder, variable) = int_bound(&mut arena, "x");
    let application = arena.apply(function, &[variable]).unwrap();
    let zero = arena.int_const(0);
    let body = arena.int_ge(application, zero).unwrap();
    let forall = arena.forall(binder, body).unwrap();
    let five = arena.int_const(5);
    let at_five = arena.apply(function, &[five]).unwrap();
    let three = arena.int_const(3);
    let point = arena.eq(at_five, three).unwrap();
    let assertions = [forall, point];

    let CheckResult::Sat(model) = check(&mut arena, &assertions) else {
        panic!("the positive control must produce a checked SAT model");
    };
    let certificate = model
        .quantified_uf_model_sat_certificate(forall)
        .expect("MBQI SAT must carry its source certificate")
        .clone();
    assert!(check_quantified_uf_model_sat(
        &arena,
        forall,
        &model,
        &certificate
    ));

    let other_binder = arena.declare("y", Sort::Int).unwrap();
    let wrong_binder = QuantifiedUfModelSatCertificate {
        binder: other_binder,
        ..certificate.clone()
    };
    assert!(!check_quantified_uf_model_sat(
        &arena,
        forall,
        &model,
        &wrong_binder
    ));

    let stale_assertion = QuantifiedUfModelSatCertificate {
        assertion: point,
        ..certificate.clone()
    };
    assert!(!check_quantified_uf_model_sat(
        &arena,
        forall,
        &model,
        &stale_assertion
    ));

    let mut missing_function = Model::new();
    missing_function.set_quantified_uf_model_sat_certificate(certificate.clone());
    assert!(!check_quantified_uf_model_sat(
        &arena,
        forall,
        &missing_function,
        &certificate
    ));

    let mut wrong_signature = Model::new();
    wrong_signature.set_function(
        function,
        FuncValue::constant_value(vec![Sort::Real], Sort::Int, Value::Int(0)),
    );
    wrong_signature.set_quantified_uf_model_sat_certificate(certificate.clone());
    assert!(!check_quantified_uf_model_sat(
        &arena,
        forall,
        &wrong_signature,
        &certificate
    ));

    let mut bad_default = model.clone();
    bad_default.set_function(
        function,
        FuncValue::constant_value(vec![Sort::Int], Sort::Int, Value::Int(-1)),
    );
    assert!(!check_quantified_uf_model_sat(
        &arena,
        forall,
        &bad_default,
        &certificate
    ));
    assert!(!check_model(&arena, &assertions, &bad_default).unwrap());

    let mut extra_certificate = model;
    extra_certificate.set_quantified_uf_model_sat_certificate(QuantifiedUfModelSatCertificate {
        assertion: point,
        binder,
    });
    assert!(!check_model(&arena, &assertions, &extra_certificate).unwrap());
}

#[test]
fn finite_profile_checker_handles_repeated_argument_positions() {
    // The off-diagonal table point can never match f(x,x), while the diagonal
    // point is a real profile and must be checked.
    let mut arena = TermArena::new();
    let function = arena
        .declare_fun("f", &[Sort::Int, Sort::Int], Sort::Int)
        .unwrap();
    let (binder, variable) = int_bound(&mut arena, "x");
    let application = arena.apply(function, &[variable, variable]).unwrap();
    let zero = arena.int_const(0);
    let body = arena.int_ge(application, zero).unwrap();
    let forall = arena.forall(binder, body).unwrap();
    let certificate = QuantifiedUfModelSatCertificate {
        assertion: forall,
        binder,
    };

    let off_diagonal =
        FuncValue::constant_value(vec![Sort::Int, Sort::Int], Sort::Int, Value::Int(0))
            .define_value(&[Value::Int(1), Value::Int(2)], Value::Int(-7));
    let mut model = Model::new();
    model.set_function(function, off_diagonal.clone());
    assert!(check_quantified_uf_model_sat(
        &arena,
        forall,
        &model,
        &certificate
    ));

    model.set_function(
        function,
        off_diagonal.define_value(&[Value::Int(3), Value::Int(3)], Value::Int(-1)),
    );
    assert!(!check_quantified_uf_model_sat(
        &arena,
        forall,
        &model,
        &certificate
    ));
}

#[test]
fn finite_profile_checker_checks_cartesian_binary_table_points() {
    let mut arena = TermArena::new();
    let function = arena
        .declare_fun("f", &[Sort::Int, Sort::Int], Sort::Int)
        .unwrap();
    let (x_binder, x) = int_bound(&mut arena, "x");
    let (y_binder, y) = int_bound(&mut arena, "y");
    let application = arena.apply(function, &[x, y]).unwrap();
    let zero = arena.int_const(0);
    let body = arena.int_ge(application, zero).unwrap();
    let inner = arena.forall(y_binder, body).unwrap();
    let forall = arena.forall(x_binder, inner).unwrap();
    let certificate = QuantifiedUfModelSatCertificate {
        assertion: forall,
        binder: x_binder,
    };

    let positive = FuncValue::constant_value(vec![Sort::Int, Sort::Int], Sort::Int, Value::Int(0))
        .define_value(&[Value::Int(1), Value::Int(2)], Value::Int(7));
    let mut model = Model::new();
    model.set_function(function, positive.clone());
    assert!(check_quantified_uf_model_sat(
        &arena,
        forall,
        &model,
        &certificate
    ));

    model.set_function(
        function,
        positive.define_value(&[Value::Int(1), Value::Int(2)], Value::Int(-1)),
    );
    assert!(!check_quantified_uf_model_sat(
        &arena,
        forall,
        &model,
        &certificate
    ));
}

#[test]
fn finite_profile_checker_handles_mixed_int_real_binders() {
    let mut arena = TermArena::new();
    let function = arena
        .declare_fun("f", &[Sort::Int, Sort::Real], Sort::Real)
        .unwrap();
    let (x_binder, x) = int_bound(&mut arena, "x");
    let r_binder = arena.declare("r", Sort::Real).unwrap();
    let r = arena.var(r_binder);
    let application = arena.apply(function, &[x, r]).unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let body = arena.real_ge(application, zero).unwrap();
    let inner = arena.forall(r_binder, body).unwrap();
    let forall = arena.forall(x_binder, inner).unwrap();
    let certificate = QuantifiedUfModelSatCertificate {
        assertion: forall,
        binder: x_binder,
    };
    let half = Rational::new(1, 2);
    let positive = FuncValue::constant_value(
        vec![Sort::Int, Sort::Real],
        Sort::Real,
        Value::Real(Rational::integer(0)),
    )
    .define_value(
        &[Value::Int(4), Value::Real(half)],
        Value::Real(Rational::integer(3)),
    );
    let mut model = Model::new();
    model.set_function(function, positive.clone());
    assert!(check_quantified_uf_model_sat(
        &arena,
        forall,
        &model,
        &certificate
    ));
    model.set_function(
        function,
        positive.define_value(
            &[Value::Int(4), Value::Real(half)],
            Value::Real(Rational::integer(-1)),
        ),
    );
    assert!(!check_quantified_uf_model_sat(
        &arena,
        forall,
        &model,
        &certificate
    ));
}

#[test]
fn checker_rejects_nonleading_vacuous_duplicate_and_interpreted_binders() {
    let mut arena = TermArena::new();
    let function = int_fn(&mut arena, "f");
    let (outer_binder, outer) = int_bound(&mut arena, "x");
    let application = arena.apply(function, &[outer]).unwrap();
    let zero = arena.int_const(0);
    let direct_body = arena.int_ge(application, zero).unwrap();
    let interpreted = arena.int_add(application, outer).unwrap();
    let interpreted_body = arena.int_ge(interpreted, zero).unwrap();
    let interpreted_forall = arena.forall(outer_binder, interpreted_body).unwrap();

    let (inner_binder, _inner) = int_bound(&mut arena, "y");
    let vacuous_inner = arena.forall(inner_binder, direct_body).unwrap();
    let vacuous_forall = arena.forall(outer_binder, vacuous_inner).unwrap();
    let duplicate_inner = arena.forall(outer_binder, direct_body).unwrap();
    let duplicate_forall = arena.forall(outer_binder, duplicate_inner).unwrap();
    let existential_inner = arena.exists(inner_binder, direct_body).unwrap();
    let existential_forall = arena.forall(outer_binder, existential_inner).unwrap();

    let mut model = Model::new();
    model.set_function(
        function,
        FuncValue::constant_value(vec![Sort::Int], Sort::Int, Value::Int(0)),
    );
    for assertion in [
        interpreted_forall,
        vacuous_forall,
        duplicate_forall,
        existential_forall,
    ] {
        let certificate = QuantifiedUfModelSatCertificate {
            assertion,
            binder: outer_binder,
        };
        assert!(!check_quantified_uf_model_sat(
            &arena,
            assertion,
            &model,
            &certificate
        ));
    }

    let bool_function = arena
        .declare_fun("bool_f", &[Sort::Bool], Sort::Bool)
        .unwrap();
    let bool_binder = arena.declare("b", Sort::Bool).unwrap();
    let bool_variable = arena.var(bool_binder);
    let bool_body = arena.apply(bool_function, &[bool_variable]).unwrap();
    let bool_forall = arena.forall(bool_binder, bool_body).unwrap();
    model.set_function(
        bool_function,
        FuncValue::constant(vec![Sort::Bool], Sort::Bool, 1),
    );
    let bool_certificate = QuantifiedUfModelSatCertificate {
        assertion: bool_forall,
        binder: bool_binder,
    };
    assert!(!check_quantified_uf_model_sat(
        &arena,
        bool_forall,
        &model,
        &bool_certificate
    ));
}

#[test]
fn profile_cap_overflow_declines() {
    let mut arena = TermArena::new();
    let function = int_fn(&mut arena, "f");
    let (binder, variable) = int_bound(&mut arena, "x");
    let application = arena.apply(function, &[variable]).unwrap();
    let zero = arena.int_const(0);
    let body = arena.int_ge(application, zero).unwrap();
    let forall = arena.forall(binder, body).unwrap();

    let mut interpretation = FuncValue::constant_value(vec![Sort::Int], Sort::Int, Value::Int(0));
    for value in 0..QUANTIFIED_UF_PROFILE_CAP {
        interpretation = interpretation
            .define_value(&[Value::Int(i128::try_from(value).unwrap())], Value::Int(1));
    }
    let mut model = Model::new();
    model.set_function(function, interpretation);
    let certificate = QuantifiedUfModelSatCertificate {
        assertion: forall,
        binder,
    };
    assert!(!check_quantified_uf_model_sat(
        &arena,
        forall,
        &model,
        &certificate
    ));
}

#[test]
fn cartesian_profile_and_binder_caps_decline() {
    let mut arena = TermArena::new();
    let function = arena
        .declare_fun("f", &[Sort::Int, Sort::Int], Sort::Int)
        .unwrap();
    let (x_binder, x) = int_bound(&mut arena, "x");
    let (y_binder, y) = int_bound(&mut arena, "y");
    let application = arena.apply(function, &[x, y]).unwrap();
    let zero = arena.int_const(0);
    let body = arena.int_ge(application, zero).unwrap();
    let inner = arena.forall(y_binder, body).unwrap();
    let forall = arena.forall(x_binder, inner).unwrap();
    let mut interpretation =
        FuncValue::constant_value(vec![Sort::Int, Sort::Int], Sort::Int, Value::Int(0));
    for value in 0..64_i128 {
        interpretation =
            interpretation.define_value(&[Value::Int(value), Value::Int(value)], Value::Int(1));
    }
    let mut model = Model::new();
    model.set_function(function, interpretation);
    let certificate = QuantifiedUfModelSatCertificate {
        assertion: forall,
        binder: x_binder,
    };
    assert!(!check_quantified_uf_model_sat(
        &arena,
        forall,
        &model,
        &certificate
    ));

    let parameters = vec![Sort::Int; QUANTIFIED_UF_BINDER_CAP + 1];
    let wide_function = arena.declare_fun("wide", &parameters, Sort::Int).unwrap();
    let mut binders = Vec::new();
    let mut variables = Vec::new();
    for index in 0..=QUANTIFIED_UF_BINDER_CAP {
        let name = format!("b{index}");
        let binder = arena.declare(&name, Sort::Int).unwrap();
        variables.push(arena.var(binder));
        binders.push(binder);
    }
    let wide_application = arena.apply(wide_function, &variables).unwrap();
    let zero = arena.int_const(0);
    let mut wide_assertion = arena.int_ge(wide_application, zero).unwrap();
    for &binder in binders.iter().rev() {
        wide_assertion = arena.forall(binder, wide_assertion).unwrap();
    }
    let mut wide_model = Model::new();
    wide_model.set_function(
        wide_function,
        FuncValue::constant_value(parameters, Sort::Int, Value::Int(0)),
    );
    let wide_certificate = QuantifiedUfModelSatCertificate {
        assertion: wide_assertion,
        binder: binders[0],
    };
    assert!(!check_quantified_uf_model_sat(
        &arena,
        wide_assertion,
        &wide_model,
        &wide_certificate
    ));
}
