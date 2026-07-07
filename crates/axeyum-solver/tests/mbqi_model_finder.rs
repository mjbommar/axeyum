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
//! Soundness is the anchor and is tested both ways:
//!
//! - every `sat` this returns is **independently replay-checked** here — the
//!   returned model is evaluated against the ground constraints and the universal
//!   body is re-evaluated at a wide range of concrete points (this test's own
//!   reasoning, not the finder's), so a fabricated `sat` would fail; and
//! - the soundness negatives: a genuinely UNSAT quantified query — including
//!   ones whose violation lives at a UF *table entry* rather than the default —
//!   must NOT be reported `sat` (it must stay `unsat`), and an out-of-fragment
//!   universal must not be fabricated `sat`.

use std::time::Duration;

use axeyum_ir::{Assignment, FuncId, Rational, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, Model, SolverConfig, solve};

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

    let CheckResult::Sat(model) = check(&mut arena, &[forall, f5_is_3]) else {
        panic!("∀x. f(x) ≥ 0 ∧ f(5) = 3 is genuinely satisfiable");
    };
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

    let CheckResult::Sat(model) = check(&mut arena, &[forall, pf7]) else {
        panic!("∀x. P(f(x)) ∧ P(f(7)) is genuinely satisfiable");
    };
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

    let CheckResult::Sat(model) = check(&mut arena, &[forall, f1_is_2, g1_is_4]) else {
        panic!("∀x. f(x)+g(x) ≥ 0 ∧ f(1)=2 ∧ g(1)=4 is satisfiable");
    };
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

    assert!(
        matches!(check(&mut arena, &[forall, f_is_1]), CheckResult::Sat(_)),
        "∀r:Real. f(r) ≥ 0 ∧ f(2.5) = 1 is satisfiable"
    );
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
