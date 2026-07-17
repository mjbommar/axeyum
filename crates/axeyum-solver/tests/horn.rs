//! Integration tests for the Constrained Horn Clause (`CHC`) front-end
//! ([`solve_horn`]).
//!
//! Every `Sat` is re-checked **test-side, independently of the solver's own
//! verify-before-return gate**: the returned interpretation is substituted into
//! each original clause and the resulting validity obligation is discharged with
//! [`check_auto`], so a wrong `Sat` cannot slip past. `Unsat`/`Unknown` outcomes
//! are asserted directly; the solver must never panic on malformed input.
#![cfg(feature = "full")]

use axeyum_ir::{Op, Sort, TermArena, TermId, TermNode};
use axeyum_solver::{
    CheckResult, HornClause, HornModel, HornOutcome, HornSystem, SolverConfig, check_auto,
    solve_horn,
};

/// Substitutes the interpretation of `predicate` (in `model`) into a predicate
/// application `P(args)`, returning `I[params ↦ args]`. The test-side mirror of
/// the solver's own substitution, kept deliberately independent.
fn instantiate(arena: &mut TermArena, model: &HornModel, app: TermId) -> TermId {
    let (op, args) = match arena.node(app).clone() {
        TermNode::App { op, args } => (op, args.to_vec()),
        other => panic!("expected a predicate application, got {other:?}"),
    };
    let Op::Apply(func) = op else {
        panic!("expected an Op::Apply application");
    };
    let (params, body) = model
        .interpretation(func)
        .expect("model must interpret the predicate");
    assert_eq!(params.len(), args.len(), "interpretation arity must match");
    let mapping: Vec<(_, _)> = params.iter().copied().zip(args.iter().copied()).collect();
    subst(arena, body, &mapping)
}

fn subst(arena: &mut TermArena, term: TermId, mapping: &[(axeyum_ir::SymbolId, TermId)]) -> TermId {
    match arena.node(term).clone() {
        TermNode::Symbol(sym) => mapping
            .iter()
            .find(|&&(s, _)| s == sym)
            .map_or(term, |&(_, t)| t),
        TermNode::App { args, .. } => {
            let new_args: Vec<TermId> = args.iter().map(|&a| subst(arena, a, mapping)).collect();
            arena.rebuild_with_args(term, &new_args)
        }
        _ => term,
    }
}

/// Independently re-checks a `HornModel` against every clause of `system`:
/// `(⋀ body[P↦I]) ∧ constraint ∧ ¬(head[P↦I])` must be `Unsat` (head `None` ⇒ the
/// negated head is `true`, so the obligation is `bodies ∧ constraint`).
fn recheck_model(arena: &mut TermArena, system: &HornSystem, model: &HornModel) {
    let config = SolverConfig::default();
    for (i, clause) in system.clauses.iter().enumerate() {
        let mut assertions: Vec<TermId> = Vec::new();
        for &atom in &clause.body {
            assertions.push(instantiate(arena, model, atom));
        }
        assertions.push(clause.constraint);
        if let Some(head) = clause.head {
            let inst = instantiate(arena, model, head);
            assertions.push(arena.not(inst).unwrap());
        }
        match check_auto(arena, &assertions, &config) {
            Ok(CheckResult::Unsat) => {}
            other => panic!("clause {i} is not valid under the returned interpretation: {other:?}"),
        }
    }
}

/// Safe `LRA` Horn: `Inv(x:Real)`; init `x=0 ⇒ Inv(x)`; inductive
/// `Inv(x) ∧ x'=x+1 ⇒ Inv(x')`; query `Inv(x) ∧ x<0 ⇒ false`. `Inv := x ≥ 0` is
/// inductive ⇒ `Sat`.
#[test]
fn safe_lra_horn_is_sat_and_rechecks() {
    let mut arena = TermArena::new();
    let inv = arena.declare_fun("Inv", &[Sort::Real], Sort::Bool).unwrap();

    // init: x = 0 ⇒ Inv(x).
    let x = arena.declare("x", Sort::Real).unwrap();
    let xv = arena.var(x);
    let zero = arena.real_ratio(0, 1);
    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let inv_x = arena.apply(inv, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(inv_x),
    };

    // inductive: Inv(x) ∧ x' = x + 1 ⇒ Inv(x').
    let xp = arena.declare("xp", Sort::Real).unwrap();
    let xpv = arena.var(xp);
    let one = arena.real_ratio(1, 1);
    let x_plus_1 = arena.real_add(xv, one).unwrap();
    let xp_eq = arena.eq(xpv, x_plus_1).unwrap();
    let inv_x_body = arena.apply(inv, &[xv]).unwrap();
    let inv_xp = arena.apply(inv, &[xpv]).unwrap();
    let inductive = HornClause {
        body: vec![inv_x_body],
        constraint: xp_eq,
        head: Some(inv_xp),
    };

    // query: Inv(x) ∧ x < 0 ⇒ false.
    let x_lt_0 = arena.real_lt(xv, zero).unwrap();
    let inv_x_q = arena.apply(inv, &[xv]).unwrap();
    let query = HornClause {
        body: vec![inv_x_q],
        constraint: x_lt_0,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![inv],
        clauses: vec![fact, inductive, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    let HornOutcome::Sat(model) = outcome else {
        panic!("expected Sat for the inductive ‘x ≥ 0’ Horn system, got {outcome:?}");
    };
    // Independent test-side re-check of all three clauses.
    recheck_model(&mut arena, &system, &model);
}

/// Unsafe Horn: `Bad(x:Real)`; init `x=0 ⇒ Bad(x)`; inductive
/// `Bad(x) ∧ x'=x+1 ⇒ Bad(x')`; query `Bad(x) ∧ x=3 ⇒ false`. `x=3` is reachable
/// from `x=0` in three steps ⇒ `Unsat`.
#[test]
fn unsafe_horn_query_is_reachable() {
    let mut arena = TermArena::new();
    let p = arena.declare_fun("P", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let xv = arena.var(x);
    let zero = arena.real_ratio(0, 1);
    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let p_x = arena.apply(p, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(p_x),
    };

    let xp = arena.declare("xp", Sort::Real).unwrap();
    let xpv = arena.var(xp);
    let one = arena.real_ratio(1, 1);
    let x_plus_1 = arena.real_add(xv, one).unwrap();
    let xp_eq = arena.eq(xpv, x_plus_1).unwrap();
    let p_x_body = arena.apply(p, &[xv]).unwrap();
    let p_xp = arena.apply(p, &[xpv]).unwrap();
    let inductive = HornClause {
        body: vec![p_x_body],
        constraint: xp_eq,
        head: Some(p_xp),
    };

    let three = arena.real_ratio(3, 1);
    let x_eq_3 = arena.eq(xv, three).unwrap();
    let p_x_q = arena.apply(p, &[xv]).unwrap();
    let query = HornClause {
        body: vec![p_x_q],
        constraint: x_eq_3,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![p],
        clauses: vec![fact, inductive, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Unsat { steps } => {
            assert!(steps >= 3, "x=3 needs at least three +1 steps, got {steps}");
        }
        other => panic!("expected Unsat (the query is reachable), got {other:?}"),
    }
}

/// BV Horn: `Inv(x:BitVec(8))`; init `x=0 ⇒ Inv(x)`; inductive
/// `Inv(x) ∧ x'=x+2 ⇒ Inv(x')`; query `Inv(x) ∧ (x & 1)=1 ⇒ false` (x is odd).
/// `Inv := even` is inductive ⇒ `Sat` (or a sound `Unknown`).
#[test]
fn bv_horn_is_sat_or_sound_unknown() {
    let mut arena = TermArena::new();
    let inv = arena
        .declare_fun("Inv", &[Sort::BitVec(8)], Sort::Bool)
        .unwrap();

    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let xv = arena.var(x);
    let zero = arena.bv_const(8, 0).unwrap();
    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let inv_x = arena.apply(inv, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(inv_x),
    };

    let xp = arena.declare("xp", Sort::BitVec(8)).unwrap();
    let xpv = arena.var(xp);
    let two = arena.bv_const(8, 2).unwrap();
    let x_plus_2 = arena.bv_add(xv, two).unwrap();
    let xp_eq = arena.eq(xpv, x_plus_2).unwrap();
    let inv_x_body = arena.apply(inv, &[xv]).unwrap();
    let inv_xp = arena.apply(inv, &[xpv]).unwrap();
    let inductive = HornClause {
        body: vec![inv_x_body],
        constraint: xp_eq,
        head: Some(inv_xp),
    };

    let one = arena.bv_const(8, 1).unwrap();
    let lsb = arena.bv_and(xv, one).unwrap();
    let is_odd = arena.eq(lsb, one).unwrap();
    let inv_x_q = arena.apply(inv, &[xv]).unwrap();
    let query = HornClause {
        body: vec![inv_x_q],
        constraint: is_odd,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![inv],
        clauses: vec![fact, inductive, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Sat(model) => recheck_model(&mut arena, &system, &model),
        HornOutcome::Unknown { .. } => {} // a sound decline is acceptable
        HornOutcome::Unsat { .. } => {
            panic!("‘x even’ is genuinely safe; an Unsat would be a soundness bug")
        }
    }
}

/// Unsafe BV Horn whose query is reachable: init `x=0`, step `x'=x+1`, query
/// `x=5 ⇒ false`. 5 is reached in five steps ⇒ `Unsat` (or a sound `Unknown`,
/// never `Sat`).
#[test]
fn bv_horn_reachable_is_unsat_or_unknown() {
    let mut arena = TermArena::new();
    let p = arena
        .declare_fun("P", &[Sort::BitVec(8)], Sort::Bool)
        .unwrap();

    let x = arena.declare("x", Sort::BitVec(8)).unwrap();
    let xv = arena.var(x);
    let zero = arena.bv_const(8, 0).unwrap();
    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let p_x = arena.apply(p, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(p_x),
    };

    let xp = arena.declare("xp", Sort::BitVec(8)).unwrap();
    let xpv = arena.var(xp);
    let one = arena.bv_const(8, 1).unwrap();
    let x_plus_1 = arena.bv_add(xv, one).unwrap();
    let xp_eq = arena.eq(xpv, x_plus_1).unwrap();
    let p_x_body = arena.apply(p, &[xv]).unwrap();
    let p_xp = arena.apply(p, &[xpv]).unwrap();
    let inductive = HornClause {
        body: vec![p_x_body],
        constraint: xp_eq,
        head: Some(p_xp),
    };

    let five = arena.bv_const(8, 5).unwrap();
    let x_eq_5 = arena.eq(xv, five).unwrap();
    let p_x_q = arena.apply(p, &[xv]).unwrap();
    let query = HornClause {
        body: vec![p_x_q],
        constraint: x_eq_5,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![p],
        clauses: vec![fact, inductive, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Unsat { .. } | HornOutcome::Unknown { .. } => {}
        HornOutcome::Sat(_) => panic!("x=5 is reachable; a Sat would be a soundness bug"),
    }
}

/// In fragment now — a query-free two-predicate acyclic system (`x=0 ⇒ P(x)`,
/// `P(x) ⇒ Q(x)`) is solved: with no query nothing is unsafe, so `Sat`, and the
/// returned model re-checks. (Formerly out of fragment; the acyclic
/// multi-predicate slice covers it.)
#[test]
fn two_predicate_no_query_is_sat() {
    let mut arena = TermArena::new();
    let p = arena.declare_fun("P", &[Sort::Real], Sort::Bool).unwrap();
    let q = arena.declare_fun("Q", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let xv = arena.var(x);
    let zero = arena.real_ratio(0, 1);
    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let p_x = arena.apply(p, &[xv]).unwrap();
    let q_x = arena.apply(q, &[xv]).unwrap();

    // P(x) ∧ true ⇒ Q(x): a legitimate clause that references two predicates.
    let tru = arena.bool_const(true);
    let clause = HornClause {
        body: vec![p_x],
        constraint: tru,
        head: Some(q_x),
    };
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(arena.apply(p, &[xv]).unwrap()),
    };

    let system = HornSystem {
        predicates: vec![p, q],
        clauses: vec![fact, clause],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Sat(model) => recheck_model(&mut arena, &system, &model),
        HornOutcome::Unknown { .. } => {} // a sound decline is also acceptable
        HornOutcome::Unsat { .. } => panic!("no query clause ⇒ nothing unsafe; Unsat is a bug"),
    }
}

/// Out of fragment — a clause body with two predicate atoms (nonlinear) ⇒ a clean
/// `Unknown`.
#[test]
fn two_body_atoms_declines() {
    let mut arena = TermArena::new();
    let p = arena
        .declare_fun("P", &[Sort::Real, Sort::Real], Sort::Bool)
        .unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let y = arena.declare("y", Sort::Real).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let p_xy = arena.apply(p, &[xv, yv]).unwrap();
    let p_yx = arena.apply(p, &[yv, xv]).unwrap();
    let tru = arena.bool_const(true);
    // P(x,y) ∧ P(y,x) ∧ true ⇒ false: a body with two atoms (nonlinear).
    let clause = HornClause {
        body: vec![p_xy, p_yx],
        constraint: tru,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![p],
        clauses: vec![clause],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    assert!(
        matches!(outcome, HornOutcome::Unknown { .. }),
        "a two-atom body is nonlinear (out of fragment); expected Unknown, got {outcome:?}"
    );
}

/// Two-predicate acyclic `LRA`, SAFE: `Inv(x:Real)` is a self-recursive counter
/// (init `x=0`, step `x'=x+1`), `Q(x) :- Inv(x), x ≥ 0` is a derived predicate,
/// and the query `Q(x), x < 0 ⇒ false`. `Inv := x ≥ 0` and `Q := x ≥ 0` satisfy
/// every clause ⇒ `Sat`, independently re-checked.
#[test]
fn two_predicate_acyclic_lra_is_sat_and_rechecks() {
    let mut arena = TermArena::new();
    let inv = arena.declare_fun("Inv", &[Sort::Real], Sort::Bool).unwrap();
    let q = arena.declare_fun("Q", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let xv = arena.var(x);
    let zero = arena.real_ratio(0, 1);

    // init: x = 0 ⇒ Inv(x).
    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let inv_x = arena.apply(inv, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(inv_x),
    };

    // inductive: Inv(x) ∧ x' = x + 1 ⇒ Inv(x').
    let xp = arena.declare("xp", Sort::Real).unwrap();
    let xpv = arena.var(xp);
    let one = arena.real_ratio(1, 1);
    let x_plus_1 = arena.real_add(xv, one).unwrap();
    let xp_eq = arena.eq(xpv, x_plus_1).unwrap();
    let inv_x_body = arena.apply(inv, &[xv]).unwrap();
    let inv_xp = arena.apply(inv, &[xpv]).unwrap();
    let inductive = HornClause {
        body: vec![inv_x_body],
        constraint: xp_eq,
        head: Some(inv_xp),
    };

    // derived: Inv(x) ∧ x ≥ 0 ⇒ Q(x).
    let x_ge_0 = arena.real_ge(xv, zero).unwrap();
    let inv_x_d = arena.apply(inv, &[xv]).unwrap();
    let q_x = arena.apply(q, &[xv]).unwrap();
    let derived = HornClause {
        body: vec![inv_x_d],
        constraint: x_ge_0,
        head: Some(q_x),
    };

    // query: Q(x) ∧ x < 0 ⇒ false.
    let x_lt_0 = arena.real_lt(xv, zero).unwrap();
    let q_x_q = arena.apply(q, &[xv]).unwrap();
    let query = HornClause {
        body: vec![q_x_q],
        constraint: x_lt_0,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![inv, q],
        clauses: vec![fact, inductive, derived, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    let HornOutcome::Sat(model) = outcome else {
        panic!("expected Sat for the two-predicate acyclic LRA system, got {outcome:?}");
    };
    recheck_model(&mut arena, &system, &model);
}

/// Two-predicate acyclic, UNSAFE: `Inv` is the same self-recursive counter, the
/// derived `Q(x) :- Inv(x)` mirrors it, and the query `Q(x), x = 3 ⇒ false` is
/// reachable (x=3 is reached from x=0) ⇒ `Unsat` (never `Sat`).
#[test]
fn two_predicate_acyclic_unsafe_is_unsat() {
    let mut arena = TermArena::new();
    let inv = arena.declare_fun("Inv", &[Sort::Real], Sort::Bool).unwrap();
    let q = arena.declare_fun("Q", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let xv = arena.var(x);
    let zero = arena.real_ratio(0, 1);
    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let inv_x = arena.apply(inv, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(inv_x),
    };

    let xp = arena.declare("xp", Sort::Real).unwrap();
    let xpv = arena.var(xp);
    let one = arena.real_ratio(1, 1);
    let x_plus_1 = arena.real_add(xv, one).unwrap();
    let xp_eq = arena.eq(xpv, x_plus_1).unwrap();
    let inv_x_body = arena.apply(inv, &[xv]).unwrap();
    let inv_xp = arena.apply(inv, &[xpv]).unwrap();
    let inductive = HornClause {
        body: vec![inv_x_body],
        constraint: xp_eq,
        head: Some(inv_xp),
    };

    // derived: Inv(x) ⇒ Q(x).
    let tru = arena.bool_const(true);
    let inv_x_d = arena.apply(inv, &[xv]).unwrap();
    let q_x = arena.apply(q, &[xv]).unwrap();
    let derived = HornClause {
        body: vec![inv_x_d],
        constraint: tru,
        head: Some(q_x),
    };

    // query: Q(x) ∧ x = 3 ⇒ false (reachable).
    let three = arena.real_ratio(3, 1);
    let x_eq_3 = arena.eq(xv, three).unwrap();
    let q_x_q = arena.apply(q, &[xv]).unwrap();
    let query = HornClause {
        body: vec![q_x_q],
        constraint: x_eq_3,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![inv, q],
        clauses: vec![fact, inductive, derived, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Unsat { .. } => {}
        HornOutcome::Sat(_) => panic!("x=3 is reachable through Q; a Sat would be a soundness bug"),
        HornOutcome::Unknown { .. } => {
            panic!("the query is reachable; expected Unsat, not a decline")
        }
    }
}

/// Mutual recursion with no facts and no query (`P :- Q`, `Q :- P`) ⇒ `Sat`: the
/// merged tagged predicate has an empty init and no bad states, so nothing is
/// unsafe. The all-`false` interpretation (`P := false`, `Q := false`) satisfies
/// every clause and re-checks. (Formerly declined; the merge reduction covers it.)
#[test]
fn mutual_recursion_no_fact_is_sat() {
    let mut arena = TermArena::new();
    let p = arena.declare_fun("P", &[Sort::Real], Sort::Bool).unwrap();
    let q = arena.declare_fun("Q", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let xv = arena.var(x);
    let tru = arena.bool_const(true);

    // P(x) ⇒ Q(x).
    let p_x = arena.apply(p, &[xv]).unwrap();
    let q_x = arena.apply(q, &[xv]).unwrap();
    let p_to_q = HornClause {
        body: vec![p_x],
        constraint: tru,
        head: Some(q_x),
    };
    // Q(x) ⇒ P(x): closes the cycle P ↔ Q.
    let q_x_b = arena.apply(q, &[xv]).unwrap();
    let p_x_h = arena.apply(p, &[xv]).unwrap();
    let q_to_p = HornClause {
        body: vec![q_x_b],
        constraint: tru,
        head: Some(p_x_h),
    };

    let system = HornSystem {
        predicates: vec![p, q],
        clauses: vec![p_to_q, q_to_p],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Sat(model) => recheck_model(&mut arena, &system, &model),
        HornOutcome::Unknown { .. } => {} // a sound decline is acceptable
        HornOutcome::Unsat { .. } => {
            panic!("no fact and no query ⇒ nothing unsafe; an Unsat would be a soundness bug")
        }
    }
}

/// Genuine 2-predicate mutual recursion that is SAFE: `Even`/`Odd` over the reals
/// with a fact `Even(0)`, the cross steps `Even(x) ∧ y=x+1 ⇒ Odd(y)` and
/// `Odd(x) ∧ y=x+1 ⇒ Even(y)`, and the safety query `Even(x) ∧ x < 0 ⇒ false`.
/// The reachable `Even`/`Odd` values are all `≥ 0`, so the property holds ⇒ `Sat`,
/// projected back per member and independently re-checked. (Or a sound `Unknown`.)
#[test]
fn even_odd_mutual_recursion_is_sat_or_unknown() {
    let mut arena = TermArena::new();
    let even = arena
        .declare_fun("Even", &[Sort::Real], Sort::Bool)
        .unwrap();
    let odd = arena.declare_fun("Odd", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let y = arena.declare("y", Sort::Real).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);

    // fact: x = 0 ⇒ Even(x).
    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let even_x = arena.apply(even, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(even_x),
    };

    // Even(x) ∧ y = x + 1 ⇒ Odd(y).
    let x_plus_1 = arena.real_add(xv, one).unwrap();
    let y_eq = arena.eq(yv, x_plus_1).unwrap();
    let even_x_b = arena.apply(even, &[xv]).unwrap();
    let odd_y = arena.apply(odd, &[yv]).unwrap();
    let even_to_odd = HornClause {
        body: vec![even_x_b],
        constraint: y_eq,
        head: Some(odd_y),
    };

    // Odd(x) ∧ y = x + 1 ⇒ Even(y).
    let x_plus_1b = arena.real_add(xv, one).unwrap();
    let y_eq_b = arena.eq(yv, x_plus_1b).unwrap();
    let odd_x_b = arena.apply(odd, &[xv]).unwrap();
    let even_y = arena.apply(even, &[yv]).unwrap();
    let odd_to_even = HornClause {
        body: vec![odd_x_b],
        constraint: y_eq_b,
        head: Some(even_y),
    };

    // query: Even(x) ∧ x < 0 ⇒ false (holds: reachable Even values are ≥ 0).
    let x_lt_0 = arena.real_lt(xv, zero).unwrap();
    let even_x_q = arena.apply(even, &[xv]).unwrap();
    let query = HornClause {
        body: vec![even_x_q],
        constraint: x_lt_0,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![even, odd],
        clauses: vec![fact, even_to_odd, odd_to_even, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Sat(model) => recheck_model(&mut arena, &system, &model),
        HornOutcome::Unknown { .. } => {} // a sound decline is acceptable
        HornOutcome::Unsat { .. } => {
            panic!(
                "the Even/Odd reachable set is x ≥ 0; the x<0 query is unreachable — Unsat is a \
                    soundness bug"
            )
        }
    }
}

/// 2-predicate mutual recursion that is UNSAFE: same `Even`/`Odd` cross steps from
/// `Even(0)`, but the query `Even(x) ∧ x = 2 ⇒ false` IS reachable (0 → 1 (Odd) →
/// 2 (Even)). ⇒ `Unsat` (or a sound `Unknown`), never `Sat`.
#[test]
fn even_odd_mutual_recursion_unsafe_is_unsat_or_unknown() {
    let mut arena = TermArena::new();
    let even = arena
        .declare_fun("Even", &[Sort::Real], Sort::Bool)
        .unwrap();
    let odd = arena.declare_fun("Odd", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let y = arena.declare("y", Sort::Real).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let two = arena.real_ratio(2, 1);

    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let even_x = arena.apply(even, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(even_x),
    };

    let x_plus_1 = arena.real_add(xv, one).unwrap();
    let y_eq = arena.eq(yv, x_plus_1).unwrap();
    let even_x_b = arena.apply(even, &[xv]).unwrap();
    let odd_y = arena.apply(odd, &[yv]).unwrap();
    let even_to_odd = HornClause {
        body: vec![even_x_b],
        constraint: y_eq,
        head: Some(odd_y),
    };

    let x_plus_1b = arena.real_add(xv, one).unwrap();
    let y_eq_b = arena.eq(yv, x_plus_1b).unwrap();
    let odd_x_b = arena.apply(odd, &[xv]).unwrap();
    let even_y = arena.apply(even, &[yv]).unwrap();
    let odd_to_even = HornClause {
        body: vec![odd_x_b],
        constraint: y_eq_b,
        head: Some(even_y),
    };

    // query: Even(x) ∧ x = 2 ⇒ false (reachable: 0 →Odd 1 →Even 2).
    let x_eq_2 = arena.eq(xv, two).unwrap();
    let even_x_q = arena.apply(even, &[xv]).unwrap();
    let query = HornClause {
        body: vec![even_x_q],
        constraint: x_eq_2,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![even, odd],
        clauses: vec![fact, even_to_odd, odd_to_even, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Unsat { .. } | HornOutcome::Unknown { .. } => {}
        HornOutcome::Sat(_) => {
            panic!("Even(2) is reachable; the query is derivable — a Sat would be a soundness bug")
        }
    }
}

/// Builds one cross step `from(pre) ∧ succ = pre + 1 ⇒ to(succ)` of a real
/// counter, used to wire the 3-predicate `SCC` cycle.
fn counter_step(
    arena: &mut TermArena,
    pre: axeyum_ir::SymbolId,
    succ: axeyum_ir::SymbolId,
    from: axeyum_ir::FuncId,
    to: axeyum_ir::FuncId,
) -> HornClause {
    let pre_v = arena.var(pre);
    let succ_v = arena.var(succ);
    let one = arena.real_ratio(1, 1);
    let pre_plus_1 = arena.real_add(pre_v, one).unwrap();
    let succ_eq = arena.eq(succ_v, pre_plus_1).unwrap();
    let from_pre = arena.apply(from, &[pre_v]).unwrap();
    let to_succ = arena.apply(to, &[succ_v]).unwrap();
    HornClause {
        body: vec![from_pre],
        constraint: succ_eq,
        head: Some(to_succ),
    }
}

/// A 3-predicate SCC cycle `P → Q → R → P` over the reals: fact `P(0)`, steps
/// `P(x) ∧ y=x+1 ⇒ Q(y)`, `Q(x) ∧ y=x+1 ⇒ R(y)`, `R(x) ∧ y=x+1 ⇒ P(y)`, and the
/// safety query `P(x) ∧ x < 0 ⇒ false`. Reachable values are `≥ 0` ⇒ `Sat`
/// (re-checked per member), or a sound `Unknown` — never `Unsat`.
#[test]
fn three_predicate_scc_is_sat_or_unknown() {
    let mut arena = TermArena::new();
    let p = arena.declare_fun("P", &[Sort::Real], Sort::Bool).unwrap();
    let q = arena.declare_fun("Q", &[Sort::Real], Sort::Bool).unwrap();
    let r = arena.declare_fun("R", &[Sort::Real], Sort::Bool).unwrap();

    let x0 = arena.declare("x", Sort::Real).unwrap();
    let x1 = arena.declare("y", Sort::Real).unwrap();
    let xv = arena.var(x0);
    let zero = arena.real_ratio(0, 1);

    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let p_x = arena.apply(p, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(p_x),
    };

    let p_to_q = counter_step(&mut arena, x0, x1, p, q);
    let q_to_r = counter_step(&mut arena, x0, x1, q, r);
    let r_to_p = counter_step(&mut arena, x0, x1, r, p);

    let x_lt_0 = arena.real_lt(xv, zero).unwrap();
    let p_x_q = arena.apply(p, &[xv]).unwrap();
    let query = HornClause {
        body: vec![p_x_q],
        constraint: x_lt_0,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![p, q, r],
        clauses: vec![fact, p_to_q, q_to_r, r_to_p, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Sat(model) => recheck_model(&mut arena, &system, &model),
        HornOutcome::Unknown { .. } => {}
        HornOutcome::Unsat { .. } => {
            panic!(
                "the 3-cycle reachable set is x ≥ 0; the x<0 query is unreachable — Unsat is a \
                    soundness bug"
            )
        }
    }
}

/// Soundness-negative mutual recursion: the ONLY plausible-looking candidate model
/// is wrong. `Even(0)`, the usual cross steps, and the query `Odd(x) ∧ x = 2 ⇒
/// false` — but `Odd(2)` is NOT reachable (Odd holds only at odd values), so the
/// query is genuinely unreachable and the system is SAFE. A buggy projection that
/// conflated the two members' reachable sets would wrongly report `Unsat`; the
/// verify-before-return gate must keep this `Sat` (per member) or `Unknown`,
/// never a wrong `Unsat`, and never a `Sat` whose model fails the re-check.
#[test]
fn mutual_recursion_soundness_negative() {
    let mut arena = TermArena::new();
    let even = arena
        .declare_fun("Even", &[Sort::Real], Sort::Bool)
        .unwrap();
    let odd = arena.declare_fun("Odd", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let y = arena.declare("y", Sort::Real).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let two = arena.real_ratio(2, 1);

    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let even_x = arena.apply(even, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(even_x),
    };
    let x_plus_1 = arena.real_add(xv, one).unwrap();
    let y_eq = arena.eq(yv, x_plus_1).unwrap();
    let even_x_b = arena.apply(even, &[xv]).unwrap();
    let odd_y = arena.apply(odd, &[yv]).unwrap();
    let even_to_odd = HornClause {
        body: vec![even_x_b],
        constraint: y_eq,
        head: Some(odd_y),
    };
    let x_plus_1b = arena.real_add(xv, one).unwrap();
    let y_eq_b = arena.eq(yv, x_plus_1b).unwrap();
    let odd_x_b = arena.apply(odd, &[xv]).unwrap();
    let even_y = arena.apply(even, &[yv]).unwrap();
    let odd_to_even = HornClause {
        body: vec![odd_x_b],
        constraint: y_eq_b,
        head: Some(even_y),
    };
    // query: Odd(x) ∧ x = 2 ⇒ false (UNREACHABLE — Odd holds only at odd values).
    let x_eq_2 = arena.eq(xv, two).unwrap();
    let odd_x_q = arena.apply(odd, &[xv]).unwrap();
    let query = HornClause {
        body: vec![odd_x_q],
        constraint: x_eq_2,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![even, odd],
        clauses: vec![fact, even_to_odd, odd_to_even, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        // SAFE: a sound Sat must survive the independent re-check.
        HornOutcome::Sat(model) => recheck_model(&mut arena, &system, &model),
        HornOutcome::Unknown { .. } => {}
        HornOutcome::Unsat { .. } => {
            panic!(
                "Odd(2) is unreachable (Odd holds only at odd values); an Unsat here would be a \
                    projection-conflation soundness bug"
            )
        }
    }
}

/// A non-recursive predicate chain `A ⇒ B ⇒ C` (with a fact seeding `A` and a
/// query off `C`) ⇒ `Sat`, independently re-checked. No predicate is recursive;
/// each gets a direct formula in topological order `A, B, C`.
#[test]
fn non_recursive_chain_is_sat_and_rechecks() {
    let mut arena = TermArena::new();
    let a = arena.declare_fun("A", &[Sort::Real], Sort::Bool).unwrap();
    let b = arena.declare_fun("B", &[Sort::Real], Sort::Bool).unwrap();
    let c = arena.declare_fun("C", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let xv = arena.var(x);
    let zero = arena.real_ratio(0, 1);
    let tru = arena.bool_const(true);

    // fact: x ≥ 0 ⇒ A(x).
    let x_ge_0 = arena.real_ge(xv, zero).unwrap();
    let a_x = arena.apply(a, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_ge_0,
        head: Some(a_x),
    };
    // A(x) ⇒ B(x).
    let a_x_b = arena.apply(a, &[xv]).unwrap();
    let b_x = arena.apply(b, &[xv]).unwrap();
    let a_to_b = HornClause {
        body: vec![a_x_b],
        constraint: tru,
        head: Some(b_x),
    };
    // B(x) ⇒ C(x).
    let b_x_b = arena.apply(b, &[xv]).unwrap();
    let c_x = arena.apply(c, &[xv]).unwrap();
    let b_to_c = HornClause {
        body: vec![b_x_b],
        constraint: tru,
        head: Some(c_x),
    };
    // query: C(x) ∧ x < 0 ⇒ false (unreachable: A only holds for x ≥ 0).
    let x_lt_0 = arena.real_lt(xv, zero).unwrap();
    let c_x_q = arena.apply(c, &[xv]).unwrap();
    let query = HornClause {
        body: vec![c_x_q],
        constraint: x_lt_0,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![a, b, c],
        clauses: vec![fact, a_to_b, b_to_c, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    let HornOutcome::Sat(model) = outcome else {
        panic!("expected Sat for the non-recursive A ⇒ B ⇒ C chain, got {outcome:?}");
    };
    recheck_model(&mut arena, &system, &model);
}

/// A two-predicate chain whose query IS reachable through the chain ⇒ `Unsat`:
/// fact `x = 5 ⇒ A(x)`, `A(x) ⇒ B(x)`, query `B(x) ∧ x = 5 ⇒ false`.
#[test]
fn non_recursive_chain_reachable_is_unsat() {
    let mut arena = TermArena::new();
    let a = arena.declare_fun("A", &[Sort::Real], Sort::Bool).unwrap();
    let b = arena.declare_fun("B", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let xv = arena.var(x);
    let five = arena.real_ratio(5, 1);
    let tru = arena.bool_const(true);

    let x_eq_5 = arena.eq(xv, five).unwrap();
    let a_x = arena.apply(a, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_5,
        head: Some(a_x),
    };
    let a_x_b = arena.apply(a, &[xv]).unwrap();
    let b_x = arena.apply(b, &[xv]).unwrap();
    let a_to_b = HornClause {
        body: vec![a_x_b],
        constraint: tru,
        head: Some(b_x),
    };
    let x_eq_5_q = arena.eq(xv, five).unwrap();
    let b_x_q = arena.apply(b, &[xv]).unwrap();
    let query = HornClause {
        body: vec![b_x_q],
        constraint: x_eq_5_q,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![a, b],
        clauses: vec![fact, a_to_b, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Unsat { .. } => {}
        other => panic!("the query is reachable through A ⇒ B; expected Unsat, got {other:?}"),
    }
}

/// Stratified **nonlinear** SAT: two lower predicates `P`, `Q` are solved directly
/// (`x ≥ 0 ⇒ P(x)`, `x ≤ 10 ⇒ Q(x)`), then `R(x) ⇐ P(x) ∧ Q(x) ∧ true` is a
/// nonlinear (`k = 2`) clause whose body atoms are both lower-stratum. The query
/// `R(x) ∧ x < 0 ⇒ false` holds (every reachable `R` value has `0 ≤ x ≤ 10`).
/// Both body atoms fold into the constraint, leaving no recursive remainder ⇒
/// `R := P ∧ Q = (0 ≤ x ≤ 10)` ⇒ `Sat`, independently re-checked.
#[test]
fn stratified_nonlinear_two_lower_bodies_is_sat() {
    let mut arena = TermArena::new();
    let p = arena.declare_fun("P", &[Sort::Real], Sort::Bool).unwrap();
    let q = arena.declare_fun("Q", &[Sort::Real], Sort::Bool).unwrap();
    let r = arena.declare_fun("R", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let xv = arena.var(x);
    let zero = arena.real_ratio(0, 1);
    let ten = arena.real_ratio(10, 1);
    let tru = arena.bool_const(true);

    // x ≥ 0 ⇒ P(x).
    let x_ge_0 = arena.real_ge(xv, zero).unwrap();
    let p_x = arena.apply(p, &[xv]).unwrap();
    let p_fact = HornClause {
        body: vec![],
        constraint: x_ge_0,
        head: Some(p_x),
    };
    // x ≤ 10 ⇒ Q(x).
    let x_le_10 = arena.real_le(xv, ten).unwrap();
    let q_x = arena.apply(q, &[xv]).unwrap();
    let q_fact = HornClause {
        body: vec![],
        constraint: x_le_10,
        head: Some(q_x),
    };
    // P(x) ∧ Q(x) ∧ true ⇒ R(x): a nonlinear (2-atom) body, both lower-stratum.
    let p_x_b = arena.apply(p, &[xv]).unwrap();
    let q_x_b = arena.apply(q, &[xv]).unwrap();
    let r_x = arena.apply(r, &[xv]).unwrap();
    let r_clause = HornClause {
        body: vec![p_x_b, q_x_b],
        constraint: tru,
        head: Some(r_x),
    };
    // query: R(x) ∧ x < 0 ⇒ false (unreachable: R ⇒ x ≥ 0).
    let x_lt_0 = arena.real_lt(xv, zero).unwrap();
    let r_x_q = arena.apply(r, &[xv]).unwrap();
    let query = HornClause {
        body: vec![r_x_q],
        constraint: x_lt_0,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![p, q, r],
        clauses: vec![p_fact, q_fact, r_clause, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    let HornOutcome::Sat(model) = outcome else {
        panic!("expected Sat for the stratified nonlinear P ∧ Q ⇒ R system, got {outcome:?}");
    };
    recheck_model(&mut arena, &system, &model);
}

/// Nonlinear **fact UNSAT**: `false` is reachable through a 2-atom body. `P(x)`
/// holds for `x = 5` and `Q(x)` for `x = 5`, then `P(x) ∧ Q(x) ⇒ false` is a
/// nonlinear query whose body is satisfiable (at `x = 5`) ⇒ `Unsat`.
#[test]
fn nonlinear_fact_query_is_unsat() {
    let mut arena = TermArena::new();
    let p = arena.declare_fun("P", &[Sort::Real], Sort::Bool).unwrap();
    let q = arena.declare_fun("Q", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let xv = arena.var(x);
    let five = arena.real_ratio(5, 1);
    let tru = arena.bool_const(true);

    let x_eq_5 = arena.eq(xv, five).unwrap();
    let p_x = arena.apply(p, &[xv]).unwrap();
    let p_fact = HornClause {
        body: vec![],
        constraint: x_eq_5,
        head: Some(p_x),
    };
    let x_eq_5b = arena.eq(xv, five).unwrap();
    let q_x = arena.apply(q, &[xv]).unwrap();
    let q_fact = HornClause {
        body: vec![],
        constraint: x_eq_5b,
        head: Some(q_x),
    };
    // P(x) ∧ Q(x) ⇒ false: a nonlinear query, satisfiable at x = 5.
    let p_x_b = arena.apply(p, &[xv]).unwrap();
    let q_x_b = arena.apply(q, &[xv]).unwrap();
    let query = HornClause {
        body: vec![p_x_b, q_x_b],
        constraint: tru,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![p, q],
        clauses: vec![p_fact, q_fact, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Unsat { .. } => {}
        HornOutcome::Sat(_) => {
            panic!("P(5) ∧ Q(5) derives false; a Sat would be a soundness bug")
        }
        HornOutcome::Unknown { .. } => {
            panic!("the nonlinear query is satisfiable at x = 5; expected Unsat, not a decline")
        }
    }
}

/// **Linear recursion plus a solved side atom**: `Inv` is the usual self-recursive
/// counter (`x = 0`, `x' = x + 1`), `Bound(x) :- x ≤ 1000000` is a solved lower
/// predicate, and the inductive step *also* consults it:
/// `Inv(x) ∧ Bound(x') ∧ x' = x + 1 ⇒ Inv(x')` (a 2-atom body: one recursive
/// `Inv`, one solved `Bound`). After folding `Bound`, the clause is the linear
/// inductive shape. The query `Inv(x) ∧ x < 0 ⇒ false` holds ⇒ `Sat`
/// (re-checked), or a sound `Unknown` — never `Unsat`.
#[test]
fn linear_recursion_with_solved_side_atom_is_sat_or_unknown() {
    let mut arena = TermArena::new();
    let inv = arena.declare_fun("Inv", &[Sort::Real], Sort::Bool).unwrap();
    let bound = arena
        .declare_fun("Bound", &[Sort::Real], Sort::Bool)
        .unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let xp = arena.declare("xp", Sort::Real).unwrap();
    let xv = arena.var(x);
    let xpv = arena.var(xp);
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let big = arena.real_ratio(1_000_000, 1);

    // Bound(x) :- x ≤ 1000000.
    let x_le_big = arena.real_le(xv, big).unwrap();
    let bound_x = arena.apply(bound, &[xv]).unwrap();
    let bound_fact = HornClause {
        body: vec![],
        constraint: x_le_big,
        head: Some(bound_x),
    };
    // init: x = 0 ⇒ Inv(x).
    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let inv_x = arena.apply(inv, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(inv_x),
    };
    // inductive: Inv(x) ∧ Bound(x') ∧ x' = x + 1 ⇒ Inv(x').
    let x_plus_1 = arena.real_add(xv, one).unwrap();
    let xp_eq = arena.eq(xpv, x_plus_1).unwrap();
    let inv_x_b = arena.apply(inv, &[xv]).unwrap();
    let bound_xp = arena.apply(bound, &[xpv]).unwrap();
    let inv_xp = arena.apply(inv, &[xpv]).unwrap();
    let inductive = HornClause {
        body: vec![inv_x_b, bound_xp],
        constraint: xp_eq,
        head: Some(inv_xp),
    };
    // query: Inv(x) ∧ x < 0 ⇒ false.
    let x_lt_0 = arena.real_lt(xv, zero).unwrap();
    let inv_x_q = arena.apply(inv, &[xv]).unwrap();
    let query = HornClause {
        body: vec![inv_x_q],
        constraint: x_lt_0,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![bound, inv],
        clauses: vec![bound_fact, fact, inductive, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Sat(model) => recheck_model(&mut arena, &system, &model),
        HornOutcome::Unknown { .. } => {}
        HornOutcome::Unsat { .. } => {
            panic!(
                "the reachable Inv set is 0 ≤ x ≤ 1000000; the x<0 query is unreachable — Unsat \
                    would be a soundness bug"
            )
        }
    }
}

/// **Genuine nonlinear recursion** declines: `R(z) ⇐ R(x) ∧ R(y) ∧ z = x + y` keeps
/// *two* recursive `R`-atoms in the body even after folding (nothing to fold — both
/// are in `R`'s own SCC). With a fact `R(1)` and a query, the system must decline
/// to `Unknown` (sound), never guess a Sat/Unsat.
#[test]
fn genuine_nonlinear_recursion_declines() {
    let mut arena = TermArena::new();
    let r = arena.declare_fun("R", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let y = arena.declare("y", Sort::Real).unwrap();
    let z = arena.declare("z", Sort::Real).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let zv = arena.var(z);
    let one = arena.real_ratio(1, 1);

    // fact: x = 1 ⇒ R(x).
    let x_eq_1 = arena.eq(xv, one).unwrap();
    let r_x = arena.apply(r, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_1,
        head: Some(r_x),
    };
    // R(x) ∧ R(y) ∧ z = x + y ⇒ R(z): two recursive R-atoms (genuine nonlinear).
    let x_plus_y = arena.real_add(xv, yv).unwrap();
    let z_eq = arena.eq(zv, x_plus_y).unwrap();
    let rec_first = arena.apply(r, &[xv]).unwrap();
    let rec_second = arena.apply(r, &[yv]).unwrap();
    let r_z = arena.apply(r, &[zv]).unwrap();
    let nonlinear = HornClause {
        body: vec![rec_first, rec_second],
        constraint: z_eq,
        head: Some(r_z),
    };
    // query: R(x) ∧ x < 0 ⇒ false.
    let zero = arena.real_ratio(0, 1);
    let x_lt_0 = arena.real_lt(xv, zero).unwrap();
    let r_x_q = arena.apply(r, &[xv]).unwrap();
    let query = HornClause {
        body: vec![r_x_q],
        constraint: x_lt_0,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![r],
        clauses: vec![fact, nonlinear, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    assert!(
        matches!(outcome, HornOutcome::Unknown { .. }),
        "genuine nonlinear recursion (two recursive body atoms) must decline soundly; got {outcome:?}"
    );
}

/// **Soundness-negative nonlinear**: a 2-atom-body system whose only plausible
/// candidate model is wrong must never return `Sat`. `P(x) :- x = 0`,
/// `Q(x) :- x = 1`, then `R(x) ⇐ P(x) ∧ Q(x)` — but `P ∧ Q` is empty (no `x` is
/// both 0 and 1), so `R` is empty. The query `R(x) ∧ x = 0 ⇒ false` is genuinely
/// SAFE (R is empty). A buggy fold that dropped one atom (treating the body as just
/// `P`) would make `R = {0}` and wrongly report `Unsat`. The verify-before-return
/// gate must keep this `Sat` (re-checked) or `Unknown`, never a wrong `Unsat`.
#[test]
fn nonlinear_soundness_negative_empty_conjunction() {
    let mut arena = TermArena::new();
    let p = arena.declare_fun("P", &[Sort::Real], Sort::Bool).unwrap();
    let q = arena.declare_fun("Q", &[Sort::Real], Sort::Bool).unwrap();
    let r = arena.declare_fun("R", &[Sort::Real], Sort::Bool).unwrap();

    let x = arena.declare("x", Sort::Real).unwrap();
    let xv = arena.var(x);
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let tru = arena.bool_const(true);

    // P(x) :- x = 0.
    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let p_x = arena.apply(p, &[xv]).unwrap();
    let p_fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(p_x),
    };
    // Q(x) :- x = 1.
    let x_eq_1 = arena.eq(xv, one).unwrap();
    let q_x = arena.apply(q, &[xv]).unwrap();
    let q_fact = HornClause {
        body: vec![],
        constraint: x_eq_1,
        head: Some(q_x),
    };
    // R(x) ⇐ P(x) ∧ Q(x): the conjunction is empty (no x is both 0 and 1).
    let p_x_b = arena.apply(p, &[xv]).unwrap();
    let q_x_b = arena.apply(q, &[xv]).unwrap();
    let r_x = arena.apply(r, &[xv]).unwrap();
    let r_clause = HornClause {
        body: vec![p_x_b, q_x_b],
        constraint: tru,
        head: Some(r_x),
    };
    // query: R(x) ∧ x = 0 ⇒ false (UNREACHABLE — R is empty).
    let x_eq_0_q = arena.eq(xv, zero).unwrap();
    let r_x_q = arena.apply(r, &[xv]).unwrap();
    let query = HornClause {
        body: vec![r_x_q],
        constraint: x_eq_0_q,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![p, q, r],
        clauses: vec![p_fact, q_fact, r_clause, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Sat(model) => recheck_model(&mut arena, &system, &model),
        HornOutcome::Unknown { .. } => {}
        HornOutcome::Unsat { .. } => {
            panic!(
                "P ∧ Q is empty so R is empty and the query is unreachable; an Unsat here would \
                    be a dropped-atom soundness bug"
            )
        }
    }
}

/// A malformed/empty system (no predicates) ⇒ a graceful `Unknown`, never a panic.
#[test]
fn empty_system_is_graceful_unknown() {
    let mut arena = TermArena::new();
    let system = HornSystem {
        predicates: vec![],
        clauses: vec![],
    };
    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    assert!(
        matches!(outcome, HornOutcome::Unknown { .. }),
        "an empty system has no predicate to solve; expected Unknown, got {outcome:?}"
    );
}

/// A single-predicate system with no query clause is trivially safe (`bad` is
/// `false`): the engine proves safety and the interpretation re-checks. Exercises
/// the empty-query reduction path without a panic.
#[test]
fn no_query_clause_is_trivially_safe() {
    let mut arena = TermArena::new();
    let inv = arena.declare_fun("Inv", &[Sort::Real], Sort::Bool).unwrap();
    let x = arena.declare("x", Sort::Real).unwrap();
    let xv = arena.var(x);
    let zero = arena.real_ratio(0, 1);
    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let inv_x = arena.apply(inv, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(inv_x),
    };
    let system = HornSystem {
        predicates: vec![inv],
        clauses: vec![fact],
    };
    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Sat(model) => recheck_model(&mut arena, &system, &model),
        HornOutcome::Unknown { .. } => {}
        HornOutcome::Unsat { .. } => panic!("no query clause ⇒ nothing unsafe; Unsat is a bug"),
    }
}
