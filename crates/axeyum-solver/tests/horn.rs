//! Integration tests for the Constrained Horn Clause (`CHC`) front-end
//! ([`solve_horn`]).
//!
//! Every `Sat` is re-checked **test-side, independently of the solver's own
//! verify-before-return gate**: the returned interpretation is substituted into
//! each original clause and the resulting validity obligation is discharged with
//! [`check_auto`], so a wrong `Sat` cannot slip past. `Unsat`/`Unknown` outcomes
//! are asserted directly; the solver must never panic on malformed input.

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

/// Mutual recursion (`P :- Q`, `Q :- P`) ⇒ `Ok(Unknown)` (decline): a cycle among
/// distinct predicates is out of the acyclic fragment.
#[test]
fn mutual_recursion_declines() {
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
    assert!(
        matches!(outcome, HornOutcome::Unknown { .. }),
        "mutual recursion is a cycle among distinct predicates (out of fragment); expected \
         Unknown, got {outcome:?}"
    );
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
