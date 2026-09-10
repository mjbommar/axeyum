//! Integration tests for the **`Int`-sorted** Constrained Horn Clause route:
//! [`solve_horn`] dispatching an all-`Int` predicate vocabulary to the native-ℤ
//! engines `prove_safety_pdr_lia` / `prove_safety_imc_lia`.
//!
//! Before this route existed, `horn.rs` classified an `Int` state vocabulary as
//! `StateClass::Unsupported` and declined every such system to
//! [`HornOutcome::Unknown`] — which is why the two `LIA` engines (1,771 lines)
//! had no production caller at all. These tests are the observation that the
//! route is live: they assert a **definite** `Sat`/`Unsat`, never accepting a
//! `Unknown`, so reverting the dispatch makes them fail rather than pass
//! vacuously.
//!
//! Every `Sat` is re-checked **test-side, independently of the solver's own
//! verify-before-return gate**: the returned interpretation is substituted into
//! each original clause and the resulting validity obligation is discharged with
//! [`check_auto`], so a wrong `Sat` cannot slip past.
#![cfg(feature = "full")]

use axeyum_ir::{Op, Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_solver::{
    CheckResult, HornClause, HornModel, HornOutcome, HornSystem, SolverConfig, check_auto,
    solve_horn,
};

/// Substitutes the interpretation of the applied predicate into `P(args)`,
/// returning `I[params ↦ args]`. Deliberately independent of the solver's own
/// substitution.
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

fn subst(arena: &mut TermArena, term: TermId, mapping: &[(SymbolId, TermId)]) -> TermId {
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

/// Independently re-checks a [`HornModel`] against every clause of `system`:
/// `(⋀ body[P↦I]) ∧ constraint ∧ ¬(head[P↦I])` must be `Unsat`.
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

/// Builds the counter system `P(x:Int)`: `x = 0 ⇒ P(x)`,
/// `P(x) ∧ x' = x + 1 ⇒ P(x')`, `P(x) ∧ query ⇒ false`, where `query` is built
/// from the single `Int` state variable by `make_query`.
fn counter_system(
    arena: &mut TermArena,
    name: &str,
    make_query: impl FnOnce(&mut TermArena, TermId) -> TermId,
) -> HornSystem {
    let p = arena.declare_fun(name, &[Sort::Int], Sort::Bool).unwrap();

    // init: x = 0 ⇒ P(x)
    let x = arena.declare(&format!("{name}_x"), Sort::Int).unwrap();
    let xv = arena.var(x);
    let zero = arena.int_const(0);
    let x_eq_0 = arena.eq(xv, zero).unwrap();
    let p_x = arena.apply(p, &[xv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: x_eq_0,
        head: Some(p_x),
    };

    // inductive: P(x) ∧ x' = x + 1 ⇒ P(x')
    let xp = arena.declare(&format!("{name}_xp"), Sort::Int).unwrap();
    let xpv = arena.var(xp);
    let one = arena.int_const(1);
    let x_plus_1 = arena.int_add(xv, one).unwrap();
    let xp_eq = arena.eq(xpv, x_plus_1).unwrap();
    let p_x_body = arena.apply(p, &[xv]).unwrap();
    let p_xp = arena.apply(p, &[xpv]).unwrap();
    let inductive = HornClause {
        body: vec![p_x_body],
        constraint: xp_eq,
        head: Some(p_xp),
    };

    // query: P(x) ∧ <query> ⇒ false
    let constraint = make_query(arena, xv);
    let p_x_q = arena.apply(p, &[xv]).unwrap();
    let query = HornClause {
        body: vec![p_x_q],
        constraint,
        head: None,
    };

    HornSystem {
        predicates: vec![p],
        clauses: vec![fact, inductive, query],
    }
}

/// Safe `LIA` Horn: the `Int` counter with the query `x < 0`. `Inv := x ≥ 0` is
/// inductive over ℤ ⇒ a definite `Sat`, re-checked test-side.
///
/// This is the observation that the `Int` dispatch exists: with `Int` classified
/// `Unsupported` (the pre-wiring behaviour) `solve_horn` returns `Unknown` here.
#[test]
fn safe_lia_horn_is_sat_and_rechecks() {
    let mut arena = TermArena::new();
    let system = counter_system(&mut arena, "InvLia", |arena, xv| {
        let zero = arena.int_const(0);
        arena.int_lt(xv, zero).unwrap()
    });

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    let HornOutcome::Sat(model) = outcome else {
        panic!("expected a definite Sat for the inductive Int system ‘x ≥ 0’, got {outcome:?}");
    };
    recheck_model(&mut arena, &system, &model);
}

/// Unsafe `LIA` Horn: the `Int` counter with the query `x = 3`, reachable from
/// `x = 0` in three `+1` steps ⇒ a definite `Unsat` at depth `≥ 3`.
#[test]
fn unsafe_lia_horn_query_is_reachable() {
    let mut arena = TermArena::new();
    let system = counter_system(&mut arena, "PLia", |arena, xv| {
        let three = arena.int_const(3);
        arena.eq(xv, three).unwrap()
    });

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    match outcome {
        HornOutcome::Unsat { steps } => {
            assert!(steps >= 3, "x=3 needs at least three +1 steps, got {steps}");
        }
        other => panic!("expected a definite Unsat (the query is reachable), got {other:?}"),
    }
}

/// A **mixed** `Int`/`Real` state vocabulary still declines. The `Int` route is a
/// new engine family, not a relaxation of the sort discipline: a vocabulary that
/// is not uniformly one family has no engine and must degrade to `Unknown`,
/// never to a guess.
#[test]
fn mixed_int_real_state_still_declines() {
    let mut arena = TermArena::new();
    let p = arena
        .declare_fun("Mixed", &[Sort::Int, Sort::Real], Sort::Bool)
        .unwrap();

    let i = arena.declare("mixed_i", Sort::Int).unwrap();
    let r = arena.declare("mixed_r", Sort::Real).unwrap();
    let iv = arena.var(i);
    let rv = arena.var(r);
    let izero = arena.int_const(0);
    let rzero = arena.real_ratio(0, 1);
    let i_eq_0 = arena.eq(iv, izero).unwrap();
    let r_eq_0 = arena.eq(rv, rzero).unwrap();
    let init_c = arena.and(i_eq_0, r_eq_0).unwrap();
    let p_app = arena.apply(p, &[iv, rv]).unwrap();
    let fact = HornClause {
        body: vec![],
        constraint: init_c,
        head: Some(p_app),
    };

    let i_lt_0 = arena.int_lt(iv, izero).unwrap();
    let p_q = arena.apply(p, &[iv, rv]).unwrap();
    let query = HornClause {
        body: vec![p_q],
        constraint: i_lt_0,
        head: None,
    };

    let system = HornSystem {
        predicates: vec![p],
        clauses: vec![fact, query],
    };

    let outcome = solve_horn(&mut arena, &system, &SolverConfig::default()).unwrap();
    assert!(
        matches!(outcome, HornOutcome::Unknown { .. }),
        "a mixed Int/Real state vocabulary has no engine family; expected Unknown, got {outcome:?}"
    );
}
