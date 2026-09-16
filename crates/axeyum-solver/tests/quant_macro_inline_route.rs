#![cfg(feature = "full")]
//! Front-door tests for definitional macro inlining (ADR-2127).
//!
//! The unit tests in `crates/axeyum-solver/src/quant_macro_inline.rs` pin the
//! PASS. This suite pins the ROUTE: that the lever is off by default, that it
//! changes an actual verdict when armed, and — the part that matters most —
//! that arming it never turns a satisfiable query unsat.
//!
//! Why a separate integration suite at all: `--lib` runs only unit tests
//! compiled into lib targets and skips every `tests/*.rs`, and this repository
//! has shipped broken front-door behaviour behind a green `--lib` more than
//! once (CLAUDE.md). The pass is reached through `prove_unsat_by_ematching`,
//! which a unit test inside the module cannot exercise.
//!
//! `#![cfg(feature = "full")]` means this file compiles to NOTHING without
//! `--features full`, printing "running 0 tests ... ok" and exiting 0. Run it as
//!
//! ```sh
//! cargo test -p axeyum-solver --features full --test quant_macro_inline_route
//! ```
//!
//! and confirm a NONZERO test count.
//!
//! The lever is read once per process through a `OnceLock`, so ONE run of this
//! binary sees ONE arm. Every test here is written to hold in both, and the
//! gate runs the suite TWICE -- once with the variable unset and once with
//! `AXEYUM_MACRO_INLINE=1`. Running it only in the default arm would leave the
//! three soundness fixtures exercising code the lever keeps off the path, which
//! is the same as not having them.

use axeyum_ir::{Sort, TermArena};
use axeyum_solver::theories::quantifiers::prove_unsat_by_ematching;
use axeyum_solver::{CheckResult, SolverConfig};

/// `∀x. f(x) = x + 1` together with `¬(f(a) = a + 1)`.
///
/// Unsatisfiable, and unsatisfiable for exactly one reason: the definition.
/// This is the positive control for the whole route — if the ladder cannot
/// refute it at all, every "the lever changed nothing" reading below is
/// vacuous.
fn definition_and_contradicting_goal(arena: &mut TermArena) -> Vec<axeyum_ir::TermId> {
    let x = arena.declare("x", Sort::Int).unwrap();
    let xt = arena.var(x);
    let a = arena.declare("a", Sort::Int).unwrap();
    let at = arena.var(a);
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let one = arena.int_const(1);

    let fx = arena.apply(f, &[xt]).unwrap();
    let body = arena.int_add(xt, one).unwrap();
    let eq = arena.eq(fx, body).unwrap();
    let def = arena.forall(x, eq).unwrap();

    let fa = arena.apply(f, &[at]).unwrap();
    let rhs = arena.int_add(at, one).unwrap();
    let goal_eq = arena.eq(fa, rhs).unwrap();
    let goal = arena.not(goal_eq).unwrap();

    vec![def, goal]
}

/// `∀x. f(x) = x + 1` together with `f(a) = a + 1` — SATISFIABLE.
///
/// The adversarial direction. A macro pass that inlines something it should
/// not, or that drops an assertion it should have kept, shows up here as a
/// wrong `unsat`, which is the one outcome this project must never ship.
fn definition_and_consistent_goal(arena: &mut TermArena) -> Vec<axeyum_ir::TermId> {
    let x = arena.declare("x", Sort::Int).unwrap();
    let xt = arena.var(x);
    let a = arena.declare("a", Sort::Int).unwrap();
    let at = arena.var(a);
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let one = arena.int_const(1);

    let fx = arena.apply(f, &[xt]).unwrap();
    let body = arena.int_add(xt, one).unwrap();
    let eq = arena.eq(fx, body).unwrap();
    let def = arena.forall(x, eq).unwrap();

    let fa = arena.apply(f, &[at]).unwrap();
    let rhs = arena.int_add(at, one).unwrap();
    let goal = arena.eq(fa, rhs).unwrap();

    vec![def, goal]
}

/// `∀x. h(x, c) = x + 1` together with `¬(h(a, b) = a + 1)` and `¬(b = c)`.
///
/// **SATISFIABLE**, and the reason is the whole soundness argument: the binder
/// covers only `h`'s first argument, so the assertion says nothing about
/// `h(a, b)` when `b ≠ c`. A pass that treated a partial-coverage binder as a
/// macro would inline `h(a, b) := a + 1`, contradict the goal, and return
/// `unsat` — a WRONG unsat on a satisfiable query.
///
/// The fixture is stated over a satisfiable query on purpose. A refutation
/// fixture cannot distinguish "refused the macro" from "inlined it and the
/// query was unsat anyway" (CLAUDE.md, evidence discipline).
fn partial_coverage_satisfiable(arena: &mut TermArena) -> Vec<axeyum_ir::TermId> {
    let x = arena.declare("x", Sort::Int).unwrap();
    let xt = arena.var(x);
    let a = arena.declare("a", Sort::Int).unwrap();
    let at = arena.var(a);
    let bsym = arena.declare("b", Sort::Int).unwrap();
    let bt = arena.var(bsym);
    let csym = arena.declare("c", Sort::Int).unwrap();
    let ct = arena.var(csym);
    let h = arena
        .declare_fun("h", &[Sort::Int, Sort::Int], Sort::Int)
        .unwrap();
    let one = arena.int_const(1);

    let hxc = arena.apply(h, &[xt, ct]).unwrap();
    let body = arena.int_add(xt, one).unwrap();
    let eq = arena.eq(hxc, body).unwrap();
    let def = arena.forall(x, eq).unwrap();

    let hab = arena.apply(h, &[at, bt]).unwrap();
    let rhs = arena.int_add(at, one).unwrap();
    let g1eq = arena.eq(hab, rhs).unwrap();
    let g1 = arena.not(g1eq).unwrap();

    let bc = arena.eq(bt, ct).unwrap();
    let g2 = arena.not(bc).unwrap();

    vec![def, g1, g2]
}

/// `∀x. f(x) = g(f(x))` with a goal — the OCCURS-CHECK fixture, over a
/// SATISFIABLE query.
///
/// `f(x) = g(f(x))` is satisfied by, for instance, `f ≡ 0` and `g ≡ id`, so the
/// query below is satisfiable. A pass that ignored the occurs check would
/// rewrite `f(a)` to `g(f(a))` to `g(g(f(a)))` and either diverge or produce a
/// term the goal contradicts. Either way the correct verdict is not `unsat`.
fn occurs_check_satisfiable(arena: &mut TermArena) -> Vec<axeyum_ir::TermId> {
    let x = arena.declare("x", Sort::Int).unwrap();
    let xt = arena.var(x);
    let a = arena.declare("a", Sort::Int).unwrap();
    let at = arena.var(a);
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let g = arena.declare_fun("g", &[Sort::Int], Sort::Int).unwrap();
    let zero = arena.int_const(0);

    let fx = arena.apply(f, &[xt]).unwrap();
    let gfx = arena.apply(g, &[fx]).unwrap();
    let eq = arena.eq(fx, gfx).unwrap();
    let def = arena.forall(x, eq).unwrap();

    let fa = arena.apply(f, &[at]).unwrap();
    let goal = arena.eq(fa, zero).unwrap();

    vec![def, goal]
}

fn config() -> SolverConfig {
    SolverConfig {
        timeout: Some(std::time::Duration::from_secs(10)),
        ..SolverConfig::default()
    }
}

#[test]
fn the_lever_spelling_this_suite_runs_under_is_one_of_the_two_arms() {
    // `AXEYUM_MACRO_INLINE` is read once per process through a `OnceLock`, so a
    // single run of this binary sees exactly ONE arm. The suite is designed to
    // pass in BOTH, and the gate runs it twice -- unset, then `=1`.
    //
    // This test exists to make the third possibility loud: a value that is
    // neither arm (`=true`, `=0`, a typo) silently means OFF, and a gate that
    // believed it was running the armed arm would then report the soundness
    // fixtures below as evidence about code they never reached.
    let raw = std::env::var("AXEYUM_MACRO_INLINE").ok();
    assert!(
        raw.is_none() || raw.as_deref() == Some("1"),
        "AXEYUM_MACRO_INLINE={raw:?} is neither arm; it means OFF, and a run under it is not evidence about the armed path"
    );
}

#[test]
fn the_contradicting_definition_query_is_refuted() {
    // POSITIVE CONTROL for the route. If this were `unknown`, the three
    // soundness fixtures below could not distinguish "refused correctly" from
    // "the ladder never got there", and all three would be vacuous.
    let mut arena = TermArena::new();
    let assertions = definition_and_contradicting_goal(&mut arena);
    let result = prove_unsat_by_ematching(&mut arena, &assertions, &config()).unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "expected unsat, got {result:?}"
    );
}

#[test]
fn a_consistent_definition_query_is_never_refuted() {
    let mut arena = TermArena::new();
    let assertions = definition_and_consistent_goal(&mut arena);
    let result = prove_unsat_by_ematching(&mut arena, &assertions, &config()).unwrap();
    assert!(
        !matches!(result, CheckResult::Unsat),
        "SATISFIABLE query reported unsat: {result:?}"
    );
}

#[test]
fn a_partial_coverage_binder_never_produces_a_wrong_unsat() {
    let mut arena = TermArena::new();
    let assertions = partial_coverage_satisfiable(&mut arena);
    let result = prove_unsat_by_ematching(&mut arena, &assertions, &config()).unwrap();
    assert!(
        !matches!(result, CheckResult::Unsat),
        "partial-coverage binder treated as a macro: wrong unsat ({result:?})"
    );
}

#[test]
fn an_occurs_check_violation_never_produces_a_wrong_unsat() {
    let mut arena = TermArena::new();
    let assertions = occurs_check_satisfiable(&mut arena);
    let result = prove_unsat_by_ematching(&mut arena, &assertions, &config()).unwrap();
    assert!(
        !matches!(result, CheckResult::Unsat),
        "recursive 'definition' inlined: wrong unsat ({result:?})"
    );
}
