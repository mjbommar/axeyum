//! ADR-1920: uninterpreted functions over datatype sorts.
//!
//! The IR used to reject `declare-fun` whose parameter or result sort was
//! `Sort::Datatype(_)`, which made four whole SMT-LIB divisions (UFDT,
//! UFDTLIRA, AUFDTLIRA, UFDTNIRA — 27,785 files) unparseable. The gate is
//! lifted; the capability gate now lives in `datatype_native`, which fails
//! closed.
//!
//! What each test here would print if the change were broken:
//!
//! * `gate_*` — a `SortMismatch` instead of a `FuncId`, i.e. the lift reverted.
//! * `terminates_*` — **nothing**: the process aborts with a stack overflow.
//!   (Since ADR-1935 the UF-over-a-datatype-argument one also asserts the
//!   verdict and the model, because the query now decides rather than being
//!   refused; the termination property is unchanged.)
//!   These are the regression guards for the two measured non-termination
//!   cycles. They are written so a revert kills the whole test binary loudly
//!   rather than producing a wrong answer quietly.
//! * `sound_*` — a decided verdict that contradicts the mathematics. These are
//!   the ones that matter: the fragment is allowed to say `Unsupported`, and is
//!   never allowed to say the wrong thing.

use std::time::Duration;

use axeyum_ir::{ArraySortKey, ConstructorId, DatatypeId, IrError, Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, SolverError, solve};

fn cfg() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(5))
}

/// `Color = red | green` — a finite enum, no fields.
fn color(arena: &mut TermArena) -> (DatatypeId, ConstructorId, ConstructorId) {
    let dt = arena.declare_datatype("Color");
    let red = arena.add_constructor(dt, "red", &[]);
    let green = arena.add_constructor(dt, "green", &[]);
    (dt, red, green)
}

/// `Box = mk(v : Int)`.
fn boxed(arena: &mut TermArena) -> (DatatypeId, ConstructorId) {
    let dt = arena.declare_datatype("Box");
    let mk = arena.add_constructor(dt, "mk", &[("v".to_owned(), Sort::Int)]);
    (dt, mk)
}

fn var_of(arena: &mut TermArena, name: &str, sort: Sort) -> TermId {
    let sym = arena.declare(name, sort).expect("declare");
    arena.var(sym)
}

// ---------------------------------------------------------------- the gate

#[test]
fn gate_admits_a_datatype_parameter() {
    let mut arena = TermArena::new();
    let (dt, _, _) = color(&mut arena);
    arena
        .declare_fun("p", &[Sort::Datatype(dt)], Sort::Bool)
        .expect("a datatype parameter is admitted (ADR-1920)");
}

#[test]
fn gate_admits_a_datatype_result() {
    let mut arena = TermArena::new();
    let (dt, _) = boxed(&mut arena);
    arena
        .declare_fun("f", &[Sort::Int], Sort::Datatype(dt))
        .expect("a datatype result is admitted (ADR-1920)");
}

#[test]
fn gate_still_rejects_a_sequence_parameter() {
    // What ADR-1920 deliberately did NOT open. No lane has measured sequences
    // end to end, so they keep the declaration-time refusal. If this test ever
    // fails, someone widened the gate without the measurement.
    let mut arena = TermArena::new();
    let err = arena
        .declare_fun("q", &[Sort::Seq(ArraySortKey::BitVec(8))], Sort::Bool)
        .expect_err("a sequence parameter is still rejected");
    assert!(
        matches!(err, IrError::SortMismatch { .. }),
        "expected SortMismatch, got {err:?}"
    );
}

#[test]
fn gate_still_rejects_a_sequence_result() {
    let mut arena = TermArena::new();
    let err = arena
        .declare_fun("q", &[Sort::Int], Sort::Seq(ArraySortKey::BitVec(8)))
        .expect_err("a sequence result is still rejected");
    assert!(
        matches!(err, IrError::SortMismatch { .. }),
        "expected SortMismatch, got {err:?}"
    );
}

// ------------------------------------------------------- non-termination

#[test]
fn terminates_on_a_uf_applied_to_a_datatype_variable() {
    // MEASURED 2026-09-11: with the gate lifted and no guard, this exact query
    // — the simplest one the four divisions can produce — aborted the process
    // with `fatal runtime error: stack overflow`. `check_auto_dispatch` diverts
    // on the datatype SORT, `datatype_native` has no rewrite for `p(o)` so `o`
    // survives into the residual, and the residual routes straight back. The
    // dispatcher also recomputes its deadline on every entry, so the timeout
    // cannot break the cycle.
    let mut arena = TermArena::new();
    let (dt, _, _) = color(&mut arena);
    let pred = arena
        .declare_fun("p", &[Sort::Datatype(dt)], Sort::Bool)
        .expect("declare p");
    let obj = var_of(&mut arena, "o", Sort::Datatype(dt));
    let app = arena.apply(pred, &[obj]).expect("apply");

    // ADR-1935 CHANGED THIS ASSERTION, and the reason is the whole point of the
    // test. It used to demand `Unsupported`, because refusing was the only thing
    // that broke the cycle. The Ackermann pre-pass now ELIMINATES the
    // application instead, so the query reduces to a Boolean witness variable
    // and decides. The termination property this test exists for is unchanged
    // and is still what a revert would violate -- the failure mode is a stack
    // overflow that kills the whole test binary before any assertion runs.
    //
    // The verdict is asserted rather than merely bounded, and so is the model,
    // because a route that eliminated the application without recording `p`'s
    // interpretation would return a `sat` that cannot be checked by evaluating
    // the original term -- which the empty-scan path did on the first cut.
    let got = solve(&mut arena, &[app], &cfg());
    let Ok(CheckResult::Sat(model)) = got else {
        panic!("`(assert (p o))` is satisfiable and must decide, got {got:?}");
    };
    assert_eq!(
        model.functions().count(),
        1,
        "the sat model must carry p's interpretation: {model:?}"
    );
    assert!(
        !model
            .iter()
            .any(|(s, _)| arena.symbol(s).0.starts_with("!dt_")),
        "the expansion's internal symbols must not leak into the model: {model:?}"
    );
}

#[test]
fn terminates_on_an_array_of_datatypes() {
    // The SAME cycle with NO uninterpreted function anywhere, so it was already
    // live before ADR-1920 lifted the gate: an array whose ELEMENT sort is a
    // datatype parses today and `(= a (store b 1 o)) /\ (not (= a b))` aborted
    // the pre-change binary with a stack overflow. This is what makes the
    // termination guard in `datatype_native` a live check and not a fence
    // around a case the `Op::Apply` arm already catches.
    let mut arena = TermArena::new();
    let (dt, _, _) = color(&mut arena);
    let arr = Sort::Array {
        index: ArraySortKey::Int,
        element: ArraySortKey::Datatype(dt),
    };
    let left = var_of(&mut arena, "a", arr);
    let right = var_of(&mut arena, "b", arr);
    let obj = var_of(&mut arena, "o", Sort::Datatype(dt));
    let one = arena.int_const(1);
    let stored = arena.store(right, one, obj).expect("store");
    let same_store = arena.eq(left, stored).expect("eq");
    let same_array = arena.eq(left, right).expect("eq");
    let differ = arena.not(same_array).expect("not");

    let got = solve(&mut arena, &[same_store, differ], &cfg());
    assert!(
        matches!(got, Err(SolverError::Unsupported(_))),
        "expected a clean Unsupported, got {got:?}"
    );
}

#[test]
fn terminates_on_an_array_of_datatypes_with_no_datatype_sorted_term() {
    // A THIRD instance of the same cycle, and the one that survived the first
    // two guards. `(not (= a b))` over two `(Array Int Color)` constants has
    // **no term of sort `Sort::Datatype(_)` anywhere** — the arrays have sort
    // `Array`. But `Features::note_sort` recurses into an array's component
    // sorts, so the dispatcher still diverts on `has_datatype`, while both the
    // route's "is there datatype content" scan and the first version of the
    // termination guard tested only `Sort::Datatype(_)` on the term itself and
    // said no. Divert-yes plus content-no is exactly the cycle.
    //
    // Measured 2026-09-12 on a real 22 KB AUFDTLIRA benchmark
    // (`spark2014bench/P518-021__frame_for_max__…`): it still overflowed a
    // **1 GiB** stack, so an unbounded cycle rather than a deep term. The fix
    // is that the guards and the divert condition now share ONE predicate,
    // `sort_mentions_datatype`.
    //
    // This test is distinct from `terminates_on_an_array_of_datatypes`: that
    // one carries a datatype-sorted `o` inside a `store`, which the narrower
    // predicate already caught. Revert the widening and only THIS one dies.
    let mut arena = TermArena::new();
    let (dt, _, _) = color(&mut arena);
    let arr = Sort::Array {
        index: ArraySortKey::Int,
        element: ArraySortKey::Datatype(dt),
    };
    let left = var_of(&mut arena, "a", arr);
    let right = var_of(&mut arena, "b", arr);
    assert!(
        !matches!(arena.sort_of(left), Sort::Datatype(_))
            && !matches!(arena.sort_of(right), Sort::Datatype(_)),
        "the point of this fixture is that NO term has sort Datatype"
    );
    let same = arena.eq(left, right).expect("eq");
    let differ = arena.not(same).expect("not");

    let got = solve(&mut arena, &[differ], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "WRONG UNSAT: two unconstrained arrays can differ: {got:?}"
    );
}

// ------------------------------------------------------------- soundness
//
// These are the tests that would catch the failure the ADR is not allowed to
// have: a WRONG verdict on a query the lifted gate now lets through. Each one
// asserts the absence of the wrong answer, not the presence of the right one,
// because the fragment is entitled to refuse.

#[test]
fn sound_congruence_over_a_datatype_argument_is_never_sat() {
    // `x = y /\ p(x) /\ not p(y)` is UNSAT by congruence. A `sat` would mean we
    // built a model where a function disagrees with itself.
    let mut arena = TermArena::new();
    let (dt, _, _) = color(&mut arena);
    let pred = arena
        .declare_fun("p", &[Sort::Datatype(dt)], Sort::Bool)
        .expect("declare p");
    let lhs = var_of(&mut arena, "x", Sort::Datatype(dt));
    let rhs = var_of(&mut arena, "y", Sort::Datatype(dt));
    let same = arena.eq(lhs, rhs).expect("eq");
    let p_lhs = arena.apply(pred, &[lhs]).expect("apply");
    let p_rhs = arena.apply(pred, &[rhs]).expect("apply");
    let not_p_rhs = arena.not(p_rhs).expect("not");

    let got = solve(&mut arena, &[same, p_lhs, not_p_rhs], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Sat(_))),
        "WRONG SAT on a congruence-unsat query: {got:?}"
    );
}

#[test]
fn sound_distinct_constructors_are_never_merged() {
    // `p(red) /\ not p(green)` is SAT: red and green are distinct, so there is
    // no congruence conflict. An `unsat` would mean two distinct constructors
    // were merged — the classic datatype soundness bug.
    let mut arena = TermArena::new();
    let (dt, red, green) = color(&mut arena);
    let pred = arena
        .declare_fun("p", &[Sort::Datatype(dt)], Sort::Bool)
        .expect("declare p");
    let red_t = arena.construct(red, &[]).expect("red");
    let green_t = arena.construct(green, &[]).expect("green");
    let holds_of_red = arena.apply(pred, &[red_t]).expect("apply");
    let holds_of_green = arena.apply(pred, &[green_t]).expect("apply");
    let fails_of_green = arena.not(holds_of_green).expect("not");

    let got = solve(&mut arena, &[holds_of_red, fails_of_green], &cfg());
    assert!(
        !matches!(got, Ok(CheckResult::Unsat)),
        "WRONG UNSAT: two distinct constructors were merged: {got:?}"
    );
}

#[test]
fn sound_congruence_through_a_datatype_result_is_unsat() {
    // `f : Int -> Box`, `select_v(f(1)) = 5 /\ select_v(f(1)) = 6`. UNSAT by
    // congruence on `f` plus functionality of the selector. This one the
    // fragment actually DECIDES, so it is the positive control for the
    // result-sort half of the lift: without it every assertion in this file
    // would be satisfied by a route that refuses everything.
    let mut arena = TermArena::new();
    let (dt, mk) = boxed(&mut arena);
    let func = arena
        .declare_fun("f", &[Sort::Int], Sort::Datatype(dt))
        .expect("declare f");
    let one = arena.int_const(1);
    let applied = arena.apply(func, &[one]).expect("apply");
    let field = arena.dt_select(mk, 0, applied).expect("select");
    let five = arena.int_const(5);
    let six = arena.int_const(6);
    let is_five = arena.eq(field, five).expect("eq");
    let is_six = arena.eq(field, six).expect("eq");

    let got = solve(&mut arena, &[is_five, is_six], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "expected unsat, got {got:?}"
    );
}
