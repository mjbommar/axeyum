//! ADR-1920: uninterpreted functions over datatype sorts.
//!
//! The IR used to reject `declare-fun` whose parameter or result sort was
//! `Sort::Datatype(_)`, which made four whole SMT-LIB divisions (UFDT,
//! UFDTLIRA, AUFDTLIRA, AUFDTNIRA — 27,785 files) unparseable. The gate is
//! lifted; the capability gate now lives in `datatype_native`, which fails
//! closed.
//!
//! What each test here would print if the change were broken:
//!
//! * `gate_*` — a `SortMismatch` instead of a `FuncId`, i.e. the lift reverted.
//! * `terminates_*` — **nothing**: the process aborts with a stack overflow.
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
fn color(a: &mut TermArena) -> (DatatypeId, ConstructorId, ConstructorId) {
    let d = a.declare_datatype("Color");
    let red = a.add_constructor(d, "red", &[]);
    let green = a.add_constructor(d, "green", &[]);
    (d, red, green)
}

/// `Box = mk(v : Int)`.
fn boxed(a: &mut TermArena) -> (DatatypeId, ConstructorId) {
    let d = a.declare_datatype("Box");
    let mk = a.add_constructor(d, "mk", &[("v".to_owned(), Sort::Int)]);
    (d, mk)
}

fn var_of(a: &mut TermArena, name: &str, sort: Sort) -> TermId {
    let s = a.declare(name, sort).expect("declare");
    a.var(s)
}

// ---------------------------------------------------------------- the gate

#[test]
fn gate_admits_a_datatype_parameter() {
    let mut a = TermArena::new();
    let (d, _, _) = color(&mut a);
    a.declare_fun("p", &[Sort::Datatype(d)], Sort::Bool)
        .expect("a datatype parameter is admitted (ADR-1920)");
}

#[test]
fn gate_admits_a_datatype_result() {
    let mut a = TermArena::new();
    let (d, _) = boxed(&mut a);
    a.declare_fun("f", &[Sort::Int], Sort::Datatype(d))
        .expect("a datatype result is admitted (ADR-1920)");
}

#[test]
fn gate_still_rejects_a_sequence_parameter() {
    // What ADR-1920 deliberately did NOT open. No lane has measured sequences
    // end to end, so they keep the declaration-time refusal. If this test ever
    // fails, someone widened the gate without the measurement.
    let mut a = TermArena::new();
    let err = a
        .declare_fun("q", &[Sort::Seq(ArraySortKey::BitVec(8))], Sort::Bool)
        .expect_err("a sequence parameter is still rejected");
    assert!(
        matches!(err, IrError::SortMismatch { .. }),
        "expected SortMismatch, got {err:?}"
    );
}

#[test]
fn gate_still_rejects_a_sequence_result() {
    let mut a = TermArena::new();
    let err = a
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
    let mut a = TermArena::new();
    let (d, _, _) = color(&mut a);
    let p = a
        .declare_fun("p", &[Sort::Datatype(d)], Sort::Bool)
        .expect("declare p");
    let o = var_of(&mut a, "o", Sort::Datatype(d));
    let t = a.apply(p, &[o]).expect("apply");

    let got = solve(&mut a, &[t], &cfg());
    assert!(
        matches!(got, Err(SolverError::Unsupported(_))),
        "expected a clean Unsupported, got {got:?}"
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
    let mut a = TermArena::new();
    let (d, _, _) = color(&mut a);
    let arr = Sort::Array {
        index: ArraySortKey::Int,
        element: ArraySortKey::Datatype(d),
    };
    let x = var_of(&mut a, "a", arr);
    let y = var_of(&mut a, "b", arr);
    let o = var_of(&mut a, "o", Sort::Datatype(d));
    let one = a.int_const(1);
    let st = a.store(y, one, o).expect("store");
    let e1 = a.eq(x, st).expect("eq");
    let e2 = a.eq(x, y).expect("eq");
    let ne = a.not(e2).expect("not");

    let got = solve(&mut a, &[e1, ne], &cfg());
    assert!(
        matches!(got, Err(SolverError::Unsupported(_))),
        "expected a clean Unsupported, got {got:?}"
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
    let mut a = TermArena::new();
    let (d, _, _) = color(&mut a);
    let p = a
        .declare_fun("p", &[Sort::Datatype(d)], Sort::Bool)
        .expect("declare p");
    let x = var_of(&mut a, "x", Sort::Datatype(d));
    let y = var_of(&mut a, "y", Sort::Datatype(d));
    let eq = a.eq(x, y).expect("eq");
    let px = a.apply(p, &[x]).expect("apply");
    let py = a.apply(p, &[y]).expect("apply");
    let npy = a.not(py).expect("not");

    let got = solve(&mut a, &[eq, px, npy], &cfg());
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
    let mut a = TermArena::new();
    let (d, red, green) = color(&mut a);
    let p = a
        .declare_fun("p", &[Sort::Datatype(d)], Sort::Bool)
        .expect("declare p");
    let r = a.construct(red, &[]).expect("red");
    let g = a.construct(green, &[]).expect("green");
    let pr = a.apply(p, &[r]).expect("apply");
    let pg = a.apply(p, &[g]).expect("apply");
    let npg = a.not(pg).expect("not");

    let got = solve(&mut a, &[pr, npg], &cfg());
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
    let mut a = TermArena::new();
    let (d, mk) = boxed(&mut a);
    let f = a
        .declare_fun("f", &[Sort::Int], Sort::Datatype(d))
        .expect("declare f");
    let one = a.int_const(1);
    let fa = a.apply(f, &[one]).expect("apply");
    let sel = a.dt_select(mk, 0, fa).expect("select");
    let five = a.int_const(5);
    let six = a.int_const(6);
    let e5 = a.eq(sel, five).expect("eq");
    let e6 = a.eq(sel, six).expect("eq");

    let got = solve(&mut a, &[e5, e6], &cfg());
    assert!(
        matches!(got, Ok(CheckResult::Unsat)),
        "expected unsat, got {got:?}"
    );
}
