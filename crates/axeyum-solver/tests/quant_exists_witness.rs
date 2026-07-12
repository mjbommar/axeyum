//! Bounded `∀∃` decision by Skolem-witness synthesis (sat-side, one-directional).
//!
//! The front door [`solve`] decides a prenex `∀x⃗. ∃z. body` query **Sat** when it
//! can synthesize a witness `z := g(x⃗)` whose universal closure validates, and
//! declines (never `unsat`, never a wrong `sat`) otherwise. These tests pin the
//! decided-`Sat` cases and the soundness negatives (which must NOT come back `Sat`
//! and must NOT come back `Unsat` from this pass).

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{CheckResult, SolverConfig, check_model, solve};

fn config() -> SolverConfig {
    // A tight timeout so any accidental non-termination surfaces as a test hang
    // well within the harness budget rather than a silent slow pass.
    SolverConfig::new().with_timeout(Duration::from_secs(20))
}

fn decide(arena: &mut TermArena, assertions: &[TermId]) -> CheckResult {
    solve(arena, assertions, &config()).expect("query decides without error")
}

fn assert_sat_replays(arena: &mut TermArena, assertion: TermId, message: &str) {
    let CheckResult::Sat(model) = decide(arena, &[assertion]) else {
        panic!("{message}");
    };
    assert!(
        check_model(arena, &[assertion], &model).expect("quantified model check"),
        "returned quantified Sat must replay through its Skolem certificate"
    );
}

// ---------------------------------------------------------------------------
// DECIDES Sat — a validated witness exists.
// ---------------------------------------------------------------------------

#[test]
fn forall_exists_int_strictly_greater_is_sat() {
    // ∀x:Int. ∃z:Int. z > x   — witness z := x + 1, valid (x + 1 > x). Sat.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let z = arena.declare("z", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zv = arena.var(z);
    let gt = arena.int_gt(zv, xv).unwrap();
    let exists = arena.exists(z, gt).unwrap();
    let all = arena.forall(x, exists).unwrap();
    assert_sat_replays(
        &mut arena,
        all,
        "forall x:Int. exists z:Int. z>x must be Sat (witness x+1)",
    );
}

#[test]
fn forall_exists_int_equality_successor_is_sat() {
    // ∀x:Int. ∃z:Int. z = x + 1   — witness z := x + 1, valid. Sat.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let z = arena.declare("z", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zv = arena.var(z);
    let one = arena.int_const(1);
    let xp1 = arena.int_add(xv, one).unwrap();
    let eq = arena.eq(zv, xp1).unwrap();
    let exists = arena.exists(z, eq).unwrap();
    let all = arena.forall(x, exists).unwrap();
    assert_sat_replays(
        &mut arena,
        all,
        "forall x:Int. exists z:Int. z=x+1 must be Sat",
    );
}

#[test]
fn forall_exists_real_strictly_greater_is_sat() {
    // ∀x:Real. ∃z:Real. z > x   — witness z := x + 1, valid. Sat.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Real).unwrap();
    let z = arena.declare("z", Sort::Real).unwrap();
    let xv = arena.var(x);
    let zv = arena.var(z);
    let gt = arena.real_gt(zv, xv).unwrap();
    let exists = arena.exists(z, gt).unwrap();
    let all = arena.forall(x, exists).unwrap();
    assert_sat_replays(
        &mut arena,
        all,
        "forall x:Real. exists z:Real. z>x must be Sat (witness x+1)",
    );
}

#[test]
fn forall_exists_int_two_sided_pinned_is_sat() {
    // ∀x:Int. ∃z:Int. z >= x ∧ z <= x   — witness z := x, valid. Sat.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let z = arena.declare("z", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zv = arena.var(z);
    let ge = arena.int_ge(zv, xv).unwrap();
    let le = arena.int_le(zv, xv).unwrap();
    let body = arena.and(ge, le).unwrap();
    let exists = arena.exists(z, body).unwrap();
    let all = arena.forall(x, exists).unwrap();
    assert_sat_replays(
        &mut arena,
        all,
        "forall x:Int. exists z:Int. z>=x and z<=x must be Sat (witness x)",
    );
}

#[test]
fn forall_exists_int_lower_bound_on_parameter_sum_is_sat() {
    // ∀x:Int.∀y:Int. ∃z:Int. z > x + y   — witness z := (x+y) + 1, valid. Sat.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let y = arena.declare("y", Sort::Int).unwrap();
    let z = arena.declare("z", Sort::Int).unwrap();
    let xv = arena.var(x);
    let yv = arena.var(y);
    let zv = arena.var(z);
    let xy = arena.int_add(xv, yv).unwrap();
    let gt = arena.int_gt(zv, xy).unwrap();
    let exists = arena.exists(z, gt).unwrap();
    let inner = arena.forall(y, exists).unwrap();
    let all = arena.forall(x, inner).unwrap();
    assert_sat_replays(
        &mut arena,
        all,
        "forall x,y:Int. exists z:Int. z>x+y must be Sat",
    );
}

#[test]
fn forall_exists_bv_signed_identity_is_sat() {
    let mut arena = TermArena::new();
    let a = arena.declare("a", Sort::BitVec(32)).unwrap();
    let b = arena.declare("b", Sort::BitVec(32)).unwrap();
    let av = arena.var(a);
    let bv = arena.var(b);
    let body = arena.bv_sle(av, bv).unwrap();
    let exists = arena.exists(b, body).unwrap();
    let theorem = arena.forall(a, exists).unwrap();
    assert_sat_replays(
        &mut arena,
        theorem,
        "forall a:BV32. exists b:BV32. bvsle a b must be Sat by b:=a",
    );
}

#[test]
fn forall_exists_bv_unsigned_identity_is_sat() {
    let mut arena = TermArena::new();
    let a = arena.declare("a", Sort::BitVec(16)).unwrap();
    let b = arena.declare("b", Sort::BitVec(16)).unwrap();
    let av = arena.var(a);
    let bv = arena.var(b);
    let body = arena.bv_ule(av, bv).unwrap();
    let exists = arena.exists(b, body).unwrap();
    let theorem = arena.forall(a, exists).unwrap();
    assert_sat_replays(
        &mut arena,
        theorem,
        "forall a:BV16. exists b:BV16. bvule a b must be Sat by b:=a",
    );
}

// ---------------------------------------------------------------------------
// SOUNDNESS NEGATIVES — must NOT be (mis-)decided. The witness pass declines;
// the result must be neither a wrong `Sat` *from a bogus witness* nor an
// `Unsat`. (Whatever the OTHER passes conclude is fine as long as it is sound;
// these cases are unsatisfiable, so `Unsat` and `Unknown` are both acceptable —
// only a `Sat` would be unsound.)
// ---------------------------------------------------------------------------

#[test]
fn forall_exists_inconsistent_bounds_is_not_sat() {
    // ∀x:Int. ∃z:Int. z > x ∧ z < x   — inconsistent (no z between x and x).
    // The witness candidates (x+1, x-1) fail validation ⇒ decline. Must NOT be Sat.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let z = arena.declare("z", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zv = arena.var(z);
    let gt = arena.int_gt(zv, xv).unwrap();
    let lt = arena.int_lt(zv, xv).unwrap();
    let body = arena.and(gt, lt).unwrap();
    let exists = arena.exists(z, body).unwrap();
    let all = arena.forall(x, exists).unwrap();
    assert!(
        !matches!(decide(&mut arena, &[all]), CheckResult::Sat(_)),
        "∀x:Int.∃z:Int. z>x ∧ z<x must NOT be Sat (it is unsatisfiable)"
    );
}

#[test]
fn forall_exists_no_integer_in_open_unit_gap_is_not_sat() {
    // ∀x:Int. ∃z:Int. z > x ∧ z < x + 1   — no integer strictly between x and x+1.
    // Witness x+1 gives `x+1 < x+1` (false) ⇒ does not validate ⇒ decline. The
    // truth is Unsat; a wrong `Sat` would be unsound, so it must NOT be Sat.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let z = arena.declare("z", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zv = arena.var(z);
    let one = arena.int_const(1);
    let xp1 = arena.int_add(xv, one).unwrap();
    let gt = arena.int_gt(zv, xv).unwrap();
    let lt = arena.int_lt(zv, xp1).unwrap();
    let body = arena.and(gt, lt).unwrap();
    let exists = arena.exists(z, body).unwrap();
    let all = arena.forall(x, exists).unwrap();
    assert!(
        !matches!(decide(&mut arena, &[all]), CheckResult::Sat(_)),
        "∀x:Int.∃z:Int. z>x ∧ z<x+1 must NOT be Sat (no integer in the gap)"
    );
}

#[test]
fn forall_exists_nonunit_coefficient_declines_no_wrong_sat() {
    // ∀x:Int. ∃z:Int. 2*z > x   — `z` has coefficient 2, outside the ±1 fragment;
    // the witness pass declines. The query is actually Sat, but the witness pass
    // must not claim it via a bogus (non-±1) witness — and must never be Unsat.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let z = arena.declare("z", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zv = arena.var(z);
    let two = arena.int_const(2);
    let twoz = arena.int_mul(two, zv).unwrap();
    let gt = arena.int_gt(twoz, xv).unwrap();
    let exists = arena.exists(z, gt).unwrap();
    let all = arena.forall(x, exists).unwrap();
    // Whatever the verdict, it must be sound: never `Unsat` for this satisfiable
    // query. (The witness pass declines; downstream may stay `Unknown`.)
    assert!(
        !matches!(decide(&mut arena, &[all]), CheckResult::Unsat),
        "∀x:Int.∃z:Int. 2z>x must never be decided Unsat (it is satisfiable)"
    );
}

#[test]
fn forall_exists_bv_strict_identity_is_not_sat() {
    let mut arena = TermArena::new();
    let a = arena.declare("a", Sort::BitVec(8)).unwrap();
    let b = arena.declare("b", Sort::BitVec(8)).unwrap();
    let av = arena.var(a);
    let bv = arena.var(b);
    let body = arena.bv_slt(av, bv).unwrap();
    let exists = arena.exists(b, body).unwrap();
    let theorem = arena.forall(a, exists).unwrap();
    assert!(
        !matches!(decide(&mut arena, &[theorem]), CheckResult::Sat(_)),
        "strict signed order has a maximum element and must not receive identity Sat credit"
    );
}

#[test]
fn forall_exists_bv_nonreflexive_identity_declines_soundly() {
    let mut arena = TermArena::new();
    let a = arena.declare("a", Sort::BitVec(8)).unwrap();
    let b = arena.declare("b", Sort::BitVec(8)).unwrap();
    let av = arena.var(a);
    let bv = arena.var(b);
    let not_a = arena.bv_not(av).unwrap();
    let body = arena.bv_sle(not_a, bv).unwrap();
    let exists = arena.exists(b, body).unwrap();
    let theorem = arena.forall(a, exists).unwrap();
    assert!(
        !matches!(decide(&mut arena, &[theorem]), CheckResult::Unsat),
        "the nonreflexive theorem is satisfiable and must never be refuted"
    );
}

// ---------------------------------------------------------------------------
// SHAPE GUARDS — the pass declines anything outside `∀…∃z. QF-body`.
// ---------------------------------------------------------------------------

#[test]
fn bare_existential_is_handled_soundly() {
    // ∃z:Int. z > 0   — no leading ∀; the witness pass declines and the top-level
    // skolemizer decides it Sat. (Pins that the pass does not misfire on ∃-only.)
    let mut arena = TermArena::new();
    let z = arena.declare("z", Sort::Int).unwrap();
    let zv = arena.var(z);
    let zero = arena.int_const(0);
    let gt = arena.int_gt(zv, zero).unwrap();
    let exists = arena.exists(z, gt).unwrap();
    assert!(
        matches!(decide(&mut arena, &[exists]), CheckResult::Sat(_)),
        "∃z:Int. z>0 must be Sat (skolemized, not via the ∀∃ pass)"
    );
}

#[test]
fn forall_only_is_not_misdecided_as_sat() {
    // ∀x:Int. x > 0   — no inner ∃; the witness pass declines. This universal is
    // false, so the result must NOT be Sat.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zero = arena.int_const(0);
    let gt = arena.int_gt(xv, zero).unwrap();
    let all = arena.forall(x, gt).unwrap();
    assert!(
        !matches!(decide(&mut arena, &[all]), CheckResult::Sat(_)),
        "∀x:Int. x>0 must NOT be Sat"
    );
}
