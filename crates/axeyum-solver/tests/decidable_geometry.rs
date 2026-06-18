//! The `decidable-geometry` curriculum node — coordinate geometry over ℝ.
//! Euclidean geometry is a real-closed field (Tarski: decidable), but its
//! *polynomial* facts (Pythagoras, circles, `det`-based collinearity) need the
//! SOS/CAD path that is the open NRA frontier (#16). Its **linear** facts
//! (midpoints, betweenness) are pure LRA and provable today with re-checked
//! Farkas certificates — that linear slice is what this exercises.

use std::time::Duration;

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(10))
}

fn real(arena: &mut TermArena, name: &str) -> TermId {
    arena.real_var(name).unwrap()
}

fn assert_proved(arena: &mut TermArena, hyps: &[TermId], goal: TermId, label: &str) {
    match prove(arena, hyps, goal, &config()).unwrap() {
        ProofOutcome::Proved(report) => {
            assert!(
                report.evidence.is_certified(),
                "{label}: certificate not re-checked"
            );
        }
        other => panic!("{label}: expected Proved, got {other:?}"),
    }
}

/// The **midpoint is equidistant** (1-D): if `m` is the midpoint of `a` and `b`
/// (`2m = a + b`) then `m − a = b − m`. Linear ⇒ LRA + Farkas.
#[test]
fn midpoint_is_equidistant() {
    let mut a = TermArena::new();
    let pa = real(&mut a, "a");
    let pb = real(&mut a, "b");
    let m = real(&mut a, "m");
    let two_m = a.real_add(m, m).unwrap();
    let a_plus_b = a.real_add(pa, pb).unwrap();
    let is_midpoint = a.eq(two_m, a_plus_b).unwrap();
    let m_minus_a = a.real_sub(m, pa).unwrap();
    let b_minus_m = a.real_sub(pb, m).unwrap();
    let goal = a.eq(m_minus_a, b_minus_m).unwrap();
    assert_proved(&mut a, &[is_midpoint], goal, "midpoint equidistant");
}

/// **Betweenness of the midpoint**: if `a < b` and `2m = a + b`, then
/// `a < m ∧ m < b` — the midpoint lies strictly between the endpoints. Linear.
#[test]
fn midpoint_lies_between_endpoints() {
    let mut a = TermArena::new();
    let pa = real(&mut a, "a");
    let pb = real(&mut a, "b");
    let m = real(&mut a, "m");
    let a_lt_b = a.real_lt(pa, pb).unwrap();
    let two_m = a.real_add(m, m).unwrap();
    let a_plus_b = a.real_add(pa, pb).unwrap();
    let is_midpoint = a.eq(two_m, a_plus_b).unwrap();
    let a_lt_m = a.real_lt(pa, m).unwrap();
    let m_lt_b = a.real_lt(m, pb).unwrap();
    let goal = a.and(a_lt_m, m_lt_b).unwrap();
    assert_proved(&mut a, &[a_lt_b, is_midpoint], goal, "midpoint betweenness");
}
