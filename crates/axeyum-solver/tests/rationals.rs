//! The `rationals` curriculum node — exact-ℚ order facts proved with re-checked
//! Farkas certificates (the ordered-field shadow of Spivak Ch.1, over the
//! rationals). Density and antisymmetry of `<`, stated without division so they
//! stay strictly linear (LRA).
#![cfg(feature = "full")]

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

/// **Density**: `a < b ⇒ a < (a+b)/2 < b`. Stated in division-free form
/// (`2a < a+b` and `a+b < 2b`), which is what density reduces to and which is
/// pure LRA.
#[test]
fn rationals_are_dense() {
    let mut a = TermArena::new();
    let x = real(&mut a, "a");
    let y = real(&mut a, "b");
    let x_lt_y = a.real_lt(x, y).unwrap();
    let two_a = a.real_add(x, x).unwrap();
    let a_plus_b = a.real_add(x, y).unwrap();
    let lower = a.real_lt(two_a, a_plus_b).unwrap(); // 2a < a+b  ⇔ a < midpoint
    let two_b = a.real_add(y, y).unwrap();
    let a_plus_b2 = a.real_add(x, y).unwrap();
    let upper = a.real_lt(a_plus_b2, two_b).unwrap(); // a+b < 2b  ⇔ midpoint < b
    let goal = a.and(lower, upper).unwrap();
    assert_proved(&mut a, &[x_lt_y], goal, "density");
}

/// **Antisymmetry / strict order**: `a < b ⇒ ¬(b < a)`.
#[test]
fn strict_order_is_antisymmetric() {
    let mut a = TermArena::new();
    let x = real(&mut a, "a");
    let y = real(&mut a, "b");
    let x_lt_y = a.real_lt(x, y).unwrap();
    let y_lt_x = a.real_lt(y, x).unwrap();
    let goal = a.not(y_lt_x).unwrap();
    assert_proved(&mut a, &[x_lt_y], goal, "antisymmetry");
}

/// **Transitivity** over ℚ: `a < b ∧ b < c ⇒ a < c`.
#[test]
fn strict_order_is_transitive() {
    let mut a = TermArena::new();
    let x = real(&mut a, "a");
    let y = real(&mut a, "b");
    let z = real(&mut a, "c");
    let xy = a.real_lt(x, y).unwrap();
    let yz = a.real_lt(y, z).unwrap();
    let xz = a.real_lt(x, z).unwrap();
    assert_proved(&mut a, &[xy, yz], xz, "transitivity");
}
