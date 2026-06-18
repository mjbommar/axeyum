//! Linear algebra over ℚ — solving `Ax = b` and refuting inconsistent systems
//! with re-checked Farkas certificates (VMLS Part II / Shoup Ch. 15, the
//! *decidable* matrix core). These are linear over the rationals, so they go
//! through axeyum's exact-rational engine (LRA). Coefficients are built by
//! repeated addition to stay strictly linear.

use std::time::Duration;

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_solver::{CheckResult, ProofOutcome, SolverConfig, check_with_lra, prove};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(10))
}

fn real(arena: &mut TermArena, name: &str) -> TermId {
    arena.real_var(name).unwrap()
}

fn int(arena: &mut TermArena, n: i128) -> TermId {
    arena.real_const(Rational::integer(n))
}

/// `2x + y = 5 ∧ x + 3y = 10` is consistent (unique solution `x=1, y=3`); the
/// exact-rational engine reports `sat`.
#[test]
fn consistent_2x2_system_is_sat() {
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let two_x = a.real_add(x, x).unwrap();
    let lhs1 = a.real_add(two_x, y).unwrap(); // 2x + y
    let five = int(&mut a, 5);
    let eq1 = a.eq(lhs1, five).unwrap();
    let three_y = {
        let yy = a.real_add(y, y).unwrap();
        a.real_add(yy, y).unwrap()
    };
    let lhs2 = a.real_add(x, three_y).unwrap(); // x + 3y
    let ten = int(&mut a, 10);
    let eq2 = a.eq(lhs2, ten).unwrap();
    let r = check_with_lra(&mut a, &[eq1, eq2]).unwrap();
    assert!(
        matches!(r, CheckResult::Sat(_)),
        "consistent system should be sat, got {r:?}"
    );
}

/// The same system **determines** `x = 1`: proved by refuting
/// `2x+y=5 ∧ x+3y=10 ∧ x≠1` with a re-checked Farkas certificate.
#[test]
fn system_determines_x_with_a_certificate() {
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let two_x = a.real_add(x, x).unwrap();
    let lhs1 = a.real_add(two_x, y).unwrap();
    let five = int(&mut a, 5);
    let eq1 = a.eq(lhs1, five).unwrap();
    let yy = a.real_add(y, y).unwrap();
    let three_y = a.real_add(yy, y).unwrap();
    let lhs2 = a.real_add(x, three_y).unwrap();
    let ten = int(&mut a, 10);
    let eq2 = a.eq(lhs2, ten).unwrap();
    let one = int(&mut a, 1);
    let goal = a.eq(x, one).unwrap();
    match prove(&mut a, &[eq1, eq2], goal, &config()).unwrap() {
        ProofOutcome::Proved(report) => {
            assert!(
                report.evidence.is_certified(),
                "Farkas certificate should be re-checked"
            );
        }
        other => panic!("system should determine x=1, got {other:?}"),
    }
}

/// An over-determined inconsistent system `x+y=1 ∧ x+y=2` is refuted: from
/// `x+y=1` we prove `¬(x+y=2)` with a Farkas certificate.
#[test]
fn inconsistent_system_is_farkas_refuted() {
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let sum = a.real_add(x, y).unwrap();
    let one = int(&mut a, 1);
    let hyp = a.eq(sum, one).unwrap();
    let sum2 = a.real_add(x, y).unwrap();
    let two = int(&mut a, 2);
    let eq2 = a.eq(sum2, two).unwrap();
    let goal = a.not(eq2).unwrap();
    match prove(&mut a, &[hyp], goal, &config()).unwrap() {
        ProofOutcome::Proved(report) => assert!(report.evidence.is_certified()),
        other => panic!("inconsistent system should be Farkas-refuted, got {other:?}"),
    }
}
