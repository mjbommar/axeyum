//! The precondition for closing the induction flywheel: both obligations
//! reconstruct into kernel-checked terms.
//!
//! The arrow this project is built around is
//! *solver → reconstruction → kernel-checked theorem → ledger*. For ℕ-induction
//! the three pieces now exist separately:
//!
//! * the solver discharges base and step
//!   ([`prove_by_nat_induction`](axeyum_solver::prove_by_nat_induction));
//! * the kernel assembles a theorem from a base and a step
//!   (`axeyum-lean-kernel/tests/induction_arrow.rs`, driven from outside the
//!   crate through the public `NatOps::induct`);
//! * and reconstruction turns a refutation into a kernel-checked term.
//!
//! What was never checked is whether the third applies to the *particular*
//! shapes the first produces. If an induction obligation could not be
//! reconstructed, closing the loop would mean building a new reconstruction
//! route; if it can, it is assembly. This file answers that, and keeps
//! answering it — a regression here silently turns the remaining work from
//! plumbing back into invention.
//!
//! Measured 2026-08-17: both reconstruct, including the step, which carries an
//! uninterpreted function and a fresh Skolem-like constant.

#![cfg(feature = "full")]

use axeyum_smtlib::parse_script;
use axeyum_solver::prove_unsat_to_lean;

/// Whether the assertion set reconstructs to a kernel-checked refutation.
fn reconstructs(script: &str) -> bool {
    let mut parsed = parse_script(script).expect("script parses");
    let assertions = parsed.assertions.clone();
    prove_unsat_to_lean(&mut parsed.arena, &assertions).is_ok()
}

/// The BASE obligation of `∀n ≥ 0. f(n) = 2n` under `f(0) = 0`.
#[test]
fn the_base_obligation_reconstructs() {
    assert!(reconstructs(
        "(set-logic UFLIA)\n\
         (declare-fun f (Int) Int)\n\
         (assert (= (f 0) 0))\n\
         (assert (not (= (f 0) (* 2 0))))\n\
         (check-sat)"
    ));
}

/// The STEP obligation, instantiated at a fresh `k`.
///
/// This is the harder of the two and the one that decides the question: it
/// carries an uninterpreted function applied at two different points and a
/// constant standing for an arbitrary non-negative integer.
#[test]
fn the_step_obligation_reconstructs() {
    assert!(reconstructs(
        "(set-logic UFLIA)\n\
         (declare-fun f (Int) Int)\n\
         (declare-fun k () Int)\n\
         (assert (>= k 0))\n\
         (assert (= (f (+ k 1)) (+ (f k) 2)))\n\
         (assert (= (f k) (* 2 k)))\n\
         (assert (not (= (f (+ k 1)) (* 2 (+ k 1)))))\n\
         (check-sat)"
    ));
}

/// The control: a satisfiable set must NOT reconstruct.
///
/// Without it these tests would pass against a reconstruction layer that
/// returned `Ok` unconditionally, and the measurement above would mean nothing.
#[test]
fn a_satisfiable_set_does_not_reconstruct() {
    assert!(
        !reconstructs(
            "(set-logic UFLIA)\n\
             (declare-fun f (Int) Int)\n\
             (assert (= (f 0) 0))\n\
             (assert (not (= (f 0) 1)))\n\
             (check-sat)"
        ),
        "there is no refutation here to reconstruct; returning one would be a wrong proof"
    );
}
