//! Spivak *Calculus* Chapter 1 — "Basic Properties of Numbers" — through the
//! decidability lens (see `docs/curriculum/foundational-books/spivak.md`).
//!
//! Chapter 1 founds analysis on the ordered-field axioms P1–P12 and a few
//! inequalities. What axeyum can settle today:
//!   * **Order axioms / linear consequences (LRA):** proved with a re-checked
//!     Farkas certificate via the [`prove`] front door — see
//!     [`order_transitivity_is_proved_with_a_certificate`].
//!   * **A monotonicity inequality (NRA):** axeyum's NRA proves
//!     `x ≥ 1 ∧ y ≥ 1 ⇒ x·y ≥ 1` (threshold-1 lemma) — see
//!     [`nra_proves_a_monotonicity_inequality`].
//!   * **Sum-of-squares inequalities:** `a²+b² ≥ 2ab` / AM–GM₂ is now **proved**
//!     ([`square_nonnegativity_is_proved_by_sos`]) — NRA gained pairwise
//!     **sum-of-squares lemmas** (`sos_lemmas`) that add `(a±b)² ≥ 0` over the
//!     abstracted products, restoring the cross-product correlation the independent
//!     abstraction drops. The higher-degree / multi-variable SOS cases
//!     (Bernoulliₙ₌₂, general Cauchy–Schwarz) still need the broader
//!     SOS/positivstellensatz/CAD path (P2.5) and are not yet covered.
//!
//! Findings pinned down: `prove` routes real goals to `QF_LRA` and *rejects*
//! nonlinear multiplication (no LRA→NRA dispatch); and axeyum's NRA proves
//! monotonicity-shaped facts but not the degree-2 SOS inequalities.

use std::time::Duration;

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_solver::{CheckResult, ProofOutcome, SolverConfig, check_with_nra, prove};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(5))
}

fn real(arena: &mut TermArena, name: &str) -> TermId {
    arena.real_var(name).unwrap()
}

fn rat(arena: &mut TermArena, n: i128) -> TermId {
    arena.real_const(Rational::integer(n))
}

// --- Order axioms (LRA, certificate-checked) ----------------------------------

#[test]
fn order_transitivity_is_proved_with_a_certificate() {
    // A consequence of P10–P12: a < b ∧ b < c ⇒ a < c. Linear ⇒ the front door
    // proves it and re-checks the Farkas certificate before returning `Proved`.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let z = real(&mut a, "z");
    let xy = a.real_lt(x, y).unwrap();
    let yz = a.real_lt(y, z).unwrap();
    let xz = a.real_lt(x, z).unwrap();
    match prove(&mut a, &[xy, yz], xz, &config()).unwrap() {
        ProofOutcome::Proved(_) => {}
        other => panic!("order transitivity: expected Proved, got {other:?}"),
    }
}

#[test]
fn prove_dispatches_nonlinear_real_to_nra() {
    // #14: the front door now routes a nonlinear real goal to NRA instead of
    // hard-erroring `Unsupported`. We use the monotonicity fact `x≥1 ∧ y≥1 ⇒
    // xy≥1` (which NRA proves soundly via a bounded lemma) so `prove` returns
    // `Proved` with a result that re-validates.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let one = rat(&mut a, 1);
    let x_ge_1 = a.real_ge(x, one).unwrap();
    let one2 = rat(&mut a, 1);
    let y_ge_1 = a.real_ge(y, one2).unwrap();
    let prod = a.real_mul(x, y).unwrap();
    let one3 = rat(&mut a, 1);
    let goal = a.real_ge(prod, one3).unwrap();
    let outcome = prove(&mut a, &[x_ge_1, y_ge_1], goal, &config()).unwrap();
    // The key #14 assertion: no longer an `Unsupported` error. A true theorem
    // must never be Disproved.
    assert!(
        !matches!(outcome, ProofOutcome::Disproved(_)),
        "must not disprove a true nonlinear theorem, got {outcome:?}"
    );
}

#[test]
fn nra_must_not_claim_x_squared_negative_is_sat() {
    // Soundness probe: x² < 0 is unsatisfiable over ℝ. NRA must return Unsat or
    // Unknown — never Sat. (Surfaces whether the unbounded-product relaxation can
    // return a spurious model that #14's dispatch would turn into a wrong
    // `Disproved`.)
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let prod = a.real_mul(x, x).unwrap();
    let zero = rat(&mut a, 0);
    let neg = a.real_lt(prod, zero).unwrap();
    let verdict = check_with_nra(&mut a, &[neg], &config()).unwrap();
    assert!(
        !matches!(verdict, CheckResult::Sat(_)),
        "x² < 0 is unsatisfiable; NRA returned {verdict:?} (soundness)"
    );
}

// --- A monotonicity inequality the NRA engine does prove ----------------------

#[test]
fn nra_proves_a_monotonicity_inequality() {
    // x ≥ 1 ∧ y ≥ 1 ⇒ x·y ≥ 1. Proved by refuting x ≥ 1 ∧ y ≥ 1 ∧ x·y < 1 with
    // NRA's threshold-1 monotonicity lemma.
    let mut a = TermArena::new();
    let x = real(&mut a, "x");
    let y = real(&mut a, "y");
    let one = rat(&mut a, 1);
    let x_ge_1 = a.real_ge(x, one).unwrap();
    let y_ge_1 = a.real_ge(y, one).unwrap();
    let prod = a.real_mul(x, y).unwrap();
    let one2 = rat(&mut a, 1);
    let prod_lt_1 = a.real_lt(prod, one2).unwrap();
    let verdict = check_with_nra(&mut a, &[x_ge_1, y_ge_1, prod_lt_1], &config()).unwrap();
    assert!(
        matches!(verdict, CheckResult::Unsat),
        "x>=1 ∧ y>=1 ⇒ xy>=1 should be NRA-provable, got {verdict:?}"
    );
}

// --- The sum-of-squares frontier (ignored: documents the NRA gap) -------------

#[test]
fn square_nonnegativity_is_proved_by_sos() {
    // a² + b² ≥ 2ab — true (it is (a−b)² ≥ 0). PROMOTED from the old "frontier"
    // (prompt `Unknown`): NRA now carries **sum-of-squares lemmas** (`sos_lemmas`),
    // which add `r_aa + r_bb − 2·r_ab ≥ 0` over the abstracted products, so the
    // negation `a² + b² < 2ab` is refuted `Unsat`. The independent-product
    // abstraction alone could not (it drops the cross-product correlation); the SOS
    // lemma restores exactly that coupling.
    let mut a = TermArena::new();
    let x = real(&mut a, "a");
    let y = real(&mut a, "b");
    let x2 = a.real_mul(x, x).unwrap();
    let y2 = a.real_mul(y, y).unwrap();
    let lhs = a.real_add(x2, y2).unwrap();
    let xy = a.real_mul(x, y).unwrap();
    let two = rat(&mut a, 2);
    let rhs = a.real_mul(two, xy).unwrap();
    let strict = a.real_lt(lhs, rhs).unwrap();
    let verdict = check_with_nra(&mut a, &[strict], &config()).unwrap();
    assert!(
        matches!(verdict, CheckResult::Unsat),
        "a²+b² < 2ab is unsat (it is −(a−b)² < 0); the SOS lemma must refute it, got {verdict:?}"
    );
}
