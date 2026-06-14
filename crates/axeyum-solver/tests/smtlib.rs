//! The SMT-LIB text front door (ADR-0018): raw SMT-LIB 2 text in, a checked
//! `sat`/`unsat`/`unknown` out, cross-checked against the script's declared
//! `(set-info :status ...)`. This locks the real-world end-to-end use case —
//! "hand it an SMT-LIB file and get a checked answer."

use std::time::Duration;

use axeyum_solver::{CheckResult, SmtLibOutcome, SolverConfig, solve_smtlib};

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(30))
}

fn run(text: &str) -> SmtLibOutcome {
    solve_smtlib(text, &config()).expect("supported script decides without error")
}

/// A `sat` decision must agree with a declared `:status sat`.
#[test]
fn decides_sat_bitvector_script() {
    let text = "\
(set-info :status sat)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x (_ bv1 8)) (_ bv5 8)))
(check-sat)
";
    let outcome = run(text);
    assert_eq!(outcome.logic.as_deref(), Some("QF_BV"));
    assert_eq!(outcome.expected_status.as_deref(), Some("sat"));
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "decision must match declared status"
    );
}

/// An `unsat` decision must agree with a declared `:status unsat`. (No BV value
/// is unsigned-less-than zero.)
#[test]
fn decides_unsat_bitvector_script() {
    let text = "\
(set-info :status unsat)
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (bvult x (_ bv0 8)))
(check-sat)
";
    let outcome = run(text);
    assert_eq!(outcome.expected_status.as_deref(), Some("unsat"));
    assert_eq!(outcome.result, CheckResult::Unsat);
}

/// A quantified script flows through the same front door: `forall x:BV3. x|x = x`
/// is valid, so its assertion is `sat` (decided by finite-domain expansion).
#[test]
fn decides_quantified_script() {
    let text = "\
(set-info :status sat)
(set-logic BV)
(assert (forall ((x (_ BitVec 3))) (= (bvor x x) x)))
(check-sat)
";
    let outcome = run(text);
    assert_eq!(outcome.expected_status.as_deref(), Some("sat"));
    assert!(matches!(outcome.result, CheckResult::Sat(_)));
}

/// Malformed text is a [`axeyum_solver::SolverError::Parse`], never a panic.
#[test]
fn malformed_text_is_a_parse_error() {
    use axeyum_solver::SolverError;
    let err = solve_smtlib("(assert (bvadd", &config()).expect_err("malformed input must error");
    assert!(matches!(err, SolverError::Parse(_)));
}

/// A symbolic signed bit-vector -> Float32 conversion is now bit-blasted (not
/// just constant-folded): find a 32-bit x whose signed value converts to 2.0f.
/// x = 2 works, so this is sat and the model replays through the conversion
/// circuit (ADR-0026 / int->fp).
#[test]
fn decides_symbolic_sbv_to_fp_conversion() {
    let text = "\
(set-info :status sat)
(set-logic QF_BVFP)
(declare-const x (_ BitVec 32))
(assert (fp.eq ((_ to_fp 8 24) RNE x) (fp #b0 #b10000000 #b00000000000000000000000)))
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "symbolic int->fp conversion must decide sat, got {:?}",
        outcome.result
    );
}
