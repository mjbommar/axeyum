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

/// A symbolic FP->int conversion is now bit-blasted (not just constant-folded):
/// find a Float32 x with `fp.to_sbv(RNE, x)` == 5. x = 5.0 works -> sat, replayed
/// through the conversion circuit (ADR-0026 / fp->int).
#[test]
fn decides_symbolic_fp_to_sbv_conversion() {
    let text = "\
(set-info :status sat)
(set-logic QF_BVFP)
(declare-const x Float32)
(assert (= ((_ fp.to_sbv 32) RNE x) (_ bv5 32)))
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "symbolic fp->int must decide sat, got {:?}",
        outcome.result
    );
}

/// FP->int is a function: two occurrences on the same operand denote one value,
/// so their inequality is unsat even when the operand is unconstrained (the
/// shared fresh value for the unspecified out-of-range case must be the SAME).
#[test]
fn fp_to_int_is_functional_even_when_unspecified() {
    let text = "\
(set-info :status unsat)
(set-logic QF_BVFP)
(declare-const x Float32)
(assert (not (= ((_ fp.to_ubv 8) RNE x) ((_ fp.to_ubv 8) RNE x))))
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Unsat),
        "fp.to_ubv(x) must equal itself (functional), got {:?}",
        outcome.result
    );
}

/// Quantifier over a small floating-point format decides by finite-domain
/// expansion (ADR-0016 + ADR-0026): an 8-value `(_ FloatingPoint 3 3)` domain.
/// `forall x. (x <= x or isNaN x)` is valid (leq is reflexive except on NaN,
/// which isNaN catches), so asserting it is sat.
#[test]
fn quantified_small_float_tautology_is_sat() {
    let text = "\
(set-logic FP)
(assert (forall ((x (_ FloatingPoint 3 3))) (or (fp.leq x x) (fp.isNaN x))))
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "valid small-FP forall must be sat, got {:?}",
        outcome.result
    );
}

/// `forall x:(_ FloatingPoint 3 3). fp.eq(x, x)` is false (a NaN value makes
/// `fp.eq` false), so asserting it is unsat — found by exhaustive expansion.
#[test]
fn quantified_small_float_nan_makes_eq_unsat() {
    let text = "\
(set-logic FP)
(assert (forall ((x (_ FloatingPoint 3 3))) (fp.eq x x)))
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Unsat),
        "forall x. fp.eq(x,x) is false (NaN), so unsat, got {:?}",
        outcome.result
    );
}

/// `QF_UFFP`: an uninterpreted function over a floating-point sort. `f(x) == 2.0`
/// and `f(x) == 3.0` (same argument) is unsat by functional consistency; the FP
/// sort flows through Ackermann reduction and bit-blasting (ADR-0026).
#[test]
fn uninterpreted_function_over_float_is_unsat() {
    let text = "\
(set-info :status unsat)
(set-logic QF_UFFP)
(declare-fun f (Float32) Float32)
(declare-const x Float32)
(assert (fp.eq (f x) (fp #b0 #b10000000 #b00000000000000000000000)))
(assert (fp.eq (f x) (fp #b0 #b10000000 #b10000000000000000000000)))
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Unsat),
        "f(x)=2.0 and f(x)=3.0 must be unsat, got {:?}",
        outcome.result
    );
}

/// `QF_UFFP` sat: `f(x) == 2.0` with a distinct argument is consistent (sat); the
/// model is replayed through the original UF+FP query.
#[test]
fn uninterpreted_function_over_float_is_sat() {
    let text = "\
(set-info :status sat)
(set-logic QF_UFFP)
(declare-fun f (Float32) Float32)
(declare-const x Float32)
(declare-const y Float32)
(assert (fp.eq (f x) (fp #b0 #b10000000 #b00000000000000000000000)))
(assert (fp.eq (f y) (fp #b0 #b01111111 #b00000000000000000000000)))
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "consistent UF+FP query must be sat, got {:?}",
        outcome.result
    );
}

/// Incremental script: `push`/`pop` scope the assertion stack and each
/// `check-sat` decides the currently-active assertions (ADR-0009 lifecycle).
/// x=5 (sat); push, x=6 too (unsat); pop, x<10 (sat again) -> [sat, unsat, sat].
#[test]
fn incremental_push_pop_multiple_check_sats() {
    use axeyum_solver::solve_smtlib_incremental;
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x05))
(check-sat)
(push 1)
(assert (= x #x06))
(check-sat)
(pop 1)
(assert (bvult x #x0a))
(check-sat)
";
    let results = solve_smtlib_incremental(text, &config()).expect("incremental script decides");
    assert_eq!(results.len(), 3, "one result per check-sat");
    assert!(matches!(results[0], CheckResult::Sat(_)), "x=5 is sat");
    assert_eq!(results[1], CheckResult::Unsat, "x=5 and x=6 is unsat");
    assert!(
        matches!(results[2], CheckResult::Sat(_)),
        "after pop, x=5 and x<10 is sat again"
    );
}

/// `push`/`pop` are no longer rejected by the front door, and a flat script
/// (no push/pop) still decides as before through `solve_smtlib`.
#[test]
fn incremental_nested_scopes_restore_on_pop() {
    use axeyum_solver::solve_smtlib_incremental;
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(push 2)
(assert (= x #x1))
(assert (= x #x2))
(check-sat)
(pop 2)
(check-sat)
";
    let results = solve_smtlib_incremental(text, &config()).expect("decides");
    assert_eq!(results[0], CheckResult::Unsat, "x=1 and x=2 contradict");
    assert!(
        matches!(results[1], CheckResult::Sat(_)),
        "popping both scopes removes the contradiction"
    );
}

/// `check-sat-assuming` decides the active assertions plus the given assumption
/// literals, without retaining them. x<5: assuming x=3 is sat, assuming x=7 is
/// unsat, and a plain check-sat afterwards is sat (assumptions not kept).
#[test]
fn check_sat_assuming_does_not_retain_assumptions() {
    use axeyum_solver::solve_smtlib_incremental;
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (bvult x #x05))
(check-sat-assuming ((= x #x03)))
(check-sat-assuming ((= x #x07)))
(check-sat)
";
    let results = solve_smtlib_incremental(text, &config()).expect("decides");
    assert_eq!(results.len(), 3);
    assert!(matches!(results[0], CheckResult::Sat(_)), "x<5 & x=3 sat");
    assert_eq!(results[1], CheckResult::Unsat, "x<5 & x=7 unsat");
    assert!(
        matches!(results[2], CheckResult::Sat(_)),
        "assumptions were not retained, so x<5 is still sat"
    );
}

/// Named assertions + unsat core: `x>5 ∧ x<3` is unsat; the minimized core is
/// the two named conflicting assertions, excluding an irrelevant tautology.
#[test]
fn unsat_core_returns_named_minimal_subset() {
    use axeyum_solver::solve_smtlib_unsat_core;
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (! (bvugt x #x05) :named a))
(assert (! (bvult x #x03) :named b))
(assert (! (= x x) :named irrelevant))
(check-sat)
(get-unsat-core)
";
    let core = solve_smtlib_unsat_core(text, &config())
        .expect("decides")
        .expect("query is unsat, so a core exists");
    assert!(core.contains(&"a".to_owned()), "core must include a: {core:?}");
    assert!(core.contains(&"b".to_owned()), "core must include b: {core:?}");
    assert!(
        !core.contains(&"irrelevant".to_owned()),
        "minimized core excludes the tautology: {core:?}"
    );
}

/// A satisfiable script has no unsat core.
#[test]
fn unsat_core_is_none_when_sat() {
    use axeyum_solver::solve_smtlib_unsat_core;
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (! (bvugt x #x05) :named a))
(check-sat)
(get-unsat-core)
";
    assert_eq!(solve_smtlib_unsat_core(text, &config()).expect("decides"), None);
}

/// `(get-value (t …))` reads the sat model: with `x+1 == 5`, the model has x=4,
/// so `x` is 4 and `(bvadd x x)` is 8 (evaluated through the ground evaluator).
#[test]
fn get_value_reads_the_model() {
    use axeyum_ir::Value;
    use axeyum_solver::solve_smtlib_get_value;
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x (_ bv1 8)) (_ bv5 8)))
(check-sat)
(get-value (x (bvadd x x)))
";
    let values = solve_smtlib_get_value(text, &config())
        .expect("decides")
        .expect("sat, so a model exists");
    assert_eq!(values.len(), 2);
    assert_eq!(values[0], Value::Bv { width: 8, value: 4 }, "x = 4");
    assert_eq!(values[1], Value::Bv { width: 8, value: 8 }, "x+x = 8");
}

/// `get-value` has nothing to read when the script is unsat.
#[test]
fn get_value_is_none_when_unsat() {
    use axeyum_solver::solve_smtlib_get_value;
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (bvult x (_ bv0 8)))
(check-sat)
(get-value (x))
";
    assert_eq!(solve_smtlib_get_value(text, &config()).expect("decides"), None);
}

/// Optimization (OMT): maximize/minimize an Int objective under linear bounds.
#[test]
fn optimize_integer_objective() {
    use axeyum_solver::{OptOutcome, optimize_smtlib};
    let text = "\
(set-logic QF_LIA)
(declare-const x Int)
(assert (<= x 10))
(assert (>= x 0))
(maximize x)
(minimize x)
(check-sat)
(get-objectives)
";
    let outcomes = optimize_smtlib(text, &config()).expect("optimizes");
    assert_eq!(outcomes.len(), 2);
    assert_eq!(outcomes[0], OptOutcome::Optimal(10), "max x in [0,10] = 10");
    assert_eq!(outcomes[1], OptOutcome::Optimal(0), "min x in [0,10] = 0");
}

/// OMT over a bit-vector objective (unsigned): maximize x with x <=u 100.
#[test]
fn optimize_bitvector_objective() {
    use axeyum_solver::{OptOutcome, optimize_smtlib};
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (bvule x #x64))
(maximize x)
(check-sat)
(get-objectives)
";
    let outcomes = optimize_smtlib(text, &config()).expect("optimizes");
    assert_eq!(outcomes[0], OptOutcome::Optimal(100), "max unsigned x <= 100 = 100");
}
