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

/// cvc5's `:arrays-exp` `eqrange` extension lowers to finite pointwise array
/// equalities when the bounds are constant. This is the shape of the AUFLIA
/// `eqrange3` regression row.
#[test]
fn decides_cvc5_eqrange_extension_script() {
    let text = "\
(set-info :status sat)
(set-logic QF_AUFLIA)
(set-option :arrays-exp true)
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun e1 () Int)
(declare-fun e2 () Int)
(assert (distinct e1 e2))
(assert (= a1 (store (store (store (store a1 0 e1) 1 e1) 2 e1) 3 e1)))
(assert (= a2 (store (store (store (store a2 1 e1) 0 e1) 2 e2) 3 e1)))
(assert (eqrange a1 a2 (- 1) 1))
(assert (eqrange a1 a2 3 3))
(check-sat)
";
    let outcome = run(text);
    assert_eq!(outcome.logic.as_deref(), Some("QF_AUFLIA"));
    assert_eq!(outcome.expected_status.as_deref(), Some("sat"));
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "eqrange extension row must decide sat, got {:?}",
        outcome.result
    );
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

/// A symbolic **Float64 `fp.fma`** is now bit-blasted through the wide
/// bit-vector path (the 164-bit intermediate exceeds `u128`): find a Float64 `x`
/// with `fma(x, 3.0, 1.0) == 7.0`. `x = 2.0` works, so this is sat and the model
/// replays through the 164-bit fma circuit. This is the symbolic-wide-FP gap that
/// the `sconst` sign-extension fix closed (the circuit is validated against
/// native `f64::mul_add`).
#[test]
fn decides_symbolic_float64_fma() {
    let text = "\
(set-info :status sat)
(set-logic QF_FP)
(declare-const x Float64)
(assert (fp.eq
          (fp.fma RNE
            x
            ((_ to_fp 11 53) #x4008000000000000)
            ((_ to_fp 11 53) #x3FF0000000000000))
          ((_ to_fp 11 53) #x401C000000000000)))
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "symbolic Float64 fp.fma must decide sat (x = 2.0), got {:?}",
        outcome.result
    );
}

/// A symbolic Float64 `fp.fma` with an unsatisfiable target is `unsat`: no `x`
/// gives `fma(x, +0, +0) == 7.0` (the product is `±0` or NaN, never 7), and the
/// answer is sound through the wide circuit.
#[test]
fn decides_symbolic_float64_fma_unsat() {
    let text = "\
(set-info :status unsat)
(set-logic QF_FP)
(declare-const x Float64)
(assert (fp.eq
          (fp.fma RNE
            x
            ((_ to_fp 11 53) #x0000000000000000)
            ((_ to_fp 11 53) #x0000000000000000))
          ((_ to_fp 11 53) #x401C000000000000)))
(check-sat)
";
    let outcome = run(text);
    assert_eq!(
        outcome.result,
        CheckResult::Unsat,
        "fma(x, 0, 0) can never equal 7.0"
    );
}

/// A symbolic **Float128 `fp.fma`** is bit-blasted through the wide path (the
/// 344-bit intermediate far exceeds `u128`): find a Float128 `x` with
/// `fma(x, 2.0, 1.0) == 7.0`. `x = 3.0` works, so this is sat and the model
/// replays through the 344-bit fma circuit (validated against `rustc_apfloat`'s
/// quad, ADR-0028). Constants are `to_fp` bit-reinterprets of their IEEE quad
/// hex: 2.0 = `0x4000<<112`, 1.0 = `0x3FFF<<112`, 7.0 = `0x4001<<112 | 0xC<<108`.
#[test]
fn decides_symbolic_float128_fma() {
    let text = "\
(set-info :status sat)
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 15 113))
(assert (fp.eq
          (fp.fma RNE
            x
            ((_ to_fp 15 113) #x40000000000000000000000000000000)
            ((_ to_fp 15 113) #x3FFF0000000000000000000000000000))
          ((_ to_fp 15 113) #x4001C000000000000000000000000000)))
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "symbolic Float128 fp.fma must decide sat (x = 3.0), got {:?}",
        outcome.result
    );
}

/// A **Float128 `fp.sqrt`** is bit-blasted through the wide path (234 bits) and
/// decided end-to-end: `sqrt(4.0) == 2.0` holds, so the assertion is sat. The
/// 234-bit isqrt makes a deep CNF, so the operand is the constant 4.0 (the
/// search for a *free* root is correct but slow); the wide circuit's correctness
/// over all inputs is covered exhaustively at the IR level by the exact
/// correct-rounding oracle (`symbolic_f128_sqrt_matches_oracle`, ADR-0028).
/// 4.0 = `0x4001<<112`, 2.0 = `0x4000<<112`.
#[test]
fn decides_float128_sqrt() {
    let text = "\
(set-info :status sat)
(set-logic QF_FP)
(assert (fp.eq
          (fp.sqrt RNE ((_ to_fp 15 113) #x40010000000000000000000000000000))
          ((_ to_fp 15 113) #x40000000000000000000000000000000)))
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "Float128 sqrt(4.0) == 2.0 must decide sat, got {:?}",
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

#[test]
fn flat_front_door_honors_single_push_pop_scope() {
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(assert (= x #x1))
(push 1)
(assert (= x #x2))
(pop 1)
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "single-result solve_smtlib must use the scoped stack at check-sat, not all flat assertions"
    );
}

#[test]
fn flat_front_door_honors_single_reset_assertions() {
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x05))
(reset-assertions)
(assert (= x #x07))
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "single-result solve_smtlib must clear stale assertions at reset-assertions"
    );
}

#[test]
fn flat_front_door_rejects_multiple_check_sats() {
    use axeyum_solver::SolverError;
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x05))
(check-sat)
(assert (= x #x06))
(check-sat)
";
    let err = solve_smtlib(text, &config()).expect_err("multi-query scripts use incremental API");
    let SolverError::Unsupported(message) = err else {
        panic!("expected Unsupported, got {err:?}");
    };
    assert!(message.contains("solve_smtlib_incremental"));
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
    assert!(
        core.contains(&"a".to_owned()),
        "core must include a: {core:?}"
    );
    assert!(
        core.contains(&"b".to_owned()),
        "core must include b: {core:?}"
    );
    assert!(
        !core.contains(&"irrelevant".to_owned()),
        "minimized core excludes the tautology: {core:?}"
    );
}

#[test]
fn unsat_core_uses_scoped_active_assertion_names() {
    use axeyum_solver::solve_smtlib_unsat_core;
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(push 1)
(assert (! (= x #x01) :named stale))
(pop 1)
(assert (! (= x #x02) :named active_eq))
(assert (! (not (= x #x02)) :named active_neq))
(check-sat)
(get-unsat-core)
";
    let core = solve_smtlib_unsat_core(text, &config())
        .expect("decides")
        .expect("active assertions are contradictory");
    assert!(
        core.contains(&"active_eq".to_owned()),
        "core must use active scoped names: {core:?}"
    );
    assert!(
        core.contains(&"active_neq".to_owned()),
        "core must use active scoped names: {core:?}"
    );
    assert!(
        !core.contains(&"stale".to_owned()),
        "popped assertion name must not leak into the core: {core:?}"
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
    assert_eq!(
        solve_smtlib_unsat_core(text, &config()).expect("decides"),
        None
    );
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
    assert_eq!(
        solve_smtlib_get_value(text, &config()).expect("decides"),
        None
    );
}

#[test]
fn get_assignment_reads_named_active_assertions() {
    use axeyum_solver::solve_smtlib_get_assignment;
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (! (= x #x05) :named fixed))
(assert (! (bvult x #x0a) :named small))
(check-sat)
(get-assignment)
";
    let assignment = solve_smtlib_get_assignment(text, &config())
        .expect("decides")
        .expect("sat query has named assertions");
    assert_eq!(
        assignment,
        vec![("fixed".to_owned(), true), ("small".to_owned(), true)]
    );
}

#[test]
fn get_assignment_uses_scoped_active_names() {
    use axeyum_solver::solve_smtlib_get_assignment;
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(push 1)
(assert (! (= x #x01) :named stale))
(pop 1)
(assert (! (= x #x02) :named active))
(check-sat)
(get-assignment)
";
    let assignment = solve_smtlib_get_assignment(text, &config())
        .expect("decides")
        .expect("sat query has one active named assertion");
    assert_eq!(assignment, vec![("active".to_owned(), true)]);
}

#[test]
fn get_assignment_is_none_without_sat_model() {
    use axeyum_solver::solve_smtlib_get_assignment;
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (! (= x #x01) :named one))
(assert (! (= x #x02) :named two))
(check-sat)
(get-assignment)
";
    assert_eq!(
        solve_smtlib_get_assignment(text, &config()).expect("decides"),
        None
    );
}

#[test]
fn get_info_returns_recorded_metadata() {
    use axeyum_solver::solve_smtlib_get_info;
    let text = "\
(set-logic QF_BV)
(set-info :status sat)
(set-info :name \"tiny\")
(declare-const x (_ BitVec 8))
(assert (= x #x05))
(check-sat)
(get-info :name)
(get-info :status)
";
    let info = solve_smtlib_get_info(text, &config())
        .expect("metadata helper succeeds")
        .expect("script requested info");
    assert_eq!(
        info,
        vec![
            (":name".to_owned(), "\"tiny\"".to_owned()),
            (":status".to_owned(), "sat".to_owned()),
        ]
    );
}

#[test]
fn get_info_has_defaults_and_unsupported_marker() {
    use axeyum_solver::solve_smtlib_get_info;
    let text = "\
(set-logic QF_BV)
(get-info :name)
(get-info :version)
(get-info :not-a-real-key)
";
    let info = solve_smtlib_get_info(text, &config())
        .expect("metadata helper succeeds")
        .expect("script requested info");
    assert_eq!(info[0], (":name".to_owned(), "\"axeyum\"".to_owned()));
    assert_eq!(info[1].0, ":version");
    assert!(
        info[1].1.contains(env!("CARGO_PKG_VERSION")),
        "version should include crate version: {info:?}"
    );
    assert_eq!(
        info[2],
        (":not-a-real-key".to_owned(), "unsupported".to_owned())
    );
}

#[test]
fn get_option_returns_recorded_values_and_defaults() {
    use axeyum_solver::solve_smtlib_get_option;
    let text = "\
(set-logic QF_BV)
(set-option :produce-models true)
(set-option :regular-output-channel \"stdout\")
(get-option :produce-models)
(get-option :produce-proofs)
(get-option :regular-output-channel)
(get-option :not-a-real-option)
";
    let options = solve_smtlib_get_option(text, &config())
        .expect("option helper succeeds")
        .expect("script requested options");
    assert_eq!(
        options,
        vec![
            (":produce-models".to_owned(), "true".to_owned()),
            (":produce-proofs".to_owned(), "false".to_owned()),
            (
                ":regular-output-channel".to_owned(),
                "\"stdout\"".to_owned()
            ),
            (":not-a-real-option".to_owned(), "unsupported".to_owned()),
        ]
    );
}

#[test]
fn get_option_is_none_without_requests() {
    use axeyum_solver::solve_smtlib_get_option;
    let text = "\
(set-logic QF_BV)
(set-option :produce-models true)
";
    assert_eq!(
        solve_smtlib_get_option(text, &config()).expect("option helper succeeds"),
        None
    );
}

#[test]
fn get_model_returns_declared_constant_values() {
    use axeyum_ir::Value;
    use axeyum_solver::solve_smtlib_get_model;
    let text = "\
(set-logic QF_BV)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(declare-fun b () Bool)
(assert (= x #x05))
(assert b)
(check-sat)
(get-model)
";
    let model = solve_smtlib_get_model(text, &config())
        .expect("model helper succeeds")
        .expect("sat script requested a model");
    assert_eq!(
        model.constants,
        vec![
            ("x".to_owned(), Value::Bv { width: 8, value: 5 },),
            ("b".to_owned(), Value::Bool(true)),
        ]
    );
    assert!(model.functions.is_empty());
}

#[test]
fn get_model_is_none_without_request_or_without_sat_model() {
    use axeyum_solver::solve_smtlib_get_model;
    let no_request = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x05))
(check-sat)
";
    assert_eq!(
        solve_smtlib_get_model(no_request, &config()).expect("model helper succeeds"),
        None
    );

    let unsat = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x05))
(assert (= x #x06))
(check-sat)
(get-model)
";
    assert_eq!(
        solve_smtlib_get_model(unsat, &config()).expect("model helper succeeds"),
        None
    );
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
    assert_eq!(
        outcomes[0],
        OptOutcome::Optimal(100),
        "max unsigned x <= 100 = 100"
    );
}

/// Enum datatype: `Color` with three nullary constructors. `c != red ∧ c != green`
/// forces `c = blue` (sat); the `(_ is C)` tester contradicting equality is unsat.
#[test]
fn enum_datatype_decides() {
    let sat = "\
(set-logic QF_DT)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-const c Color)
(assert (not (= c red)))
(assert (not (= c green)))
(check-sat)
";
    assert!(
        matches!(run(sat).result, CheckResult::Sat(_)),
        "c=blue is sat"
    );

    let unsat = "\
(set-logic QF_DT)
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-const c Color)
(assert ((_ is red) c))
(assert (not (= c red)))
(check-sat)
";
    assert_eq!(
        run(unsat).result,
        CheckResult::Unsat,
        "is-red ∧ c≠red is unsat"
    );
}

/// Record datatype with selectors: `Pair` over bit-vectors. Constraining the
/// fields is satisfiable and `(get-value)` reads them back via the selectors.
#[test]
fn record_datatype_constructor_and_selectors() {
    use axeyum_ir::Value;
    use axeyum_solver::solve_smtlib_get_value;
    let text = "\
(set-logic QF_DT)
(declare-datatypes ((Pair 0)) (((mk (fst (_ BitVec 8)) (snd (_ BitVec 8))))))
(declare-const p Pair)
(assert (= (fst p) #x03))
(assert (= (snd p) #x05))
(check-sat)
(get-value ((fst p) (snd p)))
";
    let values = solve_smtlib_get_value(text, &config())
        .expect("decides")
        .expect("sat");
    assert_eq!(values[0], Value::Bv { width: 8, value: 3 });
    assert_eq!(values[1], Value::Bv { width: 8, value: 5 });
}

/// Recursive datatype (a list): `((_ is cons) l) ∧ hd(l) = 5` is satisfiable
/// (l = cons(5, _)); the native solver unfolds the recursive `tl` field into a
/// fresh child (relaxation), and the sat candidate replays (ADR-0022).
#[test]
fn recursive_datatype_list_decides() {
    let sat = "\
(set-logic QF_DT)
(declare-datatypes ((Lst 0)) (((cons (hd (_ BitVec 8)) (tl Lst)) (nil))))
(declare-const l Lst)
(assert ((_ is cons) l))
(assert (= (hd l) #x05))
(check-sat)
";
    assert!(
        matches!(run(sat).result, CheckResult::Sat(_)),
        "cons-headed list with hd=5 is sat"
    );

    // is-cons and is-nil are mutually exclusive: unsat.
    let unsat = "\
(set-logic QF_DT)
(declare-datatypes ((Lst 0)) (((cons (hd (_ BitVec 8)) (tl Lst)) (nil))))
(declare-const l Lst)
(assert ((_ is cons) l))
(assert ((_ is nil) l))
(check-sat)
";
    assert_eq!(
        run(unsat).result,
        CheckResult::Unsat,
        "cons and nil exclude"
    );
}

/// Lexicographic vs boxed optimization differ when objectives interact. With
/// x+y <= 10, x,y >= 0 and priorities (maximize y, maximize x):
/// - lexicographic: y=10 first, then x maximal subject to y=10 -> x=0  => [10, 0]
/// - boxed (independent): y=10 and x=10 independently               => [10, 10]
#[test]
fn lexicographic_optimization_differs_from_boxed() {
    use axeyum_solver::{OptOutcome, optimize_smtlib, optimize_smtlib_lexicographic};
    let text = "\
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (<= (+ x y) 10))
(assert (>= x 0))
(assert (>= y 0))
(maximize y)
(maximize x)
(check-sat)
(get-objectives)
";
    let lex = optimize_smtlib_lexicographic(text, &config()).expect("lex optimizes");
    assert_eq!(
        lex,
        vec![OptOutcome::Optimal(10), OptOutcome::Optimal(0)],
        "lex"
    );

    let boxed = optimize_smtlib(text, &config()).expect("box optimizes");
    assert_eq!(
        boxed,
        vec![OptOutcome::Optimal(10), OptOutcome::Optimal(10)],
        "box"
    );
}

/// First slice of the SMT-LIB string front end (ADR-0029): a bounded `String`
/// is a packed bit-vector with a canonical well-formedness constraint, so string
/// equality decides through the bit-vector path. Find s with s == "ab" -> sat.
#[test]
fn decides_string_equality_sat() {
    let text = "\
(set-info :status sat)
(declare-const s String)
(assert (= s \"ab\"))
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "s == \"ab\" must be sat, got {:?}",
        outcome.result
    );
}

/// Conflicting string equalities are unsat (s cannot be both "ab" and "ac").
#[test]
fn decides_string_equality_unsat() {
    let text = "\
(set-info :status unsat)
(declare-const s String)
(assert (= s \"ab\"))
(assert (= s \"ac\"))
(check-sat)
";
    let outcome = run(text);
    assert_eq!(
        outcome.result,
        CheckResult::Unsat,
        "s == \"ab\" ∧ s == \"ac\" must be unsat"
    );
}

/// String disequality is sound through the canonical packing: with s == "ab" and
/// s != t, a distinct t exists -> sat (the canonical-padding wf makes BV
/// disequality coincide with string disequality).
#[test]
fn decides_string_disequality_sat() {
    let text = "\
(set-info :status sat)
(declare-const s String)
(declare-const t String)
(assert (= s \"ab\"))
(assert (not (= s t)))
(check-sat)
";
    let outcome = run(text);
    assert!(
        matches!(outcome.result, CheckResult::Sat(_)),
        "s==\"ab\" ∧ s!=t must be sat, got {:?}",
        outcome.result
    );
}

/// `str.len` returns an Int (via `bv2nat`) composing with integer arithmetic
/// (ADR-0029). The SAT direction decides — useful for generating strings with
/// length properties. The conflicting direction may return `Unknown`: a bounded
/// integer-blast can't soundly conclude `unsat` (ADR-0014) and the simplex path
/// doesn't see the string BV constraints — a known BV+LIA combination gap.
/// `Unknown` is sound; what matters is it is never a wrong `sat`.
#[test]
fn str_len_sat_direction_decides() {
    let sat = run("\
(declare-const s String)
(assert (= (str.len s) 2))
(check-sat)
");
    assert!(
        matches!(sat.result, CheckResult::Sat(_)),
        "a length-2 string exists, got {:?}",
        sat.result
    );

    let sat2 = run("\
(declare-const s String)
(assert (= s \"ab\"))
(assert (= (str.len s) 2))
(check-sat)
");
    assert!(
        matches!(sat2.result, CheckResult::Sat(_)),
        "s==\"ab\" with len 2 must be sat, got {:?}",
        sat2.result
    );

    // Conflicting length: decided soundly — Unsat or (soundly) Unknown, never sat.
    let conflict = run("\
(declare-const s String)
(assert (= s \"ab\"))
(assert (= (str.len s) 3))
(check-sat)
");
    assert!(
        matches!(
            conflict.result,
            CheckResult::Unsat | CheckResult::Unknown(_)
        ),
        "len(\"ab\")==3 must not be wrongly sat, got {:?}",
        conflict.result
    );
}

/// `str.prefixof` is a pure bit-vector/Boolean formula over packed strings, so
/// it decides both sat and unsat (no Int/theory-combination gap). ADR-0029.
#[test]
fn decides_str_prefixof_both_directions() {
    // Ground truths.
    assert!(matches!(
        run("(assert (str.prefixof \"ab\" \"abc\"))\n(check-sat)\n").result,
        CheckResult::Sat(_)
    ));
    assert_eq!(
        run("(assert (str.prefixof \"ac\" \"abc\"))\n(check-sat)\n").result,
        CheckResult::Unsat,
        "\"ac\" is not a prefix of \"abc\""
    );
    // With a variable: s is a prefix of "abcd" and s == "ab" -> sat.
    assert!(matches!(
        run("\
(declare-const s String)
(assert (str.prefixof s \"abcd\"))
(assert (= s \"ab\"))
(check-sat)
")
        .result,
        CheckResult::Sat(_)
    ));
    // s == "xy" cannot be a prefix of "abc" -> unsat (decides, no gap).
    assert_eq!(
        run("\
(declare-const s String)
(assert (= s \"xy\"))
(assert (str.prefixof s \"abc\"))
(check-sat)
")
        .result,
        CheckResult::Unsat,
        "\"xy\" is not a prefix of \"abc\""
    );
}

/// `str.contains` (substring search) is pure BV/Bool over packed strings —
/// decides both directions (ADR-0029).
#[test]
fn decides_str_contains_both_directions() {
    // Ground truths.
    assert!(matches!(
        run("(assert (str.contains \"abcd\" \"bc\"))\n(check-sat)\n").result,
        CheckResult::Sat(_)
    ));
    assert_eq!(
        run("(assert (str.contains \"abcd\" \"bd\"))\n(check-sat)\n").result,
        CheckResult::Unsat,
        "\"bd\" is not a contiguous substring of \"abcd\""
    );
    // Empty string is contained in everything.
    assert!(matches!(
        run("(assert (str.contains \"ab\" \"\"))\n(check-sat)\n").result,
        CheckResult::Sat(_)
    ));
    // Variable haystack containing "xy" with s == "axyz" -> sat.
    assert!(matches!(
        run("\
(declare-const s String)
(assert (= s \"axyz\"))
(assert (str.contains s \"xy\"))
(check-sat)
")
        .result,
        CheckResult::Sat(_)
    ));
    // s == "ab" cannot contain "abc" (needle longer) -> unsat.
    assert_eq!(
        run("\
(declare-const s String)
(assert (= s \"ab\"))
(assert (str.contains s \"abc\"))
(check-sat)
")
        .result,
        CheckResult::Unsat,
        "a 2-byte string cannot contain a 3-byte substring"
    );
}

/// `str.suffixof` over packed strings — pure BV/Bool, decides both directions.
#[test]
fn decides_str_suffixof_both_directions() {
    assert!(matches!(
        run("(assert (str.suffixof \"cd\" \"abcd\"))\n(check-sat)\n").result,
        CheckResult::Sat(_)
    ));
    assert_eq!(
        run("(assert (str.suffixof \"ab\" \"abcd\"))\n(check-sat)\n").result,
        CheckResult::Unsat,
        "\"ab\" is a prefix, not a suffix, of \"abcd\""
    );
    // Variable: s == "world" and "rld" is a suffix -> sat.
    assert!(matches!(
        run("\
(declare-const s String)
(assert (= s \"world\"))
(assert (str.suffixof \"rld\" s))
(check-sat)
")
        .result,
        CheckResult::Sat(_)
    ));
}

/// `str.at` with a constant index returns the indexed character as a length-1
/// string (empty when out of range) — packed, canonical, decides both
/// directions (ADR-0029).
#[test]
fn decides_str_at_constant_index() {
    // s == "abc": s[1] == "b" sat, s[1] == "c" unsat.
    assert!(matches!(
        run("\
(declare-const s String)
(assert (= s \"abc\"))
(assert (= (str.at s 1) \"b\"))
(check-sat)
")
        .result,
        CheckResult::Sat(_)
    ));
    assert_eq!(
        run("\
(declare-const s String)
(assert (= s \"abc\"))
(assert (= (str.at s 1) \"c\"))
(check-sat)
")
        .result,
        CheckResult::Unsat,
        "s[1] is 'b', not 'c'"
    );
    // Out-of-range index yields the empty string.
    assert!(matches!(
        run("\
(declare-const s String)
(assert (= s \"abc\"))
(assert (= (str.at s 5) \"\"))
(check-sat)
")
        .result,
        CheckResult::Sat(_)
    ));
}

/// `str.++` over constant strings folds to a literal (ADR-0029): s == "foo"++"bar"
/// is sat with s=="foobar"; an over-bound concat is a clean error.
#[test]
fn decides_str_concat_of_constants() {
    assert!(matches!(
        run("\
(declare-const s String)
(assert (= s (str.++ \"foo\" \"bar\")))
(check-sat)
")
        .result,
        CheckResult::Sat(_)
    ));
    // The folded "foobar" really equals the literal: contains "oob".
    assert!(matches!(
        run("\
(declare-const s String)
(assert (= s (str.++ \"foo\" \"bar\")))
(assert (str.contains s \"oob\"))
(check-sat)
")
        .result,
        CheckResult::Sat(_)
    ));
    // Wrong concat result is unsat.
    assert_eq!(
        run("\
(declare-const s String)
(assert (= s (str.++ \"foo\" \"bar\")))
(assert (= s \"foobaz\"))
(check-sat)
")
        .result,
        CheckResult::Unsat
    );
}

/// `(get-proof)` on an in-fragment `QF_BV` `unsat` returns a checkable Alethe proof
/// that closes to the empty clause via `bitblast_*` + resolution.
#[test]
fn get_proof_returns_a_checkable_alethe_proof() {
    use axeyum_cnf::{check_alethe, parse_alethe};
    use axeyum_solver::solve_smtlib_get_proof;
    let text = "\
(set-logic QF_BV)
(declare-const a (_ BitVec 4))
(declare-const b (_ BitVec 4))
(assert (bvult a b))
(assert (bvult b a))
(check-sat)
(get-proof)
";
    let proof = solve_smtlib_get_proof(text, &config())
        .expect("decides")
        .expect("an Alethe proof for the unsat QF_BV script");
    assert!(
        proof.contains("bitblast_ult"),
        "uses the bitblast layer:\n{proof}"
    );
    assert!(
        proof.contains(":rule resolution"),
        "closes by resolution:\n{proof}"
    );
    // The textual proof round-trips and re-validates with the in-tree checker.
    let parsed = parse_alethe(&proof).expect("emitted Alethe parses");
    assert_eq!(check_alethe(&parsed), Ok(true), "proof re-checks to (cl)");
}

/// `(get-proof)` is `None` when the script is satisfiable.
#[test]
fn get_proof_is_none_when_sat() {
    use axeyum_solver::solve_smtlib_get_proof;
    let text = "\
(set-logic QF_BV)
(declare-const a (_ BitVec 4))
(assert (bvult a #xf))
(check-sat)
(get-proof)
";
    assert_eq!(
        solve_smtlib_get_proof(text, &config()).expect("decides"),
        None
    );
}

/// `(get-proof)` is `None` for an `unsat` whose refutation needs **shift
/// semantics** — outside every supported Alethe fragment. `a = 1 ∧ a≪1 = 0` is
/// unsat (1≪1 = 2 ≠ 0), but the `QF_BV` driver has no `bvshl` bitblast rule and the
/// EUF path (which treats `bvshl` as an opaque function) sees no contradiction, so
/// no fragment can prove it even though it is genuinely unsatisfiable.
#[test]
fn get_proof_is_none_outside_the_fragment() {
    use axeyum_solver::solve_smtlib_get_proof;
    let text = "\
(set-logic QF_BV)
(declare-const a (_ BitVec 4))
(assert (= a (_ bv1 4)))
(assert (= (bvshl a (_ bv1 4)) (_ bv0 4)))
(check-sat)
(get-proof)
";
    assert_eq!(
        solve_smtlib_get_proof(text, &config()).expect("decides"),
        None
    );
}

/// `(get-proof)` serves the **EUF** fragment: `a=b ∧ f(a)≠f(b)` is unsat by
/// congruence, and the returned proof closes by `eq_congruent`/resolution.
#[test]
fn get_proof_serves_the_euf_fragment() {
    use axeyum_cnf::{check_alethe, parse_alethe};
    use axeyum_solver::solve_smtlib_get_proof;
    let text = "\
(set-logic QF_UFBV)
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
(get-proof)
";
    let proof = solve_smtlib_get_proof(text, &config())
        .expect("decides")
        .expect("an Alethe proof for the EUF congruence conflict");
    let parsed = parse_alethe(&proof).expect("emitted Alethe parses");
    assert_eq!(
        check_alethe(&parsed),
        Ok(true),
        "EUF proof re-checks to (cl)"
    );
}

/// `(get-proof)` serves the **`QF_LRA`** fragment: `x ≤ 0 ∧ x ≥ 1` is unsat, and the
/// returned proof is a Farkas `la_generic` refutation (re-checked by `check_alethe_lra`).
#[test]
fn get_proof_serves_the_lra_fragment() {
    use axeyum_cnf::parse_alethe;
    use axeyum_solver::{check_alethe_lra, solve_smtlib_get_proof};
    let text = "\
(set-logic QF_LRA)
(declare-const x Real)
(assert (<= x 0.0))
(assert (>= x 1.0))
(check-sat)
(get-proof)
";
    let proof = solve_smtlib_get_proof(text, &config())
        .expect("decides")
        .expect("an Alethe proof for the LRA conflict");
    assert!(
        proof.contains("la_generic"),
        "uses the Farkas layer:\n{proof}"
    );
    let parsed = parse_alethe(&proof).expect("emitted Alethe parses");
    assert_eq!(
        check_alethe_lra(&parsed),
        Ok(true),
        "LRA proof re-checks to (cl)"
    );
}

/// `(get-proof)` serves the **`QF_LIA`** fragment: `x ≤ 0 ∧ x ≥ 1` over the integers
/// is unsat, and the returned proof is a `lia_generic` refutation (re-checked by
/// `check_alethe_lra`; internally checkable only — Carcara holes `lia_generic`).
#[test]
fn get_proof_serves_the_lia_fragment() {
    use axeyum_cnf::parse_alethe;
    use axeyum_solver::{check_alethe_lra, solve_smtlib_get_proof};
    let text = "\
(set-logic QF_LIA)
(declare-const x Int)
(assert (<= x 0))
(assert (>= x 1))
(check-sat)
(get-proof)
";
    let proof = solve_smtlib_get_proof(text, &config())
        .expect("decides")
        .expect("an Alethe proof for the integer conflict");
    assert!(
        proof.contains("lia_generic"),
        "uses the integer Farkas layer:\n{proof}"
    );
    let parsed = parse_alethe(&proof).expect("emitted Alethe parses");
    assert_eq!(
        check_alethe_lra(&parsed),
        Ok(true),
        "LIA proof re-checks to (cl)"
    );
}

/// `(get-proof)` serves the **`QF_ABV`** read-over-write-same fragment: the
/// disequality `(select (store a i v) i) != v` is unsat by the ROW-same axiom, and
/// the returned proof re-checks in-tree (the `read_over_write_same` rule).
#[test]
fn get_proof_serves_the_array_row_same_fragment() {
    use axeyum_cnf::{check_alethe, parse_alethe};
    use axeyum_solver::solve_smtlib_get_proof;
    let text = "\
(set-logic QF_ABV)
(declare-const a (Array (_ BitVec 4) (_ BitVec 8)))
(declare-const i (_ BitVec 4))
(declare-const v (_ BitVec 8))
(assert (not (= (select (store a i v) i) v)))
(check-sat)
(get-proof)
";
    let proof = solve_smtlib_get_proof(text, &config())
        .expect("decides")
        .expect("an Alethe proof for the read-over-write-same conflict");
    assert!(
        proof.contains("read_over_write_same"),
        "uses the array axiom rule:\n{proof}"
    );
    let parsed = parse_alethe(&proof).expect("emitted Alethe parses");
    assert_eq!(
        check_alethe(&parsed),
        Ok(true),
        "array proof re-checks to (cl)"
    );
}

#[test]
fn reset_assertions_clears_assertions_not_a_no_op() {
    use axeyum_solver::solve_smtlib_incremental;
    // Without honoring reset-assertions, the third check-sat would see
    // x=5 ∧ x=6 ∧ x=7 and report UNSAT — solving a DIFFERENT problem than the
    // script asked. With it cleared, only `x=7` is active → sat.
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x05))
(check-sat)
(assert (= x #x06))
(check-sat)
(reset-assertions)
(assert (= x #x07))
(check-sat)
";
    let results = solve_smtlib_incremental(text, &config()).expect("script decides");
    assert_eq!(results.len(), 3, "one result per check-sat");
    assert!(matches!(results[0], CheckResult::Sat(_)), "x=5 is sat");
    assert_eq!(results[1], CheckResult::Unsat, "x=5 ∧ x=6 is unsat");
    assert!(
        matches!(results[2], CheckResult::Sat(_)),
        "after reset-assertions, only x=7 is active → sat (not the stale contradiction)"
    );
}

#[test]
fn full_reset_is_rejected_not_silently_ignored() {
    use axeyum_solver::solve_smtlib_incremental;
    // `(reset)` (full reset incl. declarations) is not soundly supported in the
    // shared-arena model, so it must be REJECTED rather than treated as a no-op
    // (which would silently keep stale state).
    let text = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x05))
(reset)
(check-sat)
";
    let result = solve_smtlib_incremental(text, &config());
    assert!(
        result.is_err(),
        "full (reset) must be rejected, not silently ignored; got {result:?}"
    );
}
