//! Ground floating-point division coverage at the SMT-LIB front door.
#![cfg(feature = "full")]

use std::time::Duration;

#[cfg(feature = "z3")]
use axeyum_fp::{FloatFormat, RoundingMode, div};
#[cfg(feature = "z3")]
use axeyum_ir::{Assignment, TermArena, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, solve_smtlib};

const ISSUE130: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../corpus/public-curated/non-incremental/QF_BVFP/bitwuzla-regress-clean/solver__fp__issue130.smt2"
));

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(5))
}

#[test]
fn decides_public_custom_format_division() {
    let outcome = solve_smtlib(ISSUE130, &config()).expect("public QF_BVFP row is supported");
    assert_eq!(outcome.logic.as_deref(), Some("QF_BVFP"));
    assert_eq!(outcome.expected_status.as_deref(), Some("sat"));
    assert!(matches!(outcome.result, CheckResult::Sat(_)));
}

#[test]
fn refutes_negation_of_public_custom_format_division() {
    let text = r"
        (set-logic QF_BVFP)
        (assert (not (=
          (fp.div RNA (fp #b1 #xe #b11111111111) (fp #b1 #xb #b01100000000))
          (fp #b0 #xa #b01110100010))))
        (set-info :status unsat)
        (check-sat)
    ";
    let outcome = solve_smtlib(text, &config()).expect("ground custom division is supported");
    assert_eq!(outcome.result, CheckResult::Unsat);
}

#[cfg(feature = "z3")]
fn fp_literal(bits: u128) -> String {
    let sign = bits >> 15;
    let exponent = (bits >> 11) & 0xf;
    let trailing = bits & 0x7ff;
    format!("(fp #b{sign} #x{exponent:x} #b{trailing:011b})")
}

#[cfg(feature = "z3")]
fn ground_quotient(a_bits: u128, b_bits: u128, mode: RoundingMode) -> u128 {
    let mut arena = TermArena::new();
    let a = arena.bv_const(16, a_bits).unwrap();
    let b = arena.bv_const(16, b_bits).unwrap();
    let quotient = div(
        &mut arena,
        FloatFormat {
            exp_bits: 4,
            sig_bits: 12,
        },
        a,
        b,
        mode,
    )
    .unwrap();
    match eval(&arena, quotient, &Assignment::new()).unwrap() {
        Value::Bv { value, .. } => value,
        other => panic!("expected bit-vector quotient, got {other:?}"),
    }
}

/// Independent custom-format differential: Z3 checks a deterministic
/// finite/nonzero battery for every rounding mode. The exact Axeyum result is
/// asserted wrong, so Z3 must refute the disjunction of all mismatches.
#[cfg(feature = "z3")]
#[test]
fn ground_custom_format_division_agrees_with_z3() {
    use z3::{Params, SatResult, Solver};

    let modes = [
        ("RNE", RoundingMode::NearestEven),
        ("RNA", RoundingMode::NearestAway),
        ("RTP", RoundingMode::TowardPositive),
        ("RTN", RoundingMode::TowardNegative),
        ("RTZ", RoundingMode::TowardZero),
    ];
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut cases = vec![
        (0x3800u128, 0x4000u128), // 1 / 2
        (0xb800, 0x4000),         // -1 / 2
        (0x0001, 0x3800),         // smallest subnormal / 1
        (0x77ff, 0x3000),         // max finite / 0.5 (overflow)
        (0xf7ff, 0x3000),         // negative overflow
        (0x3800, 0x0001),         // finite / smallest subnormal
    ];
    for _ in 0..14 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let finite_nonzero = |raw: u16| -> u128 {
            let mut bits = u128::from(raw);
            if (bits >> 11) & 0xf == 0xf {
                bits = (bits & !(0xf << 11)) | (0xe << 11);
            }
            if bits.trailing_zeros() >= 15 {
                bits |= 1;
            }
            bits
        };
        let state_bytes = state.to_le_bytes();
        cases.push((
            finite_nonzero(u16::from_le_bytes([state_bytes[0], state_bytes[1]])),
            finite_nonzero(u16::from_le_bytes([state_bytes[4], state_bytes[5]])),
        ));
    }

    for (mode_name, mode) in modes {
        let mut mismatch_terms = Vec::with_capacity(cases.len());
        for &(a_bits, b_bits) in &cases {
            let expected = ground_quotient(a_bits, b_bits, mode);
            mismatch_terms.push(format!(
                "(not (= (fp.div {mode_name} {} {}) {}))",
                fp_literal(a_bits),
                fp_literal(b_bits),
                fp_literal(expected),
            ));
        }
        let script = format!(
            "(set-logic QF_FP)\n(assert (or {}))\n(check-sat)\n",
            mismatch_terms.join("\n")
        );
        let mut params = Params::new();
        params.set_u32("timeout", 10_000);
        let oracle = Solver::new();
        oracle.set_params(&params);
        oracle.from_string(script.as_str());
        assert_eq!(
            oracle.check(),
            SatResult::Unsat,
            "Z3 custom-format mismatch under {mode_name}"
        );
        assert_eq!(
            solve_smtlib(&script, &config()).unwrap().result,
            CheckResult::Unsat,
            "Axeyum custom-format mismatch under {mode_name}"
        );
    }
}
