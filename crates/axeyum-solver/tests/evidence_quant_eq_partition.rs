//! ADR-0101: checked finite equality partitions for nested Bool/Int quantifiers.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, Evidence, SolverConfig, produce_evidence, solve};

const SDLX: &str = include_str!(
    "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__cbqi-sdlx-fixpoint-3-dd.smt2"
);

#[test]
fn sdlx_nested_formula_has_checked_partition_evidence() {
    let mut script = parse_script(SDLX).expect("parse sdlx");
    let assertions = script.assertions.clone();
    assert_eq!(
        solve(
            &mut script.arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("solve sdlx"),
        CheckResult::Unsat
    );
    let report = produce_evidence(
        &mut script.arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(2)),
    )
    .expect("produce sdlx evidence");
    let Evidence::UnsatEqualityPartition(certificate) = &report.evidence else {
        panic!(
            "expected equality-partition evidence, got {:?}",
            report.evidence
        );
    };
    assert_eq!(certificate.assertion, assertions[0]);
    assert!(certificate.representative_cases > 0);
    assert_eq!(report.evidence.kind_label(), "unsat-equality-partition");
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
}

#[test]
fn tampered_case_count_is_rejected() {
    let mut script = parse_script(SDLX).expect("parse sdlx");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &SolverConfig::default())
        .expect("produce sdlx evidence");
    let Evidence::UnsatEqualityPartition(mut certificate) = report.evidence else {
        panic!("expected equality-partition evidence");
    };
    certificate.representative_cases += 1;
    assert!(
        !Evidence::UnsatEqualityPartition(certificate)
            .check(&script.arena, &assertions)
            .unwrap()
    );
}

#[test]
fn multiple_constants_bool_binders_and_negated_exists_are_exact() {
    for text in [
        "(set-logic LIA) \
         (assert (or false (forall ((x Int)) (or (= x (- 2)) (= x 7))))) (check-sat)",
        "(set-logic LIA) \
         (assert (or false (forall ((b Bool)) (= b true)))) (check-sat)",
        "(set-logic LIA) (assert (not (exists ((x Int)) (= x 2)))) (check-sat)",
    ] {
        let mut script = parse_script(text).expect("parse partition theorem");
        let assertions = script.assertions.clone();
        let report = produce_evidence(&mut script.arena, &assertions, &SolverConfig::default())
            .expect("produce partition theorem evidence");
        assert!(
            matches!(report.evidence, Evidence::UnsatEqualityPartition(_)),
            "missing partition evidence: {text}"
        );
        assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    }
}

#[test]
fn free_symbols_and_direct_arithmetic_uses_are_rejected() {
    for text in [
        "(set-logic LIA) (declare-fun p () Int) \
         (assert (forall ((x Int)) (= (= x 0) (= p 0)))) (check-sat)",
        "(set-logic LIA) \
         (assert (forall ((x Int)) (= (+ x 1) x))) (check-sat)",
        "(set-logic LIA) \
         (assert (forall ((x Int) (y Int)) (= x y))) (check-sat)",
    ] {
        let mut script = parse_script(text).expect("parse rejected partition shape");
        let assertions = script.assertions.clone();
        let report = produce_evidence(
            &mut script.arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("produce honest fallback evidence");
        assert!(
            !matches!(report.evidence, Evidence::UnsatEqualityPartition(_)),
            "out-of-contract formula received partition evidence: {text}"
        );
    }
}

#[test]
fn valid_partitioned_formulas_are_not_refuted() {
    for text in [
        "(set-logic LIA) \
         (assert (forall ((x Int)) (or (= x 3) (not (= x 3))))) (check-sat)",
        "(set-logic LIA) \
         (assert (exists ((x Int)) (= x 3))) (check-sat)",
    ] {
        let mut script = parse_script(text).expect("parse valid partition formula");
        let assertions = script.assertions.clone();
        let result = solve(
            &mut script.arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("solve valid partition formula");
        assert!(!matches!(result, CheckResult::Unsat), "wrong UNSAT: {text}");
    }
}

#[cfg(feature = "z3")]
#[test]
fn equality_partition_sweep_agrees_with_z3() {
    use z3::{Params, SatResult, Solver};

    let smt_int = |value: i64| {
        if value < 0 {
            format!("(- {})", value.unsigned_abs())
        } else {
            value.to_string()
        }
    };

    for seed in 0i64..64 {
        let a = seed % 17 - 8;
        let b = a + 1;
        let c = seed % 13 - 6;
        let false_formula = format!(
            "(set-logic LIA)\n\
             (assert (or\n\
               (forall ((x Int)) (= (= x {}) (= x {})))\n\
               (not (exists ((y Int)) (= y {})))))\n\
             (check-sat)\n",
            smt_int(a),
            smt_int(b),
            smt_int(c)
        );
        let mut script = parse_script(&false_formula).expect("parse generated false partition");
        let assertions = script.assertions.clone();
        let report = produce_evidence(
            &mut script.arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("produce generated partition evidence");
        assert!(
            matches!(report.evidence, Evidence::UnsatEqualityPartition(_)),
            "missing partition evidence at seed {seed}: {false_formula}"
        );
        assert!(report.evidence.check(&script.arena, &assertions).unwrap());

        let mut params = Params::new();
        params.set_u32("timeout", 2_000);
        let oracle = Solver::new();
        oracle.set_params(&params);
        oracle.from_string(false_formula.as_str());
        assert_eq!(oracle.check(), SatResult::Unsat, "false seed {seed}");

        let valid_formula = format!(
            "(set-logic LIA)\n\
             (assert (forall ((x Int))\n\
               (exists ((y Int)) (= (= x {}) (= y {})))))\n\
             (check-sat)\n",
            smt_int(a),
            smt_int(b)
        );
        let mut valid_script = parse_script(&valid_formula).expect("parse valid alternation");
        let valid_assertions = valid_script.assertions.clone();
        let result = solve(
            &mut valid_script.arena,
            &valid_assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("solve valid alternation");
        assert!(
            !matches!(result, CheckResult::Unsat),
            "wrong UNSAT at seed {seed}: {valid_formula}"
        );
        let valid_oracle = Solver::new();
        valid_oracle.set_params(&params);
        valid_oracle.from_string(valid_formula.as_str());
        assert_eq!(valid_oracle.check(), SatResult::Sat, "valid seed {seed}");
    }
}
