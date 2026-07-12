//! ADR-0100: evaluator-replayed closed-universal counterexample evidence.

use std::time::Duration;

use axeyum_ir::Value;
use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, Evidence, SolverConfig, produce_evidence, solve};

const ARI176E1: &str = include_str!(
    "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress0__quantifiers__ARI176e1.smt2"
);
const ISSUE_5279: &str = include_str!(
    "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__issue5279-nqe.smt2"
);
#[test]
fn measured_bare_rows_gain_evaluator_replayed_evidence() {
    for (name, text, expected_bindings) in [("ARI176e1", ARI176E1, 2), ("issue5279", ISSUE_5279, 2)]
    {
        let mut script = parse_script(text).unwrap_or_else(|error| panic!("parse {name}: {error}"));
        let assertions = script.assertions.clone();
        let report = produce_evidence(
            &mut script.arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .unwrap_or_else(|error| panic!("produce {name}: {error}"));
        let Evidence::UnsatClosedUniversalCounterexample(certificate) = &report.evidence else {
            panic!(
                "expected closed-universal evidence for {name}, got {:?}",
                report.evidence
            );
        };
        assert_eq!(certificate.assertion, assertions[0]);
        assert_eq!(certificate.bindings.len(), expected_bindings);
        assert_eq!(
            report.evidence.kind_label(),
            "unsat-closed-universal-counterexample"
        );
        assert!(report.evidence.is_certified());
        assert!(report.evidence.check(&script.arena, &assertions).unwrap());
        assert!(report.trusted_steps.is_empty());
    }
}

#[test]
fn tampered_values_sorts_and_binder_order_are_rejected() {
    let mut script = parse_script(ARI176E1).expect("parse ARI176e1");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &SolverConfig::default())
        .expect("produce ARI176e1 evidence");
    let Evidence::UnsatClosedUniversalCounterexample(certificate) = report.evidence else {
        panic!("expected closed-universal evidence");
    };

    let mut wrong_values = certificate.clone();
    for (_, value) in &mut wrong_values.bindings {
        *value = Value::Int(0);
    }
    assert!(
        !Evidence::UnsatClosedUniversalCounterexample(wrong_values)
            .check(&script.arena, &assertions)
            .unwrap()
    );

    let mut wrong_sort = certificate.clone();
    wrong_sort.bindings[0].1 = Value::Bool(false);
    assert!(
        !Evidence::UnsatClosedUniversalCounterexample(wrong_sort)
            .check(&script.arena, &assertions)
            .unwrap()
    );

    let mut reordered = certificate;
    reordered.bindings.swap(0, 1);
    assert!(
        !Evidence::UnsatClosedUniversalCounterexample(reordered)
            .check(&script.arena, &assertions)
            .unwrap()
    );

    let report = produce_evidence(&mut script.arena, &assertions, &SolverConfig::default())
        .expect("reproduce ARI176e1 evidence");
    let Evidence::UnsatClosedUniversalCounterexample(certificate) = report.evidence else {
        panic!("expected closed-universal evidence");
    };
    let mut missing = certificate.clone();
    missing.bindings.pop();
    assert!(
        !Evidence::UnsatClosedUniversalCounterexample(missing)
            .check(&script.arena, &assertions)
            .unwrap()
    );
    let mut extra = certificate.clone();
    extra.bindings.push(extra.bindings[0].clone());
    assert!(
        !Evidence::UnsatClosedUniversalCounterexample(extra)
            .check(&script.arena, &assertions)
            .unwrap()
    );
    let mut wrong_assertion = certificate;
    wrong_assertion.assertion = script.arena.bool_const(true);
    assert!(
        !Evidence::UnsatClosedUniversalCounterexample(wrong_assertion)
            .check(&script.arena, &assertions)
            .unwrap()
    );
}

#[test]
fn open_nested_and_uf_universals_do_not_receive_the_certificate() {
    for text in [
        "(set-logic LIA) (declare-fun p () Int) \
         (assert (forall ((x Int)) (= x p))) (check-sat)",
        "(set-logic LIA) \
         (assert (forall ((x Int)) (exists ((y Int)) (= y x)))) (check-sat)",
        "(set-logic UF) (declare-sort U 0) (declare-fun f (U) U) \
         (assert (forall ((x U)) (= (f x) x))) (check-sat)",
        "(set-logic UFLIA) (declare-fun f (Int) Int) \
         (assert (forall ((x Int)) (= (f x) x))) (check-sat)",
    ] {
        let mut script = parse_script(text).expect("parse declined universal");
        let assertions = script.assertions.clone();
        let report = produce_evidence(
            &mut script.arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("declined universal still has an honest result");
        assert!(
            !matches!(
                report.evidence,
                Evidence::UnsatClosedUniversalCounterexample(_)
            ),
            "out-of-contract universal received ADR-0100 evidence: {text}"
        );
    }
}

#[test]
fn valid_closed_universal_is_not_falsified() {
    let text = "(set-logic LIA) \
        (assert (forall ((x Int) (b Bool)) (or (= x x) b))) (check-sat)";
    let mut script = parse_script(text).expect("parse valid universal");
    let assertions = script.assertions.clone();
    let report = produce_evidence(
        &mut script.arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(2)),
    )
    .expect("produce valid-universal result");
    assert!(!matches!(
        report.evidence,
        Evidence::UnsatClosedUniversalCounterexample(_)
    ));
    assert!(!matches!(
        solve(
            &mut script.arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("solve valid universal"),
        CheckResult::Unsat
    ));
}

#[cfg(feature = "z3")]
#[test]
fn generated_counterexamples_and_valid_wrappers_agree_with_z3() {
    use z3::{Params, SatResult, Solver};

    let smt_int = |value: i64| {
        if value < 0 {
            format!("(- {})", value.unsigned_abs())
        } else {
            value.to_string()
        }
    };

    for seed in 0i64..64 {
        let text = if seed & 1 == 0 {
            let coefficient = seed % 7 + 1;
            let multiplier = seed % 9 - 4;
            let witness_u = seed % 11 - 5;
            let witness_v = seed % 13 - 6;
            let offset = coefficient * witness_u - multiplier * witness_v;
            format!(
                "(set-logic LIA)\n\
                 (assert (forall ((u Int) (v Int))\n\
                   (not (= (* {coefficient} u)\n\
                           (+ {} (* {} v))))))\n\
                 (check-sat)\n",
                smt_int(offset),
                smt_int(multiplier)
            )
        } else {
            let then_value = seed % 17 - 8;
            let else_value = then_value + 1;
            format!(
                "(set-logic LIA)\n\
                 (assert (forall ((a Int) (b Bool))\n\
                   (= a (ite b {} {}))))\n\
                 (check-sat)\n",
                smt_int(then_value),
                smt_int(else_value)
            )
        };

        let mut script = parse_script(&text).expect("parse generated false universal");
        let assertions = script.assertions.clone();
        let report = produce_evidence(
            &mut script.arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("produce generated evidence");
        assert!(
            matches!(
                report.evidence,
                Evidence::UnsatClosedUniversalCounterexample(_)
            ),
            "missing certificate at seed {seed}: {text}"
        );
        assert!(report.evidence.check(&script.arena, &assertions).unwrap());

        let mut params = Params::new();
        params.set_u32("timeout", 2_000);
        let oracle = Solver::new();
        oracle.set_params(&params);
        oracle.from_string(text.as_str());
        assert_eq!(
            oracle.check(),
            SatResult::Unsat,
            "Z3 disagreed on false universal seed {seed}: {text}"
        );

        let valid = format!(
            "(set-logic LIA)\n\
             (assert (forall ((u Int) (v Int))\n\
               (or (= u u) {false_body})))\n\
             (check-sat)\n",
            false_body = if seed & 1 == 0 {
                "(not (= u v))"
            } else {
                "(< u v)"
            }
        );
        let mut valid_script = parse_script(&valid).expect("parse generated valid universal");
        let valid_assertions = valid_script.assertions.clone();
        let valid_report = produce_evidence(
            &mut valid_script.arena,
            &valid_assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("produce generated valid result");
        assert!(
            !matches!(
                valid_report.evidence,
                Evidence::UnsatClosedUniversalCounterexample(_)
            ),
            "valid universal received a counterexample at seed {seed}: {valid}"
        );
        let valid_oracle = Solver::new();
        valid_oracle.set_params(&params);
        valid_oracle.from_string(valid.as_str());
        assert_eq!(
            valid_oracle.check(),
            SatResult::Sat,
            "Z3 rejected valid universal seed {seed}: {valid}"
        );
    }
}
