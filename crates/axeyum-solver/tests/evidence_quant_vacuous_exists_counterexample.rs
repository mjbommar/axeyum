//! ADR-0128 checked counterexamples below vacuous existential prefixes.
#![cfg(feature = "full")]

use std::time::Duration;

use axeyum_ir::{Sort, TermArena, Value};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, Evidence, SolverConfig, SolverError, VACUOUS_EXISTS_COUNTEREXAMPLE_BINDER_CAP,
    VACUOUS_EXISTS_COUNTEREXAMPLE_NODE_CAP, VacuousExistsUniversalCounterexampleCertificate,
    check_vacuous_exists_universal_counterexample, produce_evidence, solve,
};

const TARGET: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress0__quantifiers__issue2031-bv-var-elim.smt2"
);

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(2))
}

fn target_certificate() -> (
    axeyum_smtlib::Script,
    Vec<axeyum_ir::TermId>,
    VacuousExistsUniversalCounterexampleCertificate,
) {
    let mut script = parse_script(TARGET).expect("target parses");
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config())
        .expect("target produces evidence");
    let Evidence::UnsatVacuousExistsUniversalCounterexample(certificate) = report.evidence else {
        panic!(
            "expected ADR-0128 evidence, got {}",
            report.evidence.kind_label()
        );
    };
    assert!(report.trusted_steps.is_empty());
    assert!(check_vacuous_exists_universal_counterexample(
        &script.arena,
        &assertions,
        &certificate
    ));
    (script, assertions, certificate)
}

#[test]
fn public_bv_variable_elimination_row_has_checked_evidence() {
    let (mut script, assertions, certificate) = target_certificate();
    assert_eq!(certificate.assertion, assertions[0]);
    assert_eq!(certificate.bindings.len(), 2);

    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    assert_eq!(
        report.evidence.kind_label(),
        "unsat-vacuous-exists-universal-counterexample"
    );
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(matches!(
        solve(&mut script.arena, &assertions, &config()).unwrap(),
        CheckResult::Unsat
    ));

    let mut bool_script = parse_script(
        "(set-logic BV) (assert (exists ((e Bool)) (forall ((u Bool)) u))) (check-sat)",
    )
    .expect("mixed Bool prefix parses");
    let bool_assertions = bool_script.assertions.clone();
    let bool_report = produce_evidence(&mut bool_script.arena, &bool_assertions, &config())
        .expect("mixed Bool prefix produces evidence");
    assert!(matches!(
        bool_report.evidence,
        Evidence::UnsatVacuousExistsUniversalCounterexample(_)
    ));
    assert!(
        bool_report
            .evidence
            .check(&bool_script.arena, &bool_assertions)
            .unwrap()
    );
}

#[test]
fn binding_and_source_mutations_fail_closed() {
    let (mut script, assertions, certificate) = target_certificate();

    let mut wrong_value = certificate.clone();
    let Value::Bv { width, value } = wrong_value.bindings[0].1 else {
        panic!("target binding is a bit-vector")
    };
    wrong_value.bindings[0].1 = Value::Bv {
        width,
        value: value.wrapping_add(1) & ((1u128 << width) - 1),
    };
    assert!(!check_vacuous_exists_universal_counterexample(
        &script.arena,
        &assertions,
        &wrong_value
    ));

    let mut wrong_sort = certificate.clone();
    wrong_sort.bindings[0].1 = Value::Bool(false);
    assert!(!check_vacuous_exists_universal_counterexample(
        &script.arena,
        &assertions,
        &wrong_sort
    ));

    let mut reordered = certificate.clone();
    reordered.bindings.swap(0, 1);
    assert!(!check_vacuous_exists_universal_counterexample(
        &script.arena,
        &assertions,
        &reordered
    ));

    let mut missing = certificate.clone();
    missing.bindings.pop();
    assert!(!check_vacuous_exists_universal_counterexample(
        &script.arena,
        &assertions,
        &missing
    ));

    let mut extra = certificate.clone();
    extra.bindings.push(extra.bindings[0].clone());
    assert!(!check_vacuous_exists_universal_counterexample(
        &script.arena,
        &assertions,
        &extra
    ));

    let mut stale = certificate;
    stale.assertion = script.arena.bool_const(true);
    assert!(!check_vacuous_exists_universal_counterexample(
        &script.arena,
        &assertions,
        &stale
    ));
}

#[test]
fn nonvacuous_open_reversed_nested_and_function_forms_decline() {
    for text in [
        "(set-logic BV) (assert (exists ((e (_ BitVec 4))) \
         (forall ((u (_ BitVec 4))) (= e e)))) (check-sat)",
        "(set-logic BV) (declare-fun a () (_ BitVec 4)) \
         (assert (exists ((e (_ BitVec 4))) \
           (forall ((u (_ BitVec 4))) (= u a)))) (check-sat)",
        "(set-logic BV) (assert (forall ((u (_ BitVec 4))) \
           (exists ((e (_ BitVec 4))) (= u e)))) (check-sat)",
        "(set-logic BV) (assert (exists ((e (_ BitVec 4))) \
           (forall ((u (_ BitVec 4))) \
             (exists ((v (_ BitVec 4))) (= u v))))) (check-sat)",
        "(set-logic UFBV) (declare-fun f ((_ BitVec 4)) (_ BitVec 4)) \
         (assert (exists ((e (_ BitVec 4))) \
           (forall ((u (_ BitVec 4))) (= (f u) u)))) (check-sat)",
        "(set-logic BV) (assert (exists ((e (_ BitVec 4))) (= e e))) (check-sat)",
    ] {
        let mut script = parse_script(text).expect("declined source parses");
        let assertions = script.assertions.clone();
        match produce_evidence(&mut script.arena, &assertions, &config()) {
            Ok(report) => assert!(
                !matches!(
                    report.evidence,
                    Evidence::UnsatVacuousExistsUniversalCounterexample(_)
                ),
                "out-of-contract source received ADR-0128 evidence: {text}"
            ),
            Err(SolverError::Unsupported(_)) => {}
            Err(error) => panic!("unexpected decline error for {text}: {error}"),
        }
    }
}

#[test]
fn satisfiable_vacuous_neighbor_is_not_refuted() {
    let text = "(set-logic BV) \
        (assert (exists ((e (_ BitVec 4))) \
          (forall ((u (_ BitVec 4))) (= (bvadd u (_ bv3 4)) \
                                          (bvadd u (_ bv3 4)))))) \
        (check-sat)";
    let mut script = parse_script(text).unwrap();
    let assertions = script.assertions.clone();
    let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
    assert!(!matches!(
        report.evidence,
        Evidence::UnsatVacuousExistsUniversalCounterexample(_)
    ));
    assert!(!matches!(
        solve(&mut script.arena, &assertions, &config()).unwrap(),
        CheckResult::Unsat
    ));
}

#[test]
fn binder_and_source_node_caps_fail_closed() {
    let mut arena = TermArena::new();
    let mut body = arena.bool_const(false);
    let mut bindings = Vec::new();
    for index in 0..VACUOUS_EXISTS_COUNTEREXAMPLE_BINDER_CAP - 1 {
        let binder = arena
            .declare(&format!("cap_universal_{index}"), Sort::Bool)
            .unwrap();
        bindings.push((binder, Value::Bool(false)));
        body = arena.forall(binder, body).unwrap();
    }
    bindings.reverse();
    let existential = arena.declare("cap_existential", Sort::Bool).unwrap();
    let assertion = arena.exists(existential, body).unwrap();
    let exact_binders = VacuousExistsUniversalCounterexampleCertificate {
        assertion,
        bindings: bindings.clone(),
    };
    assert!(check_vacuous_exists_universal_counterexample(
        &arena,
        &[assertion],
        &exact_binders
    ));

    let extra = arena.declare("cap_universal_extra", Sort::Bool).unwrap();
    body = arena.forall(extra, body).unwrap();
    bindings.insert(0, (extra, Value::Bool(false)));
    let assertion = arena.exists(existential, body).unwrap();
    let over_binders = VacuousExistsUniversalCounterexampleCertificate {
        assertion,
        bindings,
    };
    assert!(!check_vacuous_exists_universal_counterexample(
        &arena,
        &[assertion],
        &over_binders
    ));

    let mut arena = TermArena::new();
    let universal = arena.declare("node_universal", Sort::BitVec(16)).unwrap();
    let universal_term = arena.var(universal);
    let mut body = arena.bool_const(false);
    for index in 0..=VACUOUS_EXISTS_COUNTEREXAMPLE_NODE_CAP {
        let constant = arena.bv_const(16, index as u128).unwrap();
        let equality = arena.eq(universal_term, constant).unwrap();
        body = arena.or(body, equality).unwrap();
    }
    let quantified = arena.forall(universal, body).unwrap();
    let existential = arena.declare("node_existential", Sort::Bool).unwrap();
    let assertion = arena.exists(existential, quantified).unwrap();
    let over_nodes = VacuousExistsUniversalCounterexampleCertificate {
        assertion,
        bindings: vec![(
            universal,
            Value::Bv {
                width: 16,
                value: 0,
            },
        )],
    };
    assert!(!check_vacuous_exists_universal_counterexample(
        &arena,
        &[assertion],
        &over_nodes
    ));

    let mut arena = TermArena::new();
    let repeated = arena.declare("repeated", Sort::Bool).unwrap();
    let false_body = arena.bool_const(false);
    let universal = arena.forall(repeated, false_body).unwrap();
    let assertion = arena.exists(repeated, universal).unwrap();
    let duplicate_binder = VacuousExistsUniversalCounterexampleCertificate {
        assertion,
        bindings: vec![(repeated, Value::Bool(false))],
    };
    assert!(!check_vacuous_exists_universal_counterexample(
        &arena,
        &[assertion],
        &duplicate_binder
    ));
}

#[cfg(feature = "z3")]
#[test]
fn generated_vacuous_prefix_cases_agree_with_direct_z3() {
    use z3::{Params, SatResult, Solver};

    for seed in 0u32..64 {
        let width = seed % 8 + 2;
        let mask = (1u128 << width) - 1;
        let addend = u128::from(seed.wrapping_mul(17)) & mask;
        let target = u128::from(seed.wrapping_mul(29).wrapping_add(3)) & mask;
        let unsat = format!(
            "(set-logic BV) \
             (assert (exists ((e (_ BitVec {width}))) \
               (forall ((u (_ BitVec {width}))) \
                 (not (= (bvadd u (_ bv{addend} {width})) \
                         (_ bv{target} {width})))))) (check-sat)"
        );
        let sat = format!(
            "(set-logic BV) \
             (assert (exists ((e (_ BitVec {width}))) \
               (forall ((u (_ BitVec {width}))) \
                 (= (bvadd u (_ bv{addend} {width})) \
                    (bvadd u (_ bv{addend} {width})))))) (check-sat)"
        );

        for (text, expected) in [(unsat, SatResult::Unsat), (sat, SatResult::Sat)] {
            let mut script = parse_script(&text).expect("generated source parses");
            let assertions = script.assertions.clone();
            let report = produce_evidence(&mut script.arena, &assertions, &config()).unwrap();
            let axeyum = match &report.evidence {
                Evidence::UnsatVacuousExistsUniversalCounterexample(_) => {
                    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
                    SatResult::Unsat
                }
                Evidence::Sat(_) => SatResult::Sat,
                other => panic!("unexpected generated evidence: {}", other.kind_label()),
            };

            let mut params = Params::new();
            params.set_u32("timeout", 2_000);
            let oracle = Solver::new();
            oracle.set_params(&params);
            oracle.from_string(text.as_str());
            let z3 = oracle.check();
            assert_eq!(z3, expected, "unexpected oracle result: {text}");
            assert_eq!(axeyum, z3, "axeyum/Z3 disagreement: {text}");
            assert_eq!(
                matches!(
                    report.evidence,
                    Evidence::UnsatVacuousExistsUniversalCounterexample(_)
                ),
                expected == SatResult::Unsat,
                "certificate polarity mismatch: {text}"
            );
        }
    }
}
