//! ADR-0099: checked evidence for the exact nested-XOR quantifier refutation.

use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, Evidence, SolverConfig, int_nested_xor_refutation, produce_evidence, solve,
};

const ISSUE_4433: &str = include_str!(
    "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__issue4433-nqe.smt2"
);

#[test]
fn issue4433_carries_checked_nested_xor_evidence() {
    let mut script = parse_script(ISSUE_4433).expect("parse issue4433");
    let assertions = script.assertions.clone();
    assert_eq!(
        solve(
            &mut script.arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("solve issue4433"),
        CheckResult::Unsat
    );

    let report = produce_evidence(
        &mut script.arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(2)),
    )
    .expect("produce issue4433 evidence");
    let Evidence::UnsatIntNestedXor(cert) = &report.evidence else {
        panic!("expected nested-XOR evidence, got {:?}", report.evidence);
    };
    assert_eq!(cert.active_pivot, 0);
    assert_eq!(cert.passive_pivot, 0);
    assert_eq!(cert.nested_pivot, 0);
    assert_eq!((cert.then_value, cert.else_value), (0, 1));
    assert_eq!(report.evidence.kind_label(), "unsat-int-nested-xor");
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
}

#[test]
fn tampered_nested_xor_certificate_is_rejected() {
    let mut script = parse_script(ISSUE_4433).expect("parse issue4433");
    let assertions = script.assertions.clone();
    let report =
        produce_evidence(&mut script.arena, &assertions, &SolverConfig::default()).unwrap();
    let Evidence::UnsatIntNestedXor(mut cert) = report.evidence else {
        panic!("expected nested-XOR evidence");
    };
    cert.then_value = cert.else_value;
    assert!(
        !Evidence::UnsatIntNestedXor(cert)
            .check(&script.arena, &assertions)
            .unwrap()
    );
}

#[test]
fn nested_xor_child_and_equality_swaps_are_certified() {
    let text = r"
        (set-logic LIA)
        (assert (forall ((a Int) (b Int))
          (xor
            (forall ((c Int))
              (= (ite (= 3 c) 7 (- 2))
                 (ite (= 5 a) 7 (- 2))))
            (xor (= (- 4) b) (= 5 a)))))
        (check-sat)
    ";
    let mut script = parse_script(text).expect("parse swapped nested-XOR theorem");
    let assertions = script.assertions.clone();
    let cert = int_nested_xor_refutation(&script.arena, &assertions)
        .expect("swapped theorem must certify");
    assert_eq!(cert.active_pivot, 5);
    assert_eq!(cert.passive_pivot, -4);
    assert_eq!(cert.nested_pivot, 3);
    assert_eq!((cert.then_value, cert.else_value), (7, -2));
    assert_eq!(
        solve(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat
    );
}

#[test]
fn satisfiable_context_near_misses_are_not_refuted_or_certified() {
    for text in [
        "(set-logic LIA) (assert (not (forall ((a Int) (b Int)) \
         (xor (xor (= a 0) (= b 0)) (forall ((c Int)) \
         (= (ite (= a 0) 0 1) (ite (= c 0) 0 1))))))) (check-sat)",
        "(set-logic LIA) (assert (forall ((a Int) (b Int)) \
         (or true (xor (xor (= a 0) (= b 0)) (forall ((c Int)) \
         (= (ite (= a 0) 0 1) (ite (= c 0) 0 1))))))) (check-sat)",
    ] {
        let mut script = parse_script(text).expect("parse satisfiable near miss");
        let assertions = script.assertions.clone();
        assert!(int_nested_xor_refutation(&script.arena, &assertions).is_none());
        let result = solve(
            &mut script.arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        );
        assert!(
            !matches!(result, Ok(CheckResult::Unsat)),
            "satisfiable context must not be refuted: {text}"
        );
    }
}

#[cfg(feature = "z3")]
#[test]
#[allow(clippy::too_many_lines)]
fn nested_xor_parameter_sweep_agrees_with_z3() {
    use z3::{Params, SatResult, Solver};

    let smt_int = |value: i64| {
        if value < 0 {
            format!("(- {})", value.unsigned_abs())
        } else {
            value.to_string()
        }
    };

    for seed in 0i64..64 {
        let pa = smt_int(seed % 11 - 5);
        let pb = smt_int(seed % 13 - 6);
        let pc = smt_int(seed % 17 - 8);
        let then_value = smt_int(seed % 19 - 9);
        let else_value = smt_int(seed % 19 - 8);
        let a_eq = if seed & 1 == 0 {
            format!("(= a {pa})")
        } else {
            format!("(= {pa} a)")
        };
        let b_eq = if seed & 2 == 0 {
            format!("(= b {pb})")
        } else {
            format!("(= {pb} b)")
        };
        let c_eq = if seed & 4 == 0 {
            format!("(= c {pc})")
        } else {
            format!("(= {pc} c)")
        };
        let selector = if seed & 8 == 0 {
            format!("(xor {a_eq} {b_eq})")
        } else {
            format!("(xor {b_eq} {a_eq})")
        };
        let active = format!("(ite {a_eq} {then_value} {else_value})");
        let nested = format!("(ite {c_eq} {then_value} {else_value})");
        let equality = if seed & 16 == 0 {
            format!("(= {active} {nested})")
        } else {
            format!("(= {nested} {active})")
        };
        let inner = format!("(forall ((c Int)) {equality})");
        let body = if seed & 32 == 0 {
            format!("(xor {selector} {inner})")
        } else {
            format!("(xor {inner} {selector})")
        };
        let text = format!(
            "(set-logic LIA)\n\
             (assert (forall ((a Int) (b Int)) {body}))\n\
             (check-sat)\n"
        );

        let mut script = parse_script(&text).expect("parse generated nested-XOR theorem");
        let assertions = script.assertions.clone();
        assert!(
            int_nested_xor_refutation(&script.arena, &assertions).is_some(),
            "checker declined seed {seed}: {text}"
        );
        assert_eq!(
            solve(
                &mut script.arena,
                &assertions,
                &SolverConfig::new().with_timeout(Duration::from_secs(2)),
            )
            .expect("solve generated nested-XOR theorem"),
            CheckResult::Unsat,
            "axeyum failed seed {seed}: {text}"
        );

        let oracle = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", 2_000);
        oracle.set_params(&params);
        oracle.from_string(text.as_str());
        assert_eq!(
            oracle.check(),
            SatResult::Unsat,
            "Z3 disagreed on positive seed {seed}: {text}"
        );

        let sat_text = format!(
            "(set-logic LIA)\n\
             (assert (forall ((a Int) (b Int)) (or true {body})))\n\
             (check-sat)\n"
        );
        let mut sat_script = parse_script(&sat_text).expect("parse generated satisfiable wrapper");
        let sat_assertions = sat_script.assertions.clone();
        assert!(int_nested_xor_refutation(&sat_script.arena, &sat_assertions).is_none());
        let sat_axeyum = solve(
            &mut sat_script.arena,
            &sat_assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        );
        assert!(
            !matches!(sat_axeyum, Ok(CheckResult::Unsat)),
            "axeyum returned wrong Unsat on seed {seed}: {sat_text}"
        );
        let sat_oracle = Solver::new();
        sat_oracle.set_params(&params);
        sat_oracle.from_string(sat_text.as_str());
        assert_eq!(
            sat_oracle.check(),
            SatResult::Sat,
            "Z3 did not validate satisfiable seed {seed}: {sat_text}"
        );
    }
}
