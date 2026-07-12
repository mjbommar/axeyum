//! ADR-0097: checked evidence for positive-slope affine-growth universals.

use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, Evidence, SolverConfig, produce_evidence, prove_quantified_unsat_via_egraph,
    prove_unsat_by_ematching, solve,
};

const REPAIR_CONST_NTERM: &str = include_str!(
    "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__repair-const-nterm.smt2"
);

#[test]
fn repair_const_nterm_carries_checked_affine_growth_evidence() {
    let mut script = parse_script(REPAIR_CONST_NTERM).expect("parse repair-const-nterm");
    let assertions = script.assertions.clone();
    assert_eq!(
        solve(&mut script.arena, &assertions, &SolverConfig::default()).expect("solve target"),
        CheckResult::Unsat
    );

    let report =
        produce_evidence(&mut script.arena, &assertions, &SolverConfig::default()).unwrap();
    let Evidence::UnsatIntAffineGrowth(cert) = &report.evidence else {
        panic!("expected affine-growth evidence, got {:?}", report.evidence);
    };
    assert_eq!(cert.coefficient, 3);
    assert_eq!(report.evidence.kind_label(), "unsat-int-affine-growth");
    assert!(report.evidence.is_certified());
    assert!(report.evidence.check(&script.arena, &assertions).unwrap());
    assert!(report.trusted_steps.is_empty());
}

#[test]
fn tampered_affine_growth_certificate_is_rejected() {
    let mut script = parse_script(REPAIR_CONST_NTERM).expect("parse repair-const-nterm");
    let assertions = script.assertions.clone();
    let report =
        produce_evidence(&mut script.arena, &assertions, &SolverConfig::default()).unwrap();
    let Evidence::UnsatIntAffineGrowth(mut cert) = report.evidence else {
        panic!("expected affine-growth evidence");
    };
    cert.coefficient = 2;
    assert!(
        !Evidence::UnsatIntAffineGrowth(cert)
            .check(&script.arena, &assertions)
            .unwrap()
    );
}

#[test]
fn satisfiable_binder_dependent_near_miss_is_not_certified() {
    let text = "(set-logic LIA) (declare-fun p () Int) (declare-fun a () Int) \
        (assert (forall ((x Int)) \
          (not (>= (- x (ite (= x p) a x)) 1)))) (check-sat)";
    let mut script = parse_script(text).unwrap();
    let assertions = script.assertions.clone();
    let report =
        produce_evidence(&mut script.arena, &assertions, &SolverConfig::default()).unwrap();
    assert!(
        !matches!(report.evidence, Evidence::UnsatIntAffineGrowth(_)),
        "binder-dependent else branch must not receive ADR-0097 evidence"
    );
    assert!(
        !matches!(
            solve(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        ),
        "the near miss is satisfiable with a=p"
    );
}

#[test]
fn five_binder_growth_near_miss_fallbacks_terminate() {
    let text = "(set-logic LIA) (declare-fun p () Int) (declare-fun a () Int) \
        (assert (forall ((x0 Int) (x1 Int) (x2 Int) (x3 Int) (x4 Int)) \
          (not (>= (- x4 (ite (= x4 (+ p 2)) (+ a 1) x4)) 1)))) (check-sat)";
    let mut script = parse_script(text).unwrap();
    let assertions = script.assertions.clone();
    let result = prove_quantified_unsat_via_egraph(
        &mut script.arena,
        &assertions,
        &SolverConfig::default().with_timeout(std::time::Duration::from_secs(2)),
    )
    .unwrap();
    assert!(!matches!(result, CheckResult::Unsat));
    let legacy = prove_unsat_by_ematching(
        &mut script.arena,
        &assertions,
        &SolverConfig::default().with_timeout(std::time::Duration::from_secs(2)),
    )
    .unwrap();
    assert!(!matches!(legacy, CheckResult::Unsat));
}

#[cfg(feature = "z3")]
#[test]
fn affine_growth_parameter_sweep_agrees_with_z3() {
    use std::time::Duration;

    use z3::{Params, SatResult, Solver};

    let smt_int = |value: i128| {
        if value < 0 {
            format!("(- {})", value.unsigned_abs())
        } else {
            value.to_string()
        }
    };

    for seed in 0i128..64 {
        let coefficient = seed % 7 + 1;
        let pivot_offset = seed % 5 - 2;
        let then_offset = seed % 9 - 4;
        let else_offset = seed % 11 - 5;
        let threshold_offset = seed % 13 - 6;
        let pivot_offset = smt_int(pivot_offset);
        let then_offset = smt_int(then_offset);
        let else_offset = smt_int(else_offset);
        let threshold_offset = smt_int(threshold_offset);
        let binder_count = seed % 10 + 1;
        let binders = (0..binder_count)
            .map(|index| format!("(x{index} Int)"))
            .collect::<Vec<_>>()
            .join(" ");
        let active = format!("x{}", seed % binder_count);
        let text = format!(
            "(set-logic LIA)\n\
             (declare-fun p () Int)\n\
             (declare-fun a () Int)\n\
             (declare-fun b () Int)\n\
             (declare-fun t () Int)\n\
             (assert (forall ({binders})\n\
               (not (>= (- (* {coefficient} {active})\n\
                 (ite (= {active} (+ p {pivot_offset}))\n\
                      (+ a {then_offset}) (+ b {else_offset})))\n\
                 (+ t {threshold_offset})))))\n\
             (check-sat)\n"
        );

        let mut script = parse_script(&text).expect("generated affine-growth parse");
        let assertions = script.assertions.clone();
        let axeyum = solve(
            &mut script.arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("generated affine-growth solve");

        let oracle = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", 2_000);
        oracle.set_params(&params);
        oracle.from_string(text.as_str());
        let z3 = oracle.check();
        assert_eq!(
            z3,
            SatResult::Unsat,
            "Z3 did not refute seed {seed}: {text}"
        );
        assert_eq!(
            axeyum,
            CheckResult::Unsat,
            "axeyum/Z3 disagreement at seed {seed}: {text}"
        );

        // Load-bearing negative: when the else branch is the binder itself,
        // the free parameters can make the universal true (`a := pivot`). The
        // ADR-0097 matcher must decline rather than apply its growth theorem.
        let near_miss = format!(
            "(set-logic LIA)\n\
             (declare-fun p () Int)\n\
             (declare-fun a () Int)\n\
             (assert (forall ({binders})\n\
               (not (>= (- {active}\n\
                 (ite (= {active} (+ p {pivot_offset}))\n\
                      (+ a {then_offset}) {active})) 1))))\n\
             (check-sat)\n"
        );
        let mut near_script = parse_script(&near_miss).expect("generated near-miss parse");
        let near_assertions = near_script.assertions.clone();
        let near_axeyum = solve(
            &mut near_script.arena,
            &near_assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("generated near-miss solve");
        let near_oracle = Solver::new();
        near_oracle.set_params(&params);
        near_oracle.from_string(near_miss.as_str());
        assert_eq!(
            near_oracle.check(),
            SatResult::Sat,
            "Z3 did not find the expected near-miss model at seed {seed}"
        );
        assert!(
            !matches!(near_axeyum, CheckResult::Unsat),
            "wrong UNSAT on satisfiable binder-dependent seed {seed}: {near_miss}"
        );
    }
}
