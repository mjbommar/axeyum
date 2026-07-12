//! ADR-0122: checked outer-BV witnesses for vacuous guarded alternation.

use std::time::Duration;

use axeyum_ir::{Op, Sort, TermArena, TermNode, Value, WideUint};
use axeyum_smtlib::{ScriptCommand, parse_script};
use axeyum_solver::{
    CheckResult, Evidence, QuantifiedGuardSatCertificate, SolverConfig, check_model,
    check_quantified_guard_sat, produce_evidence, solve,
};

const ISSUE_5365: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__issue5365-nqe.smt2"
);

fn assertions(script: &axeyum_smtlib::Script) -> Vec<axeyum_ir::TermId> {
    script
        .commands
        .iter()
        .filter_map(|command| match command {
            ScriptCommand::Assert(term) => Some(*term),
            _ => None,
        })
        .collect()
}

fn config() -> SolverConfig {
    SolverConfig::new().with_timeout(Duration::from_secs(2))
}

#[test]
fn issue5365_outer_guard_witness_is_sat_and_evidence_replays() {
    let script = parse_script(ISSUE_5365).expect("parse issue5365");
    let assertions = assertions(&script);
    let original_terms = script.arena.len();
    let mut solving_arena = script.arena.clone();
    let result = solve(&mut solving_arena, &assertions, &config()).expect("solve issue5365");
    let CheckResult::Sat(model) = result else {
        panic!("issue5365 must be Sat by a nonzero outer witness, got {result:?}");
    };
    assert_eq!(model.quantified_guard_sat_certificates().count(), 1);
    assert!(check_model(&script.arena, &assertions, &model).expect("model replay"));
    assert_eq!(script.arena.len(), original_terms);

    let mut evidence_arena = script.arena.clone();
    let report = produce_evidence(&mut evidence_arena, &assertions, &config())
        .expect("produce issue5365 evidence");
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert!(report.evidence.is_certified());
    assert!(
        report
            .evidence
            .check(&script.arena, &assertions)
            .expect("evidence replay")
    );
    assert!(report.trusted_steps.is_empty());
}

#[test]
fn guard_operand_orders_constants_and_wide_widths_are_checked() {
    for (width, constant, swapped) in [
        (1u32, 1u128, false),
        (8, 5, true),
        (32, 0, false),
        (129, 7, true),
    ] {
        let equality = if swapped {
            format!("(= a (_ bv{constant} {width}))")
        } else {
            format!("(= (_ bv{constant} {width}) a)")
        };
        let text = format!(
            "(set-logic BV)\n\
             (assert (exists ((a (_ BitVec {width})))\n\
               (forall ((p Bool)) (=> {equality} false))))\n\
             (check-sat)\n"
        );
        let mut script = parse_script(&text).expect("parse guarded width theorem");
        let assertions = assertions(&script);
        let result =
            solve(&mut script.arena, &assertions, &config()).expect("solve guarded theorem");
        let CheckResult::Sat(model) = result else {
            panic!("guarded width {width} theorem must be Sat, got {result:?}");
        };
        assert_eq!(model.quantified_guard_sat_certificates().count(), 1);
        assert!(check_model(&script.arena, &assertions, &model).expect("width model replay"));
    }
}

#[test]
fn tampered_guard_certificates_fail_closed() {
    let mut script = parse_script(ISSUE_5365).expect("parse issue5365");
    let assertions = assertions(&script);
    let CheckResult::Sat(model) =
        solve(&mut script.arena, &assertions, &config()).expect("solve issue5365 for certificate")
    else {
        panic!("issue5365 should be Sat");
    };
    let cert = model
        .quantified_guard_sat_certificate(assertions[0])
        .expect("guard certificate")
        .clone();

    let mut equal_to_guard = cert.clone();
    equal_to_guard.witness = Value::Bv {
        width: 32,
        value: 0,
    };
    let mut wrong_width = cert.clone();
    wrong_width.witness = Value::Bv {
        width: 31,
        value: 1,
    };
    let foreign = script
        .arena
        .declare("foreign_outer", Sort::BitVec(32))
        .expect("declare foreign outer");
    let mut wrong_binder = cert.clone();
    wrong_binder.existential = foreign;
    let unrelated = script.arena.bool_const(true);
    let mut stale = cert.clone();
    stale.assertion = unrelated;

    for (name, candidate) in [
        ("guard-equal witness", equal_to_guard),
        ("wrong-width witness", wrong_width),
        ("wrong binder", wrong_binder),
        ("stale assertion", stale),
    ] {
        assert!(
            !check_quantified_guard_sat(&script.arena, assertions[0], &candidate),
            "tampered {name} certificate must fail"
        );
    }

    let mut tampered_model = model.clone();
    tampered_model.set_quantified_guard_sat_certificate(QuantifiedGuardSatCertificate {
        assertion: assertions[0],
        existential: cert.existential,
        witness: Value::Bv {
            width: 32,
            value: 0,
        },
    });
    assert!(!check_model(&script.arena, &assertions, &tampered_model).expect("tampered replay"));

    let mut extra_model = model;
    extra_model.set_quantified_guard_sat_certificate(QuantifiedGuardSatCertificate {
        assertion: unrelated,
        existential: cert.existential,
        witness: Value::Bv {
            width: 32,
            value: 1,
        },
    });
    assert!(!check_model(&script.arena, &assertions, &extra_model).expect("extraneous replay"));
}

#[test]
fn changed_guard_shapes_and_polarity_are_rejected() {
    let cases = [
        ("negative polarity", "(=> (not (= (_ bv0 8) a)) false)"),
        ("disjunction", "(or (= (_ bv0 8) a) false)"),
        ("nonconstant guard", "(=> (= b a) false)"),
    ];
    for (name, matrix) in cases {
        let text = format!(
            "(set-logic BV)\n\
             (assert (exists ((a (_ BitVec 8)))\n\
               (forall ((b (_ BitVec 8))) {matrix})))\n\
             (check-sat)\n"
        );
        let script = parse_script(&text).expect("parse guard near miss");
        let assertion = assertions(&script)[0];
        let existential = match script.arena.node(assertion) {
            TermNode::App {
                op: Op::Exists(symbol),
                ..
            } => *symbol,
            _ => panic!("outer exists"),
        };
        let cert = QuantifiedGuardSatCertificate {
            assertion,
            existential,
            witness: Value::Bv { width: 8, value: 1 },
        };
        assert!(
            !check_quantified_guard_sat(&script.arena, assertion, &cert),
            "{name} must stay outside the exact checker"
        );
    }
}

#[test]
fn missing_prefix_and_reused_binders_are_rejected() {
    let no_nested = r"
        (set-logic BV)
        (assert (exists ((a (_ BitVec 8)))
          (=> (= (_ bv0 8) a) false)))
        (check-sat)
    ";
    let script = parse_script(no_nested).expect("parse no-prefix theorem");
    let assertion = assertions(&script)[0];
    let existential = match script.arena.node(assertion) {
        TermNode::App {
            op: Op::Exists(symbol),
            ..
        } => *symbol,
        _ => panic!("outer exists"),
    };
    let cert = QuantifiedGuardSatCertificate {
        assertion,
        existential,
        witness: Value::Bv { width: 8, value: 1 },
    };
    assert!(!check_quantified_guard_sat(&script.arena, assertion, &cert));

    let mut arena = TermArena::new();
    let a = arena.declare("a", Sort::BitVec(8)).unwrap();
    let av = arena.var(a);
    let zero = arena.bv_const(8, 0).unwrap();
    let guard = arena.eq(zero, av).unwrap();
    let falsity = arena.bool_const(false);
    let matrix = arena.implies(guard, falsity).unwrap();
    let reused = arena.forall(a, matrix).unwrap();
    let assertion = arena.exists(a, reused).unwrap();
    let cert = QuantifiedGuardSatCertificate {
        assertion,
        existential: a,
        witness: Value::Bv { width: 8, value: 1 },
    };
    assert!(!check_quantified_guard_sat(&arena, assertion, &cert));

    let wide = QuantifiedGuardSatCertificate {
        assertion,
        existential: a,
        witness: Value::WideBv(WideUint::from_u128(1, 129)),
    };
    assert!(!check_quantified_guard_sat(&arena, assertion, &wide));
}
