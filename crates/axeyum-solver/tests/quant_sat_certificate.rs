//! ADR-0096/0098/0121: replayable certificates for quantified SAT.

use std::time::Duration;

use axeyum_ir::{Rational, Sort, TermArena};
use axeyum_smtlib::{ScriptCommand, parse_script};
use axeyum_solver::{
    AffineSkolemWitness, CheckResult, Evidence, QuantifiedSkolemSatCertificate, SolverConfig,
    check_model, check_quantified_skolem_sat, produce_evidence, solve,
};

const ISSUE_4849: &str = include_str!(
    "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__issue4849-nqe.smt2"
);
const ISSUE_4328: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__issue4328-nqe.smt2"
);
const SYGUS_INFER_NESTED: &str = include_str!(
    "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__sygus-infer-nested.smt2"
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

#[test]
fn issue4849_identity_skolem_is_sat_and_replays() {
    let mut script = parse_script(ISSUE_4849).expect("parse issue4849");
    let assertions = assertions(&script);
    let result = solve(
        &mut script.arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(10)),
    )
    .expect("solve issue4849");
    let CheckResult::Sat(model) = result else {
        panic!("issue4849 must be Sat by identity Skolem, got {result:?}");
    };
    assert_eq!(model.quantified_sat_certificates().count(), 1);
    assert!(check_model(&script.arena, &assertions, &model).expect("model check"));

    let report = produce_evidence(
        &mut script.arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(10)),
    )
    .expect("produce quantified Sat evidence");
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert!(report.evidence.is_certified());
    assert!(
        report
            .evidence
            .check(&script.arena, &assertions)
            .expect("evidence check")
    );
    assert!(report.trusted_steps.is_empty());
}

#[test]
fn issue4328_bv_identity_skolem_is_sat_and_replays() {
    let script = parse_script(ISSUE_4328).expect("parse issue4328");
    let assertions = assertions(&script);
    let original_term_count = script.arena.len();
    let mut solving_arena = script.arena.clone();
    let result = solve(
        &mut solving_arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(10)),
    )
    .expect("solve issue4328");
    let CheckResult::Sat(model) = result else {
        panic!("issue4328 must be Sat by BV identity Skolem, got {result:?}");
    };
    assert_eq!(model.quantified_sat_certificates().count(), 1);
    assert!(check_model(&script.arena, &assertions, &model).expect("model check"));
    assert_eq!(
        script.arena.len(),
        original_term_count,
        "certificate replay must not mutate the caller's arena"
    );

    let mut evidence_arena = script.arena.clone();
    let report = produce_evidence(
        &mut evidence_arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(10)),
    )
    .expect("produce quantified BV Sat evidence");
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert!(report.evidence.is_certified());
    assert!(
        report
            .evidence
            .check(&script.arena, &assertions)
            .expect("evidence check")
    );
    assert!(report.trusted_steps.is_empty());
}

#[test]
fn tampered_bv_identity_recipes_are_rejected() {
    let mut script = parse_script(ISSUE_4328).expect("parse issue4328");
    let assertions = assertions(&script);
    let CheckResult::Sat(model) = solve(
        &mut script.arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(2)),
    )
    .expect("solve issue4328") else {
        panic!("issue4328 should be Sat");
    };
    let cert = model
        .quantified_sat_certificate(assertions[0])
        .expect("BV identity certificate")
        .clone();
    let [(identity, coefficient)] = cert.witness.terms.as_slice() else {
        panic!("BV identity certificate must carry one term");
    };
    assert_eq!(*coefficient, Rational::integer(1));

    let mut variants = Vec::new();
    let mut nonzero_constant = cert.clone();
    nonzero_constant.witness.constant = Rational::integer(1);
    variants.push(("nonzero constant", nonzero_constant));

    let mut nonunit_coefficient = cert.clone();
    nonunit_coefficient.witness.terms[0].1 = Rational::integer(2);
    variants.push(("nonunit coefficient", nonunit_coefficient));

    let composite = script
        .arena
        .bv_not(*identity)
        .expect("same-width composite");
    let mut composite_atom = cert.clone();
    composite_atom.witness.terms = vec![(composite, Rational::integer(1))];
    variants.push(("composite BV atom", composite_atom));

    let foreign = script
        .arena
        .declare("foreign_bv32", Sort::BitVec(32))
        .expect("declare foreign same-width symbol");
    let foreign_term = script.arena.var(foreign);
    let mut foreign_symbol = cert.clone();
    foreign_symbol.witness.terms = vec![(foreign_term, Rational::integer(1))];
    variants.push(("foreign universal", foreign_symbol));

    let wrong_width = script
        .arena
        .declare("foreign_bv31", Sort::BitVec(31))
        .expect("declare wrong-width symbol");
    let wrong_width_term = script.arena.var(wrong_width);
    let mut width_mismatch = cert.clone();
    width_mismatch.witness.terms = vec![(wrong_width_term, Rational::integer(1))];
    variants.push(("width mismatch", width_mismatch));

    for (name, variant) in variants {
        assert!(
            !check_quantified_skolem_sat(&script.arena, assertions[0], &variant),
            "tampered {name} recipe must fail closed"
        );
    }
}

#[test]
fn bv_source_term_skolem_certificate_is_exact_and_source_bound() {
    let mut arena = TermArena::new();
    let a = arena.declare("source_a", Sort::BitVec(32)).unwrap();
    let b = arena.declare("source_b", Sort::BitVec(32)).unwrap();
    let av = arena.var(a);
    let bv = arena.var(b);
    let seven = arena.bv_const(32, 7).unwrap();
    let source_term = arena.bv_add(av, seven).unwrap();
    let body = arena.eq(bv, source_term).unwrap();
    let exists = arena.exists(b, body).unwrap();
    let assertion = arena.forall(a, exists).unwrap();

    let CheckResult::Sat(model) = solve(
        &mut arena,
        &[assertion],
        &SolverConfig::new().with_timeout(Duration::from_secs(2)),
    )
    .expect("solve source-term theorem") else {
        panic!("source-term theorem should be Sat")
    };
    let certificate = model
        .quantified_sat_certificate(assertion)
        .expect("source-term certificate")
        .clone();
    assert_eq!(
        certificate.witness.terms,
        vec![(source_term, Rational::integer(1))]
    );
    assert!(certificate.witness.constant.is_zero());
    assert!(check_quantified_skolem_sat(&arena, assertion, &certificate));

    // Even a well-sorted term over the right universal is not an admissible
    // recipe unless it is literally reachable from the untouched assertion.
    let non_source = arena.bv_not(av).unwrap();
    let mut detached = certificate.clone();
    detached.witness.terms = vec![(non_source, Rational::integer(1))];
    assert!(!check_quantified_skolem_sat(&arena, assertion, &detached));

    // A source-shaped term with an out-of-scope free symbol also fails closed.
    let free = arena
        .declare("source_free", Sort::BitVec(32))
        .expect("declare free symbol");
    let free_term = arena.var(free);
    let out_of_scope = arena.bv_add(av, free_term).unwrap();
    let mut foreign = certificate;
    foreign.witness.terms = vec![(out_of_scope, Rational::integer(1))];
    assert!(!check_quantified_skolem_sat(&arena, assertion, &foreign));
}

#[test]
fn sygus_infer_nested_successor_skolem_is_sat_and_replays() {
    let mut script = parse_script(SYGUS_INFER_NESTED).expect("parse sygus-infer-nested");
    let assertions = assertions(&script);
    let mut solving_arena = script.arena.clone();
    let result = solve(
        &mut solving_arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(10)),
    )
    .expect("solve sygus-infer-nested");
    let CheckResult::Sat(model) = result else {
        panic!("sygus-infer-nested must be Sat by successor Skolem, got {result:?}");
    };
    assert_eq!(model.quantified_sat_certificates().count(), 1);
    assert!(check_model(&script.arena, &assertions, &model).expect("model check"));

    let report = produce_evidence(
        &mut script.arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(10)),
    )
    .expect("produce nested quantified Sat evidence");
    assert!(matches!(report.evidence, Evidence::Sat(_)));
    assert!(report.evidence.is_certified());
    assert!(
        report
            .evidence
            .check(&script.arena, &assertions)
            .expect("evidence check")
    );
    assert!(report.trusted_steps.is_empty());
}

#[test]
fn synthesized_affine_recipe_replays_against_untouched_arena() {
    let input = r"
        (set-logic LIA)
        (assert (forall ((x Int)) (exists ((z Int)) (> z x))))
        (check-sat)
    ";
    let script = parse_script(input).expect("parse strict successor theorem");
    let assertions = assertions(&script);
    let original_term_count = script.arena.len();
    let mut solving_arena = script.arena.clone();
    let CheckResult::Sat(model) = solve(
        &mut solving_arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(2)),
    )
    .expect("solve strict successor theorem") else {
        panic!("strict successor theorem should be Sat");
    };
    assert!(solving_arena.len() > original_term_count);
    assert!(
        check_model(&script.arena, &assertions, &model).expect("untouched-arena model check"),
        "owned affine witness must not retain clone-local term IDs"
    );
}

#[test]
fn guarded_unit_gap_real_successor_is_certified() {
    let input = r"
        (set-logic LRA)
        (assert (forall ((x Real) (y Real))
          (or (<= x (+ y 1))
              (exists ((z Real)) (and (> z y) (< z x))))))
        (check-sat)
    ";
    let mut script = parse_script(input).expect("parse Real unit-gap theorem");
    let assertions = assertions(&script);
    let CheckResult::Sat(model) = solve(
        &mut script.arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(2)),
    )
    .expect("solve Real unit-gap theorem") else {
        panic!("Real unit-gap theorem should receive checked Sat credit");
    };
    assert!(check_model(&script.arena, &assertions, &model).expect("Real model check"));
}

#[test]
fn tampered_nested_successor_certificate_is_rejected() {
    let mut script = parse_script(SYGUS_INFER_NESTED).expect("parse sygus-infer-nested");
    let assertions = assertions(&script);
    let CheckResult::Sat(mut model) =
        solve(&mut script.arena, &assertions, &SolverConfig::default()).expect("solve target")
    else {
        panic!("sygus-infer-nested should be Sat");
    };
    let mut cert = model
        .quantified_sat_certificate(assertions[0])
        .expect("nested certificate")
        .clone();
    cert.witness = AffineSkolemWitness {
        terms: Vec::new(),
        constant: Rational::zero(),
    };
    assert!(!check_quantified_skolem_sat(
        &script.arena,
        assertions[0],
        &cert
    ));
    model.set_quantified_sat_certificate(cert);
    assert!(!check_model(&script.arena, &assertions, &model).expect("tampered model check"));
}

#[test]
fn guarded_unit_gap_near_misses_do_not_receive_sat_credit() {
    let missing_margin = r"
        (set-logic LIA)
        (assert (forall ((x Int) (y Int))
          (or (<= x y)
              (exists ((z Int)) (and (> z y) (< z x))))))
        (check-sat)
    ";
    let negative_polarity = r"
        (set-logic LIA)
        (assert (forall ((x Int) (y Int))
          (not (or (<= x (+ y 1))
                   (exists ((z Int)) (and (> z y) (< z x)))))))
        (check-sat)
    ";
    for (name, input) in [
        ("missing unit margin", missing_margin),
        ("negative polarity", negative_polarity),
    ] {
        let mut script = parse_script(input).expect("parse nested near miss");
        let assertions = assertions(&script);
        let result = solve(
            &mut script.arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("solve nested near miss");
        assert!(
            !matches!(result, CheckResult::Sat(_)),
            "{name} must not receive guarded-unit-gap Sat credit: {result:?}"
        );
    }
}

#[cfg(feature = "z3")]
#[test]
fn guarded_unit_gap_sweep_agrees_with_z3() {
    use z3::{Params, SatResult, Solver};

    let smt_int = |value: i64| {
        if value < 0 {
            format!("(- {})", value.unsigned_abs())
        } else {
            value.to_string()
        }
    };

    for seed in 0i64..64 {
        let (logic, sort) = if seed % 2 == 0 {
            ("LIA", "Int")
        } else {
            ("LRA", "Real")
        };
        let coefficient = seed % 7 + 1;
        let offset = smt_int(seed % 11 - 5);
        let lower = format!("(+ (* {coefficient} y) {offset})");
        let guard = format!("(<= x (+ {lower} 1))");
        let bounds = if seed % 4 < 2 {
            format!("(and (> z {lower}) (< z x))")
        } else {
            format!("(and (< z x) (> z {lower}))")
        };
        let body = if seed % 8 < 4 {
            format!("(or {guard} (exists ((z {sort})) {bounds}))")
        } else {
            format!("(or (exists ((z {sort})) {bounds}) {guard})")
        };
        let text = format!(
            "(set-logic {logic})\n\
             (assert (forall ((x {sort}) (y {sort})) {body}))\n\
             (check-sat)\n"
        );

        let mut script = parse_script(&text).expect("parse generated unit-gap theorem");
        let assertions = assertions(&script);
        let axeyum = solve(
            &mut script.arena,
            &assertions,
            &SolverConfig::new().with_timeout(Duration::from_secs(2)),
        )
        .expect("solve generated unit-gap theorem");
        let CheckResult::Sat(model) = axeyum else {
            panic!("axeyum failed to certify unit-gap seed {seed}: {text}");
        };
        assert!(
            check_model(&script.arena, &assertions, &model).expect("generated model check"),
            "certificate replay failed at seed {seed}: {text}"
        );

        let oracle = Solver::new();
        let mut params = Params::new();
        params.set_u32("timeout", 2_000);
        oracle.set_params(&params);
        oracle.from_string(text.as_str());
        assert_eq!(
            oracle.check(),
            SatResult::Sat,
            "Z3 disagreed on unit-gap seed {seed}: {text}"
        );

        if sort == "Int" {
            let near_miss =
                text.replace(&format!("(<= x (+ {lower} 1))"), &format!("(<= x {lower})"));
            let mut near_script = parse_script(&near_miss).expect("parse generated near miss");
            let near_assertions = near_script.assertions.clone();
            let near_axeyum = solve(
                &mut near_script.arena,
                &near_assertions,
                &SolverConfig::new().with_timeout(Duration::from_secs(2)),
            )
            .expect("solve generated near miss");
            assert!(
                !matches!(near_axeyum, CheckResult::Sat(_)),
                "missing-margin seed received wrong Sat credit: {near_miss}"
            );
            let near_oracle = Solver::new();
            near_oracle.set_params(&params);
            near_oracle.from_string(near_miss.as_str());
            assert_eq!(
                near_oracle.check(),
                SatResult::Unsat,
                "Z3 did not refute missing-margin seed {seed}: {near_miss}"
            );
        }
    }
}

#[test]
fn tampered_skolem_certificate_is_rejected() {
    let mut script = parse_script(ISSUE_4849).expect("parse issue4849");
    let assertions = assertions(&script);
    let CheckResult::Sat(mut model) =
        solve(&mut script.arena, &assertions, &SolverConfig::default()).expect("solve issue4849")
    else {
        panic!("issue4849 should be Sat");
    };
    let mut cert = model
        .quantified_sat_certificate(assertions[0])
        .expect("certificate")
        .clone();
    cert.witness = AffineSkolemWitness {
        terms: Vec::new(),
        constant: Rational::zero(),
    };
    assert!(!check_quantified_skolem_sat(
        &script.arena,
        assertions[0],
        &cert
    ));
    model.set_quantified_sat_certificate(cert);
    assert!(!check_model(&script.arena, &assertions, &model).expect("tampered model check"));
}

#[test]
fn foreign_bound_symbol_and_stale_assertion_are_rejected() {
    let mut script = parse_script(ISSUE_4849).expect("parse issue4849");
    let assertions = assertions(&script);
    let CheckResult::Sat(model) =
        solve(&mut script.arena, &assertions, &SolverConfig::default()).expect("solve issue4849")
    else {
        panic!("issue4849 should be Sat");
    };
    let cert = model
        .quantified_sat_certificate(assertions[0])
        .expect("certificate")
        .clone();

    let foreign = script.arena.declare("foreign", Sort::Int).unwrap();
    let mut foreign_cert = cert.clone();
    foreign_cert.witness = AffineSkolemWitness {
        terms: vec![(script.arena.var(foreign), Rational::integer(1))],
        constant: Rational::zero(),
    };
    assert!(!check_quantified_skolem_sat(
        &script.arena,
        assertions[0],
        &foreign_cert
    ));

    let unrelated = script.arena.bool_const(true);
    let mut stale_model = model.clone();
    let mut stale_cert = cert.clone();
    stale_cert.assertion = unrelated;
    stale_model.set_quantified_sat_certificate(stale_cert);
    assert!(!check_model(&script.arena, &[unrelated], &stale_model).expect("stale model check"));

    let mut extra_model = model;
    let mut extra_cert = cert.clone();
    extra_cert.assertion = unrelated;
    extra_model.set_quantified_sat_certificate(extra_cert);
    assert!(
        !check_model(&script.arena, &[assertions[0], unrelated], &extra_model)
            .expect("extraneous certificate check")
    );
}

#[test]
fn reused_universal_and_existential_binder_id_is_rejected() {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).expect("declare x");
    let xv = arena.var(x);
    let body = arena.eq(xv, xv).expect("reflexive body");
    let exists = arena.exists(x, body).expect("exists");
    let assertion = arena.forall(x, exists).expect("forall");
    let cert = QuantifiedSkolemSatCertificate {
        assertion,
        universals: vec![x],
        existential: x,
        witness: AffineSkolemWitness {
            terms: vec![(xv, Rational::integer(1))],
            constant: Rational::zero(),
        },
    };
    assert!(!check_quantified_skolem_sat(&arena, assertion, &cert));
}

#[test]
fn identity_near_miss_does_not_receive_sat_credit() {
    let input = r"
        (set-logic LIA)
        (assert (forall ((a Int))
          (exists ((b Int))
            (= (ite (= a 0) 0 1)
               (ite (= (+ b 1) 0) 0 1)))))
        (check-sat)
    ";
    let mut script = parse_script(input).expect("parse near miss");
    let assertions = assertions(&script);
    let result = solve(
        &mut script.arena,
        &assertions,
        &SolverConfig::new().with_timeout(Duration::from_secs(2)),
    )
    .expect("solve near miss");
    assert!(
        !matches!(result, CheckResult::Sat(_)),
        "non-reflexive identity candidate must not receive Sat credit: {result:?}"
    );
}
