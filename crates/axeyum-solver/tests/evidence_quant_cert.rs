//! Certified-`unsat` evidence for guarded-`Int` universals.
//!
//! A guarded-finite-`Int` universal `∀x:Int. (lo<=x<=hi) => inner` whose finite
//! expansion is integer-`unsat` has an independently checkable Alethe emitter.
//! ADR-0100's concrete closed-universal counterexample is preferred by
//! `produce_evidence` when it applies. These tests cover both routes, reject a
//! tampered Alethe proof, and keep quantifier-free `unsat` certificates and a
//! satisfiable guarded-`Int` universal unaffected.

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{
    Evidence, SolverConfig, check_alethe_lra_guarded_inst, check_alethe_lra_guarded_inst_against,
    guarded_universal_form_for_test, produce_evidence, prove_finite_int_quant_unsat_alethe,
};

/// Replaces every in-range integer numeral (`0..=2`) in `t` with an out-of-range
/// `99` — used by the tamper test to corrupt a `forall_inst_guarded` witness so the
/// guard-truth re-check must reject it.
fn bump_consts(t: &AletheTerm) -> AletheTerm {
    match t {
        AletheTerm::Const(s) => {
            if s.parse::<i128>().is_ok_and(|n| (0..=2).contains(&n)) {
                AletheTerm::Const("99".to_owned())
            } else {
                t.clone()
            }
        }
        AletheTerm::App(h, a) => AletheTerm::App(h.clone(), a.iter().map(bump_consts).collect()),
        AletheTerm::Indexed { op, indices, args } => AletheTerm::Indexed {
            op: op.clone(),
            indices: indices.clone(),
            args: args.iter().map(bump_consts).collect(),
        },
    }
}

/// `∀x:Int. (0<=x ∧ x<=2) => x>=5` — each instance `v>=5` (v∈{0,1,2}) is false, so
/// the expansion is integer-`unsat`. The expected certified shape.
fn forall_x_ge_5(arena: &mut TermArena) -> axeyum_ir::TermId {
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zero = arena.int_const(0);
    let two = arena.int_const(2);
    let five = arena.int_const(5);
    let lo = arena.int_ge(xv, zero).unwrap();
    let hi = arena.int_le(xv, two).unwrap();
    let guard = arena.and(lo, hi).unwrap();
    let inner = arena.int_ge(xv, five).unwrap();
    let body = arena.implies(guard, inner).unwrap();
    arena.forall(x, body).unwrap()
}

#[test]
fn guarded_int_universal_unsat_certifies() {
    let mut arena = TermArena::new();
    let forall = forall_x_ge_5(&mut arena);
    let config = SolverConfig::default();

    let report = produce_evidence(&mut arena, &[forall], &config).expect("decides");
    assert!(
        matches!(
            report.evidence,
            Evidence::UnsatClosedUniversalCounterexample(_)
        ),
        "expected a checked closed-universal counterexample, got {:?}",
        report.evidence
    );
    assert!(report.evidence.is_certified());
    assert_eq!(
        report.evidence.check(&arena, &[forall]),
        Ok(true),
        "the certificate must independently re-check"
    );
}

#[test]
fn guarded_int_universal_eq_clash_certifies() {
    // `∀x:Int. (0<=x<=1) => x=9` — instances `0=9`, `1=9` both false ⇒ unsat.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let nine = arena.int_const(9);
    let lo = arena.int_ge(xv, zero).unwrap();
    let hi = arena.int_le(xv, one).unwrap();
    let guard = arena.and(lo, hi).unwrap();
    let inner = arena.eq(xv, nine).unwrap();
    let body = arena.implies(guard, inner).unwrap();
    let forall = arena.forall(x, body).unwrap();
    let config = SolverConfig::default();

    let report = produce_evidence(&mut arena, &[forall], &config).expect("decides");
    assert!(
        matches!(
            report.evidence,
            Evidence::UnsatClosedUniversalCounterexample(_)
        ),
        "expected a checked closed-universal counterexample, got {:?}",
        report.evidence
    );
    assert_eq!(report.evidence.check(&arena, &[forall]), Ok(true));
}

#[test]
fn guarded_int_universal_with_side_fact_certifies() {
    // `∀x:Int. (0<=x<=2) => x<=3`  ∧  `y>=10 ∧ y<=2`  -- the SIDE facts alone are
    // unsat; the universal expands harmlessly. Confirms ground LIA side assertions
    // flow through the spliced tail.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zero = arena.int_const(0);
    let two = arena.int_const(2);
    let three = arena.int_const(3);
    let lo = arena.int_ge(xv, zero).unwrap();
    let hi = arena.int_le(xv, two).unwrap();
    let guard = arena.and(lo, hi).unwrap();
    let inner = arena.int_le(xv, three).unwrap();
    let body = arena.implies(guard, inner).unwrap();
    let forall = arena.forall(x, body).unwrap();

    let y = arena.declare("y", Sort::Int).unwrap();
    let yv = arena.var(y);
    let ten = arena.int_const(10);
    let two2 = arena.int_const(2);
    let yge = arena.int_ge(yv, ten).unwrap();
    let yle = arena.int_le(yv, two2).unwrap();

    let config = SolverConfig::default();
    let asserts = [forall, yge, yle];
    let report = produce_evidence(&mut arena, &asserts, &config).expect("decides");
    assert!(
        matches!(
            report.evidence,
            Evidence::UnsatGuardedQuantAletheProof { .. }
        ),
        "expected guarded-quantifier cert, got {:?}",
        report.evidence
    );
    assert_eq!(report.evidence.check(&arena, &asserts), Ok(true));
}

#[test]
fn tamper_rejects_guarded_quant_certificate() {
    // Build the genuine proof, then mutate a `forall_inst_guarded` instance literal
    // to an OUT-OF-RANGE / wrong witness and confirm the checker rejects it.
    let mut arena = TermArena::new();
    let forall = forall_x_ge_5(&mut arena);

    let proof = prove_finite_int_quant_unsat_alethe(&mut arena, &[forall])
        .expect("emits a guarded-quantifier proof");
    let universal =
        guarded_universal_form_for_test(&arena, &[forall]).expect("detects the universal form");
    // Sanity: the genuine proof checks.
    assert_eq!(
        check_alethe_lra_guarded_inst(&universal, &proof),
        Ok(true),
        "genuine proof must check"
    );

    // Tamper #1: corrupt a `forall_inst_guarded` instance literal to an out-of-range
    // witness (replace an in-range constant in the instance with `99`), which the
    // guard truth re-check must reject.
    let mut tampered = proof.clone();
    let mut mutated = false;
    for cmd in &mut tampered {
        if let AletheCommand::Step { rule, clause, .. } = cmd
            && rule == "forall_inst_guarded"
        {
            // literal 1 is the instance; bump its in-range witness out of range.
            if let Some(l) = clause.get_mut(1) {
                *l = AletheLit {
                    atom: bump_consts(&l.atom),
                    negated: l.negated,
                };
                mutated = true;
            }
            break;
        }
    }
    assert!(mutated, "test must have mutated a forall_inst_guarded step");
    assert_ne!(
        check_alethe_lra_guarded_inst(&universal, &tampered),
        Ok(true),
        "a tampered (out-of-range witness) proof must be rejected"
    );

    // Tamper #2: replace a `forall_inst_guarded` instance literal with an unrelated
    // atom that is NOT a substitution instance of the inner body — the structural
    // half of the instantiation check must reject it.
    let mut tampered2 = proof.clone();
    let mut mutated2 = false;
    for cmd in &mut tampered2 {
        if let AletheCommand::Step { rule, clause, .. } = cmd
            && rule == "forall_inst_guarded"
        {
            if let Some(l) = clause.get_mut(1) {
                // `(>= x 5)`[x:=v] replaced by an unrelated `(<= 0 0)`.
                l.atom = AletheTerm::App(
                    "<=".to_owned(),
                    vec![
                        AletheTerm::Const("0".to_owned()),
                        AletheTerm::Const("0".to_owned()),
                    ],
                );
                mutated2 = true;
            }
            break;
        }
    }
    assert!(
        mutated2,
        "test must have mutated a forall_inst_guarded step"
    );
    assert_ne!(
        check_alethe_lra_guarded_inst(&universal, &tampered2),
        Ok(true),
        "a non-instance (structural-mismatch) proof must be rejected"
    );
}

#[test]
fn assume_independent_check_rejects_fabricated_premise() {
    // SOUNDNESS-NEGATIVE: build a genuine proof, then INJECT a bogus `assume`
    // (`(= a 5)`) that is NOT among the original assertions. The old, emitter-trusting
    // checker (`check_alethe_lra_guarded_inst`) still accepts the proof — an unused
    // extra hypothesis does not break the empty-clause derivation — but the
    // assume-independent checker (`check_alethe_lra_guarded_inst_against`) must REJECT
    // it: the fabricated premise is not a consequence of THIS query, so the proof is
    // not a sound refutation of it. This is exactly the emitter-trust gap being closed.
    let mut arena = TermArena::new();
    let forall = forall_x_ge_5(&mut arena);

    let proof = prove_finite_int_quant_unsat_alethe(&mut arena, &[forall])
        .expect("emits a guarded-quantifier proof");
    let universal =
        guarded_universal_form_for_test(&arena, &[forall]).expect("detects the universal form");

    // Inject an unrelated `(= a 5)` assume not in the query.
    let mut tampered = proof.clone();
    tampered.push(AletheCommand::Assume {
        id: "bogus".to_owned(),
        clause: vec![AletheLit {
            atom: AletheTerm::App(
                "=".to_owned(),
                vec![
                    AletheTerm::Const("a".to_owned()),
                    AletheTerm::Const("5".to_owned()),
                ],
            ),
            negated: false,
        }],
    });

    // The OLD checker trusts the injected premise and still accepts (the gap).
    assert_eq!(
        check_alethe_lra_guarded_inst(&universal, &tampered),
        Ok(true),
        "the emitter-trusting checker accepts the fabricated premise (the gap)"
    );
    // The STRENGTHENED checker verifies every assume against the query and rejects.
    assert_ne!(
        check_alethe_lra_guarded_inst_against(&universal, &tampered, &arena, &[forall]),
        Ok(true),
        "the assume-independent checker must reject a fabricated premise"
    );

    // And via the consumer-facing `Evidence::check` (which now uses the strengthened
    // route): the tampered proof packaged as evidence must not re-check `true`.
    let evidence = Evidence::UnsatGuardedQuantAletheProof {
        proof: tampered,
        universal,
    };
    assert_ne!(
        evidence.check(&arena, &[forall]),
        Ok(true),
        "Evidence::check must reject the fabricated-premise proof"
    );
}

#[test]
fn assume_independent_check_rejects_non_fresh_definition() {
    // SOUNDNESS-NEGATIVE (definition class): inject a definition-shaped `assume`
    // `(= x (g x))` keyed on a NON-fresh constant — `x` occurs in the query, so this
    // is a genuine constraint, not a conservative fresh-var extension. The
    // assume-independent checker must reject it (it is neither an original assertion
    // nor a fresh-var definition).
    let mut arena = TermArena::new();
    let forall = forall_x_ge_5(&mut arena);

    let proof = prove_finite_int_quant_unsat_alethe(&mut arena, &[forall])
        .expect("emits a guarded-quantifier proof");
    let universal =
        guarded_universal_form_for_test(&arena, &[forall]).expect("detects the universal form");

    let mut tampered = proof;
    tampered.push(AletheCommand::Assume {
        id: "bad_def".to_owned(),
        clause: vec![AletheLit {
            // `x` is the universal's binder name (in the query), so NOT fresh.
            atom: AletheTerm::App(
                "=".to_owned(),
                vec![
                    AletheTerm::Const("x".to_owned()),
                    AletheTerm::App("g".to_owned(), vec![AletheTerm::Const("x".to_owned())]),
                ],
            ),
            negated: false,
        }],
    });
    assert_ne!(
        check_alethe_lra_guarded_inst_against(&universal, &tampered, &arena, &[forall]),
        Ok(true),
        "a definition keyed on a non-fresh (query) constant must be rejected"
    );
}

#[test]
fn assume_independent_check_rejects_forged_carried_universal() {
    // SOUNDNESS-NEGATIVE (carried-universal class): the carried `GuardedUniversalForm`
    // itself must correspond to a guarded universal in the original assertions. A
    // forged form — one whose `body`/`inner` does NOT match any original assertion's
    // rendering — would otherwise pass the class-1 `assume` test (which compares the
    // proof's `q_forall` assume against the *carried* form, not the query). The
    // strengthened check cross-verifies the carried universal against the query and
    // must reject the forgery.
    let mut arena = TermArena::new();
    let forall = forall_x_ge_5(&mut arena);

    let proof = prove_finite_int_quant_unsat_alethe(&mut arena, &[forall])
        .expect("emits a guarded-quantifier proof");
    let genuine =
        guarded_universal_form_for_test(&arena, &[forall]).expect("detects the universal form");

    // Forge a carried form by bumping the constants in the body/inner (so the
    // structure is self-consistent with the proof's `forall_inst_guarded` steps' own
    // atoms, but no original assertion renders to this body). `bump_consts` rewrites
    // in-range numerals to `99`, changing `x>=5`'s guard range `[0,2]`/threshold off
    // the query's universal.
    let forged = axeyum_solver::GuardedUniversalForm {
        var_name: genuine.var_name.clone(),
        inner: bump_consts(&genuine.inner),
        body: bump_consts(&genuine.body),
        lo: genuine.lo,
        hi: genuine.hi,
    };
    // `forged.body` is not the rendering of any assertion in the query, so the carried
    // universal is not in the query → reject (cannot certify a refutation of THIS
    // query). It must specifically NOT accept.
    assert_ne!(
        check_alethe_lra_guarded_inst_against(&forged, &proof, &arena, &[forall]),
        Ok(true),
        "a forged carried universal not derived from the query must be rejected"
    );

    // Sanity: the GENUINE carried form against the same query still checks — the
    // strengthening is purely additive and rejects only the forgery.
    assert_eq!(
        check_alethe_lra_guarded_inst_against(&genuine, &proof, &arena, &[forall]),
        Ok(true),
        "the genuine carried universal against its own query must still certify"
    );

    // A second angle: even a GENUINE carried form fails to certify when the original
    // assertions slice OMITS the universal — there is then nothing in the query the
    // carried universal corresponds to.
    assert_ne!(
        check_alethe_lra_guarded_inst_against(&genuine, &proof, &arena, &[]),
        Ok(true),
        "an empty assertions slice cannot contain the carried universal → reject"
    );
}

#[test]
fn guarded_int_universal_sat_not_reported_unsat() {
    // `∀x:Int. (0<=x<=2) => x>=0` — every instance true, so SAT. Must NOT certify
    // unsat (no false report).
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zero = arena.int_const(0);
    let two = arena.int_const(2);
    let lo = arena.int_ge(xv, zero).unwrap();
    let hi = arena.int_le(xv, two).unwrap();
    let guard = arena.and(lo, hi).unwrap();
    let inner = arena.int_ge(xv, zero).unwrap();
    let body = arena.implies(guard, inner).unwrap();
    let forall = arena.forall(x, body).unwrap();

    // The emitter must decline on a satisfiable universal.
    assert!(
        prove_finite_int_quant_unsat_alethe(&mut arena, &[forall]).is_none(),
        "emitter must not produce a proof for a satisfiable universal"
    );

    let config = SolverConfig::default();
    let report = produce_evidence(&mut arena, &[forall], &config).expect("decides");
    assert!(
        !matches!(
            report.evidence,
            Evidence::UnsatGuardedQuantAletheProof { .. }
                | Evidence::Unsat(_)
                | Evidence::UnsatArithAletheProof(_)
        ),
        "a satisfiable guarded-Int universal must not be reported unsat, got {:?}",
        report.evidence
    );
    // It is `sat` (a model). (Its `Evidence::check` replays the *original* `forall`
    // through the enumerating evaluator, which cannot enumerate the infinite `Int`
    // domain — a pre-existing limitation of quantified-`sat` replay, unrelated to
    // this certificate; the point here is only that it is not reported `unsat`.)
    assert!(
        matches!(report.evidence, Evidence::Sat(_)),
        "expected sat, got {:?}",
        report.evidence
    );
}

// --- Regressions: quantifier-FREE unsat certs unchanged. ---

#[test]
fn qf_lia_unsat_cert_unchanged() {
    // `x>=1 ∧ x<=-1` — pure QF_LIA unsat, must keep its arithmetic Alethe cert.
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let one = arena.int_const(1);
    let neg1 = arena.int_const(-1);
    let ge = arena.int_ge(xv, one).unwrap();
    let le = arena.int_le(xv, neg1).unwrap();
    let config = SolverConfig::default();
    let asserts = [ge, le];
    let report = produce_evidence(&mut arena, &asserts, &config).expect("decides");
    assert!(
        matches!(report.evidence, Evidence::UnsatArithAletheProof(_)),
        "QF_LIA unsat must keep its arithmetic Alethe cert, got {:?}",
        report.evidence
    );
    assert_eq!(report.evidence.check(&arena, &asserts), Ok(true));
}

#[test]
fn qf_bv_unsat_cert_unchanged() {
    // `a & ~a != 0` over BV8 — pure QF_BV unsat, keeps its term-level cert.
    let mut arena = TermArena::new();
    let a = arena.declare("a", Sort::BitVec(8)).unwrap();
    let av = arena.var(a);
    let not_a = arena.bv_not(av).unwrap();
    let and = arena.bv_and(av, not_a).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let eq = arena.eq(and, zero).unwrap();
    let ne = arena.not(eq).unwrap();
    let config = SolverConfig::default();
    let report = produce_evidence(&mut arena, &[ne], &config).expect("decides");
    assert!(
        matches!(
            report.evidence,
            Evidence::UnsatTermLevel { .. } | Evidence::UnsatAletheProof(_) | Evidence::Unsat(_)
        ),
        "QF_BV unsat must keep its (non-quantifier) cert, got {:?}",
        report.evidence
    );
    assert_eq!(report.evidence.check(&arena, &[ne]), Ok(true));
}
