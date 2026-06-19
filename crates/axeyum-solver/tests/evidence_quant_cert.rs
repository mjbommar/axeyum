//! Certified-`unsat` evidence for finite-expansion guarded-`Int` universals.
//!
//! A guarded-finite-`Int` universal `∀x:Int. (lo<=x<=hi) => inner` whose finite
//! expansion is integer-`unsat` now carries an independently checkable Alethe
//! certificate ([`Evidence::UnsatGuardedQuantAletheProof`]) instead of a bare
//! `Evidence::Unsat(None)`. These tests assert it certifies, that a tampered proof
//! is rejected, and that quantifier-free `unsat` certs (and a satisfiable
//! guarded-`Int` universal) are unaffected.

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
use axeyum_ir::{Sort, TermArena};
use axeyum_solver::{
    Evidence, SolverConfig, check_alethe_lra_guarded_inst, guarded_universal_form_for_test,
    produce_evidence, prove_finite_int_quant_unsat_alethe,
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
            Evidence::UnsatGuardedQuantAletheProof { .. }
        ),
        "expected a guarded-quantifier Alethe certificate, got {:?}",
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
            Evidence::UnsatGuardedQuantAletheProof { .. }
        ),
        "expected a guarded-quantifier Alethe certificate, got {:?}",
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
        if let AletheCommand::Step { rule, clause, .. } = cmd {
            if rule == "forall_inst_guarded" {
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
        if let AletheCommand::Step { rule, clause, .. } = cmd {
            if rule == "forall_inst_guarded" {
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
