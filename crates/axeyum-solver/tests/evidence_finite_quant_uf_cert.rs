//! Certified-`unsat` evidence for finite-expansion guarded-`Int` universals whose
//! body uses an **uninterpreted function**.
//!
//! A guarded-finite-`Int` universal `∀x:Int. (lo<=x<=hi) => (= (f x) c)` whose
//! finite expansion clashes (in EUF+LIA) with quantifier-free side facts now
//! carries an independently checkable Alethe certificate
//! ([`Evidence::UnsatGuardedQuantAletheProof`]) instead of a bare
//! `Evidence::Unsat(None)`. The certificate composes THREE rule families:
//! `forall_inst_guarded` (the custom instantiation lemma), `eq_transitive` (the
//! Ackermann-abstraction bridge), and `lia_generic` (the residual). These tests
//! assert it certifies and re-checks, that a tampered proof is rejected, and that
//! the pure-LIA finite-`∀` cert, the `QF_UFLIA` ground cert, and a satisfiable
//! UF-bodied universal are all unaffected.

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm};
use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{
    Evidence, SolverConfig, check_alethe_lra_guarded_inst, check_alethe_lra_guarded_inst_against,
    produce_evidence, prove_finite_int_quant_unsat_uf_alethe,
};

/// `∀x:Int. (0<=x<=1) => f(x)=0`, with `f : Int -> Int`. Returns the universal.
fn forall_fx_eq_0(arena: &mut TermArena, f: axeyum_ir::FuncId) -> TermId {
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let lo = arena.int_ge(xv, zero).unwrap();
    let hi = arena.int_le(xv, one).unwrap();
    let guard = arena.and(lo, hi).unwrap();
    let fx = arena.apply(f, &[xv]).unwrap();
    let zero2 = arena.int_const(0);
    let inner = arena.eq(fx, zero2).unwrap();
    let body = arena.implies(guard, inner).unwrap();
    arena.forall(x, body).unwrap()
}

#[test]
fn guarded_int_universal_uf_clash_certifies() {
    // `∀x:Int. (0<=x<=1) => f(x)=0`  ∧  `f(0)=1` — the instance `f(0)=0` clashes
    // with `f(0)=1` (same application, two values), so the expansion is UNSAT.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let forall = forall_fx_eq_0(&mut arena, f);
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let f0 = arena.apply(f, &[zero]).unwrap();
    let f0_eq_1 = arena.eq(f0, one).unwrap();

    let config = SolverConfig::default();
    let asserts = [forall, f0_eq_1];
    let report = produce_evidence(&mut arena, &asserts, &config).expect("decides");
    assert!(
        matches!(
            report.evidence,
            Evidence::UnsatGuardedQuantAletheProof { .. }
        ),
        "expected a guarded-quantifier (UF) Alethe certificate, got {:?}",
        report.evidence
    );
    assert!(report.evidence.is_certified());
    assert_eq!(
        report.evidence.check(&arena, &asserts),
        Ok(true),
        "the certificate must independently re-check"
    );
}

#[test]
fn guarded_int_universal_uf_full_range_clash_certifies() {
    // `∀x:Int. (0<=x<=2) => f(x)=0`  ∧  `f(2)=7` — the instance `f(2)=0` clashes
    // with `f(2)=7`. Exercises a wider range and a non-zeroth clashing instance.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let zero = arena.int_const(0);
    let two = arena.int_const(2);
    let lo = arena.int_ge(xv, zero).unwrap();
    let hi = arena.int_le(xv, two).unwrap();
    let guard = arena.and(lo, hi).unwrap();
    let fx = arena.apply(f, &[xv]).unwrap();
    let zero2 = arena.int_const(0);
    let inner = arena.eq(fx, zero2).unwrap();
    let body = arena.implies(guard, inner).unwrap();
    let forall = arena.forall(x, body).unwrap();

    let two2 = arena.int_const(2);
    let f2 = arena.apply(f, &[two2]).unwrap();
    let seven = arena.int_const(7);
    let f2_eq_7 = arena.eq(f2, seven).unwrap();

    let config = SolverConfig::default();
    let asserts = [forall, f2_eq_7];
    let report = produce_evidence(&mut arena, &asserts, &config).expect("decides");
    assert!(
        matches!(
            report.evidence,
            Evidence::UnsatGuardedQuantAletheProof { .. }
        ),
        "expected a guarded-quantifier (UF) Alethe certificate, got {:?}",
        report.evidence
    );
    assert_eq!(report.evidence.check(&arena, &asserts), Ok(true));
}

#[test]
fn tamper_rejects_guarded_quant_uf_certificate() {
    // Build the genuine proof, then mutate it; the checker must reject every
    // tampering of the three-family certificate.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let forall = forall_fx_eq_0(&mut arena, f);
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let f0 = arena.apply(f, &[zero]).unwrap();
    let f0_eq_1 = arena.eq(f0, one).unwrap();
    let asserts = [forall, f0_eq_1];

    let proof = prove_finite_int_quant_unsat_uf_alethe(&mut arena, &asserts)
        .expect("emits a UF guarded-quantifier proof");
    // Re-derive the universal form (the same shared UF-aware detection the evidence
    // uses) so the genuine proof checks.
    let universal = {
        // The `Evidence` carries this form; re-extract via a produce_evidence pass.
        let config = SolverConfig::default();
        let mut a2 = TermArena::new();
        let f2 = a2.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
        let forall2 = forall_fx_eq_0(&mut a2, f2);
        let z2 = a2.int_const(0);
        let o2 = a2.int_const(1);
        let f02 = a2.apply(f2, &[z2]).unwrap();
        let f0_eq_1_2 = a2.eq(f02, o2).unwrap();
        let report = produce_evidence(&mut a2, &[forall2, f0_eq_1_2], &config).expect("decides");
        match report.evidence {
            Evidence::UnsatGuardedQuantAletheProof { universal, .. } => universal,
            other => panic!("expected UF guarded cert, got {other:?}"),
        }
    };
    assert_eq!(
        check_alethe_lra_guarded_inst(&universal, &proof),
        Ok(true),
        "genuine proof must check"
    );

    // Tamper #1: corrupt a `forall_inst_guarded` instance witness to out-of-range.
    let mut tampered = proof.clone();
    let mut mutated = false;
    for cmd in &mut tampered {
        if let AletheCommand::Step { rule, clause, .. } = cmd
            && rule == "forall_inst_guarded"
        {
            if let Some(l) = clause.get_mut(1) {
                // literal 1 is `(= (f v) 0)`; bump the witness `v` to 99.
                *l = AletheLit {
                    atom: bump_arg(&l.atom),
                    negated: l.negated,
                };
                mutated = true;
            }
            break;
        }
    }
    assert!(mutated, "must have mutated a forall_inst_guarded step");
    assert_ne!(
        check_alethe_lra_guarded_inst(&universal, &tampered),
        Ok(true),
        "an out-of-range-witness proof must be rejected"
    );

    // Tamper #2: corrupt the eq_transitive bridge so the abstracted conclusion no
    // longer follows from its chain (replace the conclusion's value with 99).
    let mut tampered2 = proof.clone();
    let mut mutated2 = false;
    for cmd in &mut tampered2 {
        if let AletheCommand::Step { rule, clause, .. } = cmd
            && rule == "eq_transitive"
        {
            if let Some(l) = clause.last_mut() {
                l.atom = AletheTerm::App(
                    "=".to_owned(),
                    vec![
                        AletheTerm::Const("zzz".to_owned()),
                        AletheTerm::Const("99".to_owned()),
                    ],
                );
                mutated2 = true;
            }
            break;
        }
    }
    assert!(mutated2, "must have mutated an eq_transitive step");
    assert_ne!(
        check_alethe_lra_guarded_inst(&universal, &tampered2),
        Ok(true),
        "a broken eq_transitive bridge must be rejected"
    );
}

#[test]
fn assume_independent_check_rejects_fabricated_uf_premise() {
    // SOUNDNESS-NEGATIVE (UF case): build a genuine UF proof, then INJECT a bogus
    // `assume` `(= a 5)` not among the original assertions. The old, emitter-trusting
    // checker still accepts it (an unused extra hypothesis); the assume-independent
    // checker must REJECT it, since the premise is not a consequence of THIS query.
    // This exercises the gap on the UF tail whose premises include fresh-var
    // definitions and abstracted side facts.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let forall = forall_fx_eq_0(&mut arena, f);
    let zero = arena.int_const(0);
    let one = arena.int_const(1);
    let f0 = arena.apply(f, &[zero]).unwrap();
    let f0_eq_1 = arena.eq(f0, one).unwrap();
    let asserts = [forall, f0_eq_1];

    let proof = prove_finite_int_quant_unsat_uf_alethe(&mut arena, &asserts)
        .expect("emits a UF guarded-quantifier proof");
    // Re-derive the carried universal form via a produce_evidence pass.
    let universal = {
        let config = SolverConfig::default();
        let report = produce_evidence(&mut arena, &asserts, &config).expect("decides");
        match report.evidence {
            Evidence::UnsatGuardedQuantAletheProof { universal, .. } => universal,
            other => panic!("expected UF guarded cert, got {other:?}"),
        }
    };

    let mut tampered = proof;
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
    // The STRENGTHENED checker rejects it.
    assert_ne!(
        check_alethe_lra_guarded_inst_against(&universal, &tampered, &arena, &asserts),
        Ok(true),
        "the assume-independent checker must reject a fabricated UF premise"
    );

    let evidence = Evidence::UnsatGuardedQuantAletheProof {
        proof: tampered,
        universal,
    };
    assert_ne!(
        evidence.check(&arena, &asserts),
        Ok(true),
        "Evidence::check must reject the fabricated-premise UF proof"
    );
}

/// Replaces every in-range integer numeral (`0..=1`) that is NOT a top-level value
/// with `99`. Used to corrupt the UF instance witness `v` (the `(f v)` argument)
/// without touching the body's `=0`. Simpler: bump any `0` or `1` that appears as a
/// bare function argument. We approximate by bumping ALL such constants; the test
/// only needs the resulting clause to no longer be a valid in-range instance.
fn bump_arg(t: &AletheTerm) -> AletheTerm {
    match t {
        AletheTerm::App(h, args) if h == "f" => {
            // bump the function argument out of range.
            AletheTerm::App(
                h.clone(),
                args.iter()
                    .map(|a| match a {
                        AletheTerm::Const(_) => AletheTerm::Const("99".to_owned()),
                        other @ (AletheTerm::App(..) | AletheTerm::Indexed { .. }) => other.clone(),
                    })
                    .collect(),
            )
        }
        AletheTerm::App(h, args) => AletheTerm::App(h.clone(), args.iter().map(bump_arg).collect()),
        AletheTerm::Indexed { op, indices, args } => AletheTerm::Indexed {
            op: op.clone(),
            indices: indices.clone(),
            args: args.iter().map(bump_arg).collect(),
        },
        other @ AletheTerm::Const(_) => other.clone(),
    }
}

#[test]
fn guarded_int_universal_uf_sat_not_reported_unsat() {
    // `∀x:Int. (0<=x<=1) => f(x)=0` with NO conflicting side fact — satisfiable
    // (set f(0)=f(1)=0). Must NOT certify unsat.
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let forall = forall_fx_eq_0(&mut arena, f);

    // The emitter must decline on a satisfiable universal.
    assert!(
        prove_finite_int_quant_unsat_uf_alethe(&mut arena, &[forall]).is_none(),
        "emitter must not produce a proof for a satisfiable UF universal"
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
        "a satisfiable UF universal must not be reported unsat, got {:?}",
        report.evidence
    );
}

#[test]
fn guarded_int_universal_uf_consistent_side_fact_sat() {
    // `∀x:Int. (0<=x<=1) => f(x)=0` with `f(0)=0` (CONSISTENT) — satisfiable, the
    // emitter must decline (the expansion is NOT unsat).
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let forall = forall_fx_eq_0(&mut arena, f);
    let zero = arena.int_const(0);
    let zero2 = arena.int_const(0);
    let f0 = arena.apply(f, &[zero]).unwrap();
    let f0_eq_0 = arena.eq(f0, zero2).unwrap();

    assert!(
        prove_finite_int_quant_unsat_uf_alethe(&mut arena, &[forall, f0_eq_0]).is_none(),
        "consistent side fact must not yield an unsat proof"
    );
}

// --- Regressions: pure-LIA quantified evidence and the QF_UFLIA ground cert. ---

#[test]
fn pure_lia_finite_forall_remains_checked() {
    // `∀x.(0<=x<=2) => x>=5` — pure-LIA quantified evidence must still certify
    // (the UF route must not shadow or break it). ADR-0100's independently
    // replayed concrete counterexample now intentionally precedes the older
    // guarded finite-expansion emitter in `produce_evidence`.
    let mut arena = TermArena::new();
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
    let forall = arena.forall(x, body).unwrap();

    // The UF emitter declines a pure-LIA (no UF) body.
    assert!(
        prove_finite_int_quant_unsat_uf_alethe(&mut arena, &[forall]).is_none(),
        "UF emitter must decline a pure-LIA body"
    );

    let config = SolverConfig::default();
    let report = produce_evidence(&mut arena, &[forall], &config).expect("decides");
    assert!(
        matches!(
            report.evidence,
            Evidence::UnsatClosedUniversalCounterexample(_)
        ),
        "pure-LIA finite-`∀` must use checked quantified evidence, got {:?}",
        report.evidence
    );
    assert_eq!(report.evidence.check(&arena, &[forall]), Ok(true));
}

#[test]
fn qf_uflia_ground_cert_unchanged() {
    // `f(x)=1 ∧ f(y)=2 ∧ x=y` — the QF_UFLIA congruence ground cert must still
    // certify (no quantifier; the UF finite-`∀` route declines on no universal).
    let mut arena = TermArena::new();
    let f = arena.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
    let x = arena.int_var("x").unwrap();
    let y = arena.int_var("y").unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let one = arena.int_const(1);
    let two = arena.int_const(2);
    let a1 = arena.eq(fx, one).unwrap();
    let a2 = arena.eq(fy, two).unwrap();
    let a3 = arena.eq(x, y).unwrap();
    let asserts = [a1, a2, a3];

    // The finite-`∀` UF emitter declines (no universal).
    assert!(
        prove_finite_int_quant_unsat_uf_alethe(&mut arena, &asserts).is_none(),
        "UF finite-`∀` emitter must decline a quantifier-free query"
    );

    let config = SolverConfig::default();
    let report = produce_evidence(&mut arena, &asserts, &config).expect("decides");
    assert!(
        matches!(report.evidence, Evidence::UnsatArithAletheProof(_)),
        "QF_UFLIA ground cert must be unchanged, got {:?}",
        report.evidence
    );
    assert_eq!(report.evidence.check(&arena, &asserts), Ok(true));
}
