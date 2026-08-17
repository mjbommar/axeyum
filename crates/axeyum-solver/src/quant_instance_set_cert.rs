//! Certificates for a quantifier refutation decided by e-matching.
//!
//! The e-matching driver ([`crate::qinst_egraph`]) refutes a quantified query by
//! instantiating universals at ground terms until the quantifier-free set is
//! unsatisfiable. It already builds exact provenance for each instance —
//! [`QuantifierInstanceCertificate`] — and already exposes an independent
//! replay checker for it, [`check_quantifier_ground_derivation`]. What it never
//! did was hand either to [`crate::evidence`], so the whole route reported
//! `unsat-uncertified`: the right verdict with nothing attached.
//!
//! Measured on 2026-08-17, `F:barber-no-such-barber` is the clean case. The
//! solver skolemises `∃b. ∀x. shaves(b,x) ↔ ¬shaves(x,x)` to `!sk_0`, e-matches
//! exactly one instance — the universal at the existential's own witness — and
//! refutes `p ↔ ¬p`. Every step of that is recorded; none of it was reachable.
//!
//! # What the certificate has to establish
//!
//! Two things, and the second is the one it would be easy to omit:
//!
//! 1. every instance used is a **legitimate consequence** of the original
//!    assertions (each derivation replays against the untouched input), and
//! 2. the instances actually **suffice** — the ground set is unsatisfiable.
//!
//! Checking only (1) would certify a pile of true-but-insufficient instances,
//! so [`check_quantifier_instance_set`] re-refutes the ground set rather than
//! trusting that the producer did.
//!
//! # Deliberately narrow
//!
//! A certificate is offered only when the refutation is *exactly* "original
//! ground assertions plus checked instances". Two cases decline rather than
//! claim:
//!
//! - **Promotion.** The driver may grow its own assertion list (a universal
//!   promoted from a positive-position replacement). Those additions are
//!   consequences of the input, but they are not *in* the input, so a
//!   derivation resting on one would not replay against the caller's
//!   assertions. If the list grew, no certificate is offered.
//! - **Sub-routine refutations.** `try_closed_universal_refutations`,
//!   `try_targeted_quantifier_refutations` and the candidate fixpoint each
//!   refute by their own argument, not by the ground set. They carry their own
//!   justifications and are out of scope here.
//!
//! - **Any rewriting between the query and the loop's anchor.** Instance
//!   certificates bind *syntactically* to the assertion list the driver was
//!   given, which is not always the caller's: `prove_quantified_unsat_via_egraph`
//!   may `split_universal_conjunctions` (an equivalence) or
//!   `extract_nested_universals` first, and [`crate::auto`] skolemises top-level
//!   existentials before either. Those steps are sound, but they are not
//!   *justified by this certificate*, and a checker that accepted the anchor on
//!   faith would be certifying "these instances refute a set someone told me
//!   follows from the query" — which is not the claim. So a certificate is
//!   offered only when the anchor is the caller's list verbatim.
//!
//! Declining leaves the route exactly where it was — `unsat-uncertified` — so a
//! narrow certificate strictly improves on nothing and never overstates.
//!
//! It is also offered **last** among the certifying routes in `produce_evidence`.
//! "Assertions plus checked instances" is weaker and more generic than any
//! Alethe certificate, and placed earlier it displaces them: measured, an
//! earlier placement took over four `evidence_finite_quant_uf_cert` tests and
//! one in `evidence` from the guarded-quantifier UF Alethe certificate. The job
//! is to upgrade what used to be a bare `Unsat(None)`, never to demote a
//! stronger certificate to this one.
//!
//! # Portability: the certificate must mean something in another arena
//!
//! This carries `TermId`s, and the instances it names are terms created *during*
//! e-matching — so they are not in the arena the query was parsed into, which is
//! the arena a checker gets. `smtcomp_cli` re-parses the original file on
//! purpose: "the producing solve's arena is deliberately not reused".
//!
//! An earlier version stored the instance ids and let the driver's checker
//! compare against them. That is not portable, and it failed in the worst way —
//! it *passed* for a single instance, because the checker happened to rebuild
//! that term at the same id, and failed for two. `certified=1` alongside a
//! re-check that reported FAIL.
//!
//! So the recorded `instance` is treated as **derived data, not as the claim**.
//! `assertion` and `bindings` are query-side terms, which a re-parse of the same
//! file reproduces at the same ids; the checker substitutes the bindings into
//! the assertion *in its own arena* and validates the derivation that names
//! THAT term. The ground set is likewise rebuilt rather than stored, which also
//! makes "nothing was smuggled into the ground set" structural: you cannot
//! smuggle a conjunct into a set the checker constructs itself.
//!
//! Ids that do not resolve at all — a certificate offered for a different query
//! — are rejected before anything dereferences them. `TermArena::node`,
//! `sort_of` and `var` index directly and panic on a foreign id, and a checker
//! must fail closed rather than abort.
//!
//! # Still not covered: the barber
//!
//! `F:barber-no-such-barber` is `∃b. ∀x. …`, so `auto` skolemises it and the
//! loop's anchor is not the query. It stays uncertified until the skolemisation
//! record is itself carried — `skolemize_top_existentials` returns a bare
//! `Vec<TermId>` and discards the assertion-to-`!sk_k` correspondence that would
//! justify the difference. That is the next slice and is deliberately not
//! smuggled into this one: a certificate that quietly accepted a rewritten
//! anchor would report `certified=1` on strictly less evidence than the label
//! claims.

use axeyum_ir::{TermArena, TermId};

use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::qinst_egraph::{QuantifierGroundDerivation, check_quantifier_ground_derivation};

/// A refutation by instantiation: the instances used, and the ground set they
/// make unsatisfiable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifierInstanceSetCertificate {
    /// Provenance for every instance the refutation used.
    ///
    /// The ground set is **not** stored. It is rebuilt by the checker from the
    /// caller's own assertions plus these instances, which is what makes the
    /// certificate portable: a stored set would be a list of `TermId`s from the
    /// producing run, and those name nothing in the arena a checker is handed
    /// (`smtcomp_cli` re-parses the file on purpose). Rebuilding also makes
    /// "nothing was smuggled into the ground set" structural rather than a
    /// guard — you cannot smuggle a conjunct into a set the checker constructs.
    pub derivations: Vec<QuantifierGroundDerivation>,
}

/// Build a certificate for a ground refutation, or `None` to decline.
///
/// `anchor` is the **caller's** assertion list. Every derivation is replayed
/// against it here, at build time, by the same public checker the evidence
/// layer will later use.
///
/// Replaying rather than comparing lists is what makes the scope rules in the
/// module note enforced instead of merely stated. An earlier version tried to
/// detect rewriting by testing the driver's working list against the caller's
/// for equality; that is both too strict (an identical list can be rebuilt) and
/// too weak (it says nothing about what the derivations actually cite). If a
/// split, extraction, promotion or skolemisation moved the anchor, the
/// derivations cite terms the caller never asserted, `check_quantifier_ground_derivation`
/// fails, and no certificate is offered — which is the intended outcome, reached
/// by checking rather than by guessing.
#[must_use]
pub fn build_instance_set_certificate(
    arena: &mut TermArena,
    anchor: &[TermId],
    ground: &[TermId],
    derivations: &std::collections::HashMap<TermId, QuantifierGroundDerivation>,
) -> Option<QuantifierInstanceSetCertificate> {
    let asserted: std::collections::HashSet<TermId> = anchor.iter().copied().collect();
    let mut used = Vec::new();
    for &term in ground {
        if asserted.contains(&term) {
            continue;
        }
        // A ground term that is neither asserted nor derived would make the
        // certificate unreplayable. Decline rather than emit a partial one.
        let derivation = derivations.get(&term)?;
        if !check_quantifier_ground_derivation(arena, anchor, derivation) {
            return None;
        }
        used.push(derivation.clone());
    }
    Some(QuantifierInstanceSetCertificate { derivations: used })
}

/// Peel a `∀`-prefix, returning its bound variables (outermost first) and body.
///
/// A local copy of the driver's own peeling, because the checker must rebuild an
/// instance in ITS arena rather than trust the id the producer recorded.
fn peel_foralls(arena: &TermArena, term: TermId) -> (Vec<axeyum_ir::SymbolId>, TermId) {
    use axeyum_ir::{Op, TermNode};
    let mut vars = Vec::new();
    let mut current = term;
    while let TermNode::App {
        op: Op::Forall(var),
        args,
    } = arena.node(current)
    {
        vars.push(*var);
        current = args[0];
    }
    (vars, current)
}

/// Whether `term` is a top-level universal, i.e. one of the assertions the
/// driver partitions OUT of the ground set.
fn is_top_level_forall(arena: &TermArena, term: TermId) -> bool {
    use axeyum_ir::{Op, TermNode};
    matches!(
        arena.node(term),
        TermNode::App {
            op: Op::Forall(_),
            ..
        }
    )
}

/// Rebuild `assertion`'s instance at `bindings` **in this arena**.
///
/// `None` when the shape does not match — a wrong binding count, or an assertion
/// that is not a universal.
fn rebuild_instance(
    arena: &mut TermArena,
    assertion: TermId,
    bindings: &[TermId],
) -> Option<TermId> {
    let (vars, body) = peel_foralls(arena, assertion);
    if vars.is_empty() || vars.len() != bindings.len() {
        return None;
    }
    let replacements: std::collections::HashMap<TermId, TermId> = vars
        .iter()
        .map(|&var| arena.var(var))
        .zip(bindings.iter().copied())
        .collect();
    let mut memo = std::collections::HashMap::new();
    axeyum_rewrite::replace_subterms(arena, body, &replacements, &mut memo).ok()
}

/// Whether every `TermId` the certificate cites exists in this arena.
///
/// Checked BEFORE anything dereferences them. `TermArena::node`, `sort_of` and
/// `var` all index directly and panic on a foreign id, so without this a
/// certificate from another run does not fail the check — it aborts the process.
/// A checker must fail closed.
fn references_resolve(arena: &TermArena, certificate: &QuantifierInstanceSetCertificate) -> bool {
    let limit = arena.len();
    certificate
        .derivations
        .iter()
        .all(|derivation| match derivation {
            QuantifierGroundDerivation::Instance(instance) => {
                instance.assertion.index() < limit
                    && instance.bindings.iter().all(|b| b.index() < limit)
            }
            // A propagation certificate carries nested structure whose ids are not
            // rebuilt here; decline rather than dereference them.
            QuantifierGroundDerivation::Propagation(_) => false,
        })
}

/// Independently re-derive a quantifier instance-set refutation.
///
/// Nothing from the producing run is consulted: each derivation is replayed
/// against `assertions` by the driver's own public checker, every ground member
/// is required to be asserted or derived, and the ground set is re-refuted.
///
/// # Errors
///
/// Propagates a hard backend error from the ground re-refutation. A `sat` or
/// `unknown` ground verdict is a *failed* check, not an error.
pub fn check_quantifier_instance_set(
    arena: &mut TermArena,
    assertions: &[TermId],
    certificate: &QuantifierInstanceSetCertificate,
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    use crate::qinst_egraph::QuantifierInstanceCertificate;

    // (0) Fail CLOSED on an id this arena cannot resolve, before anything
    // dereferences it. The arena indexes directly and panics on a foreign id.
    if !references_resolve(arena, certificate) {
        return Ok(false);
    }

    // (1) Rebuild each instance HERE, then check the rebuilt one.
    //
    // This is the whole of portability. `QuantifierInstanceCertificate` records
    // `(assertion, bindings, instance)`, and the driver's checker verifies the
    // first two reproduce the third BY TERM ID. `assertion` and `bindings` are
    // query-side terms, so a re-parse of the same file gives them the same ids;
    // `instance` is created DURING solving, so its id names a slot the checker's
    // arena does not have. Trusting it is how a certificate came to report
    // `certified=1` while its own re-check said FAIL.
    //
    // So the recorded `instance` is treated as derived data, not as the claim:
    // substitute the bindings into the assertion in this arena, and check the
    // derivation that names THAT term.
    let mut instances = Vec::with_capacity(certificate.derivations.len());
    for derivation in &certificate.derivations {
        let QuantifierGroundDerivation::Instance(recorded) = derivation else {
            return Ok(false);
        };
        let Some(rebuilt) = rebuild_instance(arena, recorded.assertion, &recorded.bindings) else {
            return Ok(false);
        };
        let repaired = QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
            assertion: recorded.assertion,
            bindings: recorded.bindings.clone(),
            instance: rebuilt,
        });
        // The driver's own public checker still does the real work: it re-peels
        // the universal, re-substitutes, and requires the assertion to be one of
        // the caller's. Repairing the id does not weaken it -- an instance whose
        // assertion is not asserted, or whose bindings do not fit its binders,
        // still fails here.
        if !check_quantifier_ground_derivation(arena, assertions, &repaired) {
            return Ok(false);
        }
        instances.push(rebuilt);
    }

    // (2) Rebuild the ground set: the caller's non-universal assertions, plus
    // those instances. Nothing from the producing run contributes a term.
    //
    // The universals are dropped exactly as the driver's own partition drops
    // them -- their content enters through the instances. Keeping them would
    // send the check back through the quantifier front door and yield `unknown`,
    // which reads as a failed certificate rather than as the wrong question.
    let mut ground: Vec<TermId> = assertions
        .iter()
        .copied()
        .filter(|&assertion| !is_top_level_forall(arena, assertion))
        .collect();
    ground.extend(instances);

    // (3) The instances must SUFFICE. Steps (1) and (2) only establish that each
    // instance is a legitimate consequence and that nothing else crept in; a set
    // of true-but-insufficient instances would pass both.
    match crate::auto::check_auto(arena, &ground, config) {
        Ok(CheckResult::Unsat) => Ok(true),
        // A ground set that is satisfiable, undecided, or outside the dispatch's
        // fragment all mean the same thing here: this certificate does not
        // establish its refutation. None of the three is a hard error.
        Ok(CheckResult::Sat(_) | CheckResult::Unknown(_)) | Err(SolverError::Unsupported(_)) => {
            Ok(false)
        }
        Err(error) => Err(error),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::qinst_egraph::prove_quantified_unsat_via_egraph_with_instances;
    use axeyum_smtlib::parse_script;

    /// `∀x. f(x) = 0` with `f(5) ≠ 0`: one instantiation refutes it, and there
    /// is no existential and no conjunctive universal, so the driver's anchor is
    /// the query verbatim and a certificate is in scope.
    const ONE_INSTANCE: &str = "(set-logic UFLIA)\n\
         (declare-fun f (Int) Int)\n\
         (assert (forall ((x Int)) (= (f x) 0)))\n\
         (assert (not (= (f 5) 0)))\n\
         (check-sat)";

    fn refuted(
        text: &str,
    ) -> (
        axeyum_smtlib::Script,
        Vec<TermId>,
        QuantifierInstanceSetCertificate,
    ) {
        let mut parsed = parse_script(text).expect("script parses");
        let assertions = parsed.assertions.clone();
        let config = SolverConfig::default();
        let mut certificate = None;
        let result = prove_quantified_unsat_via_egraph_with_instances(
            &mut parsed.arena,
            &assertions,
            &config,
            &mut certificate,
        )
        .expect("no hard backend error");
        assert!(
            matches!(result, CheckResult::Unsat),
            "the premise of every test here: got {result:?}"
        );
        let certificate = certificate.expect(
            "a plain universal refuted by instantiation is exactly the case this \
             certificate covers; None here means the capture never fires and the \
             negative controls below would be vacuous",
        );
        (parsed, assertions, certificate)
    }

    #[test]
    fn an_instantiation_refutation_produces_a_certificate_that_rechecks() {
        let (mut parsed, assertions, certificate) = refuted(ONE_INSTANCE);
        assert!(
            !certificate.derivations.is_empty(),
            "a refutation that used no instance would not need this route"
        );
        assert!(
            check_quantifier_instance_set(
                &mut parsed.arena,
                &assertions,
                &certificate,
                &SolverConfig::default(),
            )
            .expect("checker runs"),
            "the certificate must re-derive against the untouched assertions"
        );
    }

    /// A tampered BINDING must be rejected.
    ///
    /// Guard (2) of the old design — "nothing was smuggled into the ground set"
    /// — is now structural: the checker builds the ground set itself, so there
    /// is nowhere to smuggle a conjunct. What remains attackable is the
    /// instance's own provenance, so that is what this attacks.
    #[test]
    fn an_instance_with_a_tampered_binding_is_rejected() {
        let (mut parsed, assertions, certificate) = refuted(ONE_INSTANCE);
        let intruder = parsed.arena.int_const(7);
        let mut tampered = certificate.clone();
        for derivation in &mut tampered.derivations {
            if let QuantifierGroundDerivation::Instance(instance) = derivation {
                instance.bindings = vec![intruder];
            }
        }
        // The rebuilt instance is now `f(7) = 0`, a true consequence but not the
        // one that refutes `f(5) != 0`. It must fail on SUFFICIENCY, which is
        // the guard a provenance-only checker would not have.
        assert!(
            !check_quantifier_instance_set(
                &mut parsed.arena,
                &assertions,
                &tampered,
                &SolverConfig::default(),
            )
            .expect("checker runs")
        );
    }

    /// Guard (3). No instances at all leaves the ground set unrefuted.
    #[test]
    fn true_but_insufficient_instances_are_rejected() {
        let (mut parsed, assertions, certificate) = refuted(ONE_INSTANCE);
        let empty = QuantifierInstanceSetCertificate {
            derivations: Vec::new(),
        };
        assert!(
            !check_quantifier_instance_set(
                &mut parsed.arena,
                &assertions,
                &empty,
                &SolverConfig::default(),
            )
            .expect("checker runs"),
            "without the instance the ground set is just `f(5) != 0`, which is \
             satisfiable; a certificate that establishes nothing must not pass"
        );
        // And the real one still does, so the test above is not passing because
        // the checker rejects everything.
        assert!(
            check_quantifier_instance_set(
                &mut parsed.arena,
                &assertions,
                &certificate,
                &SolverConfig::default(),
            )
            .expect("checker runs")
        );
    }

    /// THE PORTABILITY TEST: a certificate must check against an arena that
    /// shares nothing with the run that produced it.
    ///
    /// This is the case that matters, because it is the one the gate performs —
    /// `smtcomp_cli` re-parses the original file precisely so re-validation owes
    /// nothing to what the producing run kept in memory. An earlier version of
    /// this certificate stored the instance's `TermId` and compared it directly;
    /// that passed here by allocation-order coincidence for ONE instance and
    /// failed for two, which is how a false `certified=1` shipped.
    #[test]
    fn a_certificate_checks_against_an_independently_reparsed_arena() {
        let (_producing, _assertions, certificate) = refuted(ONE_INSTANCE);
        let mut fresh = parse_script(ONE_INSTANCE).expect("re-parses");
        let fresh_assertions = fresh.assertions.clone();
        assert!(
            check_quantifier_instance_set(
                &mut fresh.arena,
                &fresh_assertions,
                &certificate,
                &SolverConfig::default(),
            )
            .expect("checker runs"),
            "the certificate must survive re-parsing; if it does not it describes \
             the producing run rather than the query"
        );
    }

    /// The same, with SEVERAL instances — the shape that exposed the defect.
    ///
    /// One instance can match by coincidence. More than one is where a stored
    /// id and a rebuilt one part company.
    #[test]
    fn several_instances_also_survive_an_independent_reparse() {
        const TWO: &str = "(set-logic UFLIA)\n\
             (declare-fun f (Int) Int)\n\
             (assert (forall ((x Int)) (= (f x) 0)))\n\
             (assert (not (= (+ (f 5) (f 7)) 0)))\n\
             (check-sat)";
        let (_producing, _assertions, certificate) = refuted(TWO);
        assert!(
            certificate.derivations.len() >= 2,
            "this test is only meaningful with more than one instance; got {}",
            certificate.derivations.len()
        );
        let mut fresh = parse_script(TWO).expect("re-parses");
        let fresh_assertions = fresh.assertions.clone();
        assert!(
            check_quantifier_instance_set(
                &mut fresh.arena,
                &fresh_assertions,
                &certificate,
                &SolverConfig::default(),
            )
            .expect("checker runs")
        );
    }

    /// A certificate offered for a DIFFERENT query must fail closed, not abort.
    ///
    /// Its ids may not resolve in this arena at all, and the arena indexes
    /// directly — so without the bounds check this is a panic rather than a
    /// verdict.
    #[test]
    fn a_certificate_for_another_query_fails_closed() {
        let (_producing, _assertions, certificate) = refuted(ONE_INSTANCE);
        let mut other = parse_script(
            "(set-logic QF_LIA)\n(declare-fun y () Int)\n(assert (= y 1))\n(check-sat)",
        )
        .expect("parses");
        let other_assertions = other.assertions.clone();
        assert!(
            !check_quantifier_instance_set(
                &mut other.arena,
                &other_assertions,
                &certificate,
                &SolverConfig::default(),
            )
            .expect("checker must return a verdict, not abort")
        );
    }
}
