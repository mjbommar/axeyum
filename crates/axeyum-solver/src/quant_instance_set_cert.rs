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
//! # Wiring to [`crate::evidence`]: why the arena is not a problem
//!
//! This carries `TermId`s, and the instances it names are terms *created during*
//! e-matching, so they are not in the arena the query was parsed into. That
//! looks fatal — a certificate naming ids a checker cannot resolve — and it is
//! not, for one reason: `produce_evidence` holds `&mut TermArena`, and
//! `quant_instance_set_certificate` runs the driver on **that** arena rather
//! than on a clone. The instances are therefore added to the very arena
//! [`Evidence::check`](crate::Evidence::check) is later handed, and its own
//! working clone inherits them.
//!
//! This is load-bearing and easy to undo by accident: producing the certificate
//! from a scratch clone (the shape most producers here use) would leave every id
//! dangling, and the recheck would report a failure that has nothing to do with
//! the mathematics. The producer says so at its definition.
//!
//! What this does **not** buy is a certificate that survives leaving the
//! process. These ids mean nothing to a different arena, so this cannot be
//! serialised and re-checked later the way an Alethe proof can. Making it
//! portable means carrying the instances as data rather than as ids — worth
//! doing, and a separate slice from this one.
//!
//! # Consequence: the barber is not yet covered
//!
//! `F:barber-no-such-barber` is `∃b. ∀x. …`, so `auto` skolemises it and the
//! loop's anchor is not the query. It stays uncertified until the skolemisation
//! record is itself carried — `skolemize_top_existentials` currently returns a
//! bare `Vec<TermId>` and discards the assertion-to-`!sk_k` correspondence. That
//! is the next slice, and it is deliberately not smuggled into this one: a
//! certificate that quietly assumed its anchor would report `certified=1` on
//! strictly less evidence than the label claims.

use axeyum_ir::{TermArena, TermId};

use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::qinst_egraph::{QuantifierGroundDerivation, check_quantifier_ground_derivation};

/// A refutation by instantiation: the instances used, and the ground set they
/// make unsatisfiable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifierInstanceSetCertificate {
    /// Provenance for every non-assertion member of `ground`.
    pub derivations: Vec<QuantifierGroundDerivation>,
    /// The quantifier-free set the driver refuted. Every member is either an
    /// original assertion or the conclusion of one of `derivations`.
    pub ground: Vec<TermId>,
}

/// The conclusion each derivation licenses.
fn conclusion(derivation: &QuantifierGroundDerivation) -> TermId {
    match derivation {
        QuantifierGroundDerivation::Instance(certificate) => certificate.instance,
        QuantifierGroundDerivation::Propagation(certificate) => certificate.propagated_literal,
    }
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
    Some(QuantifierInstanceSetCertificate {
        derivations: used,
        ground: ground.to_vec(),
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
    let asserted: std::collections::HashSet<TermId> = assertions.iter().copied().collect();

    // (1) Every instance is a legitimate consequence of the untouched input.
    let mut licensed: std::collections::HashSet<TermId> = asserted.clone();
    for derivation in &certificate.derivations {
        if !check_quantifier_ground_derivation(arena, assertions, derivation) {
            return Ok(false);
        }
        licensed.insert(conclusion(derivation));
    }

    // (2) The ground set contains nothing smuggled in. Without this a checker
    // that only validated the derivations would accept a ground set carrying an
    // extra unjustified conjunct -- and an extra conjunct is exactly how you
    // manufacture an `unsat`.
    if !certificate.ground.iter().all(|t| licensed.contains(t)) {
        return Ok(false);
    }

    // (3) The instances SUFFICE. Checking only (1) and (2) would certify a set
    // of true-but-insufficient instances.
    match crate::auto::check_auto(arena, &certificate.ground, config) {
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

    /// Guard (2). An extra ground conjunct that nothing licenses must be
    /// rejected — smuggling in a conjunct is precisely how one manufactures an
    /// `unsat`, and the derivations would all still check.
    #[test]
    fn an_unlicensed_ground_member_is_rejected() {
        let (mut parsed, assertions, mut certificate) = refuted(ONE_INSTANCE);
        let intruder = parsed.arena.int_const(7);
        certificate.ground.push(intruder);
        assert!(
            !check_quantifier_instance_set(
                &mut parsed.arena,
                &assertions,
                &certificate,
                &SolverConfig::default(),
            )
            .expect("checker runs")
        );
    }

    /// Guard (1)/(2). Dropping the provenance leaves the instances in `ground`
    /// unaccounted for, so the certificate must stop checking.
    #[test]
    fn instances_without_provenance_are_rejected() {
        let (mut parsed, assertions, mut certificate) = refuted(ONE_INSTANCE);
        certificate.derivations.clear();
        assert!(
            !check_quantifier_instance_set(
                &mut parsed.arena,
                &assertions,
                &certificate,
                &SolverConfig::default(),
            )
            .expect("checker runs")
        );
    }

    /// Guard (3). Legitimate instances that do not SUFFICE must not certify.
    /// Every derivation still replays; the ground set simply is not refuted.
    #[test]
    fn true_but_insufficient_instances_are_rejected() {
        let (mut parsed, assertions, mut certificate) = refuted(ONE_INSTANCE);
        certificate.ground.clone_from(&assertions);
        certificate.derivations.clear();
        assert!(
            !check_quantifier_instance_set(
                &mut parsed.arena,
                &assertions,
                &certificate,
                &SolverConfig::default(),
            )
            .expect("checker runs"),
            "the original assertions are still quantified, so this is not a \
             ground refutation and must not pass as one"
        );
    }
}
