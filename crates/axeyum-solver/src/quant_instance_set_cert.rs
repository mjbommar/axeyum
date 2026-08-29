//! Certificates for a quantifier refutation decided by e-matching.
//!
//! The e-matching driver ([`crate::qinst_egraph`]) refutes a quantified query by
//! instantiating universals at ground terms until the quantifier-free set is
//! unsatisfiable. It already builds exact provenance for each instance —
//! [`QuantifierInstanceCertificate`](crate::qinst_egraph::QuantifierInstanceCertificate)
//! — and already exposes an independent replay checker for it,
//! [`check_quantifier_ground_derivation`]. What it never did was hand either to
//! [`crate::evidence`], so the whole route reported `unsat-uncertified`: the
//! right verdict with nothing attached.
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
//! A certificate is offered only when the refutation is *exactly* "the
//! skolemised assertions plus checked instances". Two cases decline rather than
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
//! - **Any *other* rewriting between the query and the loop's anchor.** Instance
//!   certificates bind *syntactically* to the assertion list the driver was
//!   given, which is not always the caller's: `prove_quantified_unsat_via_egraph`
//!   may `split_universal_conjunctions` (an equivalence) or
//!   `extract_nested_universals` first. Those steps are sound, but they are not
//!   *justified by this certificate*, and a checker that accepted the anchor on
//!   faith would be certifying "these instances refute a set someone told me
//!   follows from the query" — which is not the claim. So a certificate is
//!   offered only when the anchor is the caller's list, up to the one
//!   transformation this certificate does carry: `∃`-elimination, below.
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
//! # Portability: nothing here may name a term of the producing run
//!
//! `smtcomp_cli` re-validates against a **fresh parse of the original file**, on
//! purpose: "the producing solve's arena is deliberately not reused". So every
//! `TermId` created *during* solving — every instance, every skolem witness,
//! every skolemised assertion — names a slot the checker's arena does not have.
//!
//! An earlier version stored the instance ids and let the driver's checker
//! compare against them. That is not portable, and it failed in the worst way —
//! it *passed* for a single instance, because the checker happened to rebuild
//! that term at the same id, and failed for two. `certified=1` alongside a
//! re-check that reported FAIL.
//!
//! The rule this module now follows without exception: **an id may be recorded
//! only if it names a subterm of the caller's own assertions**, which a re-parse
//! reproduces. Everything else is recorded *positionally* and rebuilt by the
//! checker in its own arena:
//!
//! - the universal an instance came from, by **index** into the skolemised
//!   assertion list (which the checker recomputes, [`PortableInstance`]);
//! - a binding that is a skolem witness, by **which witness of which assertion**
//!   it is ([`PortableBinding::Witness`]);
//! - the instance term itself: not recorded at all, but rebuilt by substituting
//!   into the checker's own universal;
//! - the ground set: not recorded at all, but rebuilt from the checker's own
//!   assertions plus those instances. That also makes "nothing was smuggled into
//!   the ground set" structural rather than a guard — you cannot smuggle a
//!   conjunct into a set the checker constructs itself.
//!
//! The producer refuses to emit a binding it cannot classify as one of those two
//! (`portable_certificate` returns `None`), so a term the checker could not name
//! becomes a declined certificate rather than a `certified=1` that fails
//! re-validation.
//!
//! # The `∃`-elimination this certificate carries
//!
//! `F:barber-no-such-barber` is `∃b. ∀x. …`, and there is no universal to
//! instantiate until the existential is eliminated. So the producer eliminates
//! it — [`crate::auto::eliminate_top_existentials`], the same function
//! [`crate::auto::solve`] uses — and the certificate records *how many* binders
//! each assertion lost. The checker runs that same elimination on the caller's
//! assertions, in its own arena, and requires the shape to match.
//!
//! Two properties make this recordable at all:
//!
//! - **Freshness needs no evidence.** It is the soundness condition for
//!   `∃`-elimination, and the checker introduces the witnesses *itself*, through
//!   the eliminator's own unused-name probe. There is nothing to take on trust
//!   from the producer, so there is nothing the producer could lie about.
//! - **Equisatisfiability is a property of the transformation, not of the run.**
//!   `∃x. body` and `body[x := c]` for fresh `c` are equisatisfiable; the ground
//!   set the checker refutes is entailed by the checker's own skolemised
//!   assertions, and those are unsatisfiable exactly when the caller's are.
//!
//! Recording *only the binder counts* is what distinguishes this from two
//! designs that were tried and reverted. Recording the skolemised assertions or
//! the witness terms as ids panics or fails, because `TermArena::var` aborts on a
//! symbol from another arena and the checker's fresh parse has no `!sk_0`.
//! Recording a bare `skolemised: bool` and trusting the ids to line up fails
//! too: this producer runs **last**, so ~20 other producers have already
//! allocated in its arena and its ids are nowhere near a fresh parse's. Indices
//! survive both, because an index is a fact about the query.

use std::collections::{HashMap, HashSet};

use axeyum_ir::{TermArena, TermId};

use crate::backend::{CheckResult, SolverConfig, SolverError};
use crate::qinst_egraph::{QuantifierGroundDerivation, check_quantifier_ground_derivation};

/// One ground term substituted for a universal binder, named so that it survives
/// leaving the arena it was chosen in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PortableBinding {
    /// A subterm of the caller's own assertions, by id.
    ///
    /// This is the only id in the whole certificate, and it is sound to record
    /// because a re-parse of the same file rebuilds the query's terms at the
    /// same ids. The checker still confirms membership in *its* query before
    /// dereferencing, so a certificate offered for another query fails closed
    /// rather than aborting.
    Query(TermId),
    /// The witness introduced for the `index`-th (outermost-first) top-level
    /// existential binder of caller assertion `assertion`.
    ///
    /// Positional because the witness *term* exists only in the producing run.
    /// The checker resolves this against the witnesses its own elimination
    /// introduced.
    Witness {
        /// Index into the caller's assertion list.
        assertion: usize,
        /// Which binder of that assertion, outermost first.
        index: usize,
    },
}

/// One universal instantiation, with nothing in it that names the producing run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PortableInstance {
    /// Index into the **skolemised** assertion list — which the checker
    /// recomputes from the caller's assertions rather than receiving.
    pub assertion: usize,
    /// Ground terms substituted for that universal's prefix, outermost first.
    pub bindings: Vec<PortableBinding>,
}

/// A refutation by instantiation: the elimination performed, the instances used,
/// and (implicitly) the ground set they make unsatisfiable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifierInstanceSetCertificate {
    /// How many top-level existential binders each caller assertion lost,
    /// positionally parallel to the caller's assertion list.
    ///
    /// All zeroes for a query with no top-level existential, which is the
    /// common case; the barber is `[1]`. The checker re-runs the elimination
    /// and requires its own counts to agree, so a certificate describing a
    /// different query is rejected here rather than later by accident.
    pub skolem_prefix: Vec<usize>,
    /// Provenance for every instance the refutation used.
    ///
    /// The ground set is **not** stored — see the module note on portability.
    pub instances: Vec<PortableInstance>,
}

// `collect_ground_derivations` used to live here, but its only caller was
// `qinst_egraph` and it operates purely on `qinst_egraph`'s own
// `QuantifierGroundDerivation`/`check_quantifier_ground_derivation` — so
// keeping it in this module made `qinst_egraph` depend on this module while
// this module already depends on `qinst_egraph` (for exactly those two
// items), closing a cycle across two of the crate's largest files. Moved to
// `qinst_egraph` (docs/refactor-2026-08/03-solver-decomposition.md,
// `scripts/analyze_solver_module_graph.py --check`, 2026-08-29). This module
// still calls into `qinst_egraph`, one-way, via `portable_certificate`'s
// `derivations: &[QuantifierGroundDerivation]` parameter.

/// Rewrite collected derivations into a certificate that names no term of the
/// producing run, or `None` if some binding cannot be named portably.
///
/// `elimination` must be the one whose `assertions` were the driver's anchor,
/// and `query` the caller's own (pre-elimination) assertion list.
#[must_use]
pub(crate) fn portable_certificate(
    arena: &mut TermArena,
    query: &[TermId],
    elimination: &crate::auto::SkolemElimination,
    derivations: &[QuantifierGroundDerivation],
) -> Option<QuantifierInstanceSetCertificate> {
    let query_terms = query_term_closure(arena, query);
    let anchor_index: HashMap<TermId, usize> = elimination
        .assertions
        .iter()
        .enumerate()
        .map(|(index, &assertion)| (assertion, index))
        .collect();
    let mut witness_index: HashMap<TermId, (usize, usize)> = HashMap::new();
    for (assertion, symbols) in elimination.witnesses.iter().enumerate() {
        for (index, &symbol) in symbols.iter().enumerate() {
            witness_index.insert(arena.var(symbol), (assertion, index));
        }
    }

    let mut instances = Vec::with_capacity(derivations.len());
    for derivation in derivations {
        // A propagation certificate carries nested structure that this
        // positional form does not describe. Decline rather than half-record it.
        let QuantifierGroundDerivation::Instance(recorded) = derivation else {
            return None;
        };
        let assertion = *anchor_index.get(&recorded.assertion)?;
        let mut bindings = Vec::with_capacity(recorded.bindings.len());
        for &binding in &recorded.bindings {
            if let Some(&(assertion, index)) = witness_index.get(&binding) {
                bindings.push(PortableBinding::Witness { assertion, index });
            } else if query_terms.contains(&binding) {
                bindings.push(PortableBinding::Query(binding));
            } else {
                // A term e-matching invented during the solve. It has no name a
                // checker's arena could resolve, so there is no honest way to
                // record it -- and recording the id anyway is exactly how a
                // `certified=1` that fails re-validation gets shipped.
                return None;
            }
        }
        instances.push(PortableInstance {
            assertion,
            bindings,
        });
    }
    Some(QuantifierInstanceSetCertificate {
        skolem_prefix: elimination.witnesses.iter().map(Vec::len).collect(),
        instances,
    })
}

/// Every subterm of `assertions` — the terms a re-parse of the same file
/// reproduces at the same ids, and therefore the only ones a certificate may
/// name.
fn query_term_closure(arena: &TermArena, assertions: &[TermId]) -> HashSet<TermId> {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let axeyum_ir::TermNode::App { args, .. } = arena.node(term) {
            stack.extend(args.iter().copied());
        }
    }
    seen
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
    let replacements: HashMap<TermId, TermId> = vars
        .iter()
        .map(|&var| arena.var(var))
        .zip(bindings.iter().copied())
        .collect();
    let mut memo = HashMap::new();
    axeyum_rewrite::replace_subterms(arena, body, &replacements, &mut memo).ok()
}

/// Independently re-derive a quantifier instance-set refutation.
///
/// Nothing from the producing run is consulted: the `∃`-elimination is redone
/// here (introducing this arena's own witnesses), each instance is rebuilt here
/// and replayed against the resulting assertions by the driver's own public
/// checker, every ground member is required to be asserted or derived, and the
/// ground set is re-refuted.
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

    // (0) Fail CLOSED on a certificate that does not describe THIS query. Its
    // ids may name nothing here, and the arena indexes directly and panics on a
    // foreign id, so every reference below is resolved through a membership or
    // bounds test before anything is dereferenced.
    if certificate.skolem_prefix.len() != assertions.len() {
        return Ok(false);
    }
    let query_terms = query_term_closure(arena, assertions);

    // (1) Redo the `∃`-elimination HERE. The witnesses are this arena's, freshly
    // named by the eliminator's own unused-name probe, so freshness -- the
    // soundness condition -- is established rather than assumed. The recorded
    // binder counts must agree: they are a fact about the query, and disagreement
    // means this certificate is about a different one.
    let Ok(elimination) = crate::auto::eliminate_top_existentials(arena, assertions) else {
        return Ok(false);
    };
    if !elimination
        .witnesses
        .iter()
        .map(Vec::len)
        .eq(certificate.skolem_prefix.iter().copied())
    {
        return Ok(false);
    }

    // (2) Rebuild each instance HERE, then check the rebuilt one.
    //
    // This is the whole of portability. The certificate names a universal by
    // index into the list step (1) just built, and each binding either by an id
    // this query owns or by which witness of which assertion it is. Nothing is
    // taken from the producer that could name a term this arena does not have.
    let mut instances = Vec::with_capacity(certificate.instances.len());
    for recorded in &certificate.instances {
        let Some(&assertion) = elimination.assertions.get(recorded.assertion) else {
            return Ok(false);
        };
        let mut bindings = Vec::with_capacity(recorded.bindings.len());
        for binding in &recorded.bindings {
            let term = match *binding {
                PortableBinding::Query(term) => {
                    if !query_terms.contains(&term) {
                        return Ok(false);
                    }
                    term
                }
                PortableBinding::Witness { assertion, index } => {
                    let Some(&symbol) = elimination
                        .witnesses
                        .get(assertion)
                        .and_then(|symbols| symbols.get(index))
                    else {
                        return Ok(false);
                    };
                    arena.var(symbol)
                }
            };
            bindings.push(term);
        }
        let Some(rebuilt) = rebuild_instance(arena, assertion, &bindings) else {
            return Ok(false);
        };
        let repaired = QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
            assertion,
            bindings,
            instance: rebuilt,
        });
        // The driver's own public checker still does the real work: it re-peels
        // the universal, re-substitutes, and requires the assertion to be one of
        // the skolemised list. Rebuilding the ids does not weaken it -- an
        // instance whose assertion is not asserted, or whose bindings do not fit
        // its binders, still fails here.
        if !check_quantifier_ground_derivation(arena, &elimination.assertions, &repaired) {
            return Ok(false);
        }
        instances.push(rebuilt);
    }

    // (3) Rebuild the ground set: this arena's own non-universal skolemised
    // assertions, plus those instances. Nothing from the producing run
    // contributes a term.
    //
    // The universals are dropped exactly as the driver's own partition drops
    // them -- their content enters through the instances. Keeping them would
    // send the check back through the quantifier front door and yield `unknown`,
    // which reads as a failed certificate rather than as the wrong question.
    let mut ground: Vec<TermId> = elimination
        .assertions
        .iter()
        .copied()
        .filter(|&assertion| !is_top_level_forall(arena, assertion))
        .collect();
    ground.extend(instances);

    // (4) The instances must SUFFICE. Steps (2) and (3) only establish that each
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

    /// The barber: the whole point of the elimination record. Nothing here is a
    /// universal until the existential is gone.
    const BARBER: &str = "(set-logic UF)\n\
         (declare-sort Person 0)\n\
         (declare-fun shaves (Person Person) Bool)\n\
         (assert (exists ((b Person)) \
            (forall ((x Person)) (= (shaves b x) (not (shaves x x))))))\n\
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
        let elimination =
            crate::auto::eliminate_top_existentials(&mut parsed.arena, &assertions).expect("elim");
        let mut derivations = None;
        let result = prove_quantified_unsat_via_egraph_with_instances(
            &mut parsed.arena,
            &elimination.assertions,
            &config,
            &mut derivations,
        )
        .expect("no hard backend error");
        assert!(
            matches!(result, CheckResult::Unsat),
            "the premise of every test here: got {result:?}"
        );
        let derivations = derivations.expect(
            "a plain universal refuted by instantiation is exactly the case this \
             certificate covers; None here means the capture never fires and the \
             negative controls below would be vacuous",
        );
        let certificate =
            portable_certificate(&mut parsed.arena, &assertions, &elimination, &derivations)
                .expect("every binding must be nameable, else there is no certificate to test");
        (parsed, assertions, certificate)
    }

    #[test]
    fn an_instantiation_refutation_produces_a_certificate_that_rechecks() {
        let (mut parsed, assertions, certificate) = refuted(ONE_INSTANCE);
        assert!(
            !certificate.instances.is_empty(),
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
    /// Guard (3) of the old design — "nothing was smuggled into the ground set"
    /// — is now structural: the checker builds the ground set itself, so there
    /// is nowhere to smuggle a conjunct. What remains attackable is the
    /// instance's own provenance, so that is what this attacks.
    #[test]
    fn an_instance_with_a_tampered_binding_is_rejected() {
        let (mut parsed, assertions, certificate) = refuted(ONE_INSTANCE);
        let intruder = parsed.arena.int_const(7);
        let mut tampered = certificate.clone();
        for instance in &mut tampered.instances {
            instance.bindings = vec![PortableBinding::Query(intruder)];
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

    /// Guard (4). No instances at all leaves the ground set unrefuted.
    #[test]
    fn true_but_insufficient_instances_are_rejected() {
        let (mut parsed, assertions, certificate) = refuted(ONE_INSTANCE);
        let empty = QuantifierInstanceSetCertificate {
            skolem_prefix: certificate.skolem_prefix.clone(),
            instances: Vec::new(),
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
            certificate.instances.len() >= 2,
            "this test is only meaningful with more than one instance; got {}",
            certificate.instances.len()
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

    /// THE SKOLEMISED CASE, re-parsed. The witness the producer instantiated at
    /// does not exist in the checker's arena until the checker makes its own —
    /// so this passes only if the elimination really is recorded positionally.
    #[test]
    fn a_skolemised_refutation_survives_an_independent_reparse() {
        let (_producing, _assertions, certificate) = refuted(BARBER);
        assert_eq!(
            certificate.skolem_prefix,
            vec![1],
            "the barber's single assertion loses exactly one existential binder"
        );
        assert!(
            certificate
                .instances
                .iter()
                .flat_map(|instance| &instance.bindings)
                .any(|binding| matches!(binding, PortableBinding::Witness { .. })),
            "the refuting instance is the universal at its own existential's \
             witness; if no binding is a witness this test proves nothing"
        );
        let mut fresh = parse_script(BARBER).expect("re-parses");
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

    /// A recorded elimination that does not match the query's is rejected.
    ///
    /// The counts are a fact about the query, so disagreement means the
    /// certificate is about a different one — and accepting it would let a
    /// refutation of some *other* skolemisation stand in for this query's.
    #[test]
    fn a_mismatched_elimination_record_is_rejected() {
        let (mut parsed, assertions, certificate) = refuted(BARBER);
        let mut tampered = certificate.clone();
        tampered.skolem_prefix = vec![0];
        assert!(
            !check_quantifier_instance_set(
                &mut parsed.arena,
                &assertions,
                &tampered,
                &SolverConfig::default(),
            )
            .expect("checker runs")
        );
        let mut wrong_length = certificate;
        wrong_length.skolem_prefix = vec![1, 1];
        assert!(
            !check_quantifier_instance_set(
                &mut parsed.arena,
                &assertions,
                &wrong_length,
                &SolverConfig::default(),
            )
            .expect("checker runs")
        );
    }

    /// A binding this arena cannot resolve must fail closed, not ABORT.
    ///
    /// This is the guard the previous test does not reach. A checker's arena is
    /// a fresh parse and is therefore *small*; a producing arena has been
    /// through a whole solve. So an id that is perfectly ordinary in the
    /// producer can be past the end of the checker's arena entirely — and
    /// `TermArena::sort_of` indexes directly, so rebuilding an instance around
    /// such a binding is a process abort rather than a `false`. Both halves of
    /// this test are id-resolution: a term-side id and a witness-side index.
    #[test]
    fn a_binding_this_arena_cannot_resolve_fails_closed() {
        let (mut producing, _assertions, certificate) = refuted(ONE_INSTANCE);
        // An id at the tail of the producing arena. Nothing about it is
        // malformed there; it simply does not exist in a fresh parse.
        let far = producing.arena.int_const(123_456);
        let mut fresh = parse_script(ONE_INSTANCE).expect("re-parses");
        let fresh_assertions = fresh.assertions.clone();
        assert!(
            far.index() >= fresh.arena.len(),
            "this test is only meaningful when the id is out of range for the \
             checker's arena; producing tail {} vs fresh len {}",
            far.index(),
            fresh.arena.len()
        );

        let mut dangling = certificate.clone();
        for instance in &mut dangling.instances {
            instance.bindings = vec![PortableBinding::Query(far)];
        }
        assert!(
            !check_quantifier_instance_set(
                &mut fresh.arena,
                &fresh_assertions,
                &dangling,
                &SolverConfig::default(),
            )
            .expect("checker must return a verdict, not abort")
        );

        // The same for a witness reference: naming a witness of an assertion
        // that has none is a lookup this arena cannot satisfy.
        let mut absent_witness = certificate;
        for instance in &mut absent_witness.instances {
            instance.bindings = vec![PortableBinding::Witness {
                assertion: 0,
                index: 0,
            }];
        }
        assert!(
            !check_quantifier_instance_set(
                &mut fresh.arena,
                &fresh_assertions,
                &absent_witness,
                &SolverConfig::default(),
            )
            .expect("checker must return a verdict, not abort")
        );
    }

    /// A certificate offered for a DIFFERENT query must fail closed, not abort.
    ///
    /// Its ids may not resolve in this arena at all, and the arena indexes
    /// directly — so without the membership tests this is a panic rather than a
    /// verdict.
    #[test]
    fn a_certificate_for_another_query_fails_closed() {
        let (_producing, _assertions, certificate) = refuted(ONE_INSTANCE);
        // Two assertions, none existential, so the certificate's shape checks
        // pass and the id-resolution path below is actually reached.
        let mut other = parse_script(
            "(set-logic QF_LIA)\n(declare-fun y () Int)\n\
             (assert (= y 1))\n(assert (> y 0))\n(check-sat)",
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
