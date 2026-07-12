//! E-matching quantifier instantiation on the e-graph keystone (Track 2, P2.6).
//!
//! [`instantiate_forall_via_egraph`] is the keystone-driven path for instantiating
//! a universal `∀x. body`: it builds an [`EGraph`] over the ground terms, selects a
//! trigger — a function-application subterm mentioning the bound variable, which
//! may be **nested** (`f(g(x))`) or **multi-argument with ground parts**
//! (`g(x, a)`) — e-matches it against the e-graph **modulo congruence**
//! ([`EGraph::ematch`]), and for each match substitutes the bound variable with a
//! representative of the matched argument class, producing the ground instances to
//! add and re-check. The solver loop evaluates equality-clause instances lazily:
//! already-true clauses are suppressed, while all-false and unit-like clauses are
//! checked before unresolved traffic. Unit-like equality clauses may detach one
//! literal only with source-bound or bounded-recursive checked provenance; the
//! public instantiation API remains the complete match set. Within one solve,
//! triggers compile/intern once and a shared bridge grows only with asserted source
//! instances; all unique patterns use one batched e-graph index per round
//! (ADR-0111). A revision-checked persistent index and root-symbol candidate
//! queues extend add-only rounds from the new node suffix and rematch only
//! affected patterns (ADR-0112). Merge rounds consume the e-graph union journal,
//! follow inverted parent paths, and root-canonicalize cached substitutions so
//! only reachable trigger roots need rematching (ADR-0113). Shared exact path
//! tries, class/ground filters, and retained top-application delta queues reduce
//! merge work without changing complete source instances (ADR-0114/0115/0116).
//!
//! Matching on the e-graph is congruence-aware for free: if the ground terms force
//! `a = b`, then `f(a)` and `f(b)` are one class and the trigger fires once, so the
//! instances follow the *semantic* term structure, not the syntactic one. This is
//! the migration of trigger instantiation onto the backtrackable, independently
//! checkable keystone (vs the bespoke congruence closure the existing
//! `axeyum_rewrite::instantiate_with_triggers` carries); deeper triggers,
//! inference, and the full instantiation loop build on it.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use axeyum_egraph::{EGraph, EMatchIndex, ENodeId, Pattern, Substitution};
use axeyum_ir::{FuncId, Op, Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

// Native uses the std clock; wasm uses the `web_time` drop-in (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};
use crate::cdclt::{CdclT, Lit as CdcltLit, Outcome as CdcltOutcome};
use crate::euf_egraph::{Encoder as EufEncoder, EufTheory, collect_eq_atoms};

/// Default e-matching instantiation rounds before giving up (`unknown`).
const MAX_INSTANTIATION_ROUNDS: usize = 8;

/// Deterministic cap on accumulated ground terms: e-matching a universal whose
/// instances generate ever-deeper terms (e.g. `∀x.(x≤y ∨ x≥y+1)` ⇒ `y, y+1, y+2, …`)
/// can explode a single round's `check_auto`, so the loop bails to `unknown` past this
/// many ground terms even with no wall-clock budget (the "never hang" rule).
const MAX_GROUND_TERMS: usize = 8192;

/// Deterministic retained-CDCL(T) admission caps (ADR-0119). Exceeding one
/// disables only the accelerator; the established fresh-QF route remains live.
const ONLINE_QUANTIFIER_LIMITS: OnlineQuantifierLimits = OnlineQuantifierLimits {
    variables: 65_536,
    clauses: 262_144,
    literals: 262_144,
};

/// Candidate equalities are a bounded search hint, never a proof premise
/// (ADR-0120). Exceeding either cap declines scoped candidate matching only.
const MAX_CANDIDATE_EQUALITIES: usize = 4096;
const MAX_CANDIDATE_APPLICATIONS: usize = 16_384;

/// Tries to refute a (possibly quantified) conjunction by **e-matching
/// instantiation on the e-graph** (Track 2, P2.6): it separates the ground
/// assertions from the universals, and repeatedly instantiates each universal over
/// the current ground terms ([`instantiate_forall_via_egraph`]), adds the fresh
/// instances, and re-checks the ground set with [`check_auto`] — until the ground
/// set is `unsat` (⇒ the original is `unsat`, since the universals entail every
/// instance), a round adds no new instance (instantiation fixpoint), or the round
/// budget is exhausted.
///
/// **Sound, incomplete:** a ground `unsat` is a real refutation; otherwise the
/// result is `unknown` (e-matching may simply not have found the refuting
/// instance). Quantifier-free inputs go straight to [`check_auto`].
///
/// # Errors
///
/// Propagates any [`SolverError`] from the ground solver.
pub fn prove_quantified_unsat_via_egraph(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let mut stats = QuantifierLoopStats::default();
    prove_quantified_unsat_via_egraph_impl(arena, assertions, config, true, true, &mut stats)
}

#[derive(Debug, Default, Clone, Copy)]
struct QuantifierLoopStats {
    qf_checks: usize,
    online_solves: usize,
    online_clauses: usize,
    candidate_checks: usize,
    candidate_equalities: usize,
    candidate_instances: usize,
    candidate_pattern_executions: usize,
    candidate_applications_scanned: usize,
}

fn prove_quantified_unsat_via_egraph_impl(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
    enable_online_clauses: bool,
    enable_candidate_equalities: bool,
    stats: &mut QuantifierLoopStats,
) -> Result<CheckResult, SolverError> {
    let (mut ground, foralls) = partition_top_level_foralls(arena, assertions);
    if foralls.is_empty() {
        return quantifier_qf_check(arena, &ground, config, stats);
    }

    if try_closed_universal_refutations(arena, &foralls, config)? {
        return Ok(CheckResult::Unsat);
    }

    if try_targeted_quantifier_refutations(arena, &ground, &foralls, config, stats)? {
        return Ok(CheckResult::Unsat);
    }

    // Honor the wall-clock budget + a deterministic ground-size cap so an exploding
    // instantiation degrades to a graceful `unknown`, never spins (the "never hang" rule).
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let mut seen: HashSet<TermId> = ground.iter().copied().collect();
    let mut ground_derivations: HashMap<TermId, QuantifierGroundDerivation> = HashMap::new();
    let mut matcher = IncrementalEmatchSession::new(arena, &foralls);
    let mut online_clauses = None;
    let mut online_attempted = !enable_online_clauses;
    let mut candidate_equalities_enabled = enable_candidate_equalities;
    for _ in 0..MAX_INSTANTIATION_ROUNDS {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: "e-matching: instantiation time budget exhausted".to_owned(),
            }));
        }
        if ground.len() > MAX_GROUND_TERMS {
            if matches!(
                quantifier_qf_check(arena, &ground, config, stats)?,
                CheckResult::Unsat
            ) {
                return Ok(CheckResult::Unsat);
            }
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: "e-matching: ground-term count budget exhausted".to_owned(),
            }));
        }
        // The first round and every accelerator fallback use the full QF route.
        // While retained CDCL(T) is live, generated checked clauses are tested
        // there directly and only a candidate refutation pays for full replay.
        if online_clauses.is_none() {
            if matches!(
                quantifier_qf_check(arena, &ground, config, stats)?,
                CheckResult::Unsat
            ) {
                return Ok(CheckResult::Unsat);
            }
            if !online_attempted {
                online_clauses = OnlineQuantifierClauseSession::new(arena, &ground, deadline);
                online_attempted = true;
            }
        }
        // Instantiate every universal over the current ground terms. Conflict and
        // unit-like clauses are scheduled globally before unresolved/non-clausal
        // instances; otherwise one noisy quantifier could hide another's immediate
        // refutation in the same round. Already-true clauses are monotone redundant
        // under this equality-only context and need not enter the ground query.
        let mut admitted = admit_next_source_batch(
            arena,
            assertions,
            &mut matcher,
            &mut seen,
            &mut ground,
            &mut ground_derivations,
        );
        if admitted.is_empty() && candidate_equalities_enabled {
            match scoped_candidate_fixpoint_step(
                arena,
                &mut ground,
                config,
                &mut matcher,
                &mut online_clauses,
                &mut seen,
                &mut ground_derivations,
                stats,
            )? {
                CandidateFixpointStep::Refuted => return Ok(CheckResult::Unsat),
                CandidateFixpointStep::Added(terms) => admitted = terms,
                CandidateFixpointStep::Disable => candidate_equalities_enabled = false,
                CandidateFixpointStep::NoProgress => {}
            }
        }
        if admitted.is_empty() {
            break; // source and scoped-candidate instantiation fixpoint
        }
        let online_outcome = online_clauses.as_mut().and_then(|session| {
            let outcome =
                session.add_checked_batch(arena, assertions, &admitted, &ground_derivations);
            if outcome.is_some() {
                stats.online_solves += 1;
                stats.online_clauses = session.inserted_clauses;
            }
            outcome
        });
        match online_outcome {
            Some(CdcltOutcome::Unsat) => {
                if replay_online_refutation(arena, &ground, config, stats)? {
                    return Ok(CheckResult::Unsat);
                }
                online_clauses = None;
            }
            Some(CdcltOutcome::Sat) => {}
            Some(CdcltOutcome::Unknown) | None => online_clauses = None,
        }
    }
    finish_quantified_ground_check(arena, &ground, config, stats)
}

enum CandidateFixpointStep {
    Refuted,
    Added(Vec<TermId>),
    Disable,
    NoProgress,
}

#[allow(clippy::too_many_arguments)]
fn scoped_candidate_fixpoint_step(
    arena: &mut TermArena,
    ground: &mut Vec<TermId>,
    config: &SolverConfig,
    matcher: &mut IncrementalEmatchSession,
    online_clauses: &mut Option<OnlineQuantifierClauseSession>,
    seen: &mut HashSet<TermId>,
    ground_derivations: &mut HashMap<TermId, QuantifierGroundDerivation>,
    stats: &mut QuantifierLoopStats,
) -> Result<CandidateFixpointStep, SolverError> {
    let Some(session) = online_clauses.as_mut() else {
        return Ok(CandidateFixpointStep::NoProgress);
    };
    let outcome = if let Some(outcome) = session.last_outcome {
        outcome
    } else {
        stats.online_solves += 1;
        let outcome = session.solve_current();
        stats.online_clauses = session.inserted_clauses;
        outcome
    };
    match outcome {
        CdcltOutcome::Unsat => {
            if replay_online_refutation(arena, ground, config, stats)? {
                return Ok(CandidateFixpointStep::Refuted);
            }
            *online_clauses = None;
            Ok(CandidateFixpointStep::NoProgress)
        }
        CdcltOutcome::Unknown => {
            *online_clauses = None;
            Ok(CandidateFixpointStep::NoProgress)
        }
        CdcltOutcome::Sat => {
            let candidate_equalities = session.true_equality_terms();
            stats.candidate_checks += 1;
            stats.candidate_equalities += candidate_equalities.len();
            let Some(candidate) = matcher.scoped_candidate_instances(arena, &candidate_equalities)
            else {
                return Ok(CandidateFixpointStep::Disable);
            };
            stats.candidate_instances += candidate.batch.urgent.len();
            stats.candidate_pattern_executions += candidate.pattern_executions;
            stats.candidate_applications_scanned += candidate.applications_scanned;
            let GeneratedGroundBatch {
                urgent,
                derivations,
                ..
            } = candidate.batch;
            Ok(CandidateFixpointStep::Added(admit_generated_ground(
                urgent,
                seen,
                ground,
                ground_derivations,
                &derivations,
            )))
        }
    }
}

fn replay_online_refutation(
    arena: &mut TermArena,
    ground: &[TermId],
    config: &SolverConfig,
    stats: &mut QuantifierLoopStats,
) -> Result<bool, SolverError> {
    Ok(matches!(
        quantifier_qf_check(arena, ground, config, stats)?,
        CheckResult::Unsat
    ))
}

fn partition_top_level_foralls(
    arena: &TermArena,
    assertions: &[TermId],
) -> (Vec<TermId>, Vec<TermId>) {
    assertions.iter().copied().partition(|&assertion| {
        !matches!(arena.node(assertion), TermNode::App { op, .. } if matches!(op, Op::Forall(_)))
    })
}

/// Refutes a closed universal sentence by solving its existentially witnessed
/// negated body once. A satisfiable negation makes the top-level universal false;
/// every other outcome declines to ordinary instantiation. The valid direction
/// is handled by `quant_valid_universal` before this route.
fn try_closed_universal_refutations(
    arena: &mut TermArena,
    foralls: &[TermId],
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    for &quantifier in foralls {
        if let Some(CheckResult::Unsat) = refute_closed_universal(arena, quantifier, config)? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Runs the narrow ADR-0095/0097/0099 instance proposers. Each proposal remains
/// untrusted until the ordinary QF solver refutes the resulting ground query.
fn try_targeted_quantifier_refutations(
    arena: &mut TermArena,
    ground: &[TermId],
    foralls: &[TermId],
    config: &SolverConfig,
    stats: &mut QuantifierLoopStats,
) -> Result<bool, SolverError> {
    for &quantifier in foralls {
        if let Some(instance) = nested_xor_discriminator_instance(arena, quantifier)? {
            let mut probe = ground.to_vec();
            probe.push(instance);
            if matches!(
                quantifier_qf_check(arena, &probe, config, stats)?,
                CheckResult::Unsat
            ) {
                return Ok(true);
            }
        }
    }
    for &quantifier in foralls {
        if let Some(instance) = euclidean_residue_instance(arena, quantifier)? {
            let mut probe = ground.to_vec();
            probe.push(instance);
            if matches!(
                quantifier_qf_check(arena, &probe, config, stats)?,
                CheckResult::Unsat
            ) {
                return Ok(true);
            }
        }
    }
    for &quantifier in foralls {
        if let Some(instances) = affine_growth_instances(arena, quantifier)? {
            let mut probe = ground.to_vec();
            probe.extend(instances);
            if matches!(
                quantifier_qf_check(arena, &probe, config, stats)?,
                CheckResult::Unsat
            ) {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn quantifier_qf_check(
    arena: &mut TermArena,
    ground: &[TermId],
    config: &SolverConfig,
    stats: &mut QuantifierLoopStats,
) -> Result<CheckResult, SolverError> {
    stats.qf_checks += 1;
    check_auto(arena, ground, config)
}

fn admit_next_source_batch(
    arena: &mut TermArena,
    assertions: &[TermId],
    matcher: &mut IncrementalEmatchSession,
    seen: &mut HashSet<TermId>,
    ground: &mut Vec<TermId>,
    retained: &mut HashMap<TermId, QuantifierGroundDerivation>,
) -> Vec<TermId> {
    matcher.extend_ground_with_derivations(arena, ground, retained);
    let GeneratedGroundBatch {
        mut urgent,
        mut deferred,
        derivations,
    } = collect_generated_ground(matcher, arena, assertions);
    urgent.sort_by_key(|term| term.index());
    urgent.dedup();
    deferred.sort_by_key(|term| term.index());
    deferred.dedup();

    let mut admitted = admit_generated_ground(urgent, seen, ground, retained, &derivations);
    // Once urgent traffic is exhausted, release unresolved clauses so mutually
    // constraining instances preserve the legacy loop's reach.
    if admitted.is_empty() {
        admitted = admit_generated_ground(deferred, seen, ground, retained, &derivations);
    }
    admitted
}

fn admit_generated_ground(
    terms: Vec<TermId>,
    seen: &mut HashSet<TermId>,
    ground: &mut Vec<TermId>,
    retained: &mut HashMap<TermId, QuantifierGroundDerivation>,
    candidates: &HashMap<TermId, QuantifierGroundDerivation>,
) -> Vec<TermId> {
    let mut added = Vec::new();
    for term in terms {
        if seen.insert(term) {
            if let Some(derivation) = candidates.get(&term) {
                retained.insert(term, derivation.clone());
            }
            ground.push(term);
            added.push(term);
        }
    }
    added
}

struct GeneratedGroundBatch {
    urgent: Vec<TermId>,
    deferred: Vec<TermId>,
    derivations: HashMap<TermId, QuantifierGroundDerivation>,
}

struct ScopedCandidateBatch {
    batch: GeneratedGroundBatch,
    pattern_executions: usize,
    applications_scanned: usize,
}

/// Retained equality-abstraction CDCL(T) state for checked generated clauses
/// (ADR-0119). It can prove refutations early but never produces product SAT.
struct OnlineQuantifierClauseSession {
    solver: CdclT,
    theory: EufTheory,
    atom_terms: Vec<TermId>,
    atom_variables: HashMap<TermId, usize>,
    inserted_clauses: usize,
    inserted_literals: usize,
    solve_calls: usize,
    last_outcome: Option<CdcltOutcome>,
    limits: OnlineQuantifierLimits,
}

#[derive(Debug, Clone, Copy)]
struct OnlineQuantifierLimits {
    variables: usize,
    clauses: usize,
    literals: usize,
}

impl OnlineQuantifierClauseSession {
    fn new(arena: &TermArena, ground: &[TermId], deadline: Option<Instant>) -> Option<Self> {
        Self::new_with_limits(arena, ground, deadline, ONLINE_QUANTIFIER_LIMITS)
    }

    fn new_with_limits(
        arena: &TermArena,
        ground: &[TermId],
        deadline: Option<Instant>,
        limits: OnlineQuantifierLimits,
    ) -> Option<Self> {
        let mut atom_terms = Vec::new();
        let mut seen = HashSet::new();
        for &assertion in ground {
            collect_eq_atoms(arena, assertion, &mut atom_terms, &mut seen);
        }
        let atom_variables: HashMap<TermId, usize> = atom_terms
            .iter()
            .copied()
            .enumerate()
            .map(|(variable, term)| (term, variable))
            .collect();
        let mut encoder = EufEncoder::new(&atom_terms);
        let mut clauses = Vec::new();
        for &assertion in ground {
            let top = encoder.encode(arena, assertion, &mut clauses)?;
            clauses.push(vec![crate::euf_egraph::Lit {
                var: top,
                positive: true,
            }]);
        }
        let literal_count = clauses.iter().map(Vec::len).sum::<usize>();
        if encoder.var_count > limits.variables
            || clauses.len() > limits.clauses
            || literal_count > limits.literals
        {
            return None;
        }
        let clauses = clauses
            .into_iter()
            .map(|clause| {
                clause
                    .into_iter()
                    .map(|literal| CdcltLit {
                        var: literal.var,
                        positive: literal.positive,
                    })
                    .collect()
            })
            .collect();
        let theory = EufTheory::new(arena, &atom_terms);
        let solver = CdclT::new(encoder.var_count, atom_terms.len(), clauses, deadline);
        Some(Self {
            solver,
            theory,
            atom_terms,
            atom_variables,
            inserted_clauses: 0,
            inserted_literals: 0,
            solve_calls: 0,
            last_outcome: None,
            limits,
        })
    }

    /// Rechecks and inserts one batch at level zero, then resumes the retained
    /// search. `None` disables the accelerator and leaves fresh-QF fallback live.
    fn add_checked_batch(
        &mut self,
        arena: &mut TermArena,
        assertions: &[TermId],
        terms: &[TermId],
        derivations: &HashMap<TermId, QuantifierGroundDerivation>,
    ) -> Option<CdcltOutcome> {
        self.solver.backtrack_to_root(&mut self.theory);
        for &term in terms {
            let derivation = derivations.get(&term)?;
            if !check_quantifier_ground_derivation(arena, assertions, derivation) {
                return None;
            }
            self.add_equality_clause(arena, term)?;
        }
        Some(self.solve_current())
    }

    fn solve_current(&mut self) -> CdcltOutcome {
        self.solve_calls += 1;
        let outcome = self.solver.solve(&mut self.theory);
        self.last_outcome = Some(outcome);
        outcome
    }

    /// Equality atoms true in the current complete SAT candidate, in stable
    /// theory-atom order. Non-SAT states expose no candidate facts.
    fn true_equality_terms(&self) -> Vec<TermId> {
        if self.last_outcome != Some(CdcltOutcome::Sat) {
            return Vec::new();
        }
        self.atom_terms
            .iter()
            .copied()
            .enumerate()
            .filter_map(|(atom, term)| {
                let variable = self.solver.theory_variable(atom)?;
                (self.solver.value(variable) == Some(true)).then_some(term)
            })
            .collect()
    }

    fn add_equality_clause(&mut self, arena: &TermArena, term: TermId) -> Option<()> {
        let atoms = match equality_clause_atoms(arena, term) {
            OnlineClauseShape::Unsupported => return None,
            OnlineClauseShape::Tautology => return Some(()),
            OnlineClauseShape::Atoms(atoms) => atoms,
        };
        if self.solver.clause_count() >= self.limits.clauses
            || self.inserted_literals.saturating_add(atoms.len()) > self.limits.literals
        {
            return None;
        }
        let mut clause = Vec::with_capacity(atoms.len());
        for (atom_term, positive) in atoms {
            let variable = self.ensure_atom(arena, atom_term)?;
            clause.push(CdcltLit {
                var: variable,
                positive,
            });
        }
        clause.sort_by_key(|literal| (literal.var, literal.positive));
        if clause
            .windows(2)
            .any(|pair| pair[0].var == pair[1].var && pair[0].positive != pair[1].positive)
        {
            return Some(()); // complementary literals make the clause true
        }
        clause.dedup();
        self.inserted_literals += clause.len();
        self.inserted_clauses += 1;
        self.solver.add_permanent_clause(clause);
        Some(())
    }

    fn ensure_atom(&mut self, arena: &TermArena, atom_term: TermId) -> Option<usize> {
        if let Some(&variable) = self.atom_variables.get(&atom_term) {
            return Some(variable);
        }
        if self.solver.variable_count() >= self.limits.variables {
            return None;
        }
        let (variable, solver_atom) = self.solver.add_theory_variable();
        let theory_atom = self.theory.add_atom_at_root(arena, atom_term).ok()?;
        if solver_atom != theory_atom {
            return None;
        }
        self.atom_terms.push(atom_term);
        self.atom_variables.insert(atom_term, variable);
        Some(variable)
    }
}

enum OnlineClauseShape {
    Unsupported,
    Tautology,
    Atoms(Vec<(TermId, bool)>),
}

/// Classifies a generated term as an unsupported shape, a tautology, or an
/// equality clause represented by underlying atom terms and polarities.
fn equality_clause_atoms(arena: &TermArena, term: TermId) -> OnlineClauseShape {
    let mut literals = Vec::new();
    collect_clause_literals(arena, term, &mut literals);
    let mut atoms = Vec::new();
    for literal in literals {
        match arena.node(literal) {
            TermNode::BoolConst(true) => return OnlineClauseShape::Tautology,
            TermNode::BoolConst(false) => {}
            TermNode::App { op: Op::Eq, args } if args.len() == 2 => {
                atoms.push((literal, true));
            }
            TermNode::App {
                op: Op::BoolNot,
                args,
            } if args.len() == 1
                && matches!(
                    arena.node(args[0]),
                    TermNode::App { op: Op::Eq, args } if args.len() == 2
                ) =>
            {
                atoms.push((args[0], false));
            }
            _ => return OnlineClauseShape::Unsupported,
        }
    }
    OnlineClauseShape::Atoms(atoms)
}

fn collect_generated_ground(
    matcher: &mut IncrementalEmatchSession,
    arena: &mut TermArena,
    assertions: &[TermId],
) -> GeneratedGroundBatch {
    let mut urgent = Vec::new();
    let mut deferred = Vec::new();
    let mut propagations = Vec::new();
    let mut derivations = HashMap::new();
    for batch in matcher.lazy_clause_batches(arena) {
        urgent.extend(batch.urgent);
        propagations.extend(batch.propagations);
        deferred.extend(batch.deferred);
        for (instance, certificate) in batch.instance_certificates {
            derivations
                .entry(instance)
                .or_insert(QuantifierGroundDerivation::Instance(certificate));
        }
    }
    for (term, derivation) in checked_propagation_additions(arena, assertions, &propagations) {
        urgent.push(term);
        derivations.entry(term).or_insert(derivation);
    }
    GeneratedGroundBatch {
        urgent,
        deferred,
        derivations,
    }
}

fn finish_quantified_ground_check(
    arena: &mut TermArena,
    ground: &[TermId],
    config: &SolverConfig,
    stats: &mut QuantifierLoopStats,
) -> Result<CheckResult, SolverError> {
    match quantifier_qf_check(arena, ground, config, stats)? {
        CheckResult::Unsat => Ok(CheckResult::Unsat),
        _ => Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: "e-matching instantiation did not refute within the round budget".to_owned(),
        })),
    }
}

fn checked_propagation_additions(
    arena: &mut TermArena,
    assertions: &[TermId],
    propagations: &[QuantifierClausePropagationCertificate],
) -> Vec<(TermId, QuantifierGroundDerivation)> {
    let checked = check_quantifier_clause_propagations(arena, assertions, propagations);
    propagations
        .iter()
        .map(|propagation| {
            if checked {
                (
                    propagation.propagated_literal,
                    QuantifierGroundDerivation::Propagation(Box::new(propagation.clone())),
                )
            } else {
                (
                    propagation.source_instance,
                    QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
                        assertion: propagation.assertion,
                        bindings: propagation.bindings.clone(),
                        instance: propagation.source_instance,
                    }),
                )
            }
        })
        .collect()
}

/// Instantiates the universal `forall_term` by e-matching a trigger against the
/// `ground` terms, returning the ground instances of its body. Returns an empty
/// vector when `forall_term` is not a universal, has no trigger covering all bound
/// variables, or the trigger's symbols do not occur in the ground terms.
///
/// # Panics
///
/// Panics only if the quantifier binds more than `u32::MAX` variables (which no
/// real input does).
#[must_use]
pub fn instantiate_forall_via_egraph(
    arena: &mut TermArena,
    ground: &[TermId],
    forall_term: TermId,
) -> Vec<TermId> {
    let Some((vars, body, tuples)) = witness_tuples_via_egraph(arena, ground, forall_term) else {
        return Vec::new();
    };
    let var_terms: Vec<TermId> = vars.iter().map(|&v| arena.var(v)).collect();
    let mut instances = Vec::new();
    for tuple in &tuples {
        let replacements: HashMap<TermId, TermId> = var_terms
            .iter()
            .copied()
            .zip(tuple.iter().copied())
            .collect();
        let mut memo = HashMap::new();
        if let Ok(instance) = replace_subterms(arena, body, &replacements, &mut memo) {
            instances.push(instance);
        }
    }
    instances.sort_by_key(|t| t.index());
    instances.dedup();
    instances
}

/// One round of conservative lazy clause evaluation (ADR-0110).
///
/// `urgent` contains complete source instances whose equality clause is false or
/// has at most one undetermined literal. `deferred` contains multi-undetermined
/// clauses and every shape outside the supported clause fragment. Clauses already
/// true in the recorded ground equality context are omitted.
#[derive(Debug, Default)]
struct LazyClauseBatch {
    urgent: Vec<TermId>,
    propagations: Vec<QuantifierClausePropagationCertificate>,
    deferred: Vec<TermId>,
    instance_certificates: BTreeMap<TermId, QuantifierInstanceCertificate>,
    redundant: usize,
}

struct CompiledUniversal {
    assertion: TermId,
    vars: Vec<SymbolId>,
    var_terms: Vec<TermId>,
    body: TermId,
    pattern_indices: Vec<usize>,
}

/// Named facts that replay one false sibling of a detached quantified clause.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifierFalseSiblingJustification {
    /// The exact false equality/disequality literal from the source instance.
    pub literal: TermId,
    /// Sorted source or recursively derived equality/disequality terms sufficient
    /// to make `literal` false in a fresh congruence closure.
    pub reasons: Vec<TermId>,
}

/// Exact provenance for one complete ground universal instance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifierInstanceCertificate {
    /// The untouched original universal assertion.
    pub assertion: TermId,
    /// Ground terms substituted for the universal prefix, outermost first.
    pub bindings: Vec<TermId>,
    /// The exact reconstructed ground instance.
    pub instance: TermId,
}

/// A generated ground equality/disequality derivation used by a later
/// false-sibling justification (ADR-0118).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantifierGroundDerivation {
    /// A complete exact universal instance.
    Instance(QuantifierInstanceCertificate),
    /// An earlier independently checked detached propagation.
    Propagation(Box<QuantifierClausePropagationCertificate>),
}

impl QuantifierGroundDerivation {
    fn conclusion(&self) -> TermId {
        match self {
            Self::Instance(certificate) => certificate.instance,
            Self::Propagation(certificate) => certificate.propagated_literal,
        }
    }
}

/// Replayable implication from one universal instance plus checked ground facts
/// to a detached equality/disequality literal (ADR-0117/0118).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifierClausePropagationCertificate {
    /// The untouched original universal assertion.
    pub assertion: TermId,
    /// Ground terms substituted for the universal prefix, outermost first.
    pub bindings: Vec<TermId>,
    /// The exact complete source instance reconstructed from `assertion`.
    pub source_instance: TermId,
    /// The sole non-false equality/disequality literal propagated to QF search.
    pub propagated_literal: TermId,
    /// Every other source-instance literal, in clause order.
    pub false_siblings: Vec<QuantifierFalseSiblingJustification>,
    /// Sorted derivations for every named false-sibling reason that is not an
    /// original assertion. Source-only ADR-0117 certificates leave this empty.
    pub derived_reasons: Vec<QuantifierGroundDerivation>,
}

/// Independently checks a detached quantifier-clause propagation.
///
/// The checker reconstructs the complete universal instance and evaluates every
/// false sibling in a fresh e-graph containing only its named source or checked
/// derived reasons. It does not consult retained matching/search state.
#[must_use]
pub fn check_quantifier_clause_propagation(
    arena: &mut TermArena,
    assertions: &[TermId],
    certificate: &QuantifierClausePropagationCertificate,
) -> bool {
    check_quantifier_clause_propagations(arena, assertions, std::slice::from_ref(certificate))
}

/// Independently checks a batch of detached propagations under one shared
/// recursive replay budget.
#[must_use]
pub fn check_quantifier_clause_propagations(
    arena: &mut TermArena,
    assertions: &[TermId],
    certificates: &[QuantifierClausePropagationCertificate],
) -> bool {
    if certificates.is_empty() {
        return true;
    }
    let mut checker = QuantifierProvenanceChecker {
        assertions: assertions.iter().copied().collect(),
        remaining_nodes: MAX_QUANTIFIER_PROVENANCE_NODES,
    };
    certificates
        .iter()
        .all(|certificate| checker.check_propagation(arena, certificate, 0))
}

/// Independently checks one generated ground derivation against the untouched
/// assertion set. This is the admission gate for retained online clauses.
#[must_use]
pub fn check_quantifier_ground_derivation(
    arena: &mut TermArena,
    assertions: &[TermId],
    derivation: &QuantifierGroundDerivation,
) -> bool {
    let mut checker = QuantifierProvenanceChecker {
        assertions: assertions.iter().copied().collect(),
        remaining_nodes: MAX_QUANTIFIER_PROVENANCE_NODES,
    };
    checker.check_derivation(arena, derivation, 0)
}

const MAX_QUANTIFIER_PROVENANCE_DEPTH: usize = 16;
const MAX_QUANTIFIER_PROVENANCE_NODES: usize = 4096;

struct QuantifierProvenanceChecker {
    assertions: HashSet<TermId>,
    remaining_nodes: usize,
}

impl QuantifierProvenanceChecker {
    fn check_propagation(
        &mut self,
        arena: &mut TermArena,
        certificate: &QuantifierClausePropagationCertificate,
        depth: usize,
    ) -> bool {
        if depth > MAX_QUANTIFIER_PROVENANCE_DEPTH || !self.take_node() {
            return false;
        }
        let instance = QuantifierInstanceCertificate {
            assertion: certificate.assertion,
            bindings: certificate.bindings.clone(),
            instance: certificate.source_instance,
        };
        if equality_literal(arena, certificate.propagated_literal).is_none()
            || !self.check_instance(arena, &instance)
            || !Self::derivation_table_is_canonical(certificate)
        {
            return false;
        }

        let mut literals = Vec::new();
        collect_clause_literals(arena, certificate.source_instance, &mut literals);
        let Some(propagated_index) = literals
            .iter()
            .position(|&literal| literal == certificate.propagated_literal)
        else {
            return false;
        };
        if literals
            .iter()
            .skip(propagated_index + 1)
            .any(|&literal| literal == certificate.propagated_literal)
            || literals.len() != certificate.false_siblings.len() + 1
        {
            return false;
        }

        let required_derived: BTreeSet<TermId> = certificate
            .false_siblings
            .iter()
            .flat_map(|sibling| sibling.reasons.iter().copied())
            .filter(|reason| !self.assertions.contains(reason))
            .collect();
        let supplied_derived: BTreeSet<TermId> = certificate
            .derived_reasons
            .iter()
            .map(QuantifierGroundDerivation::conclusion)
            .collect();
        if required_derived != supplied_derived {
            return false;
        }
        for derivation in &certificate.derived_reasons {
            if !self.check_derivation(arena, derivation, depth + 1) {
                return false;
            }
        }

        let expected_siblings = literals
            .into_iter()
            .enumerate()
            .filter_map(|(index, literal)| (index != propagated_index).then_some(literal));
        let mut all_reasons = BTreeSet::new();
        for (expected, sibling) in expected_siblings.zip(&certificate.false_siblings) {
            if sibling.literal != expected
                || sibling
                    .reasons
                    .windows(2)
                    .any(|pair| pair[0].index() >= pair[1].index())
                || sibling
                    .reasons
                    .iter()
                    .any(|reason| !self.reason_is_available(certificate, *reason))
            {
                return false;
            }
            if matches!(arena.node(sibling.literal), TermNode::BoolConst(false)) {
                if !sibling.reasons.is_empty() {
                    return false;
                }
            } else {
                let mut facts = GroundEqualityContext::new(arena, &sibling.reasons);
                if evaluate_equality_clause(arena, sibling.literal, &mut facts)
                    != Some(ClauseValue::False)
                {
                    return false;
                }
            }
            all_reasons.extend(sibling.reasons.iter().copied());
        }
        let mut facts =
            GroundEqualityContext::new(arena, &all_reasons.into_iter().collect::<Vec<_>>());
        evaluate_equality_clause(arena, certificate.source_instance, &mut facts)
            == Some(ClauseValue::Unit)
    }

    fn check_derivation(
        &mut self,
        arena: &mut TermArena,
        derivation: &QuantifierGroundDerivation,
        depth: usize,
    ) -> bool {
        if depth > MAX_QUANTIFIER_PROVENANCE_DEPTH {
            return false;
        }
        match derivation {
            QuantifierGroundDerivation::Instance(certificate) => {
                self.take_node() && self.check_instance(arena, certificate)
            }
            QuantifierGroundDerivation::Propagation(certificate) => {
                self.check_propagation(arena, certificate, depth)
            }
        }
    }

    fn check_instance(
        &self,
        arena: &mut TermArena,
        certificate: &QuantifierInstanceCertificate,
    ) -> bool {
        if !self.assertions.contains(&certificate.assertion) {
            return false;
        }
        let (vars, body) = peel_foralls(arena, certificate.assertion);
        if vars.is_empty() || vars.len() != certificate.bindings.len() {
            return false;
        }
        let bound: HashSet<SymbolId> = vars.iter().copied().collect();
        if vars
            .iter()
            .zip(&certificate.bindings)
            .any(|(&var, &binding)| {
                arena.symbol(var).1 != arena.sort_of(binding)
                    || contains_any_symbol(arena, binding, &bound)
            })
        {
            return false;
        }
        let replacements: HashMap<TermId, TermId> = vars
            .iter()
            .map(|&var| arena.var(var))
            .zip(certificate.bindings.iter().copied())
            .collect();
        let mut memo = HashMap::new();
        replace_subterms(arena, body, &replacements, &mut memo)
            .is_ok_and(|instance| instance == certificate.instance)
    }

    fn derivation_table_is_canonical(certificate: &QuantifierClausePropagationCertificate) -> bool {
        certificate
            .derived_reasons
            .windows(2)
            .all(|pair| pair[0].conclusion().index() < pair[1].conclusion().index())
    }

    fn reason_is_available(
        &self,
        certificate: &QuantifierClausePropagationCertificate,
        reason: TermId,
    ) -> bool {
        equality_literal_reason_shape(reason, &self.assertions, certificate)
    }

    fn take_node(&mut self) -> bool {
        let Some(remaining) = self.remaining_nodes.checked_sub(1) else {
            return false;
        };
        self.remaining_nodes = remaining;
        true
    }
}

fn equality_literal_reason_shape(
    reason: TermId,
    assertions: &HashSet<TermId>,
    certificate: &QuantifierClausePropagationCertificate,
) -> bool {
    assertions.contains(&reason)
        || certificate
            .derived_reasons
            .binary_search_by_key(&reason.index(), |derivation| {
                derivation.conclusion().index()
            })
            .is_ok()
}

#[derive(Debug, Default)]
struct PatternPathNode {
    children: BTreeMap<PatternPathStep, usize>,
    terminals: Vec<PatternPathTerminal>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct GroundArgumentFilter {
    argument_index: usize,
    declaration: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct PatternPathStep {
    declaration: u32,
    argument_index: usize,
    ground_argument: Option<GroundArgumentFilter>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct PatternPathTerminal {
    pattern_index: usize,
    start_declaration: Option<u32>,
}

#[derive(Debug, Clone, Copy)]
enum PatternFilterMode {
    ClassAndGround,
    #[cfg(test)]
    Unfiltered,
    #[cfg(test)]
    ClassOnly,
    #[cfg(test)]
    GroundOnly,
}

impl PatternFilterMode {
    fn use_class_labels(self) -> bool {
        match self {
            Self::ClassAndGround => true,
            #[cfg(test)]
            Self::ClassOnly => true,
            #[cfg(test)]
            Self::Unfiltered | Self::GroundOnly => false,
        }
    }

    fn use_ground_arguments(self) -> bool {
        match self {
            Self::ClassAndGround => true,
            #[cfg(test)]
            Self::GroundOnly => true,
            #[cfg(test)]
            Self::Unfiltered | Self::ClassOnly => false,
        }
    }
}

/// Shared child-to-root `(declaration, argument-index)` paths (ADR-0114).
#[derive(Debug)]
struct PatternPathIndex {
    nodes: Vec<PatternPathNode>,
}

impl Default for PatternPathIndex {
    fn default() -> Self {
        Self {
            nodes: vec![PatternPathNode::default()],
        }
    }
}

impl PatternPathIndex {
    fn add_pattern(&mut self, pattern: &Pattern, pattern_index: usize) {
        self.add_subpattern_paths(pattern, &[], pattern_index);
    }

    fn add_subpattern_paths(
        &mut self,
        pattern: &Pattern,
        outer_path: &[PatternPathStep],
        pattern_index: usize,
    ) {
        let Pattern::App(declaration, arguments) = pattern else {
            return;
        };
        let ground_argument =
            arguments
                .iter()
                .enumerate()
                .find_map(|(argument_index, argument)| match argument {
                    Pattern::App(declaration, children) if children.is_empty() => {
                        Some(GroundArgumentFilter {
                            argument_index,
                            declaration: *declaration,
                        })
                    }
                    Pattern::Var(_) | Pattern::App(_, _) => None,
                });
        for (argument_index, child) in arguments.iter().enumerate() {
            let mut path = Vec::with_capacity(outer_path.len() + 1);
            path.push(PatternPathStep {
                declaration: *declaration,
                argument_index,
                ground_argument,
            });
            path.extend_from_slice(outer_path);
            let start_declaration = match child {
                Pattern::App(declaration, _) => Some(*declaration),
                Pattern::Var(_) => None,
            };
            self.insert(
                &path,
                PatternPathTerminal {
                    pattern_index,
                    start_declaration,
                },
            );
            self.add_subpattern_paths(child, &path, pattern_index);
        }
    }

    fn insert(&mut self, path: &[PatternPathStep], terminal: PatternPathTerminal) {
        let mut node_index = 0;
        for &step in path {
            let next = if let Some(&next) = self.nodes[node_index].children.get(&step) {
                next
            } else {
                let next = self.nodes.len();
                self.nodes.push(PatternPathNode::default());
                self.nodes[node_index].children.insert(step, next);
                next
            };
            node_index = next;
        }
        self.nodes[node_index].terminals.push(terminal);
    }

    fn finish(&mut self) {
        for node in &mut self.nodes {
            node.terminals.sort_unstable();
            node.terminals.dedup();
        }
    }

    #[cfg(test)]
    fn affected_patterns(&self, egraph: &EGraph, starts: &[ENodeId]) -> BTreeSet<usize> {
        self.affected_patterns_with_filters(egraph, starts, PatternFilterMode::ClassAndGround)
    }

    fn affected_candidates(
        &self,
        egraph: &EGraph,
        starts: &[ENodeId],
    ) -> BTreeMap<usize, BTreeSet<ENodeId>> {
        self.affected_candidates_with_filters(egraph, starts, PatternFilterMode::ClassAndGround)
    }

    #[cfg(test)]
    fn affected_patterns_with_filters(
        &self,
        egraph: &EGraph,
        starts: &[ENodeId],
        filters: PatternFilterMode,
    ) -> BTreeSet<usize> {
        self.affected_candidates_with_filters(egraph, starts, filters)
            .into_keys()
            .collect()
    }

    fn affected_candidates_with_filters(
        &self,
        egraph: &EGraph,
        starts: &[ENodeId],
        filters: PatternFilterMode,
    ) -> BTreeMap<usize, BTreeSet<ENodeId>> {
        let mut pending = Vec::new();
        let mut seen = HashSet::new();
        for &start in starts {
            let start = egraph.root(start);
            let state = (start, 0, start);
            if seen.insert(state) {
                pending.push(state);
            }
        }

        let mut candidates: BTreeMap<usize, BTreeSet<ENodeId>> = BTreeMap::new();
        while let Some((class, path_node, start_class)) = pending.pop() {
            for &parent in egraph.parents(class) {
                let declaration = egraph.decl(parent);
                for (argument_index, &argument) in egraph.args(parent).iter().enumerate() {
                    if egraph.root(argument) != class {
                        continue;
                    }
                    for (step, &next_path_node) in &self.nodes[path_node].children {
                        if step.declaration != declaration
                            || step.argument_index != argument_index
                            || (filters.use_ground_arguments()
                                && !Self::ground_argument_matches(egraph, parent, *step))
                        {
                            continue;
                        }
                        for terminal in &self.nodes[next_path_node].terminals {
                            if !filters.use_class_labels()
                                || terminal.start_declaration.is_none_or(|required| {
                                    egraph.class_has_declaration(start_class, required)
                                })
                            {
                                candidates
                                    .entry(terminal.pattern_index)
                                    .or_default()
                                    .insert(parent);
                            }
                        }
                        let state = (egraph.root(parent), next_path_node, start_class);
                        if seen.insert(state) {
                            pending.push(state);
                        }
                    }
                }
            }
        }
        candidates
    }

    fn ground_argument_matches(egraph: &EGraph, parent: ENodeId, step: PatternPathStep) -> bool {
        let Some(filter) = step.ground_argument else {
            return true;
        };
        egraph
            .args(parent)
            .get(filter.argument_index)
            .is_some_and(|&argument| egraph.class_has_declaration(argument, filter.declaration))
    }
}

#[derive(Debug, Clone, Copy)]
enum MergeInvalidationMode {
    ExactPaths,
    #[cfg(test)]
    ExactPathsFullPatterns,
    #[cfg(test)]
    ExactPathsUnfiltered,
    #[cfg(test)]
    ExactPathsClassOnly,
    #[cfg(test)]
    ExactPathsGroundOnly,
    #[cfg(test)]
    Declarations,
    #[cfg(test)]
    All,
}

/// Retained matching state for one quantified refutation attempt (ADR-0111/0112).
///
/// Patterns and bridge declaration ids are stable for the complete attempt.
/// Ground terms and equalities grow monotonically between rounds. Add-only
/// rounds extend a revision-checked e-graph index and rematch only patterns whose
/// root declaration gained an application. Merge rounds additionally rematch
/// roots reached through transitive e-graph parent paths. Generated top-level
/// terms retain exact-instance or checked-propagation derivations for later
/// false-sibling explanations.
struct IncrementalEmatchSession {
    bridge: InstBridge,
    patterns: Vec<Pattern>,
    patterns_by_root: HashMap<u32, Vec<usize>>,
    quantifiers_by_pattern: HashMap<usize, Vec<usize>>,
    merge_paths: PatternPathIndex,
    /// Patterns requiring a complete root-declaration scan (initialization and
    /// test-only conservative baselines).
    dirty_patterns: BTreeSet<usize>,
    /// Exact top applications added or reached since each pattern's last scan.
    candidate_patterns: BTreeMap<usize, BTreeSet<ENodeId>>,
    pattern_matches: Vec<Vec<Substitution>>,
    match_index: EMatchIndex,
    quantifiers: Vec<CompiledUniversal>,
    processed_ground: HashSet<TermId>,
    source_ground: HashSet<TermId>,
    ground_derivations: HashMap<TermId, QuantifierGroundDerivation>,
    equality_reason_terms: HashMap<u32, TermId>,
    disequality_nodes: Vec<(TermId, ENodeId, ENodeId)>,
    disequalities: HashSet<(ENodeId, ENodeId)>,
    match_rounds: usize,
    pattern_executions: usize,
    candidate_applications_scanned: usize,
    merge_invalidations: usize,
    merge_affected_patterns: usize,
    extensions: usize,
}

impl IncrementalEmatchSession {
    fn new(arena: &mut TermArena, foralls: &[TermId]) -> Self {
        let mut bridge = InstBridge::new();
        let mut patterns = Vec::new();
        let mut pattern_ids: HashMap<Pattern, usize> = HashMap::new();
        let mut quantifiers = Vec::with_capacity(foralls.len());

        for &forall_term in foralls {
            let (vars, body) = peel_foralls(arena, forall_term);
            let var_terms = vars.iter().map(|&var| arena.var(var)).collect();
            let var_index: HashMap<SymbolId, u32> = vars
                .iter()
                .enumerate()
                .map(|(index, &var)| (var, u32::try_from(index).expect("variable count fits u32")))
                .collect();
            let mut pattern_indices = Vec::new();
            if !vars.is_empty() {
                for trigger in select_triggers(arena, body, &var_index) {
                    let pattern = bridge.trigger_to_pattern(arena, trigger, &var_index);
                    let index = if let Some(&index) = pattern_ids.get(&pattern) {
                        index
                    } else {
                        let index = patterns.len();
                        patterns.push(pattern.clone());
                        pattern_ids.insert(pattern, index);
                        index
                    };
                    pattern_indices.push(index);
                }
            }
            quantifiers.push(CompiledUniversal {
                assertion: forall_term,
                vars,
                var_terms,
                body,
                pattern_indices,
            });
        }

        let mut patterns_by_root: HashMap<u32, Vec<usize>> = HashMap::new();
        for (index, pattern) in patterns.iter().enumerate() {
            if let Pattern::App(decl, _) = pattern {
                patterns_by_root.entry(*decl).or_default().push(index);
            }
        }
        let dirty_patterns = (0..patterns.len()).collect();
        let mut quantifiers_by_pattern: HashMap<usize, Vec<usize>> = HashMap::new();
        for (quantifier_index, quantifier) in quantifiers.iter().enumerate() {
            let unique_patterns: BTreeSet<usize> =
                quantifier.pattern_indices.iter().copied().collect();
            for pattern in unique_patterns {
                quantifiers_by_pattern
                    .entry(pattern)
                    .or_default()
                    .push(quantifier_index);
            }
        }
        let pattern_matches = vec![Vec::new(); patterns.len()];
        let match_index = bridge.egraph.new_match_index();
        let mut merge_paths = PatternPathIndex::default();
        for (index, pattern) in patterns.iter().enumerate() {
            merge_paths.add_pattern(pattern, index);
        }
        merge_paths.finish();

        Self {
            bridge,
            patterns,
            patterns_by_root,
            quantifiers_by_pattern,
            merge_paths,
            dirty_patterns,
            candidate_patterns: BTreeMap::new(),
            pattern_matches,
            match_index,
            quantifiers,
            processed_ground: HashSet::new(),
            source_ground: HashSet::new(),
            ground_derivations: HashMap::new(),
            equality_reason_terms: HashMap::new(),
            disequality_nodes: Vec::new(),
            disequalities: HashSet::new(),
            match_rounds: 0,
            pattern_executions: 0,
            candidate_applications_scanned: 0,
            merge_invalidations: 0,
            merge_affected_patterns: 0,
            extensions: 0,
        }
    }

    /// Registers only top-level ground terms not seen in an earlier round. All
    /// term nodes are added before positive equalities are merged, matching the
    /// monotone add-node/merge notification order used by a retained MAM.
    #[cfg(test)]
    fn extend_ground(&mut self, arena: &TermArena, ground: &[TermId]) {
        self.extend_ground_impl(
            arena,
            ground,
            &HashMap::new(),
            MergeInvalidationMode::ExactPaths,
        );
    }

    fn extend_ground_with_derivations(
        &mut self,
        arena: &TermArena,
        ground: &[TermId],
        derivations: &HashMap<TermId, QuantifierGroundDerivation>,
    ) {
        self.extend_ground_impl(
            arena,
            ground,
            derivations,
            MergeInvalidationMode::ExactPaths,
        );
    }

    #[cfg(test)]
    fn extend_ground_with_full_merge_invalidation(&mut self, arena: &TermArena, ground: &[TermId]) {
        self.extend_ground_impl(arena, ground, &HashMap::new(), MergeInvalidationMode::All);
    }

    #[cfg(test)]
    fn extend_ground_with_declaration_merge_invalidation(
        &mut self,
        arena: &TermArena,
        ground: &[TermId],
    ) {
        self.extend_ground_impl(
            arena,
            ground,
            &HashMap::new(),
            MergeInvalidationMode::Declarations,
        );
    }

    #[cfg(test)]
    fn extend_ground_with_path_filters(
        &mut self,
        arena: &TermArena,
        ground: &[TermId],
        filters: PatternFilterMode,
    ) {
        let mode = match filters {
            PatternFilterMode::ClassAndGround => MergeInvalidationMode::ExactPaths,
            PatternFilterMode::Unfiltered => MergeInvalidationMode::ExactPathsUnfiltered,
            PatternFilterMode::ClassOnly => MergeInvalidationMode::ExactPathsClassOnly,
            PatternFilterMode::GroundOnly => MergeInvalidationMode::ExactPathsGroundOnly,
        };
        self.extend_ground_impl(arena, ground, &HashMap::new(), mode);
    }

    #[cfg(test)]
    fn extend_ground_with_full_pattern_path_invalidation(
        &mut self,
        arena: &TermArena,
        ground: &[TermId],
    ) {
        self.extend_ground_impl(
            arena,
            ground,
            &HashMap::new(),
            MergeInvalidationMode::ExactPathsFullPatterns,
        );
    }

    fn extend_ground_impl(
        &mut self,
        arena: &TermArena,
        ground: &[TermId],
        derivations: &HashMap<TermId, QuantifierGroundDerivation>,
        merge_invalidation: MergeInvalidationMode,
    ) {
        let new_terms: Vec<TermId> = ground
            .iter()
            .copied()
            .filter(|term| self.processed_ground.insert(*term))
            .collect();
        if new_terms.is_empty() {
            return;
        }
        if self.extensions == 0 {
            self.source_ground.extend(new_terms.iter().copied());
        } else {
            for &term in &new_terms {
                if let Some(derivation) = derivations.get(&term) {
                    self.ground_derivations.insert(term, derivation.clone());
                }
            }
        }
        self.extensions += 1;
        let node_start = self.bridge.egraph.len();

        for &term in &new_terms {
            self.bridge.add_term(arena, term);
        }
        let added_applications = self.bridge.egraph.application_nodes_since(node_start);
        let mut merge_starts = Vec::new();
        for &term in &new_terms {
            if let Some((true, lhs, rhs)) = equality_literal(arena, term) {
                self.equality_reason_terms
                    .insert(u32::try_from(term.index()).unwrap_or(u32::MAX), term);
                let lhs = self.bridge.add_term(arena, lhs);
                let rhs = self.bridge.add_term(arena, rhs);
                if !self.bridge.egraph.equal(lhs, rhs) {
                    merge_starts.extend([lhs, rhs]);
                }
                self.bridge
                    .egraph
                    .merge(lhs, rhs, u32::try_from(term.index()).unwrap_or(u32::MAX));
            }
        }

        for application in added_applications {
            if let Some(patterns) = self
                .patterns_by_root
                .get(&self.bridge.egraph.decl(application))
            {
                for &pattern in patterns {
                    self.candidate_patterns
                        .entry(pattern)
                        .or_default()
                        .insert(application);
                }
            }
        }
        if !merge_starts.is_empty() {
            let affected_count = self.queue_merge_invalidation(&merge_starts, merge_invalidation);
            self.merge_invalidations += 1;
            self.merge_affected_patterns += affected_count;
        }
        for &term in &new_terms {
            if let Some((false, lhs, rhs)) = equality_literal(arena, term) {
                let lhs = self.bridge.add_term(arena, lhs);
                let rhs = self.bridge.add_term(arena, rhs);
                self.disequality_nodes.push((term, lhs, rhs));
            }
        }
        self.refresh_disequalities();
    }

    fn queue_merge_invalidation(
        &mut self,
        merge_starts: &[ENodeId],
        mode: MergeInvalidationMode,
    ) -> usize {
        match mode {
            MergeInvalidationMode::ExactPaths => {
                let affected = self
                    .merge_paths
                    .affected_candidates(&self.bridge.egraph, merge_starts);
                self.queue_candidate_map(affected)
            }
            #[cfg(test)]
            MergeInvalidationMode::ExactPathsFullPatterns => {
                let affected = self
                    .merge_paths
                    .affected_patterns(&self.bridge.egraph, merge_starts);
                let count = affected.len();
                self.dirty_patterns.extend(affected);
                count
            }
            #[cfg(test)]
            MergeInvalidationMode::ExactPathsUnfiltered => {
                let affected = self.merge_paths.affected_candidates_with_filters(
                    &self.bridge.egraph,
                    merge_starts,
                    PatternFilterMode::Unfiltered,
                );
                self.queue_candidate_map(affected)
            }
            #[cfg(test)]
            MergeInvalidationMode::ExactPathsClassOnly => {
                let affected = self.merge_paths.affected_candidates_with_filters(
                    &self.bridge.egraph,
                    merge_starts,
                    PatternFilterMode::ClassOnly,
                );
                self.queue_candidate_map(affected)
            }
            #[cfg(test)]
            MergeInvalidationMode::ExactPathsGroundOnly => {
                let affected = self.merge_paths.affected_candidates_with_filters(
                    &self.bridge.egraph,
                    merge_starts,
                    PatternFilterMode::GroundOnly,
                );
                self.queue_candidate_map(affected)
            }
            #[cfg(test)]
            MergeInvalidationMode::Declarations => {
                let mut affected = BTreeSet::new();
                for declaration in self
                    .bridge
                    .egraph
                    .inverted_parent_declarations(merge_starts)
                {
                    if let Some(patterns) = self.patterns_by_root.get(&declaration) {
                        affected.extend(patterns.iter().copied());
                    }
                }
                let count = affected.len();
                self.dirty_patterns.extend(affected);
                count
            }
            #[cfg(test)]
            MergeInvalidationMode::All => {
                self.dirty_patterns.extend(0..self.patterns.len());
                self.patterns.len()
            }
        }
    }

    fn queue_candidate_map(&mut self, affected: BTreeMap<usize, BTreeSet<ENodeId>>) -> usize {
        let count = affected.len();
        for (pattern, candidates) in affected {
            self.candidate_patterns
                .entry(pattern)
                .or_default()
                .extend(candidates);
        }
        count
    }

    fn refresh_disequalities(&mut self) {
        self.disequalities.clear();
        for &(_, lhs, rhs) in &self.disequality_nodes {
            let lhs = self.bridge.egraph.root(lhs);
            let rhs = self.bridge.egraph.root(rhs);
            self.disequalities.insert(ordered_node_pair(lhs, rhs));
        }
    }

    /// Finds source instances enabled only modulo the retained SAT candidate's
    /// true equalities (ADR-0120). Candidate merges live in one e-graph scope;
    /// concrete tuples are materialized before pop, and only complete exact
    /// instances leave this method. Candidate facts never enter explanation maps.
    fn scoped_candidate_instances(
        &mut self,
        arena: &mut TermArena,
        equality_terms: &[TermId],
    ) -> Option<ScopedCandidateBatch> {
        self.scoped_candidate_instances_with_limits(
            arena,
            equality_terms,
            MAX_CANDIDATE_EQUALITIES,
            MAX_CANDIDATE_APPLICATIONS,
        )
    }

    fn scoped_candidate_instances_with_limits(
        &mut self,
        arena: &mut TermArena,
        equality_terms: &[TermId],
        equality_limit: usize,
        application_limit: usize,
    ) -> Option<ScopedCandidateBatch> {
        if equality_terms.len() > equality_limit {
            return None;
        }
        let mut endpoints = Vec::new();
        for &term in equality_terms {
            let (true, lhs, rhs) = equality_literal(arena, term)? else {
                return None;
            };
            let (&lhs, &rhs) = (
                self.bridge.term_to_node.get(&lhs)?,
                self.bridge.term_to_node.get(&rhs)?,
            );
            if !self.bridge.egraph.equal(lhs, rhs) {
                endpoints.push((lhs, rhs));
            }
        }
        if endpoints.is_empty() {
            return Some(ScopedCandidateBatch {
                batch: GeneratedGroundBatch {
                    urgent: Vec::new(),
                    deferred: Vec::new(),
                    derivations: HashMap::new(),
                },
                pattern_executions: 0,
                applications_scanned: 0,
            });
        }

        self.bridge.egraph.push();
        let mut merge_starts = Vec::with_capacity(endpoints.len() * 2);
        for (lhs, rhs) in endpoints {
            merge_starts.extend([lhs, rhs]);
            self.bridge.egraph.merge(lhs, rhs, u32::MAX);
        }
        let affected = self
            .merge_paths
            .affected_candidates(&self.bridge.egraph, &merge_starts);
        let applications_scanned = affected.values().map(BTreeSet::len).sum::<usize>();
        if applications_scanned > application_limit {
            self.bridge.egraph.pop();
            return None;
        }

        let dirty: Vec<usize> = affected.keys().copied().collect();
        let patterns: Vec<Pattern> = dirty
            .iter()
            .map(|&index| self.patterns[index].clone())
            .collect();
        let candidates: Vec<Vec<ENodeId>> = affected
            .into_values()
            .map(|nodes| nodes.into_iter().collect())
            .collect();
        let mut scoped_matches: BTreeMap<usize, Vec<Substitution>> = BTreeMap::new();
        let mut impacted_quantifiers = BTreeSet::new();
        if !dirty.is_empty() {
            let mut scoped_index = self.bridge.egraph.new_match_index();
            let matches = self.bridge.egraph.ematch_many_candidates_indexed(
                &patterns,
                &candidates,
                &mut scoped_index,
            );
            for (index, matches) in dirty.iter().copied().zip(matches) {
                let mut combined = self.pattern_matches[index].clone();
                combined.extend(matches);
                combined.sort_unstable();
                combined.dedup();
                scoped_matches.insert(index, combined);
                if let Some(quantifiers) = self.quantifiers_by_pattern.get(&index) {
                    impacted_quantifiers.extend(quantifiers.iter().copied());
                }
            }
        }
        let tuple_batches: Vec<(usize, Option<Vec<Vec<TermId>>>)> = impacted_quantifiers
            .into_iter()
            .map(|index| {
                (
                    index,
                    self.witness_tuples_with_overrides(
                        &self.quantifiers[index],
                        &self.pattern_matches,
                        Some(&scoped_matches),
                    ),
                )
            })
            .collect();
        self.bridge.egraph.pop();
        Some(ScopedCandidateBatch {
            batch: self.materialize_candidate_instances(arena, tuple_batches),
            pattern_executions: dirty.len(),
            applications_scanned,
        })
    }

    fn materialize_candidate_instances(
        &self,
        arena: &mut TermArena,
        tuple_batches: Vec<(usize, Option<Vec<Vec<TermId>>>)>,
    ) -> GeneratedGroundBatch {
        let mut urgent = Vec::new();
        let mut derivations = HashMap::new();
        for (quantifier_index, tuples) in tuple_batches {
            let Some(tuples) = tuples else {
                continue;
            };
            let quantifier = &self.quantifiers[quantifier_index];
            for tuple in tuples {
                let replacements: HashMap<TermId, TermId> = quantifier
                    .var_terms
                    .iter()
                    .copied()
                    .zip(tuple.iter().copied())
                    .collect();
                let mut memo = HashMap::new();
                let Ok(instance) =
                    replace_subterms(arena, quantifier.body, &replacements, &mut memo)
                else {
                    continue;
                };
                derivations.entry(instance).or_insert_with(|| {
                    QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
                        assertion: quantifier.assertion,
                        bindings: tuple,
                        instance,
                    })
                });
                urgent.push(instance);
            }
        }
        urgent.sort_by_key(|term| term.index());
        urgent.dedup();
        GeneratedGroundBatch {
            urgent,
            deferred: Vec::new(),
            derivations,
        }
    }

    fn lazy_clause_batches(&mut self, arena: &mut TermArena) -> Vec<LazyClauseBatch> {
        let tuple_batches = self.match_witness_tuples();
        self.quantifiers
            .iter()
            .zip(tuple_batches)
            .map(|(quantifier, tuples)| {
                let Some(tuples) = tuples else {
                    return LazyClauseBatch::default();
                };
                let mut batch = LazyClauseBatch::default();
                for tuple in &tuples {
                    let replacements: HashMap<TermId, TermId> = quantifier
                        .var_terms
                        .iter()
                        .copied()
                        .zip(tuple.iter().copied())
                        .collect();
                    let mut memo = HashMap::new();
                    let Ok(instance) =
                        replace_subterms(arena, quantifier.body, &replacements, &mut memo)
                    else {
                        continue;
                    };
                    batch
                        .instance_certificates
                        .entry(instance)
                        .or_insert_with(|| QuantifierInstanceCertificate {
                            assertion: quantifier.assertion,
                            bindings: tuple.clone(),
                            instance,
                        });
                    match evaluate_equality_clause_with(arena, instance, &mut |lhs, rhs| {
                        self.equality(lhs, rhs)
                    }) {
                        Some(ClauseValue::True) => batch.redundant += 1,
                        Some(ClauseValue::False) => batch.urgent.push(instance),
                        Some(ClauseValue::Unit) => {
                            match self.detached_propagation(arena, quantifier, tuple, instance) {
                                Some(propagation) => batch.propagations.push(propagation),
                                None => batch.urgent.push(instance),
                            }
                        }
                        Some(ClauseValue::Undetermined) | None => batch.deferred.push(instance),
                    }
                }
                batch.urgent.sort_by_key(|term| term.index());
                batch.urgent.dedup();
                batch.propagations.sort_by_key(|propagation| {
                    (
                        propagation.propagated_literal.index(),
                        propagation.source_instance.index(),
                    )
                });
                batch.propagations.dedup_by_key(|propagation| {
                    (propagation.propagated_literal, propagation.source_instance)
                });
                batch.deferred.sort_by_key(|term| term.index());
                batch.deferred.dedup();
                batch
            })
            .collect()
    }

    fn detached_propagation(
        &self,
        arena: &TermArena,
        quantifier: &CompiledUniversal,
        tuple: &[TermId],
        source_instance: TermId,
    ) -> Option<QuantifierClausePropagationCertificate> {
        let mut literals = Vec::new();
        collect_clause_literals(arena, source_instance, &mut literals);
        let mut propagated_literal = None;
        let mut false_siblings = Vec::new();
        for literal in literals {
            match self.literal_value(arena, literal)? {
                LiteralValue::True => return None,
                LiteralValue::Undetermined => {
                    if propagated_literal.replace(literal).is_some() {
                        return None;
                    }
                }
                LiteralValue::False => {
                    false_siblings.push(self.false_sibling_justification(arena, literal)?);
                }
            }
        }
        let propagated_literal = propagated_literal?;
        if false_siblings.is_empty() {
            return None;
        }
        equality_literal(arena, propagated_literal)?;
        let mut derived_reason_terms: Vec<TermId> = false_siblings
            .iter()
            .flat_map(|sibling| sibling.reasons.iter().copied())
            .filter(|reason| !self.source_ground.contains(reason))
            .collect();
        derived_reason_terms.sort_by_key(|term| term.index());
        derived_reason_terms.dedup();
        let derived_reasons = derived_reason_terms
            .into_iter()
            .map(|reason| self.ground_derivations.get(&reason).cloned())
            .collect::<Option<Vec<_>>>()?;
        Some(QuantifierClausePropagationCertificate {
            assertion: quantifier.assertion,
            bindings: tuple.to_vec(),
            source_instance,
            propagated_literal,
            false_siblings,
            derived_reasons,
        })
    }

    fn literal_value(&self, arena: &TermArena, literal: TermId) -> Option<LiteralValue> {
        if let TermNode::BoolConst(value) = arena.node(literal) {
            return Some(if *value {
                LiteralValue::True
            } else {
                LiteralValue::False
            });
        }
        let (positive, lhs, rhs) = equality_literal(arena, literal)?;
        let value = self.equality(lhs, rhs);
        Some(if positive { value } else { value.negate() })
    }

    fn false_sibling_justification(
        &self,
        arena: &TermArena,
        literal: TermId,
    ) -> Option<QuantifierFalseSiblingJustification> {
        if matches!(arena.node(literal), TermNode::BoolConst(false)) {
            return Some(QuantifierFalseSiblingJustification {
                literal,
                reasons: Vec::new(),
            });
        }
        let (positive, lhs, rhs) = equality_literal(arena, literal)?;
        let reasons = if positive {
            self.disequality_reasons(lhs, rhs)?
        } else {
            self.equality_reasons(lhs, rhs)?
        };
        Some(QuantifierFalseSiblingJustification { literal, reasons })
    }

    fn equality_reasons(&self, lhs: TermId, rhs: TermId) -> Option<Vec<TermId>> {
        let (&lhs, &rhs) = (
            self.bridge.term_to_node.get(&lhs)?,
            self.bridge.term_to_node.get(&rhs)?,
        );
        if !self.bridge.egraph.equal(lhs, rhs) {
            return None;
        }
        self.explanation_terms(lhs, rhs)
    }

    fn disequality_reasons(&self, lhs: TermId, rhs: TermId) -> Option<Vec<TermId>> {
        let (&lhs, &rhs) = (
            self.bridge.term_to_node.get(&lhs)?,
            self.bridge.term_to_node.get(&rhs)?,
        );
        let pair = ordered_node_pair(self.bridge.egraph.root(lhs), self.bridge.egraph.root(rhs));
        for &(reason, disequal_lhs, disequal_rhs) in &self.disequality_nodes {
            if !self.reason_has_provenance(reason)
                || ordered_node_pair(
                    self.bridge.egraph.root(disequal_lhs),
                    self.bridge.egraph.root(disequal_rhs),
                ) != pair
            {
                continue;
            }
            for (left, right) in [(disequal_lhs, disequal_rhs), (disequal_rhs, disequal_lhs)] {
                let (Some(mut lhs_reasons), Some(rhs_reasons)) = (
                    self.explanation_terms(lhs, left),
                    self.explanation_terms(rhs, right),
                ) else {
                    continue;
                };
                lhs_reasons.extend(rhs_reasons);
                lhs_reasons.push(reason);
                lhs_reasons.sort_by_key(|term| term.index());
                lhs_reasons.dedup();
                return Some(lhs_reasons);
            }
        }
        None
    }

    fn explanation_terms(&self, lhs: ENodeId, rhs: ENodeId) -> Option<Vec<TermId>> {
        if !self.bridge.egraph.equal(lhs, rhs) {
            return None;
        }
        let mut terms = Vec::new();
        for reason in self.bridge.egraph.explain(lhs, rhs) {
            let &term = self.equality_reason_terms.get(&reason)?;
            if !self.reason_has_provenance(term) {
                return None;
            }
            terms.push(term);
        }
        terms.sort_by_key(|term| term.index());
        terms.dedup();
        Some(terms)
    }

    fn reason_has_provenance(&self, term: TermId) -> bool {
        self.source_ground.contains(&term) || self.ground_derivations.contains_key(&term)
    }

    fn match_witness_tuples(&mut self) -> Vec<Option<Vec<Vec<TermId>>>> {
        if !self.dirty_patterns.is_empty() {
            let dirty: Vec<usize> = self.dirty_patterns.iter().copied().collect();
            let patterns: Vec<Pattern> = dirty
                .iter()
                .map(|&index| self.patterns[index].clone())
                .collect();
            let matches = self
                .bridge
                .egraph
                .ematch_many_indexed(&patterns, &mut self.match_index);
            for (index, matches) in dirty.iter().copied().zip(matches) {
                self.pattern_matches[index] = matches;
            }
            self.pattern_executions += dirty.len();
            for index in &dirty {
                self.candidate_patterns.remove(index);
            }
            self.dirty_patterns.clear();
        }
        if !self.candidate_patterns.is_empty() {
            let pending = std::mem::take(&mut self.candidate_patterns);
            let dirty: Vec<usize> = pending.keys().copied().collect();
            let patterns: Vec<Pattern> = dirty
                .iter()
                .map(|&index| self.patterns[index].clone())
                .collect();
            let candidates: Vec<Vec<ENodeId>> = pending
                .into_values()
                .map(|candidates| candidates.into_iter().collect())
                .collect();
            let matches = self.bridge.egraph.ematch_many_candidates_indexed(
                &patterns,
                &candidates,
                &mut self.match_index,
            );
            for (index, matches) in dirty.iter().copied().zip(matches) {
                self.pattern_matches[index].extend(matches);
                self.pattern_matches[index].sort_unstable();
                self.pattern_matches[index].dedup();
            }
            self.pattern_executions += dirty.len();
            self.candidate_applications_scanned += candidates.iter().map(Vec::len).sum::<usize>();
        }
        self.match_rounds += 1;
        self.quantifiers
            .iter()
            .map(|quantifier| self.witness_tuples(quantifier, &self.pattern_matches))
            .collect()
    }

    fn witness_tuples(
        &self,
        quantifier: &CompiledUniversal,
        pattern_matches: &[Vec<Vec<Option<ENodeId>>>],
    ) -> Option<Vec<Vec<TermId>>> {
        self.witness_tuples_with_overrides(quantifier, pattern_matches, None)
    }

    fn witness_tuples_with_overrides(
        &self,
        quantifier: &CompiledUniversal,
        pattern_matches: &[Vec<Substitution>],
        overrides: Option<&BTreeMap<usize, Vec<Substitution>>>,
    ) -> Option<Vec<Vec<TermId>>> {
        if quantifier.vars.is_empty() || quantifier.pattern_indices.is_empty() {
            return None;
        }
        let nvars = quantifier.vars.len();
        let mut joined: Vec<Vec<Option<ENodeId>>> = vec![vec![None; nvars]];
        for &pattern_index in &quantifier.pattern_indices {
            let matches = overrides
                .and_then(|matches| matches.get(&pattern_index))
                .or_else(|| pattern_matches.get(pattern_index))?;
            let mut next = Vec::new();
            for partial in &joined {
                for matched in matches {
                    if let Some(merged) =
                        merge_substitutions_modulo(&self.bridge.egraph, partial, matched)
                    {
                        next.push(merged);
                    }
                }
            }
            joined = next;
            if joined.is_empty() {
                return None;
            }
        }

        let mut tuples = Vec::new();
        for substitution in joined {
            let mut tuple = Vec::with_capacity(nvars);
            let complete = (0..nvars).all(|index| {
                if let Some(term) = substitution
                    .get(index)
                    .copied()
                    .flatten()
                    .map(|class| self.bridge.egraph.root(class))
                    .and_then(|root| self.bridge.repr_term.get(&root).copied())
                {
                    tuple.push(term);
                    true
                } else {
                    false
                }
            });
            if complete {
                tuples.push(tuple);
            }
        }
        tuples.sort_by(|left, right| {
            left.iter()
                .map(|term| term.index())
                .cmp(right.iter().map(|term| term.index()))
        });
        tuples.dedup();
        Some(tuples)
    }

    /// Conservative equality lookup over terms already registered from the
    /// active ground context. Missing body terms remain undetermined instead of
    /// mutating retained matching state before their source instance is asserted.
    fn equality(&self, lhs: TermId, rhs: TermId) -> LiteralValue {
        if lhs == rhs {
            return LiteralValue::True;
        }
        let (Some(&lhs), Some(&rhs)) = (
            self.bridge.term_to_node.get(&lhs),
            self.bridge.term_to_node.get(&rhs),
        ) else {
            return LiteralValue::Undetermined;
        };
        if self.bridge.egraph.equal(lhs, rhs) {
            return LiteralValue::True;
        }
        let pair = ordered_node_pair(self.bridge.egraph.root(lhs), self.bridge.egraph.root(rhs));
        if self.disequalities.contains(&pair) {
            LiteralValue::False
        } else {
            LiteralValue::Undetermined
        }
    }
}

#[cfg(test)]
fn lazy_clause_instances(
    arena: &mut TermArena,
    ground: &[TermId],
    forall_term: TermId,
) -> LazyClauseBatch {
    let Some(matches) = witness_matches_via_egraph(arena, ground, forall_term) else {
        return LazyClauseBatch::default();
    };
    let WitnessMatches {
        vars,
        body,
        tuples,
        bridge,
    } = matches;
    let var_terms: Vec<TermId> = vars.iter().map(|&v| arena.var(v)).collect();
    let mut facts = GroundEqualityContext::from_matching_bridge(arena, ground, bridge);
    let mut batch = LazyClauseBatch::default();
    for tuple in &tuples {
        let replacements: HashMap<TermId, TermId> = var_terms
            .iter()
            .copied()
            .zip(tuple.iter().copied())
            .collect();
        let mut memo = HashMap::new();
        let Ok(instance) = replace_subterms(arena, body, &replacements, &mut memo) else {
            continue;
        };
        match evaluate_equality_clause(arena, instance, &mut facts) {
            Some(ClauseValue::True) => batch.redundant += 1,
            Some(ClauseValue::False | ClauseValue::Unit) => batch.urgent.push(instance),
            Some(ClauseValue::Undetermined) | None => batch.deferred.push(instance),
        }
    }
    batch.urgent.sort_by_key(|t| t.index());
    batch.urgent.dedup();
    batch.deferred.sort_by_key(|t| t.index());
    batch.deferred.dedup();
    batch
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClauseValue {
    True,
    False,
    Unit,
    Undetermined,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LiteralValue {
    True,
    False,
    Undetermined,
}

impl LiteralValue {
    fn negate(self) -> Self {
        match self {
            Self::True => Self::False,
            Self::False => Self::True,
            Self::Undetermined => Self::Undetermined,
        }
    }
}

/// Equality/disequality unit facts used to justify clause classification.
///
/// This deliberately ignores non-unit Boolean structure. Missing information is
/// `Undetermined`, so classification can lose pruning but cannot invent truth.
struct GroundEqualityContext {
    bridge: InstBridge,
    disequalities: HashSet<(ENodeId, ENodeId)>,
}

impl GroundEqualityContext {
    fn new(arena: &TermArena, ground: &[TermId]) -> Self {
        let mut bridge = InstBridge::new();
        for &term in ground {
            bridge.add_term(arena, term);
        }
        Self::from_bridge(arena, ground, bridge)
    }

    fn from_bridge(arena: &TermArena, ground: &[TermId], mut bridge: InstBridge) -> Self {
        for &term in ground {
            if let Some((true, lhs, rhs)) = equality_literal(arena, term) {
                let lhs = bridge.add_term(arena, lhs);
                let rhs = bridge.add_term(arena, rhs);
                bridge
                    .egraph
                    .merge(lhs, rhs, u32::try_from(term.index()).unwrap_or(u32::MAX));
            }
        }
        Self::from_matching_bridge(arena, ground, bridge)
    }

    /// Reuses the bridge built by `witness_matches_via_egraph`, which has already
    /// merged every positive top-level equality for congruence-aware matching.
    fn from_matching_bridge(arena: &TermArena, ground: &[TermId], mut bridge: InstBridge) -> Self {
        let mut disequalities = HashSet::new();
        for &term in ground {
            if let Some((false, lhs, rhs)) = equality_literal(arena, term) {
                let lhs = bridge.add_term(arena, lhs);
                let rhs = bridge.add_term(arena, rhs);
                let lhs = bridge.egraph.root(lhs);
                let rhs = bridge.egraph.root(rhs);
                disequalities.insert(ordered_node_pair(lhs, rhs));
            }
        }
        Self {
            bridge,
            disequalities,
        }
    }

    fn equality(&mut self, arena: &TermArena, lhs: TermId, rhs: TermId) -> LiteralValue {
        let lhs = self.bridge.add_term(arena, lhs);
        let rhs = self.bridge.add_term(arena, rhs);
        if self.bridge.egraph.equal(lhs, rhs) {
            return LiteralValue::True;
        }
        let lhs_root = self.bridge.egraph.root(lhs);
        let rhs_root = self.bridge.egraph.root(rhs);
        if self
            .disequalities
            .contains(&ordered_node_pair(lhs_root, rhs_root))
        {
            LiteralValue::False
        } else {
            LiteralValue::Undetermined
        }
    }
}

fn ordered_node_pair(a: ENodeId, b: ENodeId) -> (ENodeId, ENodeId) {
    if a <= b { (a, b) } else { (b, a) }
}

fn equality_literal(arena: &TermArena, term: TermId) -> Option<(bool, TermId, TermId)> {
    match arena.node(term) {
        TermNode::App { op: Op::Eq, args } if args.len() == 2 => Some((true, args[0], args[1])),
        TermNode::App {
            op: Op::BoolNot,
            args,
        } if args.len() == 1 => match arena.node(args[0]) {
            TermNode::App { op: Op::Eq, args } if args.len() == 2 => {
                Some((false, args[0], args[1]))
            }
            _ => None,
        },
        _ => None,
    }
}

fn evaluate_equality_clause(
    arena: &TermArena,
    clause: TermId,
    facts: &mut GroundEqualityContext,
) -> Option<ClauseValue> {
    evaluate_equality_clause_with(arena, clause, &mut |lhs, rhs| {
        facts.equality(arena, lhs, rhs)
    })
}

fn evaluate_equality_clause_with(
    arena: &TermArena,
    clause: TermId,
    equality: &mut impl FnMut(TermId, TermId) -> LiteralValue,
) -> Option<ClauseValue> {
    let mut literals = Vec::new();
    collect_clause_literals(arena, clause, &mut literals);
    let mut undetermined = 0usize;
    for literal in literals {
        let value = if let TermNode::BoolConst(value) = arena.node(literal) {
            if *value {
                LiteralValue::True
            } else {
                LiteralValue::False
            }
        } else {
            let (positive, lhs, rhs) = equality_literal(arena, literal)?;
            let value = equality(lhs, rhs);
            if positive { value } else { value.negate() }
        };
        match value {
            LiteralValue::True => return Some(ClauseValue::True),
            LiteralValue::False => {}
            LiteralValue::Undetermined => undetermined += 1,
        }
    }
    Some(match undetermined {
        0 => ClauseValue::False,
        1 => ClauseValue::Unit,
        _ => ClauseValue::Undetermined,
    })
}

fn collect_clause_literals(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    match arena.node(term) {
        TermNode::App {
            op: Op::BoolOr,
            args,
        } if args.len() == 2 => {
            collect_clause_literals(arena, args[0], out);
            collect_clause_literals(arena, args[1], out);
        }
        _ => out.push(term),
    }
}

/// E-matches the universal `forall_term`'s trigger(s) against the `ground` terms
/// and returns, in addition to the bound variables and quantifier-free body, the
/// **witness tuples** — one ground term per bound variable, in binder order
/// (outermost first) — that the e-matching selects. Tuples are deterministically
/// ordered and de-duplicated.
///
/// This is the witness-tuple source the Alethe quantifier emitter
/// ([`crate::prove_quant_unsat_alethe`]) consumes when the brute-force cartesian
/// search would blow its candidate cap: e-matching is trigger-driven, so it scales
/// to many ground terms / multiple binders where the cartesian product does not.
/// The returned tuples are *candidates* — the caller validates that some subset
/// actually refutes the ground set before emitting a proof, so an unhelpful match
/// set is rejected cleanly, never turned into a bad proof.
///
/// Returns `None` when `forall_term` is not a universal, has no trigger covering
/// all bound variables, or no complete witness tuple is found (the trigger's
/// symbols do not occur in the ground terms).
///
/// # Panics
///
/// Panics only if the quantifier binds more than `u32::MAX` variables (which no
/// real input does).
#[must_use]
pub fn witness_tuples_via_egraph(
    arena: &mut TermArena,
    ground: &[TermId],
    forall_term: TermId,
) -> Option<(Vec<SymbolId>, TermId, Vec<Vec<TermId>>)> {
    let matches = witness_matches_via_egraph(arena, ground, forall_term)?;
    Some((matches.vars, matches.body, matches.tuples))
}

struct WitnessMatches {
    vars: Vec<SymbolId>,
    body: TermId,
    tuples: Vec<Vec<TermId>>,
    #[cfg(test)]
    bridge: InstBridge,
}

fn witness_matches_via_egraph(
    arena: &mut TermArena,
    ground: &[TermId],
    forall_term: TermId,
) -> Option<WitnessMatches> {
    // Peel the (possibly nested) universal prefix `∀x. ∀y. … body`.
    let (vars, body) = peel_foralls(arena, forall_term);
    if vars.is_empty() {
        return None;
    }
    let var_index: HashMap<SymbolId, u32> = vars
        .iter()
        .enumerate()
        .map(|(i, &v)| (v, u32::try_from(i).expect("variable count fits u32")))
        .collect();

    // Infer a (possibly multi-pattern) trigger: a set of function-application
    // subterms whose bound variables together cover all of them. A single term is
    // used when one covers all variables; otherwise a greedy set cover (matched
    // and joined below) handles patterns like `∀x,y. f(x) = g(y)`.
    let triggers = select_triggers(arena, body, &var_index);
    if triggers.is_empty() {
        return None;
    }

    let mut bridge = InstBridge::new();
    for &g in ground {
        bridge.add_term(arena, g);
        // A top-level ground equality `(= s t)` asserts s = t — merge it so matching
        // is genuinely modulo the ground congruence.
        if let TermNode::App { op, args } = arena.node(g)
            && matches!(op, Op::Eq)
            && args.len() == 2
        {
            let (s, t) = (args[0], args[1]);
            let ns = bridge.add_term(arena, s);
            let nt = bridge.add_term(arena, t);
            bridge.egraph.merge(ns, nt, 0);
        }
    }

    // Match each trigger and join the per-trigger substitutions into full
    // substitutions consistent on shared variables.
    let nvars = vars.len();
    let mut joined: Vec<Vec<Option<ENodeId>>> = vec![vec![None; nvars]];
    for trigger in triggers {
        let pattern = bridge.trigger_to_pattern(arena, trigger, &var_index);
        let matches = bridge.egraph.ematch(&pattern);
        let mut next = Vec::new();
        for partial in &joined {
            for m in &matches {
                if let Some(merged) = merge_substitutions(partial, m) {
                    next.push(merged);
                }
            }
        }
        joined = next;
        if joined.is_empty() {
            return None;
        }
    }

    let mut tuples: Vec<Vec<TermId>> = Vec::new();
    for subst in joined {
        // Build the witness tuple from every bound variable's matched class
        // representative; skip incomplete matches.
        let mut tuple: Vec<TermId> = Vec::with_capacity(nvars);
        let complete = (0..nvars).all(|i| {
            if let Some(repr) = subst
                .get(i)
                .copied()
                .flatten()
                .and_then(|class| bridge.repr_term.get(&class).copied())
            {
                tuple.push(repr);
                true
            } else {
                false
            }
        });
        if complete {
            tuples.push(tuple);
        }
    }
    // Deterministic order and de-dup (tuples compare lexicographically by index).
    tuples.sort_by(|x, y| x.iter().map(|t| t.index()).cmp(y.iter().map(|t| t.index())));
    tuples.dedup();
    Some(WitnessMatches {
        vars,
        body,
        tuples,
        #[cfg(test)]
        bridge,
    })
}

/// Peels the universal prefix `∀v1. ∀v2. … body`, returning the bound variables
/// (outer first) and the innermost non-quantified body.
fn peel_foralls(arena: &TermArena, mut term: TermId) -> (Vec<SymbolId>, TermId) {
    let mut vars = Vec::new();
    while let Some((var, body)) = as_forall(arena, term) {
        vars.push(var);
        term = body;
    }
    (vars, term)
}

/// Decomposes a `(forall x body)` term into its bound variable and body.
fn as_forall(arena: &TermArena, term: TermId) -> Option<(SymbolId, TermId)> {
    match arena.node(term) {
        TermNode::App { op, args } if matches!(op, Op::Forall(_)) && args.len() == 1 => {
            let Op::Forall(var) = op else {
                unreachable!("matched Forall above")
            };
            Some((*var, args[0]))
        }
        _ => None,
    }
}

/// Refutes a **closed** top-level universal `∀x⃗. body` by falsifying its body.
///
/// Returns `Ok(Some(Unsat))` when `forall_term` is a closed universal (a
/// quantifier-free body mentioning no symbol outside its own bound variables) and
/// `¬body[x⃗ := c⃗]` is satisfiable for fresh constants `c⃗` — a witness that the
/// closed sentence `∀x⃗. body` is *false*, hence the whole query is `unsat`.
/// Returns `Ok(None)` when the shape does not apply (not a universal, an open or
/// still-quantified body) or the falsification sub-check is not a definite `Sat`
/// (`unsat` ⇒ the universal is valid, already handled upstream; `unknown` ⇒ decline
/// so the e-matching loop still runs). Never returns a non-`Unsat` `CheckResult`.
///
/// # Errors
///
/// Propagates any [`SolverError`] from the ground [`check_auto`] sub-check.
fn refute_closed_universal(
    arena: &mut TermArena,
    forall_term: TermId,
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    let (vars, body) = peel_foralls(arena, forall_term);
    if vars.is_empty() {
        return Ok(None);
    }
    let bound: HashSet<SymbolId> = vars.iter().copied().collect();
    // Only a *closed* quantifier-free body is a sentence we can falsify exactly.
    if !body_is_closed_qf(arena, body, &bound) {
        return Ok(None);
    }
    // Substitute each bound variable with a fresh Herbrand constant of its sort, so
    // the ground solver is free to pick the falsifying witness.
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    for &v in &vars {
        let sort = arena.symbol(v).1;
        let fresh = arena
            .declare_internal(&format!("!cu_{}", v.index()), sort)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let var = arena.var(v);
        let fresh_term = arena.var(fresh);
        map.insert(var, fresh_term);
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let instance = replace_subterms(arena, body, &map, &mut memo)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let negated = arena
        .not(instance)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    // `¬body[c⃗]` satisfiable ⇒ `∃x⃗. ¬body` ⇒ `∀x⃗. body` is false ⇒ query unsat.
    match check_auto(arena, &[negated], config)? {
        CheckResult::Sat(_) => Ok(Some(CheckResult::Unsat)),
        _ => Ok(None),
    }
}

/// Whether `term` is quantifier-free and every symbol it mentions is in `bound`
/// (so the universal it bodies is a closed sentence over exactly `bound`).
fn body_is_closed_qf(arena: &TermArena, term: TermId, bound: &HashSet<SymbolId>) -> bool {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(s) if !bound.contains(s) => {
                return false; // a free symbol: not a closed sentence
            }
            TermNode::App { op, args } => {
                // Reject anything carrying a *free* symbol the substitution cannot
                // reach: an inner quantifier (not quantifier-free) or an
                // uninterpreted-function application (its `FuncId` is a free symbol
                // — `∀x. f(x)=c` is satisfiable, not a refutable closed sentence).
                if matches!(op, Op::Forall(_) | Op::Exists(_) | Op::Apply(_)) {
                    return false;
                }
                for &a in args {
                    stack.push(a);
                }
            }
            _ => {}
        }
    }
    true
}

#[derive(Clone, Copy)]
struct EuclideanResiduePattern {
    remainder: SymbolId,
    quotient: SymbolId,
    dividend: TermId,
    modulus: i128,
}

#[derive(Clone, Copy)]
struct AffineGrowthPattern {
    variable: SymbolId,
    coefficient: i128,
    else_value: TermId,
    threshold: TermId,
}

#[derive(Clone, Copy)]
struct NestedXorSearchPattern {
    outer_bindings: [(SymbolId, i128); 2],
    nested: SymbolId,
    nested_pivot: i128,
    nested_body: TermId,
}

/// Builds the final hierarchical universal instance from ADR-0099.
///
/// This search matcher is intentionally separate from the original-IR evidence
/// checker in `quant_nested_xor_cert`.
fn nested_xor_discriminator_instance(
    arena: &mut TermArena,
    forall_term: TermId,
) -> Result<Option<TermId>, SolverError> {
    let (outer, body) = peel_foralls(arena, forall_term);
    if outer.len() != 2
        || outer[0] == outer[1]
        || outer.iter().any(|&var| arena.symbol(var).1 != Sort::Int)
    {
        return Ok(None);
    }
    let Some(pattern) = search_nested_xor_pattern(arena, body, &outer) else {
        return Ok(None);
    };
    let nested_witness = pattern
        .nested_pivot
        .checked_add(1)
        .or_else(|| pattern.nested_pivot.checked_sub(1))
        .expect("every i128 value has an adjacent representable integer");

    let mut replacements = HashMap::new();
    for (var, value) in pattern.outer_bindings {
        let value = arena.int_const(value);
        replacements.insert(arena.var(var), value);
    }
    let nested_value = arena.int_const(nested_witness);
    replacements.insert(arena.var(pattern.nested), nested_value);
    let mut memo = HashMap::new();
    replace_subterms(arena, pattern.nested_body, &replacements, &mut memo)
        .map(Some)
        .map_err(|error| SolverError::Backend(error.to_string()))
}

fn search_nested_xor_pattern(
    arena: &TermArena,
    body: TermId,
    outer: &[SymbolId],
) -> Option<NestedXorSearchPattern> {
    let (selector, nested_quantifier) = search_outer_xor_children(arena, body)?;
    let outer_bindings = search_selector_bindings(arena, selector, outer)?;
    let (nested, nested_body) = as_forall(arena, nested_quantifier)?;
    if outer.contains(&nested) || arena.symbol(nested).1 != Sort::Int {
        return None;
    }
    let (active, active_pivot, nested_pivot) =
        search_nested_discriminator(arena, nested_body, outer, nested)?;
    if !outer_bindings
        .iter()
        .any(|&(var, pivot)| var == active && pivot == active_pivot)
    {
        return None;
    }
    Some(NestedXorSearchPattern {
        outer_bindings,
        nested,
        nested_pivot,
        nested_body,
    })
}

fn search_outer_xor_children(arena: &TermArena, term: TermId) -> Option<(TermId, TermId)> {
    let TermNode::App {
        op: Op::BoolXor,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    match (as_forall(arena, *left), as_forall(arena, *right)) {
        (None, Some(_)) => Some((*left, *right)),
        (Some(_), None) => Some((*right, *left)),
        _ => None,
    }
}

fn search_selector_bindings(
    arena: &TermArena,
    term: TermId,
    outer: &[SymbolId],
) -> Option<[(SymbolId, i128); 2]> {
    let TermNode::App {
        op: Op::BoolXor,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let first = search_symbol_constant_equality(arena, *left)?;
    let second = search_symbol_constant_equality(arena, *right)?;
    if first.0 == second.0 || !outer.contains(&first.0) || !outer.contains(&second.0) {
        return None;
    }
    Some([first, second])
}

fn search_nested_discriminator(
    arena: &TermArena,
    term: TermId,
    outer: &[SymbolId],
    nested: SymbolId,
) -> Option<(SymbolId, i128, i128)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    search_discriminator_ites(arena, *left, *right, outer, nested)
        .or_else(|| search_discriminator_ites(arena, *right, *left, outer, nested))
}

fn search_discriminator_ites(
    arena: &TermArena,
    active_ite: TermId,
    nested_ite: TermId,
    outer: &[SymbolId],
    nested: SymbolId,
) -> Option<(SymbolId, i128, i128)> {
    let (active_guard, active_then, active_else) = search_ite(arena, active_ite)?;
    let (nested_guard, nested_then, nested_else) = search_ite(arena, nested_ite)?;
    let (active, active_pivot) = search_symbol_constant_equality(arena, active_guard)?;
    let (found_nested, nested_pivot) = search_symbol_constant_equality(arena, nested_guard)?;
    if !outer.contains(&active) || found_nested != nested {
        return None;
    }
    let then_value = search_int_constant(arena, active_then)?;
    let else_value = search_int_constant(arena, active_else)?;
    if then_value == else_value
        || search_int_constant(arena, nested_then) != Some(then_value)
        || search_int_constant(arena, nested_else) != Some(else_value)
    {
        return None;
    }
    Some((active, active_pivot, nested_pivot))
}

fn search_symbol_constant_equality(arena: &TermArena, term: TermId) -> Option<(SymbolId, i128)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(term) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    match (arena.node(*left), arena.node(*right)) {
        (TermNode::Symbol(symbol), _) => Some((*symbol, search_int_constant(arena, *right)?)),
        (_, TermNode::Symbol(symbol)) => Some((*symbol, search_int_constant(arena, *left)?)),
        _ => None,
    }
}

fn search_ite(arena: &TermArena, term: TermId) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App { op: Op::Ite, args } = arena.node(term) else {
        return None;
    };
    let [condition, then_value, else_value] = &**args else {
        return None;
    };
    Some((*condition, *then_value, *else_value))
}

fn search_int_constant(arena: &TermArena, term: TermId) -> Option<i128> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(*value),
        TermNode::App {
            op: Op::IntNeg,
            args,
        } => {
            let [inner] = &**args else {
                return None;
            };
            match arena.node(*inner) {
                TermNode::IntConst(value) => value.checked_neg(),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Builds the two consecutive symbolic counterexample instances from
/// ADR-0097. A non-matching universal declines.
fn affine_growth_instances(
    arena: &mut TermArena,
    forall_term: TermId,
) -> Result<Option<Vec<TermId>>, SolverError> {
    let (vars, body) = peel_foralls(arena, forall_term);
    let bound: HashSet<_> = vars.iter().copied().collect();
    if vars.is_empty()
        || bound.len() != vars.len()
        || vars.iter().any(|&var| arena.symbol(var).1 != Sort::Int)
    {
        return Ok(None);
    }
    let Some(pattern) = match_affine_growth_body(arena, body, &bound) else {
        return Ok(None);
    };

    let coefficient = arena.int_const(pattern.coefficient);
    let numerator = arena
        .int_add(pattern.else_value, pattern.threshold)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    let quotient = arena
        .int_div(numerator, coefficient)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    let one = arena.int_const(1);
    let first = arena
        .int_add(quotient, one)
        .map_err(|error| SolverError::Backend(error.to_string()))?;
    let second = arena
        .int_add(first, one)
        .map_err(|error| SolverError::Backend(error.to_string()))?;

    let variable = arena.var(pattern.variable);
    let mut instances = Vec::with_capacity(2);
    for candidate in [first, second] {
        let replacements = HashMap::from([(variable, candidate)]);
        let mut memo = HashMap::new();
        instances.push(
            replace_subterms(arena, body, &replacements, &mut memo)
                .map_err(|error| SolverError::Backend(error.to_string()))?,
        );
    }
    Ok(Some(instances))
}

fn match_affine_growth_body(
    arena: &TermArena,
    body: TermId,
    bound: &HashSet<SymbolId>,
) -> Option<AffineGrowthPattern> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(body)
    else {
        return None;
    };
    let [comparison] = &**args else {
        return None;
    };
    let TermNode::App {
        op: Op::IntGe,
        args,
    } = arena.node(*comparison)
    else {
        return None;
    };
    let [difference, threshold] = &**args else {
        return None;
    };
    if contains_any_symbol(arena, *threshold, bound) {
        return None;
    }

    let (variable, coefficient, piecewise) = match_growth_difference(arena, *difference)?;
    if coefficient <= 0 || !bound.contains(&variable) {
        return None;
    }
    let (pivot, then_value, else_value) = match_growth_piecewise(arena, piecewise, variable)?;
    if [pivot, then_value, else_value]
        .into_iter()
        .any(|term| contains_any_symbol(arena, term, bound))
    {
        return None;
    }

    Some(AffineGrowthPattern {
        variable,
        coefficient,
        else_value,
        threshold: *threshold,
    })
}

fn match_growth_difference(arena: &TermArena, term: TermId) -> Option<(SymbolId, i128, TermId)> {
    match arena.node(term) {
        TermNode::App {
            op: Op::IntSub,
            args,
        } => {
            let [scaled, piecewise] = &**args else {
                return None;
            };
            let (variable, coefficient) = match_growth_scaled(arena, *scaled)?;
            Some((variable, coefficient, *piecewise))
        }
        TermNode::App {
            op: Op::IntAdd,
            args,
        } => {
            let [left, right] = &**args else {
                return None;
            };
            match_growth_scaled_plus_negated(arena, *left, *right)
                .or_else(|| match_growth_scaled_plus_negated(arena, *right, *left))
        }
        _ => None,
    }
}

fn match_growth_scaled_plus_negated(
    arena: &TermArena,
    scaled: TermId,
    negated: TermId,
) -> Option<(SymbolId, i128, TermId)> {
    let (variable, coefficient) = match_growth_scaled(arena, scaled)?;
    let TermNode::App {
        op: Op::IntMul,
        args,
    } = arena.node(negated)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let piecewise = if growth_is_minus_one(arena, *left) {
        *right
    } else if growth_is_minus_one(arena, *right) {
        *left
    } else {
        return None;
    };
    Some((variable, coefficient, piecewise))
}

fn match_growth_scaled(arena: &TermArena, term: TermId) -> Option<(SymbolId, i128)> {
    let TermNode::App {
        op: Op::IntMul,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    match (arena.node(*left), arena.node(*right)) {
        (TermNode::IntConst(coefficient), TermNode::Symbol(variable))
        | (TermNode::Symbol(variable), TermNode::IntConst(coefficient)) => {
            Some((*variable, *coefficient))
        }
        _ => None,
    }
}

fn growth_is_minus_one(arena: &TermArena, term: TermId) -> bool {
    match arena.node(term) {
        TermNode::IntConst(-1) => true,
        TermNode::App {
            op: Op::IntNeg,
            args,
        } => matches!(&**args, [one] if matches!(arena.node(*one), TermNode::IntConst(1))),
        _ => false,
    }
}

fn match_growth_piecewise(
    arena: &TermArena,
    term: TermId,
    variable: SymbolId,
) -> Option<(TermId, TermId, TermId)> {
    let TermNode::App { op: Op::Ite, args } = arena.node(term) else {
        return None;
    };
    let [condition, then_value, else_value] = &**args else {
        return None;
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(*condition) else {
        return None;
    };
    let [left, right] = &**args else {
        return None;
    };
    let pivot = match (arena.node(*left), arena.node(*right)) {
        (TermNode::Symbol(found), _) if *found == variable => *right,
        (_, TermNode::Symbol(found)) if *found == variable => *left,
        _ => return None,
    };
    Some((pivot, *then_value, *else_value))
}

/// Builds the symbolic counterexample instance for the exact Euclidean residue
/// partition described at the call site. A non-matching universal declines.
fn euclidean_residue_instance(
    arena: &mut TermArena,
    forall_term: TermId,
) -> Result<Option<TermId>, SolverError> {
    let (vars, body) = peel_foralls(arena, forall_term);
    if vars.len() != 2 || vars.iter().any(|&v| arena.symbol(v).1 != Sort::Int) {
        return Ok(None);
    }
    let bound: HashSet<SymbolId> = vars.iter().copied().collect();
    let Some(pattern) = match_euclidean_residue_body(arena, body, &bound) else {
        return Ok(None);
    };
    if !bound.contains(&pattern.remainder)
        || !bound.contains(&pattern.quotient)
        || pattern.remainder == pattern.quotient
    {
        return Ok(None);
    }

    let modulus = arena.int_const(pattern.modulus);
    let quotient = arena
        .int_div(pattern.dividend, modulus)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let remainder = arena
        .int_mod(pattern.dividend, modulus)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let mut replacements = HashMap::new();
    replacements.insert(arena.var(pattern.remainder), remainder);
    replacements.insert(arena.var(pattern.quotient), quotient);
    let mut memo = HashMap::new();
    replace_subterms(arena, body, &replacements, &mut memo)
        .map(Some)
        .map_err(|e| SolverError::Backend(e.to_string()))
}

fn match_euclidean_residue_body(
    arena: &TermArena,
    body: TermId,
    bound: &HashSet<SymbolId>,
) -> Option<EuclideanResiduePattern> {
    let mut disjuncts = Vec::new();
    flatten_or(arena, body, &mut disjuncts);
    if disjuncts.len() != 3 {
        return None;
    }

    let pattern = disjuncts
        .iter()
        .find_map(|&d| match_negated_recomposition(arena, d, bound))?;
    let mut lower = false;
    let mut upper = false;
    for &d in &disjuncts {
        if match_negated_recomposition(arena, d, bound).is_some() {
            continue;
        }
        if is_remainder_lower_guard(arena, d, pattern.remainder) {
            if lower {
                return None;
            }
            lower = true;
        } else if is_remainder_upper_guard(arena, d, pattern.remainder, pattern.modulus) {
            if upper {
                return None;
            }
            upper = true;
        } else {
            return None;
        }
    }
    (lower && upper).then_some(pattern)
}

fn flatten_or(arena: &TermArena, term: TermId, out: &mut Vec<TermId>) {
    if let TermNode::App {
        op: Op::BoolOr,
        args,
    } = arena.node(term)
    {
        let args = args.clone();
        for arg in args {
            flatten_or(arena, arg, out);
        }
    } else {
        out.push(term);
    }
}

fn match_negated_recomposition(
    arena: &TermArena,
    term: TermId,
    bound: &HashSet<SymbolId>,
) -> Option<EuclideanResiduePattern> {
    let TermNode::App {
        op: Op::BoolNot,
        args,
    } = arena.node(term)
    else {
        return None;
    };
    let TermNode::App { op: Op::Eq, args } = arena.node(args[0]) else {
        return None;
    };
    match_recomposition_equality(arena, args[0], args[1], bound)
        .or_else(|| match_recomposition_equality(arena, args[1], args[0], bound))
}

fn match_recomposition_equality(
    arena: &TermArena,
    sum: TermId,
    dividend: TermId,
    bound: &HashSet<SymbolId>,
) -> Option<EuclideanResiduePattern> {
    if contains_any_symbol(arena, dividend, bound) {
        return None;
    }
    let TermNode::App {
        op: Op::IntAdd,
        args,
    } = arena.node(sum)
    else {
        return None;
    };
    let (quotient, modulus, remainder) = match_scaled_plus_remainder(arena, args[0], args[1])
        .or_else(|| match_scaled_plus_remainder(arena, args[1], args[0]))?;
    if modulus <= 0 || !bound.contains(&quotient) || !bound.contains(&remainder) {
        return None;
    }
    Some(EuclideanResiduePattern {
        remainder,
        quotient,
        dividend,
        modulus,
    })
}

fn match_scaled_plus_remainder(
    arena: &TermArena,
    scaled: TermId,
    remainder: TermId,
) -> Option<(SymbolId, i128, SymbolId)> {
    let TermNode::Symbol(remainder) = arena.node(remainder) else {
        return None;
    };
    let TermNode::App {
        op: Op::IntMul,
        args,
    } = arena.node(scaled)
    else {
        return None;
    };
    let (modulus, quotient) = match (arena.node(args[0]), arena.node(args[1])) {
        (TermNode::IntConst(k), TermNode::Symbol(q))
        | (TermNode::Symbol(q), TermNode::IntConst(k)) => (*k, *q),
        _ => return None,
    };
    Some((quotient, modulus, *remainder))
}

fn is_remainder_lower_guard(arena: &TermArena, term: TermId, remainder: SymbolId) -> bool {
    matches!(
        arena.node(term),
        TermNode::App { op: Op::IntLt, args }
            if matches!(arena.node(args[0]), TermNode::Symbol(s) if *s == remainder)
                && matches!(arena.node(args[1]), TermNode::IntConst(0))
    )
}

fn is_remainder_upper_guard(
    arena: &TermArena,
    term: TermId,
    remainder: SymbolId,
    modulus: i128,
) -> bool {
    matches!(
        arena.node(term),
        TermNode::App { op: Op::IntGe, args }
            if matches!(arena.node(args[0]), TermNode::Symbol(s) if *s == remainder)
                && matches!(arena.node(args[1]), TermNode::IntConst(k) if *k == modulus)
    )
}

fn contains_any_symbol(arena: &TermArena, term: TermId, symbols: &HashSet<SymbolId>) -> bool {
    let mut seen = HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(s) if symbols.contains(s) => return true,
            TermNode::App { op, args } => {
                if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            _ => {}
        }
    }
    false
}

/// Infers a trigger: a set of function-application subterms whose bound variables
/// together cover all of them. Prefers a single term that covers everything (e.g.
/// `f(x)`, `g(x, y)`); otherwise a greedy set cover yields a multi-pattern (e.g.
/// `{f(x), g(y)}` for `∀x,y. f(x) = g(y)`). Returns empty when the variables cannot
/// be covered by function applications.
fn select_triggers(arena: &TermArena, body: TermId, vars: &HashMap<SymbolId, u32>) -> Vec<TermId> {
    // Candidate function-application subterms with the variable-index set each one
    // covers.
    let mut candidates: Vec<(TermId, HashSet<u32>)> = Vec::new();
    collect_app_candidates(arena, body, vars, &mut candidates);

    let all: HashSet<u32> = (0..u32::try_from(vars.len()).expect("var count fits u32")).collect();
    // A single covering term is the best trigger.
    if let Some((t, _)) = candidates.iter().find(|(_, c)| *c == all) {
        return vec![*t];
    }
    // Greedy set cover otherwise.
    let mut uncovered = all;
    let mut chosen = Vec::new();
    while !uncovered.is_empty() {
        let best = candidates
            .iter()
            .max_by_key(|(_, c)| c.intersection(&uncovered).count());
        match best {
            Some((t, c)) if c.intersection(&uncovered).next().is_some() => {
                for v in c {
                    uncovered.remove(v);
                }
                chosen.push(*t);
            }
            _ => return Vec::new(), // some variable is in no function application
        }
    }
    chosen
}

/// Collects every function-application subterm of `body`, with the set of bound
/// variable indices it mentions (only those covering ≥1 bound variable are kept).
fn collect_app_candidates(
    arena: &TermArena,
    term: TermId,
    vars: &HashMap<SymbolId, u32>,
    out: &mut Vec<(TermId, HashSet<u32>)>,
) {
    if let TermNode::App { op, args } = arena.node(term) {
        if matches!(op, Op::Apply(_)) {
            let mut seen = HashSet::new();
            collect_vars(arena, term, vars, &mut seen);
            if !seen.is_empty() {
                let indices: HashSet<u32> = seen.iter().map(|s| vars[s]).collect();
                out.push((term, indices));
            }
        }
        let args = args.clone();
        for a in args {
            collect_app_candidates(arena, a, vars, out);
        }
    }
}

/// Merges two partial substitutions, returning `None` on a variable conflict.
fn merge_substitutions(
    a: &[Option<ENodeId>],
    b: &[Option<ENodeId>],
) -> Option<Vec<Option<ENodeId>>> {
    let mut out = a.to_vec();
    for (slot, &bi) in out.iter_mut().zip(b) {
        if let Some(bv) = bi {
            match *slot {
                Some(av) if av != bv => return None,
                _ => *slot = Some(bv),
            }
        }
    }
    Some(out)
}

/// Combines retained substitutions against the e-graph's current roots.
/// Cached class ids may predate one or more ADR-0113 merge notifications.
fn merge_substitutions_modulo(
    egraph: &EGraph,
    a: &[Option<ENodeId>],
    b: &[Option<ENodeId>],
) -> Option<Vec<Option<ENodeId>>> {
    let mut out: Vec<Option<ENodeId>> = a
        .iter()
        .map(|value| value.map(|node| egraph.root(node)))
        .collect();
    for (slot, &bi) in out.iter_mut().zip(b) {
        if let Some(bv) = bi.map(|node| egraph.root(node)) {
            match *slot {
                Some(av) if av != bv => return None,
                _ => *slot = Some(bv),
            }
        }
    }
    Some(out)
}

/// Records which `vars` occur in `term`.
fn collect_vars(
    arena: &TermArena,
    term: TermId,
    vars: &HashMap<SymbolId, u32>,
    seen: &mut std::collections::HashSet<SymbolId>,
) {
    match arena.node(term) {
        TermNode::Symbol(s) if vars.contains_key(s) => {
            seen.insert(*s);
        }
        TermNode::App { args, .. } => {
            let args = args.clone();
            for a in args {
                collect_vars(arena, a, vars, seen);
            }
        }
        _ => {}
    }
}

/// Bridges ground IR terms to the e-graph for instantiation: it builds e-nodes,
/// assigns each symbol/function/constant a `decl`, and remembers a representative
/// ground term per class (to substitute back on a match).
struct InstBridge {
    egraph: EGraph,
    term_to_node: HashMap<TermId, ENodeId>,
    func_decls: HashMap<FuncId, u32>,
    symbol_decls: HashMap<usize, u32>,
    op_decls: HashMap<String, u32>,
    /// First ground term seen per class root — the instantiation witness.
    repr_term: HashMap<ENodeId, TermId>,
    next_decl: u32,
}

impl InstBridge {
    fn new() -> Self {
        Self {
            egraph: EGraph::new(),
            term_to_node: HashMap::new(),
            func_decls: HashMap::new(),
            symbol_decls: HashMap::new(),
            op_decls: HashMap::new(),
            repr_term: HashMap::new(),
            next_decl: 0,
        }
    }

    fn fresh_decl(&mut self) -> u32 {
        let d = self.next_decl;
        self.next_decl += 1;
        d
    }

    fn add_term(&mut self, arena: &TermArena, term: TermId) -> ENodeId {
        if let Some(&n) = self.term_to_node.get(&term) {
            return n;
        }
        let node = match arena.node(term) {
            TermNode::Symbol(s) => {
                let decl = self.symbol_decl(s.index());
                self.egraph.add(decl, &[])
            }
            TermNode::App {
                op: Op::Apply(func),
                args,
            } => {
                let func = *func;
                let args = args.clone();
                let children: Vec<ENodeId> =
                    args.iter().map(|&a| self.add_term(arena, a)).collect();
                let decl = self.func_decl(func);
                self.egraph.add(decl, &children)
            }
            TermNode::App { op, args } => {
                // Other interpreted operators are treated as uninterpreted for the
                // purposes of matching (sound: matching only fires on real terms).
                let op = format!("{op:?}");
                let args = args.clone();
                let children: Vec<ENodeId> =
                    args.iter().map(|&a| self.add_term(arena, a)).collect();
                let decl = self.op_decl(&op);
                self.egraph.add(decl, &children)
            }
            _ => {
                // A literal constant: each distinct value is its own leaf.
                let key = format!("c:{:?}", arena.node(term));
                let decl = self.op_decl(&key);
                self.egraph.add(decl, &[])
            }
        };
        let root = self.egraph.root(node);
        self.repr_term.entry(root).or_insert(term);
        self.term_to_node.insert(term, node);
        node
    }

    fn symbol_decl(&mut self, sym: usize) -> u32 {
        if let Some(&d) = self.symbol_decls.get(&sym) {
            return d;
        }
        let d = self.fresh_decl();
        self.symbol_decls.insert(sym, d);
        d
    }

    fn func_decl(&mut self, func: FuncId) -> u32 {
        if let Some(&d) = self.func_decls.get(&func) {
            return d;
        }
        let d = self.fresh_decl();
        self.func_decls.insert(func, d);
        d
    }

    fn op_decl(&mut self, key: &str) -> u32 {
        if let Some(&d) = self.op_decls.get(key) {
            return d;
        }
        let d = self.fresh_decl();
        self.op_decls.insert(key.to_owned(), d);
        d
    }

    /// Converts a trigger term to an e-matching [`Pattern`] under this bridge's
    /// decl assignment: the bound `var` becomes `Var(0)`, and every other subterm
    /// (symbols, applications, constants, interpreted ops) becomes an application
    /// keyed by the same decl the ground terms use — so a ground subterm in the
    /// trigger matches its own class, while only `var` is free.
    fn trigger_to_pattern(
        &mut self,
        arena: &TermArena,
        term: TermId,
        vars: &HashMap<SymbolId, u32>,
    ) -> Pattern {
        match arena.node(term) {
            TermNode::Symbol(s) if vars.contains_key(s) => Pattern::Var(vars[s]),
            TermNode::Symbol(s) => Pattern::App(self.symbol_decl(s.index()), Vec::new()),
            TermNode::App {
                op: Op::Apply(func),
                args,
            } => {
                let func = *func;
                let args = args.clone();
                let subs = args
                    .iter()
                    .map(|&a| self.trigger_to_pattern(arena, a, vars))
                    .collect();
                Pattern::App(self.func_decl(func), subs)
            }
            TermNode::App { op, args } => {
                let key = format!("{op:?}");
                let args = args.clone();
                let subs = args
                    .iter()
                    .map(|&a| self.trigger_to_pattern(arena, a, vars))
                    .collect();
                Pattern::App(self.op_decl(&key), subs)
            }
            _ => Pattern::App(
                self.op_decl(&format!("c:{:?}", arena.node(term))),
                Vec::new(),
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Sort;

    /// Builds `∀x. (= (f x) c)` and ground terms mentioning `f(a)`, `f(b)`.
    #[allow(clippy::many_single_char_names, clippy::too_many_lines)]
    fn setup() -> (
        TermArena,
        TermId,
        [TermId; 2],
        TermId,
        TermId,
        FuncId,
        SymbolId,
    ) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        // A ground assertion that contains f(a) and f(b).
        let sum = arena.bv_add(fa, fb).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(sum, zero).unwrap();

        // Body referencing the bound variable: (= (f x) c).
        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let body = arena.eq(fx, c).unwrap();
        let forall = arena.forall(x, body).unwrap();

        (arena, forall, [a, b], c, ground0, f, x)
    }

    fn shared_match_stress(
        ground_terms: usize,
        quantifier_count: usize,
    ) -> (TermArena, Vec<TermId>, Vec<TermId>) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let function = arena.declare_fun("shared_f", &[sort], sort).unwrap();
        let zero = arena.bv_const(16, 0).unwrap();
        let mut ground = Vec::with_capacity(ground_terms);
        for index in 0..ground_terms {
            let argument = arena.bv_var(&format!("shared_a_{index}"), 16).unwrap();
            let application = arena.apply(function, &[argument]).unwrap();
            let equality = arena.eq(application, zero).unwrap();
            ground.push(arena.not(equality).unwrap());
        }

        let mut foralls = Vec::with_capacity(quantifier_count);
        for index in 0..quantifier_count {
            let variable = arena.declare(&format!("shared_x_{index}"), sort).unwrap();
            let variable_term = arena.var(variable);
            let application = arena.apply(function, &[variable_term]).unwrap();
            let value = arena.bv_const(16, index as u128).unwrap();
            let body = arena.eq(application, value).unwrap();
            foralls.push(arena.forall(variable, body).unwrap());
        }
        (arena, ground, foralls)
    }

    fn unrelated_root_stress(
        pattern_count: usize,
        terms_per_pattern: usize,
    ) -> (TermArena, Vec<TermId>, Vec<TermId>, TermId) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let mut ground = Vec::with_capacity(pattern_count * terms_per_pattern);
        let mut foralls = Vec::with_capacity(pattern_count);
        let mut appended = None;

        for pattern_index in 0..pattern_count {
            let function = arena
                .declare_fun(&format!("queued_f_{pattern_index}"), &[sort], sort)
                .unwrap();
            for term_index in 0..=terms_per_pattern {
                let argument = arena
                    .bv_var(&format!("queued_a_{pattern_index}_{term_index}"), 16)
                    .unwrap();
                let application = arena.apply(function, &[argument]).unwrap();
                let equality = arena.eq(application, zero).unwrap();
                let disequality = arena.not(equality).unwrap();
                if pattern_index == 0 && term_index == terms_per_pattern {
                    appended = Some(disequality);
                } else if term_index < terms_per_pattern {
                    ground.push(disequality);
                }
            }

            let variable = arena
                .declare(&format!("queued_x_{pattern_index}"), sort)
                .unwrap();
            let variable_term = arena.var(variable);
            let application = arena.apply(function, &[variable_term]).unwrap();
            let body = arena.eq(application, zero).unwrap();
            foralls.push(arena.forall(variable, body).unwrap());
        }

        (
            arena,
            ground,
            foralls,
            appended.expect("the first root has one append-only term"),
        )
    }

    fn merge_root_stress(
        pattern_count: usize,
        terms_per_pattern: usize,
    ) -> (TermArena, Vec<TermId>, Vec<TermId>, TermId) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let mut ground = Vec::with_capacity(pattern_count * terms_per_pattern);
        let mut foralls = Vec::with_capacity(pattern_count);
        let mut merge_equality = None;

        for pattern_index in 0..pattern_count {
            let function = arena
                .declare_fun(&format!("merge_f_{pattern_index}"), &[sort, sort], sort)
                .unwrap();
            for term_index in 0..terms_per_pattern {
                let left = arena
                    .bv_var(&format!("merge_a_{pattern_index}_{term_index}"), 16)
                    .unwrap();
                let right = arena
                    .bv_var(&format!("merge_b_{pattern_index}_{term_index}"), 16)
                    .unwrap();
                let application = arena.apply(function, &[left, right]).unwrap();
                let equality = arena.eq(application, zero).unwrap();
                ground.push(arena.not(equality).unwrap());
                if pattern_index == 0 && term_index == 0 {
                    merge_equality = Some(arena.eq(left, right).unwrap());
                }
            }

            let variable = arena
                .declare(&format!("merge_x_{pattern_index}"), sort)
                .unwrap();
            let variable_term = arena.var(variable);
            let application = arena
                .apply(function, &[variable_term, variable_term])
                .unwrap();
            let body = arena.eq(application, zero).unwrap();
            foralls.push(arena.forall(variable, body).unwrap());
        }

        (
            arena,
            ground,
            foralls,
            merge_equality.expect("the first root has one merge equality"),
        )
    }

    fn shared_root_path_stress(
        pattern_count: usize,
        terms_per_pattern: usize,
    ) -> (TermArena, Vec<TermId>, Vec<TermId>, TermId) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let outer = arena.declare_fun("path_outer", &[sort], sort).unwrap();
        let mut ground = Vec::with_capacity(pattern_count * terms_per_pattern);
        let mut foralls = Vec::with_capacity(pattern_count);
        let mut merge_equality = None;

        for pattern_index in 0..pattern_count {
            let inner = arena
                .declare_fun(&format!("path_inner_{pattern_index}"), &[sort, sort], sort)
                .unwrap();
            for term_index in 0..terms_per_pattern {
                let left = arena
                    .bv_var(&format!("path_a_{pattern_index}_{term_index}"), 16)
                    .unwrap();
                let right = arena
                    .bv_var(&format!("path_b_{pattern_index}_{term_index}"), 16)
                    .unwrap();
                let inner_application = arena.apply(inner, &[left, right]).unwrap();
                let outer_application = arena.apply(outer, &[inner_application]).unwrap();
                let equality = arena.eq(outer_application, zero).unwrap();
                ground.push(arena.not(equality).unwrap());
                if pattern_index == 0 && term_index == 0 {
                    merge_equality = Some(arena.eq(left, right).unwrap());
                }
            }

            let variable = arena
                .declare(&format!("path_x_{pattern_index}"), sort)
                .unwrap();
            let variable_term = arena.var(variable);
            let inner_application = arena.apply(inner, &[variable_term, variable_term]).unwrap();
            let outer_application = arena.apply(outer, &[inner_application]).unwrap();
            let body = arena.eq(outer_application, zero).unwrap();
            foralls.push(arena.forall(variable, body).unwrap());
        }

        (
            arena,
            ground,
            foralls,
            merge_equality.expect("the first nested path has one merge equality"),
        )
    }

    fn path_filter_matrix_stress(
        label_count: usize,
        constant_count: usize,
        terms_per_pattern: usize,
    ) -> (TermArena, Vec<TermId>, Vec<TermId>, TermId) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let outer = arena
            .declare_fun("filter_outer", &[sort, sort], sort)
            .unwrap();
        let constants: Vec<TermId> = (0..constant_count)
            .map(|index| arena.bv_var(&format!("filter_c_{index}"), 16).unwrap())
            .collect();
        let inner_functions: Vec<FuncId> = (0..label_count)
            .map(|index| {
                arena
                    .declare_fun(&format!("filter_inner_{index}"), &[sort], sort)
                    .unwrap()
            })
            .collect();

        let pattern_count = label_count * constant_count;
        let mut ground = Vec::with_capacity(pattern_count * terms_per_pattern + label_count);
        let mut merge_left = None;
        for label_index in 0..label_count {
            for (constant_index, &constant) in constants.iter().enumerate() {
                for term_index in 0..terms_per_pattern {
                    let argument = arena
                        .bv_var(
                            &format!("filter_b_{label_index}_{constant_index}_{term_index}"),
                            16,
                        )
                        .unwrap();
                    let application = arena.apply(outer, &[argument, constant]).unwrap();
                    let equality = arena.eq(application, zero).unwrap();
                    ground.push(arena.not(equality).unwrap());
                    if label_index == 0 && constant_index == 0 && term_index == 0 {
                        merge_left = Some(argument);
                    }
                }
            }
        }

        let mut merge_right = None;
        for (label_index, &inner) in inner_functions.iter().enumerate() {
            let argument = arena
                .bv_var(&format!("filter_anchor_{label_index}"), 16)
                .unwrap();
            let application = arena.apply(inner, &[argument]).unwrap();
            let equality = arena.eq(application, zero).unwrap();
            ground.push(arena.not(equality).unwrap());
            if label_index == 0 {
                merge_right = Some(application);
            }
        }

        let mut foralls = Vec::with_capacity(pattern_count);
        for (label_index, &inner) in inner_functions.iter().enumerate() {
            for (constant_index, &constant) in constants.iter().enumerate() {
                let variable = arena
                    .declare(&format!("filter_x_{label_index}_{constant_index}"), sort)
                    .unwrap();
                let variable_term = arena.var(variable);
                let inner_application = arena.apply(inner, &[variable_term]).unwrap();
                let outer_application = arena.apply(outer, &[inner_application, constant]).unwrap();
                let body = arena.eq(outer_application, zero).unwrap();
                foralls.push(arena.forall(variable, body).unwrap());
            }
        }

        let merge_equality = arena
            .eq(
                merge_left.expect("matrix has one outer argument"),
                merge_right.expect("matrix has one nested anchor"),
            )
            .unwrap();
        (arena, ground, foralls, merge_equality)
    }

    fn generation_delta_stress(applications: usize) -> (TermArena, Vec<TermId>, TermId, TermId) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let constant = arena.bv_var("delta_constant", 16).unwrap();
        let inner = arena.declare_fun("delta_inner", &[sort], sort).unwrap();
        let outer = arena
            .declare_fun("delta_outer", &[sort, sort], sort)
            .unwrap();

        let mut ground = Vec::with_capacity(applications + 1);
        let mut merge_left = None;
        for index in 0..applications {
            let argument = arena
                .bv_var(&format!("delta_argument_{index}"), 16)
                .unwrap();
            let application = arena.apply(outer, &[argument, constant]).unwrap();
            let equality = arena.eq(application, zero).unwrap();
            ground.push(arena.not(equality).unwrap());
            if index == 0 {
                merge_left = Some(argument);
            }
        }
        let anchor = arena.bv_var("delta_anchor", 16).unwrap();
        let inner_anchor = arena.apply(inner, &[anchor]).unwrap();
        let inner_equality = arena.eq(inner_anchor, zero).unwrap();
        ground.push(arena.not(inner_equality).unwrap());

        let variable = arena.declare("delta_x", sort).unwrap();
        let variable_term = arena.var(variable);
        let inner_application = arena.apply(inner, &[variable_term]).unwrap();
        let outer_application = arena.apply(outer, &[inner_application, constant]).unwrap();
        let body = arena.eq(outer_application, zero).unwrap();
        let forall = arena.forall(variable, body).unwrap();
        let merge_equality = arena
            .eq(
                merge_left.expect("stress target has one outer argument"),
                inner_anchor,
            )
            .unwrap();
        (arena, ground, forall, merge_equality)
    }

    #[test]
    fn shared_session_interns_patterns_and_matches_complete_legacy_tuples() {
        const GROUND_TERMS: usize = 256;
        const QUANTIFIERS: usize = 32;

        let (mut legacy_arena, legacy_ground, legacy_foralls) =
            shared_match_stress(GROUND_TERMS, QUANTIFIERS);
        let legacy_started = Instant::now();
        let legacy_tuples: Vec<Vec<Vec<TermId>>> = legacy_foralls
            .iter()
            .map(|&quantifier| {
                witness_tuples_via_egraph(&mut legacy_arena, &legacy_ground, quantifier)
                    .expect("every shared pattern matches")
                    .2
            })
            .collect();
        let legacy_elapsed = legacy_started.elapsed();
        assert!(
            legacy_tuples
                .iter()
                .all(|tuples| tuples.len() == GROUND_TERMS)
        );

        let (mut shared_arena, shared_ground, shared_foralls) =
            shared_match_stress(GROUND_TERMS, QUANTIFIERS);
        let shared_started = Instant::now();
        let mut session = IncrementalEmatchSession::new(&mut shared_arena, &shared_foralls);
        assert_eq!(
            session.patterns.len(),
            1,
            "identical triggers across quantifiers must share one compiled pattern"
        );
        session.extend_ground(&shared_arena, &shared_ground);
        let shared_tuples: Vec<Vec<Vec<TermId>>> = session
            .match_witness_tuples()
            .into_iter()
            .map(|tuples| tuples.expect("every shared pattern matches"))
            .collect();
        let shared_elapsed = shared_started.elapsed();

        assert_eq!(shared_tuples, legacy_tuples);
        assert_eq!(session.extensions, 1);
        assert_eq!(session.match_rounds, 1);
        assert_eq!(session.processed_ground.len(), GROUND_TERMS);
        eprintln!(
            "shared MAM target: ground_terms={GROUND_TERMS} quantifiers={QUANTIFIERS} unique_patterns=1 legacy_match_us={} shared_match_us={}",
            legacy_elapsed.as_micros(),
            shared_elapsed.as_micros()
        );
    }

    #[test]
    fn add_only_candidate_queue_matches_full_rebuild_and_executes_one_root() {
        const PATTERNS: usize = 64;
        const TERMS_PER_PATTERN: usize = 64;

        let (mut arena, ground, foralls, appended) =
            unrelated_root_stress(PATTERNS, TERMS_PER_PATTERN);
        let mut queued = IncrementalEmatchSession::new(&mut arena, &foralls);
        let mut full = IncrementalEmatchSession::new(&mut arena, &foralls);
        assert_eq!(queued.patterns.len(), PATTERNS);
        assert_eq!(full.patterns, queued.patterns);

        queued.extend_ground(&arena, &ground);
        full.extend_ground(&arena, &ground);
        assert_eq!(queued.match_witness_tuples(), full.match_witness_tuples());
        assert_eq!(queued.pattern_executions, PATTERNS);

        let mut extended_ground = ground;
        extended_ground.push(appended);
        queued.extend_ground(&arena, &extended_ground);
        full.extend_ground(&arena, &extended_ground);

        let queued_before = queued.pattern_executions;
        let queued_candidates_before = queued.candidate_applications_scanned;
        let queued_started = Instant::now();
        let queued_tuples = queued.match_witness_tuples();
        let queued_elapsed = queued_started.elapsed();
        assert_eq!(queued.pattern_executions - queued_before, 1);
        assert_eq!(
            queued.candidate_applications_scanned - queued_candidates_before,
            1
        );
        assert_eq!(queued.dirty_patterns.len(), 0);

        // Recreate ADR-0111's complete per-round index construction and pattern
        // execution while retaining the same bridge and complete tuple join.
        full.match_index = full.bridge.egraph.new_match_index();
        full.dirty_patterns.extend(0..full.patterns.len());
        let full_before = full.pattern_executions;
        let full_started = Instant::now();
        let full_tuples = full.match_witness_tuples();
        let full_elapsed = full_started.elapsed();

        assert_eq!(full.pattern_executions - full_before, PATTERNS);
        assert_eq!(queued_tuples, full_tuples);
        assert!(queued_tuples.iter().all(Option::is_some));
        assert_eq!(
            queued_tuples[0].as_ref().unwrap().len(),
            TERMS_PER_PATTERN + 1
        );
        assert!(
            queued_tuples[1..]
                .iter()
                .all(|tuples| tuples.as_ref().unwrap().len() == TERMS_PER_PATTERN)
        );
        eprintln!(
            "candidate queue target: patterns={PATTERNS} retained_terms={} appended_roots=1 full_rematch_us={} queued_update_us={} full_pattern_executions={PATTERNS} queued_pattern_executions=1",
            PATTERNS * TERMS_PER_PATTERN,
            full_elapsed.as_micros(),
            queued_elapsed.as_micros()
        );
    }

    #[test]
    fn merge_candidate_queue_matches_full_rebuild_and_executes_one_root() {
        const PATTERNS: usize = 64;
        const TERMS_PER_PATTERN: usize = 64;

        let (mut arena, ground, foralls, merge_equality) =
            merge_root_stress(PATTERNS, TERMS_PER_PATTERN);
        let mut queued = IncrementalEmatchSession::new(&mut arena, &foralls);
        let mut full = IncrementalEmatchSession::new(&mut arena, &foralls);
        assert_eq!(queued.patterns.len(), PATTERNS);
        assert_eq!(full.patterns, queued.patterns);

        queued.extend_ground(&arena, &ground);
        full.extend_ground(&arena, &ground);
        assert_eq!(queued.match_witness_tuples(), full.match_witness_tuples());
        assert_eq!(queued.pattern_executions, PATTERNS);

        let mut extended_ground = ground;
        extended_ground.push(merge_equality);
        let queued_before = queued.pattern_executions;
        let queued_candidates_before = queued.candidate_applications_scanned;
        let queued_started = Instant::now();
        queued.extend_ground(&arena, &extended_ground);
        let queued_tuples = queued.match_witness_tuples();
        let queued_elapsed = queued_started.elapsed();
        assert_eq!(queued.merge_invalidations, 1);
        assert_eq!(queued.merge_affected_patterns, 1);
        assert_eq!(queued.pattern_executions - queued_before, 1);
        assert_eq!(
            queued.candidate_applications_scanned - queued_candidates_before,
            1
        );

        let full_before = full.pattern_executions;
        let full_started = Instant::now();
        full.extend_ground_with_full_merge_invalidation(&arena, &extended_ground);
        // ADR-0112 rebuilt its root-keyed index after every merge.
        full.match_index = full.bridge.egraph.new_match_index();
        let full_tuples = full.match_witness_tuples();
        let full_elapsed = full_started.elapsed();

        assert_eq!(full.pattern_executions - full_before, PATTERNS);
        assert_eq!(queued_tuples, full_tuples);
        assert_eq!(queued_tuples[0].as_ref().unwrap().len(), 1);
        assert!(queued_tuples[1..].iter().all(Option::is_none));
        eprintln!(
            "merge queue target: patterns={PATTERNS} retained_terms={} affected_roots=1 full_round_us={} queued_round_us={} full_pattern_executions={PATTERNS} queued_pattern_executions=1",
            PATTERNS * TERMS_PER_PATTERN,
            full_elapsed.as_micros(),
            queued_elapsed.as_micros()
        );
    }

    #[test]
    fn compiled_parent_paths_beat_shared_root_declaration_invalidation() {
        const PATTERNS: usize = 64;
        const TERMS_PER_PATTERN: usize = 64;

        let (mut arena, ground, foralls, merge_equality) =
            shared_root_path_stress(PATTERNS, TERMS_PER_PATTERN);
        let mut exact = IncrementalEmatchSession::new(&mut arena, &foralls);
        let mut declarations = IncrementalEmatchSession::new(&mut arena, &foralls);
        assert_eq!(exact.patterns.len(), PATTERNS);
        assert_eq!(declarations.patterns, exact.patterns);
        let root_declarations: BTreeSet<u32> = exact
            .patterns
            .iter()
            .filter_map(|pattern| match pattern {
                Pattern::App(declaration, _) => Some(*declaration),
                Pattern::Var(_) => None,
            })
            .collect();
        assert_eq!(root_declarations.len(), 1, "every trigger shares one root");

        exact.extend_ground(&arena, &ground);
        declarations.extend_ground(&arena, &ground);
        assert_eq!(
            exact.match_witness_tuples(),
            declarations.match_witness_tuples()
        );

        let mut extended_ground = ground;
        extended_ground.push(merge_equality);
        let exact_before = exact.pattern_executions;
        let exact_started = Instant::now();
        exact.extend_ground(&arena, &extended_ground);
        let exact_tuples = exact.match_witness_tuples();
        let exact_elapsed = exact_started.elapsed();

        let declaration_before = declarations.pattern_executions;
        let declaration_started = Instant::now();
        declarations.extend_ground_with_declaration_merge_invalidation(&arena, &extended_ground);
        let declaration_tuples = declarations.match_witness_tuples();
        let declaration_elapsed = declaration_started.elapsed();

        assert_eq!(exact.pattern_executions - exact_before, 1);
        assert_eq!(
            declarations.pattern_executions - declaration_before,
            PATTERNS
        );
        assert_eq!(exact.merge_affected_patterns, 1);
        assert_eq!(declarations.merge_affected_patterns, PATTERNS);
        assert_eq!(exact_tuples, declaration_tuples);
        assert_eq!(exact_tuples[0].as_ref().unwrap().len(), 1);
        assert!(exact_tuples[1..].iter().all(Option::is_none));
        eprintln!(
            "parent path target: patterns={PATTERNS} shared_roots=1 retained_terms={} affected_paths=1 declaration_round_us={} exact_path_round_us={} declaration_pattern_executions={PATTERNS} exact_pattern_executions=1",
            PATTERNS * TERMS_PER_PATTERN,
            declaration_elapsed.as_micros(),
            exact_elapsed.as_micros()
        );
    }

    #[test]
    fn compiled_parent_paths_distinguish_declarations_and_terminate_on_cycles() {
        let pattern_g = Pattern::App(30, vec![Pattern::App(20, vec![Pattern::Var(0)])]);
        let pattern_h = Pattern::App(30, vec![Pattern::App(21, vec![Pattern::Var(0)])]);
        let cyclic = Pattern::App(40, vec![Pattern::App(40, vec![Pattern::Var(0)])]);
        let mut paths = PatternPathIndex::default();
        paths.add_pattern(&pattern_g, 0);
        paths.add_pattern(&pattern_h, 1);
        paths.add_pattern(&cyclic, 2);
        paths.add_pattern(&pattern_g, 0);
        paths.finish();

        let mut egraph = EGraph::new();
        let left = egraph.add(0, &[]);
        let right = egraph.add(1, &[]);
        let unrelated = egraph.add(2, &[]);
        let g_left = egraph.add(20, &[left]);
        egraph.add(20, &[right]);
        egraph.add(30, &[g_left]);
        let h_unrelated = egraph.add(21, &[unrelated]);
        egraph.add(30, &[h_unrelated]);
        egraph.merge(left, right, 1);
        assert_eq!(paths.affected_patterns(&egraph, &[left, right]), [0].into());

        let recursive = egraph.add(40, &[unrelated]);
        egraph.merge(unrelated, recursive, 2);
        assert_eq!(
            paths.affected_patterns(&egraph, &[unrelated]),
            [1, 2].into()
        );
    }

    #[test]
    fn compiled_parent_paths_distinguish_argument_positions_after_shared_prefix() {
        let left_path = Pattern::App(
            30,
            vec![Pattern::App(20, vec![Pattern::Var(0)]), Pattern::Var(1)],
        );
        let right_path = Pattern::App(
            30,
            vec![Pattern::Var(1), Pattern::App(20, vec![Pattern::Var(0)])],
        );
        let mut paths = PatternPathIndex::default();
        paths.add_pattern(&left_path, 0);
        paths.add_pattern(&right_path, 1);
        paths.finish();

        let mut egraph = EGraph::new();
        let left = egraph.add(0, &[]);
        let right = egraph.add(1, &[]);
        let other = egraph.add(2, &[]);
        let g_left = egraph.add(20, &[left]);
        egraph.add(20, &[right]);
        egraph.add(30, &[g_left, other]);
        egraph.merge(left, right, 1);

        assert_eq!(paths.affected_patterns(&egraph, &[left, right]), [0].into());
    }

    #[test]
    fn class_and_ground_filters_reduce_same_shape_path_terminals_independently() {
        const LABELS: usize = 8;
        const CONSTANTS: usize = 8;
        const TERMS_PER_PATTERN: usize = 64;
        const PATTERNS: usize = LABELS * CONSTANTS;

        let (mut arena, ground, foralls, merge_equality) =
            path_filter_matrix_stress(LABELS, CONSTANTS, TERMS_PER_PATTERN);
        let mut unfiltered = IncrementalEmatchSession::new(&mut arena, &foralls);
        let mut class_only = IncrementalEmatchSession::new(&mut arena, &foralls);
        let mut ground_only = IncrementalEmatchSession::new(&mut arena, &foralls);
        let mut combined = IncrementalEmatchSession::new(&mut arena, &foralls);
        assert_eq!(combined.patterns.len(), PATTERNS);

        for session in [
            &mut unfiltered,
            &mut class_only,
            &mut ground_only,
            &mut combined,
        ] {
            session.extend_ground(&arena, &ground);
            assert!(
                session
                    .match_witness_tuples()
                    .into_iter()
                    .all(|tuples| tuples.is_none())
            );
        }

        let mut extended_ground = ground;
        extended_ground.push(merge_equality);

        let unfiltered_before = unfiltered.pattern_executions;
        let unfiltered_started = Instant::now();
        unfiltered.extend_ground_with_path_filters(
            &arena,
            &extended_ground,
            PatternFilterMode::Unfiltered,
        );
        let unfiltered_tuples = unfiltered.match_witness_tuples();
        let unfiltered_elapsed = unfiltered_started.elapsed();

        let class_before = class_only.pattern_executions;
        let class_started = Instant::now();
        class_only.extend_ground_with_path_filters(
            &arena,
            &extended_ground,
            PatternFilterMode::ClassOnly,
        );
        let class_tuples = class_only.match_witness_tuples();
        let class_elapsed = class_started.elapsed();

        let ground_before = ground_only.pattern_executions;
        let ground_started = Instant::now();
        ground_only.extend_ground_with_path_filters(
            &arena,
            &extended_ground,
            PatternFilterMode::GroundOnly,
        );
        let ground_tuples = ground_only.match_witness_tuples();
        let ground_elapsed = ground_started.elapsed();

        let combined_before = combined.pattern_executions;
        let combined_started = Instant::now();
        combined.extend_ground(&arena, &extended_ground);
        let combined_tuples = combined.match_witness_tuples();
        let combined_elapsed = combined_started.elapsed();

        assert_eq!(unfiltered.pattern_executions - unfiltered_before, PATTERNS);
        assert_eq!(class_only.pattern_executions - class_before, CONSTANTS);
        assert_eq!(ground_only.pattern_executions - ground_before, LABELS);
        assert_eq!(combined.pattern_executions - combined_before, 1);
        assert_eq!(unfiltered.merge_affected_patterns, PATTERNS);
        assert_eq!(class_only.merge_affected_patterns, CONSTANTS);
        assert_eq!(ground_only.merge_affected_patterns, LABELS);
        assert_eq!(combined.merge_affected_patterns, 1);
        assert_eq!(combined_tuples, unfiltered_tuples);
        assert_eq!(combined_tuples, class_tuples);
        assert_eq!(combined_tuples, ground_tuples);
        assert_eq!(combined_tuples[0].as_ref().unwrap().len(), 1);
        assert!(combined_tuples[1..].iter().all(Option::is_none));
        eprintln!(
            "path filter target: patterns={PATTERNS} labels={LABELS} constants={CONSTANTS} retained_terms={} affected_unfiltered={PATTERNS} affected_class={CONSTANTS} affected_ground={LABELS} affected_combined=1 unfiltered_round_us={} class_round_us={} ground_round_us={} combined_round_us={}",
            PATTERNS * TERMS_PER_PATTERN + LABELS,
            unfiltered_elapsed.as_micros(),
            class_elapsed.as_micros(),
            ground_elapsed.as_micros(),
            combined_elapsed.as_micros()
        );
    }

    #[test]
    fn generation_delta_candidates_avoid_full_affected_pattern_rescan() {
        const APPLICATIONS: usize = 4096;

        let (mut arena, ground, forall, merge_equality) = generation_delta_stress(APPLICATIONS);
        let mut full = IncrementalEmatchSession::new(&mut arena, &[forall]);
        let mut delta = IncrementalEmatchSession::new(&mut arena, &[forall]);
        full.extend_ground(&arena, &ground);
        delta.extend_ground(&arena, &ground);
        assert_eq!(full.match_witness_tuples(), delta.match_witness_tuples());

        let mut extended_ground = ground;
        extended_ground.push(merge_equality);

        let full_before = full.pattern_executions;
        let full_started = Instant::now();
        full.extend_ground_with_full_pattern_path_invalidation(&arena, &extended_ground);
        let full_tuples = full.match_witness_tuples();
        let full_elapsed = full_started.elapsed();

        let delta_before = delta.pattern_executions;
        let candidate_before = delta.candidate_applications_scanned;
        let delta_started = Instant::now();
        delta.extend_ground(&arena, &extended_ground);
        let delta_tuples = delta.match_witness_tuples();
        let delta_elapsed = delta_started.elapsed();

        assert_eq!(full_tuples, delta_tuples);
        assert_eq!(full.pattern_executions - full_before, 1);
        assert_eq!(delta.pattern_executions - delta_before, 1);
        assert_eq!(delta.candidate_applications_scanned - candidate_before, 1);
        assert_eq!(delta_tuples[0].as_ref().unwrap().len(), 1);
        eprintln!(
            "generation delta target: retained_outer_apps={APPLICATIONS} full_pattern_executions=1 delta_pattern_executions=1 full_top_applications_scanned={APPLICATIONS} delta_top_applications_scanned=1 full_round_us={} delta_round_us={}",
            full_elapsed.as_micros(),
            delta_elapsed.as_micros()
        );
    }

    #[test]
    fn selective_merge_queue_enables_nested_trigger_match() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let argument = arena.bv_var("nested_merge_a", 8).unwrap();
        let outer_argument = arena.bv_var("nested_merge_b", 8).unwrap();
        let inner_function = arena.declare_fun("nested_merge_g", &[sort], sort).unwrap();
        let outer_function = arena.declare_fun("nested_merge_f", &[sort], sort).unwrap();
        let ga = arena.apply(inner_function, &[argument]).unwrap();
        let fb = arena.apply(outer_function, &[outer_argument]).unwrap();
        let ga_eq_zero = arena.eq(ga, zero).unwrap();
        let fb_eq_zero = arena.eq(fb, zero).unwrap();
        let mut ground = vec![
            arena.not(ga_eq_zero).unwrap(),
            arena.not(fb_eq_zero).unwrap(),
        ];

        let variable = arena.declare("nested_merge_x", sort).unwrap();
        let variable_term = arena.var(variable);
        let gx = arena.apply(inner_function, &[variable_term]).unwrap();
        let fgx = arena.apply(outer_function, &[gx]).unwrap();
        let body = arena.eq(fgx, zero).unwrap();
        let forall = arena.forall(variable, body).unwrap();

        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall]);
        session.extend_ground(&arena, &ground);
        assert_eq!(session.match_witness_tuples(), vec![None]);
        ground.push(arena.eq(outer_argument, ga).unwrap());
        session.extend_ground(&arena, &ground);
        assert_eq!(session.dirty_patterns.len(), 0);
        assert_eq!(session.candidate_patterns.len(), 1);
        assert_eq!(session.candidate_patterns.values().next().unwrap().len(), 1);
        assert_eq!(session.merge_affected_patterns, 1);
        let tuples = session.match_witness_tuples();
        let fresh = witness_tuples_via_egraph(&mut arena, &ground, forall)
            .expect("the merge enables the nested trigger")
            .2;
        assert_eq!(tuples, vec![Some(fresh)]);
    }

    #[test]
    fn selective_merge_queue_enables_ground_subpattern_match() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let argument = arena.bv_var("ground_merge_a", 8).unwrap();
        let pattern_constant = arena.bv_var("ground_merge_c", 8).unwrap();
        let ground_constant = arena.bv_var("ground_merge_d", 8).unwrap();
        let function = arena
            .declare_fun("ground_merge_h", &[sort, sort], sort)
            .unwrap();
        let had = arena.apply(function, &[argument, ground_constant]).unwrap();
        let had_eq_zero = arena.eq(had, zero).unwrap();
        let mut ground = vec![arena.not(had_eq_zero).unwrap()];

        let variable = arena.declare("ground_merge_x", sort).unwrap();
        let variable_term = arena.var(variable);
        let hxc = arena
            .apply(function, &[variable_term, pattern_constant])
            .unwrap();
        let body = arena.eq(hxc, zero).unwrap();
        let forall = arena.forall(variable, body).unwrap();

        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall]);
        session.extend_ground(&arena, &ground);
        assert_eq!(session.match_witness_tuples(), vec![None]);
        ground.push(arena.eq(pattern_constant, ground_constant).unwrap());
        session.extend_ground(&arena, &ground);
        assert_eq!(session.dirty_patterns.len(), 0);
        assert_eq!(session.candidate_patterns.len(), 1);
        assert_eq!(session.candidate_patterns.values().next().unwrap().len(), 1);
        let tuples = session.match_witness_tuples();
        let fresh = witness_tuples_via_egraph(&mut arena, &ground, forall)
            .expect("the merge enables the ground subpattern")
            .2;
        assert_eq!(tuples, vec![Some(fresh)]);
    }

    #[test]
    fn add_and_merge_round_dirties_the_union_of_affected_roots() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let merge_left = arena.bv_var("union_round_a", 8).unwrap();
        let merge_right = arena.bv_var("union_round_b", 8).unwrap();
        let added_argument = arena.bv_var("union_round_c", 8).unwrap();
        let merge_function = arena
            .declare_fun("union_round_f", &[sort, sort], sort)
            .unwrap();
        let added_function = arena.declare_fun("union_round_u", &[sort], sort).unwrap();
        let fab = arena
            .apply(merge_function, &[merge_left, merge_right])
            .unwrap();
        let fab_eq_zero = arena.eq(fab, zero).unwrap();
        let mut ground = vec![arena.not(fab_eq_zero).unwrap()];

        let variable = arena.declare("union_round_x", sort).unwrap();
        let variable_term = arena.var(variable);
        let fxx = arena
            .apply(merge_function, &[variable_term, variable_term])
            .unwrap();
        let fbody = arena.eq(fxx, zero).unwrap();
        let forall_f = arena.forall(variable, fbody).unwrap();
        let ux = arena.apply(added_function, &[variable_term]).unwrap();
        let ubody = arena.eq(ux, zero).unwrap();
        let forall_u = arena.forall(variable, ubody).unwrap();

        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall_f, forall_u]);
        session.extend_ground(&arena, &ground);
        session.match_witness_tuples();

        let uc = arena.apply(added_function, &[added_argument]).unwrap();
        let uc_eq_zero = arena.eq(uc, zero).unwrap();
        ground.push(arena.not(uc_eq_zero).unwrap());
        ground.push(arena.eq(merge_left, merge_right).unwrap());
        session.extend_ground(&arena, &ground);
        assert_eq!(session.dirty_patterns.len(), 0);
        assert_eq!(session.candidate_patterns.len(), 2);
        assert!(
            session
                .candidate_patterns
                .values()
                .all(|candidates| candidates.len() == 1)
        );
        assert_eq!(session.merge_affected_patterns, 1);
        let tuples = session.match_witness_tuples();
        assert_eq!(tuples[0].as_ref().unwrap().len(), 1);
        assert_eq!(tuples[1].as_ref().unwrap().len(), 1);
    }

    #[test]
    fn retained_substitution_join_uses_current_eclass_roots() {
        let mut egraph = EGraph::new();
        let a = egraph.add(0, &[]);
        let b = egraph.add(1, &[]);
        let left = vec![Some(a)];
        let right = vec![Some(b)];
        assert!(merge_substitutions(&left, &right).is_none());

        egraph.merge(a, b, 1);
        assert_eq!(
            merge_substitutions_modulo(&egraph, &left, &right),
            Some(vec![Some(egraph.root(a))])
        );
    }

    #[test]
    fn equal_top_applications_preserve_cached_distinct_bindings_without_rematch() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let left = arena.bv_var("equal_apps_left", 8).unwrap();
        let right = arena.bv_var("equal_apps_right", 8).unwrap();
        let function = arena.declare_fun("equal_apps_f", &[sort], sort).unwrap();
        let left_app = arena.apply(function, &[left]).unwrap();
        let right_app = arena.apply(function, &[right]).unwrap();
        let left_eq_zero = arena.eq(left_app, zero).unwrap();
        let right_eq_zero = arena.eq(right_app, zero).unwrap();
        let mut ground = vec![
            arena.not(left_eq_zero).unwrap(),
            arena.not(right_eq_zero).unwrap(),
        ];

        let variable = arena.declare("equal_apps_x", sort).unwrap();
        let variable_term = arena.var(variable);
        let pattern_app = arena.apply(function, &[variable_term]).unwrap();
        let body = arena.eq(pattern_app, zero).unwrap();
        let forall = arena.forall(variable, body).unwrap();

        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall]);
        session.extend_ground(&arena, &ground);
        let before = session.match_witness_tuples();
        assert_eq!(before[0].as_ref().unwrap().len(), 2);
        let executions = session.pattern_executions;

        ground.push(arena.eq(left_app, right_app).unwrap());
        session.extend_ground(&arena, &ground);
        assert!(session.dirty_patterns.is_empty());
        let cached = session.match_witness_tuples();
        assert_eq!(session.pattern_executions, executions);
        let fresh = witness_tuples_via_egraph(&mut arena, &ground, forall)
            .expect("both unequal arguments remain valid trigger bindings")
            .2;
        assert_eq!(cached, vec![Some(fresh)]);
        assert_eq!(cached[0].as_ref().unwrap().len(), 2);
    }

    #[test]
    fn lazy_clause_batch_prioritizes_one_conflict_among_256_matches() {
        const MATCHES: usize = 256;

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let zero = arena.bv_const(16, 0).unwrap();
        let one = arena.bv_const(16, 1).unwrap();
        let mut ground = Vec::with_capacity(MATCHES * 2);
        let mut conflict_instance = None;
        for i in 0..MATCHES {
            let a = arena.bv_var(&format!("a{i}"), 16).unwrap();
            let fa = arena.apply(f, &[a]).unwrap();
            let ga = arena.apply(g, &[a]).unwrap();
            let fa_eq_zero = arena.eq(fa, zero).unwrap();
            ground.push(arena.not(fa_eq_zero).unwrap());
            let ga_eq_one = arena.eq(ga, one).unwrap();
            if i + 1 == MATCHES {
                ground.push(arena.not(ga_eq_one).unwrap());
                conflict_instance = Some(arena.or(fa_eq_zero, ga_eq_one).unwrap());
            } else {
                ground.push(ga_eq_one);
            }
        }

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let gx = arena.apply(g, &[xv]).unwrap();
        let fx_eq_zero = arena.eq(fx, zero).unwrap();
        let gx_eq_one = arena.eq(gx, one).unwrap();
        let body = arena.or(fx_eq_zero, gx_eq_one).unwrap();
        let forall = arena.forall(x, body).unwrap();

        let eager_total_started = Instant::now();
        let eager = instantiate_forall_via_egraph(&mut arena, &ground, forall);
        assert_eq!(eager.len(), MATCHES, "every distinct f(a_i) must match");
        let mut eager_replay = ground.clone();
        eager_replay.extend(eager.iter().copied());
        let eager_started = Instant::now();
        assert_eq!(
            check_auto(&mut arena, &eager_replay, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        let eager_elapsed = eager_started.elapsed();
        let eager_total_elapsed = eager_total_started.elapsed();

        let lazy_total_started = Instant::now();
        let batch = lazy_clause_instances(&mut arena, &ground, forall);
        assert_eq!(batch.redundant, MATCHES - 1);
        assert!(batch.deferred.is_empty());
        assert_eq!(batch.urgent, vec![conflict_instance.unwrap()]);
        assert!(
            eager.contains(&batch.urgent[0]),
            "the scheduler must retain a genuine complete source instance"
        );
        let mut retained = IncrementalEmatchSession::new(&mut arena, &[forall]);
        retained.extend_ground(&arena, &ground);
        let retained_batch = retained.lazy_clause_batches(&mut arena).remove(0);
        assert_eq!(retained_batch.redundant, batch.redundant);
        assert_eq!(retained_batch.urgent, batch.urgent);
        assert_eq!(retained_batch.deferred, batch.deferred);

        let mut replay = ground.clone();
        replay.extend(batch.urgent);
        let lazy_started = Instant::now();
        assert_eq!(
            check_auto(&mut arena, &replay, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat,
            "the original ground context plus the selected source instance refutes"
        );
        let lazy_elapsed = lazy_started.elapsed();
        let lazy_total_elapsed = lazy_total_started.elapsed();
        eprintln!(
            "lazy quantifier clause target: eager_instances={MATCHES} eager_qf_us={} eager_total_us={} lazy_instances=1 lazy_qf_us={} lazy_total_us={}",
            eager_elapsed.as_micros(),
            eager_total_elapsed.as_micros(),
            lazy_elapsed.as_micros(),
            lazy_total_elapsed.as_micros()
        );
        let mut assertions = ground;
        assertions.push(forall);
        assert_eq!(
            prove_quantified_unsat_via_egraph(&mut arena, &assertions, &SolverConfig::default(),)
                .unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    #[allow(
        clippy::many_single_char_names,
        clippy::similar_names,
        clippy::too_many_lines
    )]
    fn detached_clause_certificate_replays_and_rejects_tampering() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a = arena.bv_var("detach_a", 8).unwrap();
        let b = arena.bv_var("detach_b", 8).unwrap();
        let f = arena.declare_fun("detach_f", &[sort], sort).unwrap();
        let h = arena.declare_fun("detach_h", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ha = arena.apply(h, &[a]).unwrap();
        let fa_eq_zero = arena.eq(fa, zero).unwrap();
        let ha_eq_zero = arena.eq(ha, zero).unwrap();
        let ha_ne_zero = arena.not(ha_eq_zero).unwrap();

        let x = arena.declare("detach_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let hx = arena.apply(h, &[xv]).unwrap();
        let fx_eq_zero = arena.eq(fx, zero).unwrap();
        let false_sibling = arena.not(fx_eq_zero).unwrap();
        let propagated = arena.eq(hx, one).unwrap();
        let body = arena.or(false_sibling, propagated).unwrap();
        let forall = arena.forall(x, body).unwrap();
        let ground = vec![fa_eq_zero, ha_ne_zero];
        let assertions = vec![fa_eq_zero, ha_ne_zero, forall];

        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall]);
        session.extend_ground(&arena, &ground);
        let batch = session.lazy_clause_batches(&mut arena).remove(0);
        assert!(batch.urgent.is_empty());
        assert!(batch.deferred.is_empty());
        assert_eq!(batch.propagations.len(), 1);
        let certificate = batch.propagations[0].clone();
        assert_eq!(certificate.bindings, vec![a]);
        assert_eq!(certificate.false_siblings.len(), 1);
        assert_eq!(certificate.false_siblings[0].reasons, vec![fa_eq_zero]);
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &certificate
        ));

        let wrong_var = arena.declare("detach_wrong_x", sort).unwrap();
        let wrong_forall = arena.forall(wrong_var, body).unwrap();
        let mut tampered = certificate.clone();
        tampered.assertion = wrong_forall;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered.bindings[0] = b;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered.source_instance = certificate.propagated_literal;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered.propagated_literal = certificate.false_siblings[0].literal;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered.false_siblings[0].literal = certificate.propagated_literal;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered
            .false_siblings
            .push(certificate.false_siblings[0].clone());
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered.false_siblings[0].reasons.clear();
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate.clone();
        tampered.false_siblings[0].reasons = vec![ha_ne_zero];
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let generated_reason = arena.eq(a, a).unwrap();
        let mut tampered = certificate.clone();
        tampered.false_siblings[0].reasons = vec![generated_reason];
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
        let mut tampered = certificate;
        tampered.false_siblings[0].reasons = vec![fa_eq_zero, fa_eq_zero];
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn detached_clause_reasons_cover_congruence_and_transported_disequality() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let two = arena.bv_const(8, 2).unwrap();
        let a = arena.bv_var("detach_transport_a", 8).unwrap();
        let b = arena.bv_var("detach_transport_b", 8).unwrap();
        let f = arena
            .declare_fun("detach_transport_f", &[sort], sort)
            .unwrap();
        let h = arena
            .declare_fun("detach_transport_h", &[sort], sort)
            .unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let ha = arena.apply(h, &[a]).unwrap();
        let fa_eq_zero = arena.eq(fa, zero).unwrap();
        let fa_ne_zero = arena.not(fa_eq_zero).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let fb_eq_two = arena.eq(fb, two).unwrap();
        let fb_ne_two = arena.not(fb_eq_two).unwrap();
        let ha_eq_zero = arena.eq(ha, zero).unwrap();
        let ha_ne_zero = arena.not(ha_eq_zero).unwrap();
        let ground = vec![fa_ne_zero, a_eq_b, fb_ne_two, ha_ne_zero];

        let x = arena.declare("detach_transport_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let hx = arena.apply(h, &[xv]).unwrap();
        let positive_false = arena.eq(fx, two).unwrap();
        let hx_eq_one = arena.eq(hx, one).unwrap();
        let body = arena.or(positive_false, hx_eq_one).unwrap();
        let forall = arena.forall(x, body).unwrap();
        let mut assertions = ground.clone();
        assertions.push(forall);

        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall]);
        session.extend_ground(&arena, &ground);
        let batch = session.lazy_clause_batches(&mut arena).remove(0);
        assert_eq!(batch.propagations.len(), 1);
        let certificate = &batch.propagations[0];
        assert!(certificate.false_siblings[0].reasons.contains(&a_eq_b));
        assert!(certificate.false_siblings[0].reasons.contains(&fb_ne_two));
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            certificate
        ));

        let fx_eq_fb = arena.eq(fx, fb).unwrap();
        let negative_false = arena.not(fx_eq_fb).unwrap();
        let body = arena.or(negative_false, hx_eq_one).unwrap();
        let congruent_forall = arena.forall(x, body).unwrap();
        let mut congruent_assertions = ground.clone();
        congruent_assertions.push(congruent_forall);
        let mut congruent = IncrementalEmatchSession::new(&mut arena, &[congruent_forall]);
        congruent.extend_ground(&arena, &ground);
        let batch = congruent.lazy_clause_batches(&mut arena).remove(0);
        assert_eq!(batch.propagations.len(), 1);
        assert_eq!(
            batch.propagations[0].false_siblings[0].reasons,
            vec![a_eq_b]
        );
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &congruent_assertions,
            &batch.propagations[0]
        ));
    }

    #[test]
    fn detached_clause_checker_accepts_reflexive_and_false_constant_siblings() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let a = arena.bv_var("detach_reflexive_a", 8).unwrap();
        let f = arena
            .declare_fun("detach_reflexive_f", &[sort], sort)
            .unwrap();
        let x = arena.declare("detach_reflexive_x", sort).unwrap();
        let xv = arena.var(x);
        let reflexive = arena.eq(xv, xv).unwrap();
        let false_reflexive = arena.not(reflexive).unwrap();
        let fx = arena.apply(f, &[xv]).unwrap();
        let target = arena.eq(fx, zero).unwrap();
        let body = arena.or(false_reflexive, target).unwrap();
        let forall = arena.forall(x, body).unwrap();
        let a_eq_a = arena.eq(a, a).unwrap();
        let false_a_eq_a = arena.not(a_eq_a).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let propagated = arena.eq(fa, zero).unwrap();
        let source_instance = arena.or(false_a_eq_a, propagated).unwrap();
        let certificate = QuantifierClausePropagationCertificate {
            assertion: forall,
            bindings: vec![a],
            source_instance,
            propagated_literal: propagated,
            false_siblings: vec![QuantifierFalseSiblingJustification {
                literal: false_a_eq_a,
                reasons: Vec::new(),
            }],
            derived_reasons: Vec::new(),
        };
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &[forall],
            &certificate
        ));

        let false_term = arena.bool_const(false);
        let body = arena.or(false_term, target).unwrap();
        let forall_false = arena.forall(x, body).unwrap();
        let source_instance = arena.or(false_term, propagated).unwrap();
        let false_certificate = QuantifierClausePropagationCertificate {
            assertion: forall_false,
            bindings: vec![a],
            source_instance,
            propagated_literal: propagated,
            false_siblings: vec![QuantifierFalseSiblingJustification {
                literal: false_term,
                reasons: Vec::new(),
            }],
            derived_reasons: Vec::new(),
        };
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &[forall_false],
            &false_certificate
        ));
    }

    #[test]
    fn generated_equality_reason_falls_back_to_complete_source_instance() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a = arena.bv_var("detach_generated_a", 8).unwrap();
        let f = arena
            .declare_fun("detach_generated_f", &[sort], sort)
            .unwrap();
        let h = arena
            .declare_fun("detach_generated_h", &[sort], sort)
            .unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ha = arena.apply(h, &[a]).unwrap();
        let fa_eq_zero = arena.eq(fa, zero).unwrap();
        let fa_ne_zero = arena.not(fa_eq_zero).unwrap();
        let ha_eq_zero = arena.eq(ha, zero).unwrap();
        let ha_ne_zero = arena.not(ha_eq_zero).unwrap();
        let mut ground = vec![fa_ne_zero, ha_ne_zero];

        let x = arena.declare("detach_generated_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let hx = arena.apply(h, &[xv]).unwrap();
        let generated_body = arena.eq(fx, one).unwrap();
        let generator = arena.forall(x, generated_body).unwrap();
        let false_sibling = arena.not(generated_body).unwrap();
        let target = arena.eq(hx, one).unwrap();
        let consumer_body = arena.or(false_sibling, target).unwrap();
        let consumer = arena.forall(x, consumer_body).unwrap();

        let mut session = IncrementalEmatchSession::new(&mut arena, &[generator, consumer]);
        session.extend_ground(&arena, &ground);
        let first = session.lazy_clause_batches(&mut arena);
        assert_eq!(first[0].urgent.len(), 1);
        assert!(first[1].propagations.is_empty());
        assert_eq!(first[1].deferred.len(), 1);
        ground.push(first[0].urgent[0]);

        session.extend_ground(&arena, &ground);
        let second = session.lazy_clause_batches(&mut arena);
        assert!(second[1].propagations.is_empty());
        assert_eq!(second[1].urgent.len(), 1);
        let fa_eq_one = arena.eq(fa, one).unwrap();
        let fa_ne_one = arena.not(fa_eq_one).unwrap();
        let ha_eq_one = arena.eq(ha, one).unwrap();
        let expected = arena.or(fa_ne_one, ha_eq_one).unwrap();
        assert_eq!(second[1].urgent[0], expected);
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::too_many_lines)]
    fn exact_instance_provenance_justifies_later_detached_literal() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a = arena.bv_var("instance_provenance_a", 8).unwrap();
        let f = arena
            .declare_fun("instance_provenance_f", &[sort], sort)
            .unwrap();
        let h = arena
            .declare_fun("instance_provenance_h", &[sort], sort)
            .unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ha = arena.apply(h, &[a]).unwrap();
        let fa_eq_zero = arena.eq(fa, zero).unwrap();
        let source_f_disequality = arena.not(fa_eq_zero).unwrap();
        let ha_eq_one = arena.eq(ha, one).unwrap();
        let p = arena.bool_var("instance_provenance_p").unwrap();
        let not_ha_eq_one = arena.not(ha_eq_one).unwrap();
        let target_implies_p = arena.or(not_ha_eq_one, p).unwrap();
        let not_p = arena.not(p).unwrap();

        let x = arena.declare("instance_provenance_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let hx = arena.apply(h, &[xv]).unwrap();
        let generated_body = arena.eq(fx, one).unwrap();
        let generator = arena.forall(x, generated_body).unwrap();
        let false_sibling = arena.not(generated_body).unwrap();
        let target = arena.eq(hx, one).unwrap();
        let consumer_body = arena.or(false_sibling, target).unwrap();
        let consumer = arena.forall(x, consumer_body).unwrap();
        let assertions = vec![
            source_f_disequality,
            target_implies_p,
            not_p,
            generator,
            consumer,
        ];

        let source_ground = vec![source_f_disequality, target_implies_p, not_p];
        let mut ground = source_ground.clone();
        let mut session = IncrementalEmatchSession::new(&mut arena, &[generator, consumer]);
        let derivations = HashMap::new();
        session.extend_ground_with_derivations(&arena, &ground, &derivations);
        let first = session.lazy_clause_batches(&mut arena);
        let instance = first[0].urgent[0];
        let instance_certificate = first[0].instance_certificates[&instance].clone();
        assert_eq!(
            instance_certificate,
            QuantifierInstanceCertificate {
                assertion: generator,
                bindings: vec![a],
                instance,
            }
        );

        ground.push(instance);
        let mut derivations = HashMap::new();
        derivations.insert(
            instance,
            QuantifierGroundDerivation::Instance(instance_certificate.clone()),
        );
        session.extend_ground_with_derivations(&arena, &ground, &derivations);
        let second = session.lazy_clause_batches(&mut arena);
        assert_eq!(second[1].propagations.len(), 1);
        let propagation = &second[1].propagations[0];
        assert_eq!(
            propagation.derived_reasons,
            vec![QuantifierGroundDerivation::Instance(
                instance_certificate.clone()
            )]
        );
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            propagation
        ));

        let mut online = OnlineQuantifierClauseSession::new(&arena, &source_ground, None).unwrap();
        assert_eq!(
            online.add_checked_batch(&mut arena, &assertions, &[instance], &derivations),
            Some(CdcltOutcome::Sat)
        );
        let propagated = propagation.propagated_literal;
        let propagation_derivation =
            QuantifierGroundDerivation::Propagation(Box::new(propagation.clone()));
        assert!(check_quantifier_ground_derivation(
            &mut arena,
            &assertions,
            &propagation_derivation
        ));
        let propagation_derivations = HashMap::from([(propagated, propagation_derivation)]);
        assert_eq!(
            online.add_checked_batch(
                &mut arena,
                &assertions,
                &[propagated],
                &propagation_derivations,
            ),
            Some(CdcltOutcome::Unsat)
        );
        assert_eq!(online.inserted_clauses, 2);
        assert_eq!(online.solve_calls, 2);
        ground.push(propagated);
        assert_eq!(
            check_auto(&mut arena, &ground, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat,
            "the retained refutation candidate must independently replay in QF"
        );

        let mut wrong = instance_certificate;
        wrong.bindings[0] = one;
        let wrong_derivations =
            HashMap::from([(instance, QuantifierGroundDerivation::Instance(wrong))]);
        let mut rejecting =
            OnlineQuantifierClauseSession::new(&arena, &source_ground, None).unwrap();
        assert_eq!(
            rejecting.add_checked_batch(&mut arena, &assertions, &[instance], &wrong_derivations,),
            None
        );
        assert_eq!(rejecting.inserted_clauses, 0);
        assert_eq!(
            prove_quantified_unsat_via_egraph(&mut arena, &assertions, &SolverConfig::default(),)
                .unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::similar_names)]
    fn online_quantifier_session_mixes_full_clause_and_dynamic_disequality() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("online_clause_a", 8).unwrap();
        let b = arena.bv_var("online_clause_b", 8).unwrap();
        let f = arena.declare_fun("online_clause_f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();

        let x = arena.declare("online_clause_x", sort).unwrap();
        let xv = arena.var(x);
        let x_eq_a = arena.eq(xv, a).unwrap();
        let not_x_eq_a = arena.not(x_eq_a).unwrap();
        let fx = arena.apply(f, &[xv]).unwrap();
        let fx_eq_fa = arena.eq(fx, fa).unwrap();
        let congruence_body = arena.or(not_x_eq_a, fx_eq_fa).unwrap();
        let congruence_universal = arena.forall(x, congruence_body).unwrap();
        let disequality_body = arena.not(fx_eq_fa).unwrap();
        let disequality_universal = arena.forall(x, disequality_body).unwrap();
        let b_eq_a = arena.eq(b, a).unwrap();
        let not_b_eq_a = arena.not(b_eq_a).unwrap();
        let fb_eq_fa = arena.eq(fb, fa).unwrap();
        let full_instance = arena.or(not_b_eq_a, fb_eq_fa).unwrap();
        let disequality_instance = arena.not(fb_eq_fa).unwrap();
        let assertions = vec![a_eq_b, congruence_universal, disequality_universal];
        let full_derivation = QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
            assertion: congruence_universal,
            bindings: vec![b],
            instance: full_instance,
        });
        let disequality_derivation =
            QuantifierGroundDerivation::Instance(QuantifierInstanceCertificate {
                assertion: disequality_universal,
                bindings: vec![b],
                instance: disequality_instance,
            });
        let mut online = OnlineQuantifierClauseSession::new(&arena, &[a_eq_b], None).unwrap();
        assert_eq!(
            online.add_checked_batch(
                &mut arena,
                &assertions,
                &[full_instance],
                &HashMap::from([(full_instance, full_derivation.clone())]),
            ),
            Some(CdcltOutcome::Sat)
        );
        assert_eq!(
            online.add_checked_batch(
                &mut arena,
                &assertions,
                &[disequality_instance],
                &HashMap::from([(disequality_instance, disequality_derivation)]),
            ),
            Some(CdcltOutcome::Unsat)
        );
        assert_eq!(online.inserted_clauses, 2);
        assert_eq!(online.atom_variables.len(), 3);

        let mut limited = OnlineQuantifierClauseSession::new(&arena, &[a_eq_b], None).unwrap();
        limited.limits.variables = limited.solver.variable_count();
        assert_eq!(
            limited.add_checked_batch(
                &mut arena,
                &assertions,
                &[full_instance],
                &HashMap::from([(full_instance, full_derivation)]),
            ),
            None
        );
        assert_eq!(limited.inserted_clauses, 0);

        let ground = [a_eq_b, full_instance, disequality_instance];
        assert_eq!(
            check_auto(&mut arena, &ground, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        let mut replay_stats = QuantifierLoopStats::default();
        assert!(
            replay_online_refutation(
                &mut arena,
                &ground,
                &SolverConfig::default(),
                &mut replay_stats,
            )
            .unwrap()
        );
        assert!(
            !replay_online_refutation(
                &mut arena,
                &[a_eq_b],
                &SolverConfig::default(),
                &mut replay_stats,
            )
            .unwrap(),
            "an online outcome cannot bypass a non-refuting final QF query"
        );
    }

    #[test]
    fn online_quantifier_session_declines_unsupported_boolean_skeleton() {
        let mut arena = TermArena::new();
        let left = arena.bv_var("online_decline_left", 8).unwrap();
        let right = arena.bv_var("online_decline_right", 8).unwrap();
        let comparison = arena.bv_ult(left, right).unwrap();
        assert!(OnlineQuantifierClauseSession::new(&arena, &[comparison], None).is_none());
        assert_ne!(
            check_auto(&mut arena, &[comparison], &SolverConfig::default()).unwrap(),
            CheckResult::Unsat,
            "declining the accelerator must leave the ordinary QF result intact"
        );

        let equality = arena.eq(left, right).unwrap();
        for limits in [
            OnlineQuantifierLimits {
                variables: 0,
                clauses: usize::MAX,
                literals: usize::MAX,
            },
            OnlineQuantifierLimits {
                variables: usize::MAX,
                clauses: 0,
                literals: usize::MAX,
            },
            OnlineQuantifierLimits {
                variables: usize::MAX,
                clauses: usize::MAX,
                literals: 0,
            },
        ] {
            assert!(
                OnlineQuantifierClauseSession::new_with_limits(&arena, &[equality], None, limits,)
                    .is_none()
            );
        }
    }

    #[test]
    fn ground_count_limit_replays_an_available_qf_refutation() {
        let mut arena = TermArena::new();
        let false_term = arena.bool_const(false);
        let sort = Sort::BitVec(8);
        let function = arena.declare_fun("ground_limit_f", &[sort], sort).unwrap();
        let x = arena.declare("ground_limit_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(function, &[xv]).unwrap();
        let reflexive = arena.eq(fx, fx).unwrap();
        let universal = arena.forall(x, reflexive).unwrap();
        let mut assertions = vec![false_term; MAX_GROUND_TERMS + 1];
        assertions.push(universal);

        let mut stats = QuantifierLoopStats::default();
        assert_eq!(
            prove_quantified_unsat_via_egraph_impl(
                &mut arena,
                &assertions,
                &SolverConfig::default(),
                true,
                true,
                &mut stats,
            )
            .unwrap(),
            CheckResult::Unsat
        );
        assert_eq!(stats.qf_checks, 1);
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::too_many_lines)]
    fn scoped_sat_candidate_equality_unlocks_nested_trigger_and_then_pops() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("candidate_match_a", 8).unwrap();
        let b = arena.bv_var("candidate_match_b", 8).unwrap();
        let c = arena.bv_var("candidate_match_c", 8).unwrap();
        let p = arena.bool_var("candidate_match_p").unwrap();
        let f = arena
            .declare_fun("candidate_match_f", &[sort], sort)
            .unwrap();
        let g = arena
            .declare_fun("candidate_match_g", &[sort], sort)
            .unwrap();
        let gb = arena.apply(g, &[b]).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let a_eq_gb = arena.eq(a, gb).unwrap();
        let branch = arena.or(a_eq_gb, p).unwrap();
        let not_p = arena.not(p).unwrap();
        let fa_eq_c = arena.eq(fa, c).unwrap();

        let x = arena.declare("candidate_match_x", sort).unwrap();
        let xv = arena.var(x);
        let gx = arena.apply(g, &[xv]).unwrap();
        let fgx = arena.apply(f, &[gx]).unwrap();
        let fgx_eq_c = arena.eq(fgx, c).unwrap();
        let body = arena.not(fgx_eq_c).unwrap();
        let universal = arena.forall(x, body).unwrap();
        let assertions = vec![branch, not_p, fa_eq_c, universal];

        let mut baseline_arena = arena.clone();
        let mut baseline_stats = QuantifierLoopStats::default();
        let baseline_started = Instant::now();
        let baseline = prove_quantified_unsat_via_egraph_impl(
            &mut baseline_arena,
            &assertions,
            &SolverConfig::default(),
            true,
            false,
            &mut baseline_stats,
        )
        .unwrap();
        let baseline_elapsed = baseline_started.elapsed();
        assert!(matches!(baseline, CheckResult::Unknown(_)));

        let mut candidate_arena = arena.clone();
        let mut candidate_stats = QuantifierLoopStats::default();
        let candidate_started = Instant::now();
        let candidate = prove_quantified_unsat_via_egraph_impl(
            &mut candidate_arena,
            &assertions,
            &SolverConfig::default(),
            true,
            true,
            &mut candidate_stats,
        )
        .unwrap();
        let candidate_elapsed = candidate_started.elapsed();
        assert_eq!(candidate, CheckResult::Unsat);
        assert_eq!(candidate_stats.candidate_checks, 1);
        assert!(candidate_stats.candidate_equalities >= 2);
        assert_eq!(candidate_stats.candidate_instances, 1);
        assert_eq!(candidate_stats.candidate_pattern_executions, 1);
        assert_eq!(candidate_stats.candidate_applications_scanned, 1);
        eprintln!(
            "SAT-candidate decision target: baseline={baseline:?} candidate={candidate:?} baseline_qf_checks={} candidate_qf_checks={} online_solves={} candidate_checks={} candidate_instances={} baseline_us={} candidate_us={}",
            baseline_stats.qf_checks,
            candidate_stats.qf_checks,
            candidate_stats.online_solves,
            candidate_stats.candidate_checks,
            candidate_stats.candidate_instances,
            baseline_elapsed.as_micros(),
            candidate_elapsed.as_micros(),
        );

        let ground = [branch, not_p, fa_eq_c];
        let mut matcher = IncrementalEmatchSession::new(&mut arena, &[universal]);
        matcher.extend_ground(&arena, &ground);
        assert!(
            matcher.lazy_clause_batches(&mut arena)[0]
                .instance_certificates
                .is_empty()
        );
        let scoped = matcher
            .scoped_candidate_instances(&mut arena, &[a_eq_gb, fa_eq_c])
            .unwrap();
        assert_eq!(scoped.batch.urgent.len(), 1);
        let a_node = matcher.bridge.term_to_node[&a];
        let gb_node = matcher.bridge.term_to_node[&gb];
        assert!(
            !matcher.bridge.egraph.equal(a_node, gb_node),
            "candidate equality must be popped before an instance leaves the matcher"
        );
        assert!(
            matcher.lazy_clause_batches(&mut arena)[0]
                .instance_certificates
                .is_empty()
        );
        assert!(
            matcher
                .scoped_candidate_instances_with_limits(
                    &mut arena,
                    &[a_eq_gb],
                    MAX_CANDIDATE_EQUALITIES,
                    0,
                )
                .is_none()
        );
        assert!(
            matcher
                .scoped_candidate_instances_with_limits(
                    &mut arena,
                    &[a_eq_gb],
                    0,
                    MAX_CANDIDATE_APPLICATIONS,
                )
                .is_none()
        );

        let optional_branch_assertions = [branch, fa_eq_c, universal];
        assert!(
            !matches!(
                prove_quantified_unsat_via_egraph(
                    &mut arena,
                    &optional_branch_assertions,
                    &SolverConfig::default(),
                )
                .unwrap(),
                CheckResult::Unsat
            ),
            "a candidate from one optional equality branch cannot refute another branch"
        );
        let not_a_eq_gb = arena.not(a_eq_gb).unwrap();
        let disequality_branch = arena.or(not_a_eq_gb, p).unwrap();
        let disequality_assertions = [disequality_branch, not_p, fa_eq_c, universal];
        assert!(
            !matches!(
                prove_quantified_unsat_via_egraph(
                    &mut arena,
                    &disequality_assertions,
                    &SolverConfig::default(),
                )
                .unwrap(),
                CheckResult::Unsat
            ),
            "a false equality atom must not appear in the true-candidate snapshot"
        );
        let positive_universal = arena.forall(x, fgx_eq_c).unwrap();
        let positive_assertions = [branch, not_p, fa_eq_c, positive_universal];
        assert!(
            !matches!(
                prove_quantified_unsat_via_egraph(
                    &mut arena,
                    &positive_assertions,
                    &SolverConfig::default(),
                )
                .unwrap(),
                CheckResult::Unsat
            ),
            "candidate matching a satisfiable positive universal must remain non-UNSAT"
        );
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::too_many_lines)]
    fn scoped_candidate_paths_match_full_scan_with_one_of_many_patterns() {
        const PATTERNS: usize = 64;
        const REPEATS: usize = 128;

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let c = arena.bv_var("candidate_paths_c", 16).unwrap();
        let mut ground = Vec::new();
        let mut universals = Vec::new();
        let mut candidate_equality = None;
        let mut candidate_binding = None;

        for index in 0..PATTERNS {
            let a = arena
                .bv_var(&format!("candidate_paths_a_{index}"), 16)
                .unwrap();
            let b = arena
                .bv_var(&format!("candidate_paths_b_{index}"), 16)
                .unwrap();
            let p = arena
                .bool_var(&format!("candidate_paths_p_{index}"))
                .unwrap();
            let f = arena
                .declare_fun(&format!("candidate_paths_f_{index}"), &[sort], sort)
                .unwrap();
            let g = arena
                .declare_fun(&format!("candidate_paths_g_{index}"), &[sort], sort)
                .unwrap();
            let gb = arena.apply(g, &[b]).unwrap();
            let fa = arena.apply(f, &[a]).unwrap();
            let equality = arena.eq(a, gb).unwrap();
            ground.push(arena.or(equality, p).unwrap());
            ground.push(arena.eq(fa, c).unwrap());

            let x = arena
                .declare(&format!("candidate_paths_x_{index}"), sort)
                .unwrap();
            let xv = arena.var(x);
            let gx = arena.apply(g, &[xv]).unwrap();
            let fgx = arena.apply(f, &[gx]).unwrap();
            let body_equality = arena.eq(fgx, c).unwrap();
            let body = arena.not(body_equality).unwrap();
            universals.push(arena.forall(x, body).unwrap());
            if index == 0 {
                candidate_equality = Some(equality);
                candidate_binding = Some(b);
            }
        }

        let candidate_equality = candidate_equality.unwrap();
        let candidate_binding = candidate_binding.unwrap();
        let mut matcher = IncrementalEmatchSession::new(&mut arena, &universals);
        matcher.extend_ground(&arena, &ground);
        let initial = matcher.lazy_clause_batches(&mut arena);
        assert!(
            initial
                .iter()
                .all(|batch| batch.instance_certificates.is_empty())
        );

        let scoped = matcher
            .scoped_candidate_instances(&mut arena, &[candidate_equality])
            .unwrap();
        assert_eq!(scoped.pattern_executions, 1);
        assert_eq!(scoped.applications_scanned, 1);
        assert_eq!(scoped.batch.urgent.len(), 1);
        let instance = scoped.batch.urgent[0];
        let QuantifierGroundDerivation::Instance(certificate) =
            &scoped.batch.derivations[&instance]
        else {
            unreachable!();
        };
        assert_eq!(certificate.bindings, vec![candidate_binding]);

        let (_, lhs, rhs) = equality_literal(&arena, candidate_equality).unwrap();
        let lhs = matcher.bridge.term_to_node[&lhs];
        let rhs = matcher.bridge.term_to_node[&rhs];
        matcher.bridge.egraph.push();
        matcher.bridge.egraph.merge(lhs, rhs, u32::MAX);
        let patterns = matcher.patterns.clone();
        let mut full_index = matcher.bridge.egraph.new_match_index();
        let full_matches = matcher
            .bridge
            .egraph
            .ematch_many_indexed(&patterns, &mut full_index);
        let full_tuples: Vec<Option<Vec<Vec<TermId>>>> = matcher
            .quantifiers
            .iter()
            .map(|quantifier| matcher.witness_tuples(quantifier, &full_matches))
            .collect();
        matcher.bridge.egraph.pop();
        let nonempty: Vec<&Vec<Vec<TermId>>> = full_tuples.iter().flatten().collect();
        assert_eq!(nonempty.len(), 1);
        assert_eq!(nonempty[0], &vec![vec![candidate_binding]]);
        assert!(scoped.pattern_executions < PATTERNS);

        let exact_started = Instant::now();
        for _ in 0..REPEATS {
            let result = matcher
                .scoped_candidate_instances(&mut arena, &[candidate_equality])
                .unwrap();
            std::hint::black_box(result.batch.urgent.len());
        }
        let exact_elapsed = exact_started.elapsed();
        let full_started = Instant::now();
        for _ in 0..REPEATS {
            matcher.bridge.egraph.push();
            matcher.bridge.egraph.merge(lhs, rhs, u32::MAX);
            let mut full_index = matcher.bridge.egraph.new_match_index();
            let full_matches = matcher
                .bridge
                .egraph
                .ematch_many_indexed(&patterns, &mut full_index);
            let tuple_count = matcher
                .quantifiers
                .iter()
                .filter_map(|quantifier| matcher.witness_tuples(quantifier, &full_matches))
                .map(|tuples| tuples.len())
                .sum::<usize>();
            std::hint::black_box(tuple_count);
            matcher.bridge.egraph.pop();
        }
        let full_elapsed = full_started.elapsed();
        eprintln!(
            "SAT-candidate path target: patterns={PATTERNS} repeats={REPEATS} exact_pattern_executions={} exact_applications={} full_pattern_executions={PATTERNS} exact_us={} full_us={}",
            scoped.pattern_executions,
            scoped.applications_scanned,
            exact_elapsed.as_micros(),
            full_elapsed.as_micros(),
        );
    }

    #[test]
    #[allow(
        clippy::many_single_char_names,
        clippy::similar_names,
        clippy::too_many_lines
    )]
    fn recursive_provenance_table_is_exact_and_canonical() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a = arena.bv_var("provenance_table_a", 8).unwrap();
        let f = arena
            .declare_fun("provenance_table_f", &[sort], sort)
            .unwrap();
        let g = arena
            .declare_fun("provenance_table_g", &[sort], sort)
            .unwrap();
        let h = arena
            .declare_fun("provenance_table_h", &[sort], sort)
            .unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ga = arena.apply(g, &[a]).unwrap();
        let ha = arena.apply(h, &[a]).unwrap();
        let fa_eq_zero = arena.eq(fa, zero).unwrap();
        let source_f_disequality = arena.not(fa_eq_zero).unwrap();
        let ga_eq_zero = arena.eq(ga, zero).unwrap();
        let q = arena.bool_var("provenance_table_q").unwrap();
        let source_g_trigger = arena.or(ga_eq_zero, q).unwrap();
        let ha_eq_zero = arena.eq(ha, zero).unwrap();
        let p = arena.bool_var("provenance_table_p").unwrap();
        let source_h_trigger = arena.or(ha_eq_zero, p).unwrap();

        let x = arena.declare("provenance_table_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let gx = arena.apply(g, &[xv]).unwrap();
        let hx = arena.apply(h, &[xv]).unwrap();
        let generated_equality = arena.eq(fx, one).unwrap();
        let equality_generator = arena.forall(x, generated_equality).unwrap();
        let gx_eq_one = arena.eq(gx, one).unwrap();
        let generated_disequality = arena.not(gx_eq_one).unwrap();
        let disequality_generator = arena.forall(x, generated_disequality).unwrap();
        let first_false_sibling = arena.not(generated_equality).unwrap();
        let target = arena.eq(hx, one).unwrap();
        let partial_clause = arena.or(first_false_sibling, gx_eq_one).unwrap();
        let consumer_body = arena.or(partial_clause, target).unwrap();
        let consumer = arena.forall(x, consumer_body).unwrap();
        let universals = [equality_generator, disequality_generator, consumer];
        let mut assertions = vec![source_f_disequality, source_g_trigger, source_h_trigger];
        assertions.extend(universals);

        let mut ground = vec![source_f_disequality, source_g_trigger, source_h_trigger];
        let mut session = IncrementalEmatchSession::new(&mut arena, &universals);
        let no_derivations = HashMap::new();
        session.extend_ground_with_derivations(&arena, &ground, &no_derivations);
        let first = session.lazy_clause_batches(&mut arena);
        let equality_instance = first[0].urgent[0];
        let disequality_instance = first[1].urgent[0];
        let equality_certificate = first[0].instance_certificates[&equality_instance].clone();
        let disequality_certificate = first[1].instance_certificates[&disequality_instance].clone();
        let mut derivations = HashMap::new();
        derivations.insert(
            equality_instance,
            QuantifierGroundDerivation::Instance(equality_certificate),
        );
        derivations.insert(
            disequality_instance,
            QuantifierGroundDerivation::Instance(disequality_certificate),
        );
        ground.extend([equality_instance, disequality_instance]);
        session.extend_ground_with_derivations(&arena, &ground, &derivations);
        let second = session.lazy_clause_batches(&mut arena);
        let certificate = second[2].propagations[0].clone();
        assert_eq!(certificate.derived_reasons.len(), 2);
        assert!(matches!(
            certificate.derived_reasons.as_slice(),
            [
                QuantifierGroundDerivation::Instance(_),
                QuantifierGroundDerivation::Instance(_)
            ]
        ));
        assert!(check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &certificate
        ));

        let mut reordered = certificate.clone();
        reordered.derived_reasons.reverse();
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &reordered
        ));

        let mut missing = certificate.clone();
        missing.derived_reasons.pop();
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &missing
        ));

        let mut duplicate = certificate.clone();
        duplicate
            .derived_reasons
            .push(duplicate.derived_reasons[1].clone());
        duplicate
            .derived_reasons
            .sort_by_key(QuantifierGroundDerivation::conclusion);
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &duplicate
        ));

        let mut unused = certificate.clone();
        unused
            .derived_reasons
            .push(QuantifierGroundDerivation::Instance(
                QuantifierInstanceCertificate {
                    assertion: consumer,
                    bindings: vec![a],
                    instance: certificate.source_instance,
                },
            ));
        unused
            .derived_reasons
            .sort_by_key(QuantifierGroundDerivation::conclusion);
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &unused
        ));

        let mut wrong_conclusion = certificate.clone();
        let QuantifierGroundDerivation::Instance(instance) =
            &mut wrong_conclusion.derived_reasons[0]
        else {
            unreachable!();
        };
        instance.instance = certificate.propagated_literal;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &wrong_conclusion
        ));

        let mut wrong_variant = certificate.clone();
        wrong_variant.derived_reasons[0] =
            QuantifierGroundDerivation::Propagation(Box::new(certificate.clone()));
        wrong_variant
            .derived_reasons
            .sort_by_key(QuantifierGroundDerivation::conclusion);
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &wrong_variant
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn recursive_generated_provenance_checks_three_stage_propagation() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let a = arena.bv_var("recursive_provenance_a", 8).unwrap();
        let b = arena.bv_var("recursive_provenance_b", 8).unwrap();
        let functions: Vec<FuncId> = (0..=3)
            .map(|index| {
                arena
                    .declare_fun(&format!("recursive_provenance_f_{index}"), &[sort], sort)
                    .unwrap()
            })
            .collect();
        let applications: Vec<TermId> = functions
            .iter()
            .map(|&function| arena.apply(function, &[a]).unwrap())
            .collect();
        let equalities: Vec<TermId> = applications
            .iter()
            .map(|&application| arena.eq(application, zero).unwrap())
            .collect();
        let final_disequality = arena.not(equalities[3]).unwrap();

        let x = arena.declare("recursive_provenance_x", sort).unwrap();
        let xv = arena.var(x);
        let mut universals = Vec::new();
        for pair in functions.windows(2) {
            let current = arena.apply(pair[0], &[xv]).unwrap();
            let next = arena.apply(pair[1], &[xv]).unwrap();
            let current_equality = arena.eq(current, zero).unwrap();
            let false_sibling = arena.not(current_equality).unwrap();
            let propagated = arena.eq(next, zero).unwrap();
            let body = arena.or(false_sibling, propagated).unwrap();
            universals.push(arena.forall(x, body).unwrap());
        }
        let mut assertions = vec![equalities[0], final_disequality];
        assertions.extend(universals.iter().copied());

        let mut ground = vec![equalities[0]];
        let mut derivations = HashMap::new();
        let mut session = IncrementalEmatchSession::new(&mut arena, &universals);
        let mut certificates = Vec::new();
        for stage in 0..3 {
            session.extend_ground_with_derivations(&arena, &ground, &derivations);
            let batches = session.lazy_clause_batches(&mut arena);
            let certificate = batches[stage].propagations[0].clone();
            assert_eq!(certificate.propagated_literal, equalities[stage + 1]);
            assert_eq!(certificate.derived_reasons.len(), usize::from(stage > 0));
            assert!(check_quantifier_clause_propagation(
                &mut arena,
                &assertions,
                &certificate
            ));
            let propagated = certificate.propagated_literal;
            derivations.insert(
                propagated,
                QuantifierGroundDerivation::Propagation(Box::new(certificate.clone())),
            );
            ground.push(propagated);
            certificates.push(certificate);
        }

        let second = &certificates[1];
        assert!(matches!(
            second.derived_reasons.as_slice(),
            [QuantifierGroundDerivation::Propagation(_)]
        ));
        let third = &certificates[2];
        let QuantifierGroundDerivation::Propagation(second_derivation) = &third.derived_reasons[0]
        else {
            panic!("the third stage must retain the checked second-stage implication");
        };
        assert!(matches!(
            second_derivation.derived_reasons.as_slice(),
            [QuantifierGroundDerivation::Propagation(_)]
        ));
        let mut node_limited_checker = QuantifierProvenanceChecker {
            assertions: assertions.iter().copied().collect(),
            remaining_nodes: 2,
        };
        assert!(
            !node_limited_checker.check_propagation(&mut arena, third, 0),
            "three propagation nodes must not fit a two-node replay budget"
        );

        let mut tampered = third.clone();
        tampered.derived_reasons.clear();
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));

        let mut tampered = second.clone();
        tampered
            .derived_reasons
            .push(tampered.derived_reasons[0].clone());
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));

        let mut tampered = third.clone();
        let QuantifierGroundDerivation::Propagation(second_derivation) =
            &mut tampered.derived_reasons[0]
        else {
            unreachable!();
        };
        let QuantifierGroundDerivation::Propagation(first_derivation) =
            &mut second_derivation.derived_reasons[0]
        else {
            unreachable!();
        };
        first_derivation.bindings[0] = b;
        assert!(!check_quantifier_clause_propagation(
            &mut arena,
            &assertions,
            &tampered
        ));

        ground.push(final_disequality);
        assert_eq!(
            check_auto(&mut arena, &ground, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        assert_eq!(
            prove_quantified_unsat_via_egraph(&mut arena, &assertions, &SolverConfig::default(),)
                .unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn recursive_provenance_chain_reduces_complete_instance_volume() {
        const STAGES: usize = 6;
        const FALSE_CONSTANTS: usize = 4;

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let false_term = arena.bool_const(false);
        let a = arena.bv_var("recursive_volume_a", 16).unwrap();
        let functions: Vec<FuncId> = (0..=STAGES)
            .map(|index| {
                arena
                    .declare_fun(&format!("recursive_volume_f_{index}"), &[sort], sort)
                    .unwrap()
            })
            .collect();
        let applications: Vec<TermId> = functions
            .iter()
            .map(|&function| arena.apply(function, &[a]).unwrap())
            .collect();
        let equalities: Vec<TermId> = applications
            .iter()
            .map(|&application| arena.eq(application, zero).unwrap())
            .collect();

        let x = arena.declare("recursive_volume_x", sort).unwrap();
        let xv = arena.var(x);
        let mut universals = Vec::new();
        for pair in functions.windows(2) {
            let current = arena.apply(pair[0], &[xv]).unwrap();
            let next = arena.apply(pair[1], &[xv]).unwrap();
            let current_equality = arena.eq(current, zero).unwrap();
            let mut body = arena.not(current_equality).unwrap();
            for _ in 0..FALSE_CONSTANTS {
                body = arena.or(body, false_term).unwrap();
            }
            let propagated = arena.eq(next, zero).unwrap();
            body = arena.or(body, propagated).unwrap();
            universals.push(arena.forall(x, body).unwrap());
        }
        let final_disequality = arena.not(equalities[STAGES]).unwrap();
        let mut assertions = vec![equalities[0], final_disequality];
        assertions.extend(universals.iter().copied());

        let mut retained_ground = vec![equalities[0]];
        let mut retained_derivations = HashMap::new();
        let mut complete_instances = Vec::new();
        let mut detached_literals = Vec::new();
        let mut session = IncrementalEmatchSession::new(&mut arena, &universals);
        for stage in 0..STAGES {
            session.extend_ground_with_derivations(&arena, &retained_ground, &retained_derivations);
            let batches = session.lazy_clause_batches(&mut arena);
            let certificate = batches[stage].propagations[0].clone();
            assert!(check_quantifier_clause_propagation(
                &mut arena,
                &assertions,
                &certificate
            ));
            complete_instances.push(certificate.source_instance);
            detached_literals.push(certificate.propagated_literal);
            retained_derivations.insert(
                certificate.propagated_literal,
                QuantifierGroundDerivation::Propagation(Box::new(certificate.clone())),
            );
            retained_ground.push(certificate.propagated_literal);
        }

        let mut complete_query = vec![equalities[0], final_disequality];
        complete_query.extend(complete_instances);
        let mut detached_query = vec![equalities[0], final_disequality];
        detached_query.extend(detached_literals);
        assert_eq!(
            check_auto(&mut arena, &complete_query, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        assert_eq!(
            check_auto(&mut arena, &detached_query, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        let complete_stats = axeyum_ir::TermStats::compute(&arena, &complete_query);
        let detached_stats = axeyum_ir::TermStats::compute(&arena, &detached_query);
        assert!(complete_stats.dag_nodes > detached_stats.dag_nodes);
        assert!(complete_stats.tree_nodes > detached_stats.tree_nodes * 2);
        eprintln!(
            "recursive provenance target: stages={STAGES} false_constants={FALSE_CONSTANTS} complete_dag_nodes={} detached_dag_nodes={} complete_tree_nodes={} detached_tree_nodes={}",
            complete_stats.dag_nodes,
            detached_stats.dag_nodes,
            complete_stats.tree_nodes,
            detached_stats.tree_nodes,
        );

        let mut fresh_arena = arena.clone();
        let mut fresh_loop_stats = QuantifierLoopStats::default();
        let fresh_started = Instant::now();
        let fresh_result = prove_quantified_unsat_via_egraph_impl(
            &mut fresh_arena,
            &assertions,
            &SolverConfig::default(),
            false,
            false,
            &mut fresh_loop_stats,
        )
        .unwrap();
        let fresh_elapsed = fresh_started.elapsed();
        let mut online_arena = arena.clone();
        let mut online_loop_stats = QuantifierLoopStats::default();
        let online_started = Instant::now();
        let online_result = prove_quantified_unsat_via_egraph_impl(
            &mut online_arena,
            &assertions,
            &SolverConfig::default(),
            true,
            true,
            &mut online_loop_stats,
        )
        .unwrap();
        let online_elapsed = online_started.elapsed();
        assert_eq!(fresh_result, CheckResult::Unsat);
        assert_eq!(online_result, fresh_result);
        assert!(online_loop_stats.online_solves > 0);
        assert!(online_loop_stats.online_clauses > 0);
        assert!(
            online_loop_stats.qf_checks < fresh_loop_stats.qf_checks,
            "retained clauses must eliminate at least one complete QF rebuild"
        );
        eprintln!(
            "online quantifier target: fresh_qf_checks={} online_qf_checks={} online_solves={} online_clauses={} fresh_us={} online_us={}",
            fresh_loop_stats.qf_checks,
            online_loop_stats.qf_checks,
            online_loop_stats.online_solves,
            online_loop_stats.online_clauses,
            fresh_elapsed.as_micros(),
            online_elapsed.as_micros(),
        );
        assert_eq!(
            prove_quantified_unsat_via_egraph(&mut arena, &assertions, &SolverConfig::default(),)
                .unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    fn recursive_provenance_rejects_over_depth_chain() {
        const STAGES: usize = MAX_QUANTIFIER_PROVENANCE_DEPTH + 2;

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let zero = arena.bv_const(8, 0).unwrap();
        let a = arena.bv_var("recursive_depth_a", 8).unwrap();
        let functions: Vec<FuncId> = (0..=STAGES)
            .map(|index| {
                arena
                    .declare_fun(&format!("recursive_depth_f_{index}"), &[sort], sort)
                    .unwrap()
            })
            .collect();
        let initial_application = arena.apply(functions[0], &[a]).unwrap();
        let initial = arena.eq(initial_application, zero).unwrap();
        let x = arena.declare("recursive_depth_x", sort).unwrap();
        let xv = arena.var(x);
        let mut universals = Vec::new();
        for pair in functions.windows(2) {
            let current = arena.apply(pair[0], &[xv]).unwrap();
            let next = arena.apply(pair[1], &[xv]).unwrap();
            let current_equality = arena.eq(current, zero).unwrap();
            let false_sibling = arena.not(current_equality).unwrap();
            let propagated = arena.eq(next, zero).unwrap();
            let body = arena.or(false_sibling, propagated).unwrap();
            universals.push(arena.forall(x, body).unwrap());
        }
        let mut assertions = vec![initial];
        assertions.extend(universals.iter().copied());
        let mut ground = vec![initial];
        let mut derivations = HashMap::new();
        let mut session = IncrementalEmatchSession::new(&mut arena, &universals);

        for stage in 0..STAGES {
            session.extend_ground_with_derivations(&arena, &ground, &derivations);
            let batches = session.lazy_clause_batches(&mut arena);
            let certificate = batches[stage].propagations[0].clone();
            assert_eq!(
                check_quantifier_clause_propagation(&mut arena, &assertions, &certificate),
                stage <= MAX_QUANTIFIER_PROVENANCE_DEPTH,
                "the first rejected certificate must exceed the documented depth cap"
            );
            derivations.insert(
                certificate.propagated_literal,
                QuantifierGroundDerivation::Propagation(Box::new(certificate.clone())),
            );
            ground.push(certificate.propagated_literal);
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn checked_detached_units_reduce_qf_term_volume() {
        const MATCHES: usize = 128;
        const FALSE_SIBLINGS: usize = 6;

        let mut arena = TermArena::new();
        let sort = Sort::BitVec(16);
        let zero = arena.bv_const(16, 0).unwrap();
        let one = arena.bv_const(16, 1).unwrap();
        let f = arena.declare_fun("detach_bench_f", &[sort], sort).unwrap();
        let h = arena.declare_fun("detach_bench_h", &[sort], sort).unwrap();
        let siblings: Vec<FuncId> = (0..FALSE_SIBLINGS)
            .map(|index| {
                arena
                    .declare_fun(&format!("detach_bench_g_{index}"), &[sort], sort)
                    .unwrap()
            })
            .collect();
        let p = arena.bool_var("detach_bench_p").unwrap();
        let mut ground = Vec::new();
        let mut first_target = None;
        for index in 0..MATCHES {
            let argument = arena
                .bv_var(&format!("detach_bench_a_{index}"), 16)
                .unwrap();
            let fa = arena.apply(f, &[argument]).unwrap();
            let fa_eq_zero = arena.eq(fa, zero).unwrap();
            ground.push(fa_eq_zero);
            for &sibling in &siblings {
                let application = arena.apply(sibling, &[argument]).unwrap();
                ground.push(arena.eq(application, zero).unwrap());
            }
            let ha = arena.apply(h, &[argument]).unwrap();
            let ha_eq_zero = arena.eq(ha, zero).unwrap();
            ground.push(arena.not(ha_eq_zero).unwrap());
            if index == 0 {
                let target = arena.eq(ha, one).unwrap();
                first_target = Some(target);
                let not_target = arena.not(target).unwrap();
                ground.push(arena.or(not_target, p).unwrap());
                ground.push(arena.not(p).unwrap());
            }
        }

        let x = arena.declare("detach_bench_x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let fx_eq_zero = arena.eq(fx, zero).unwrap();
        let mut body = arena.not(fx_eq_zero).unwrap();
        for &sibling in &siblings {
            let application = arena.apply(sibling, &[xv]).unwrap();
            let equality = arena.eq(application, zero).unwrap();
            let false_literal = arena.not(equality).unwrap();
            body = arena.or(body, false_literal).unwrap();
        }
        let hx = arena.apply(h, &[xv]).unwrap();
        let target = arena.eq(hx, one).unwrap();
        body = arena.or(body, target).unwrap();
        let forall = arena.forall(x, body).unwrap();
        let mut assertions = ground.clone();
        assertions.push(forall);

        let eager_total_started = Instant::now();
        let eager = instantiate_forall_via_egraph(&mut arena, &ground, forall);
        assert_eq!(eager.len(), MATCHES);
        let mut eager_query = ground.clone();
        eager_query.extend(eager.iter().copied());
        let eager_stats = axeyum_ir::TermStats::compute(&arena, &eager_query);
        let eager_qf_started = Instant::now();
        assert_eq!(
            check_auto(&mut arena, &eager_query, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        let eager_qf_elapsed = eager_qf_started.elapsed();
        let eager_total_elapsed = eager_total_started.elapsed();

        let detached_total_started = Instant::now();
        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall]);
        session.extend_ground(&arena, &ground);
        let batch = session.lazy_clause_batches(&mut arena).remove(0);
        assert!(batch.urgent.is_empty());
        assert!(batch.deferred.is_empty());
        assert_eq!(batch.propagations.len(), MATCHES);
        assert!(check_quantifier_clause_propagations(
            &mut arena,
            &assertions,
            &batch.propagations
        ));
        let detached: Vec<TermId> = batch
            .propagations
            .iter()
            .map(|certificate| certificate.propagated_literal)
            .collect();
        assert!(detached.contains(&first_target.unwrap()));
        let mut detached_query = ground;
        detached_query.extend(detached);
        let detached_stats = axeyum_ir::TermStats::compute(&arena, &detached_query);
        let detached_qf_started = Instant::now();
        assert_eq!(
            check_auto(&mut arena, &detached_query, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat
        );
        let detached_qf_elapsed = detached_qf_started.elapsed();
        let detached_total_elapsed = detached_total_started.elapsed();

        assert!(eager_stats.tree_nodes > detached_stats.tree_nodes * 2);
        assert!(eager_stats.dag_nodes > detached_stats.dag_nodes);
        eprintln!(
            "detached quantifier target: matches={MATCHES} false_siblings={FALSE_SIBLINGS} eager_dag_nodes={} detached_dag_nodes={} eager_tree_nodes={} detached_tree_nodes={} eager_qf_us={} detached_qf_us={} eager_total_us={} detached_total_us={}",
            eager_stats.dag_nodes,
            detached_stats.dag_nodes,
            eager_stats.tree_nodes,
            detached_stats.tree_nodes,
            eager_qf_elapsed.as_micros(),
            detached_qf_elapsed.as_micros(),
            eager_total_elapsed.as_micros(),
            detached_total_elapsed.as_micros()
        );
        assert_eq!(
            prove_quantified_unsat_via_egraph(&mut arena, &assertions, &SolverConfig::default())
                .unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    fn lazy_clause_classification_is_conservative() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let ground_f_is_zero = arena.eq(fa, zero).unwrap();
        let ground_f_not_zero = arena.not(ground_f_is_zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let gx = arena.apply(g, &[xv]).unwrap();
        let quantified_f_is_zero = arena.eq(fx, zero).unwrap();
        let quantified_g_is_one = arena.eq(gx, one).unwrap();
        let clause = arena.or(quantified_f_is_zero, quantified_g_is_one).unwrap();
        let forall_clause = arena.forall(x, clause).unwrap();

        let unit = lazy_clause_instances(&mut arena, &[ground_f_not_zero], forall_clause);
        assert_eq!(unit.urgent.len(), 1, "false or unknown is unit-like");
        assert!(unit.deferred.is_empty());

        let fa_plus_one = arena.bv_add(fa, one).unwrap();
        let mention = arena.eq(fa_plus_one, zero).unwrap();
        let unresolved = lazy_clause_instances(&mut arena, &[mention], forall_clause);
        assert!(unresolved.urgent.is_empty());
        assert_eq!(unresolved.deferred.len(), 1, "two unknown literals defer");

        let conjunction = arena
            .and(quantified_f_is_zero, quantified_g_is_one)
            .unwrap();
        let forall_non_clause = arena.forall(x, conjunction).unwrap();
        let non_clause = lazy_clause_instances(&mut arena, &[mention], forall_non_clause);
        assert!(non_clause.urgent.is_empty());
        assert_eq!(
            non_clause.deferred.len(),
            1,
            "unsupported shapes retain legacy reach"
        );
    }

    #[test]
    fn lazy_clause_truth_uses_ground_congruence() {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let a_eq_b = arena.eq(a, b).unwrap();
        let asserted_value = arena.eq(fa, zero).unwrap();
        let congruent_value = arena.eq(fb, zero).unwrap();
        let mut facts = GroundEqualityContext::new(&arena, &[a_eq_b, asserted_value]);
        assert_eq!(
            evaluate_equality_clause(&arena, congruent_value, &mut facts),
            Some(ClauseValue::True),
            "f(a)=0 and a=b must justify f(b)=0 by congruence"
        );
    }

    #[test]
    fn instantiates_over_ground_applications() {
        let (mut arena, forall, [a, b], c, ground0, f, _x) = setup();
        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);

        // Expect (= (f a) c) and (= (f b) c).
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let want_a = arena.eq(fa, c).unwrap();
        let want_b = arena.eq(fb, c).unwrap();
        assert!(instances.contains(&want_a), "instance for a missing");
        assert!(instances.contains(&want_b), "instance for b missing");
        assert_eq!(instances.len(), 2);
    }

    #[test]
    fn witness_tuples_expose_the_matched_witnesses() {
        // The witness-tuple variant returns the binder→ground-term tuples (in
        // binder order) the e-matching selects: here `[a]` and `[b]` for the two
        // f-applications. This is what the Alethe quantifier emitter consumes.
        let (mut arena, forall, [a, b], _c, ground0, _f, _x) = setup();
        let (vars, _body, tuples) =
            witness_tuples_via_egraph(&mut arena, &[ground0], forall).expect("matches");
        assert_eq!(vars.len(), 1, "one binder");
        assert!(tuples.contains(&vec![a]), "witness a missing: {tuples:?}");
        assert!(tuples.contains(&vec![b]), "witness b missing: {tuples:?}");
        assert_eq!(tuples.len(), 2);
    }

    #[test]
    fn instantiation_is_modulo_congruence() {
        // Add a = b to the ground: f(a) and f(b) become one class, so the trigger
        // fires once and there is a single instance.
        let (mut arena, forall, [a, b], _c, ground0, _f, _x) = setup();
        let a_eq_b = arena.eq(a, b).unwrap();
        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0, a_eq_b], forall);
        assert_eq!(
            instances.len(),
            1,
            "congruent f-applications instantiate once, got {instances:?}"
        );
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn instantiates_over_a_nested_trigger() {
        // ∀x. (= (f (g x)) c), ground containing f(g(a)): instance (= (f (g a)) c).
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let ga = arena.apply(g, &[a]).unwrap();
        let fga = arena.apply(f, &[ga]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(fga, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let gx = arena.apply(g, &[xv]).unwrap();
        let fgx = arena.apply(f, &[gx]).unwrap();
        let body = arena.eq(fgx, c).unwrap();
        let forall = arena.forall(x, body).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);
        let want = arena.eq(fga, c).unwrap();
        assert_eq!(instances, vec![want], "nested trigger f(g(x)) → x = a");
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn instantiates_over_a_binary_trigger_with_a_ground_argument() {
        // ∀x. (= (h x a) c), ground containing h(b, a) and h(d, a): two instances;
        // the ground argument `a` in the trigger is matched by its class.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let d = arena.bv_var("d", 8).unwrap();
        let h = arena.declare_fun("h", &[sort, sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let hba = arena.apply(h, &[b, a]).unwrap();
        let hda = arena.apply(h, &[d, a]).unwrap();
        // A decoy h(a, b) whose ground argument is b, not a — must NOT match h(x, a).
        let hab = arena.apply(h, &[a, b]).unwrap();
        let hba_hda = arena.bv_add(hba, hda).unwrap();
        let sum = arena.bv_add(hba_hda, hab).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(sum, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let hxa = arena.apply(h, &[xv, a]).unwrap();
        let body = arena.eq(hxa, c).unwrap();
        let forall = arena.forall(x, body).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);
        let want_b = arena.eq(hba, c).unwrap();
        let want_d = arena.eq(hda, c).unwrap();
        assert!(instances.contains(&want_b));
        assert!(instances.contains(&want_d));
        assert_eq!(
            instances.len(),
            2,
            "only h(_, a) matches, got {instances:?}"
        );
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::similar_names)]
    fn instantiates_a_multi_pattern_trigger() {
        // ∀x. ∀y. (= (f x) (g y)): no single subterm covers both x and y, so the
        // multi-pattern {f(x), g(y)} is inferred and the matches joined.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let gb = arena.apply(g, &[b]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let g0 = arena.eq(fa, zero).unwrap();
        let g1 = arena.eq(gb, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let y = arena.declare("y", sort).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let fx = arena.apply(f, &[xv]).unwrap();
        let gy = arena.apply(g, &[yv]).unwrap();
        let inner_body = arena.eq(fx, gy).unwrap();
        let inner = arena.forall(y, inner_body).unwrap();
        let forall = arena.forall(x, inner).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[g0, g1], forall);
        let want = arena.eq(fa, gb).unwrap();
        assert_eq!(instances, vec![want], "x↦a, y↦b joined from {{f(x), g(y)}}");
    }

    #[test]
    #[allow(clippy::similar_names, clippy::many_single_char_names)]
    fn nested_trigger_fires_through_congruence_involution() {
        // The canonical congruence-only test: ∀x. f(f(x)) = x with ground
        //   f(a) = b,  f(b) = c,  a ≠ c.
        // The trigger f(f(x)) has NO syntactic match — there is no literal
        // `f(f(·))` ground term. It fires only because f(a)=b puts f(a) inside b's
        // class, so the outer ground f(b) has an inner f-application (f(a)) in its
        // argument class ⇒ x ↦ a. The instance f(f(a)) = a forces c = a ⨯ a ≠ c.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let fa_eq_b = arena.eq(fa, b).unwrap();
        let fb_eq_c = arena.eq(fb, c).unwrap();
        let a_ne_c = {
            let e = arena.eq(a, c).unwrap();
            arena.not(e).unwrap()
        };

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let ffx = arena.apply(f, &[fx]).unwrap();
        let body = arena.eq(ffx, xv).unwrap();
        let forall = arena.forall(x, body).unwrap();

        let result = prove_quantified_unsat_via_egraph(
            &mut arena,
            &[fa_eq_b, fb_eq_c, a_ne_c, forall],
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            result,
            CheckResult::Unsat,
            "nested trigger must fire via congruence and refute"
        );
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn instantiation_loop_refutes_a_quantified_contradiction() {
        // f(a) ≠ 0  ∧  ∀x. (= (f x) 0): instantiating x = a gives f(a) = 0,
        // contradicting the ground disequality → UNSAT.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let fa_eq_0 = arena.eq(fa, zero).unwrap();
        let fa_ne_0 = arena.not(fa_eq_0).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let fx_eq_0 = arena.eq(fx, zero).unwrap();
        let forall = arena.forall(x, fx_eq_0).unwrap();

        let result = prove_quantified_unsat_via_egraph(
            &mut arena,
            &[fa_ne_0, forall],
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(result, CheckResult::Unsat);
    }

    #[test]
    #[allow(clippy::similar_names, clippy::many_single_char_names)]
    fn instantiation_loop_refutes_across_multiple_rounds() {
        // A genuinely multi-round refutation: the g(x) trigger can only fire after
        // the f(x) instantiation has introduced g(a) into the ground set.
        //   ground:    f(a) ≠ 0
        //   ∀x. f(x) = g(x)   → round 1: f(a) = g(a)  (introduces ground g(a))
        //   ∀x. g(x) = 0      → round 2: g(a) = 0     (now g(a) exists to match)
        //   ⇒ f(a) = g(a) = 0 contradicts f(a) ≠ 0   → UNSAT (round 3 check)
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fa_ne_0 = {
            let e = arena.eq(fa, zero).unwrap();
            arena.not(e).unwrap()
        };

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let gx = arena.apply(g, &[xv]).unwrap();
        let fx_eq_gx = arena.eq(fx, gx).unwrap();
        let forall_fg = arena.forall(x, fx_eq_gx).unwrap();
        let gx_eq_0 = arena.eq(gx, zero).unwrap();
        let forall_g0 = arena.forall(x, gx_eq_0).unwrap();

        let mut retained_ground = vec![fa_ne_0];
        let mut session = IncrementalEmatchSession::new(&mut arena, &[forall_fg, forall_g0]);
        session.extend_ground(&arena, &retained_ground);
        let first_round = session.lazy_clause_batches(&mut arena);
        assert_eq!(first_round[0].urgent.len(), 1);
        assert!(first_round[1].urgent.is_empty());
        let first_pattern_executions = session.pattern_executions;
        assert_eq!(first_pattern_executions, session.patterns.len());
        let first_instance = first_round[0].urgent[0];
        retained_ground.push(first_instance);
        let first_node_count = session.bridge.egraph.len();

        session.extend_ground(&arena, &retained_ground);
        assert_eq!(session.merge_invalidations, 1);
        assert_eq!(session.dirty_patterns.len(), 0);
        assert_eq!(
            session.candidate_patterns.len(),
            1,
            "only the newly added g-root pattern needs delta matching"
        );
        let second_round = session.lazy_clause_batches(&mut arena);
        assert_eq!(
            session.pattern_executions - first_pattern_executions,
            1,
            "the unrelated retained f-root cache remains valid modulo roots"
        );
        assert_eq!(second_round[1].urgent.len(), 1);
        let second_instance = second_round[1].urgent[0];
        retained_ground.push(second_instance);
        assert_eq!(
            session.extensions, 2,
            "only appended ground extends the bridge"
        );
        assert_eq!(session.match_rounds, 2);
        assert!(
            session.bridge.egraph.len() > first_node_count,
            "the retained bridge must gain the newly introduced g(a) term"
        );
        assert_eq!(
            check_auto(&mut arena, &retained_ground, &SolverConfig::default()).unwrap(),
            CheckResult::Unsat,
            "retained-round source instances must independently replay"
        );

        let result = prove_quantified_unsat_via_egraph(
            &mut arena,
            &[fa_ne_0, forall_fg, forall_g0],
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            result,
            CheckResult::Unsat,
            "multi-round chaining should refute"
        );
    }

    #[test]
    fn instantiation_loop_passes_through_quantifier_free() {
        // No universals: routes straight to check_auto (here, sat).
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a_eq_1 = arena.eq(a, one).unwrap();
        let result =
            prove_quantified_unsat_via_egraph(&mut arena, &[a_eq_1], &SolverConfig::default())
                .unwrap();
        assert!(matches!(result, CheckResult::Sat(_)));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn instantiates_a_two_variable_quantifier() {
        // ∀x. ∀y. (= (g x y) c), ground containing g(a, b): instance (= (g a b) c).
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let g = arena.declare_fun("g", &[sort, sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let gab = arena.apply(g, &[a, b]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(gab, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let y = arena.declare("y", sort).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let gxy = arena.apply(g, &[xv, yv]).unwrap();
        let inner_body = arena.eq(gxy, c).unwrap();
        let inner = arena.forall(y, inner_body).unwrap();
        let forall = arena.forall(x, inner).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);
        let want = arena.eq(gab, c).unwrap();
        assert_eq!(instances, vec![want], "x↦a, y↦b from the g(x,y) trigger");
    }

    fn euclidean_clock_universal(
        arena: &mut TermArena,
        modulus: i128,
        upper: i128,
        extra_disjunct: bool,
    ) -> TermId {
        let t = arena.int_var("t").unwrap();
        let s = arena.declare("s", Sort::Int).unwrap();
        let m = arena.declare("m", Sort::Int).unwrap();
        let sv = arena.var(s);
        let mv = arena.var(m);
        let k = arena.int_const(modulus);
        let km = arena.int_mul(k, mv).unwrap();
        let sum = arena.int_add(km, sv).unwrap();
        let recomposes = arena.eq(sum, t).unwrap();
        let not_recomposes = arena.not(recomposes).unwrap();
        let zero = arena.int_const(0);
        let below_range = arena.int_lt(sv, zero).unwrap();
        let upper = arena.int_const(upper);
        let above_range = arena.int_ge(sv, upper).unwrap();
        let bounds = arena.or(below_range, above_range).unwrap();
        let mut body = arena.or(not_recomposes, bounds).unwrap();
        if extra_disjunct {
            let truth = arena.bool_const(true);
            body = arena.or(body, truth).unwrap();
        }
        let inner = arena.forall(m, body).unwrap();
        arena.forall(s, inner).unwrap()
    }

    #[test]
    fn euclidean_residue_instantiation_refutes_clock_rows() {
        for modulus in [3, 10] {
            let mut arena = TermArena::new();
            let forall = euclidean_clock_universal(&mut arena, modulus, modulus, false);
            assert!(
                euclidean_residue_instance(&mut arena, forall)
                    .unwrap()
                    .is_some(),
                "the exact modulus-{modulus} residue partition must instantiate"
            );
            let result =
                prove_quantified_unsat_via_egraph(&mut arena, &[forall], &SolverConfig::default())
                    .unwrap();
            assert_eq!(
                result,
                CheckResult::Unsat,
                "div/mod symbolic counterexample must refute the modulus-{modulus} row"
            );
        }
    }

    #[test]
    fn euclidean_residue_instantiation_declines_non_partition_shapes() {
        let mut arena = TermArena::new();
        let narrowed = euclidean_clock_universal(&mut arena, 3, 2, false);
        assert!(
            euclidean_residue_instance(&mut arena, narrowed)
                .unwrap()
                .is_none(),
            "a different upper guard is not the exact Euclidean residue partition"
        );
        assert_ne!(
            prove_quantified_unsat_via_egraph(&mut arena, &[narrowed], &SolverConfig::default(),)
                .unwrap(),
            CheckResult::Unsat,
            "a satisfiable narrowed-residue universal must not be refuted"
        );

        let mut arena = TermArena::new();
        let weakened = euclidean_clock_universal(&mut arena, 3, 3, true);
        assert!(
            euclidean_residue_instance(&mut arena, weakened)
                .unwrap()
                .is_none(),
            "an extra disjunct must decline instead of changing the theorem"
        );
        assert_ne!(
            prove_quantified_unsat_via_egraph(&mut arena, &[weakened], &SolverConfig::default(),)
                .unwrap(),
            CheckResult::Unsat,
            "the valid extra-true-disjunct universal must not be refuted"
        );
    }

    #[test]
    fn nested_xor_instantiation_refutes_issue4433() {
        let mut script = axeyum_smtlib::parse_script(include_str!(
            "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__issue4433-nqe.smt2"
        ))
        .unwrap();
        let assertion = script.assertions[0];
        let instance = nested_xor_discriminator_instance(&mut script.arena, assertion)
            .unwrap()
            .expect("exact nested-XOR shape must produce a hierarchical instance");
        assert_eq!(
            check_auto(&mut script.arena, &[instance], &SolverConfig::default()).unwrap(),
            CheckResult::Unsat,
            "the derived off-pivot selector equality must be contradictory"
        );
        assert_eq!(
            prove_quantified_unsat_via_egraph(
                &mut script.arena,
                &[assertion],
                &SolverConfig::default(),
            )
            .unwrap(),
            CheckResult::Unsat
        );
    }

    #[test]
    fn nested_xor_instantiation_declines_near_misses() {
        let shapes = [
            "(set-logic LIA) (assert (forall ((a Int) (b Int)) \
             (xor (xor (= a 0) (= b 0)) (forall ((c Int)) \
             (= (ite (= a 0) 0 0) (ite (= c 0) 0 0)))))) (check-sat)",
            "(set-logic LIA) (assert (forall ((a Int) (b Int)) \
             (xor (or (= a 0) (= b 0)) (forall ((c Int)) \
             (= (ite (= a 0) 0 1) (ite (= c 0) 0 1)))))) (check-sat)",
            "(set-logic LIA) (assert (forall ((a Int) (b Int)) \
             (xor (xor (= a 0) (= b 0)) (forall ((c Int)) \
             (and (= (ite (= a 0) 0 1) (ite (= c 0) 0 1)) true))))) (check-sat)",
        ];
        for text in shapes {
            let mut script = axeyum_smtlib::parse_script(text).unwrap();
            let assertion = script.assertions[0];
            assert!(
                nested_xor_discriminator_instance(&mut script.arena, assertion)
                    .unwrap()
                    .is_none(),
                "near-miss structure must not use ADR-0099: {text}"
            );
        }

        for text in [
            "(set-logic LIA) (assert (not (forall ((a Int) (b Int)) \
             (xor (xor (= a 0) (= b 0)) (forall ((c Int)) \
             (= (ite (= a 0) 0 1) (ite (= c 0) 0 1))))))) (check-sat)",
            "(set-logic LIA) (assert (forall ((a Int) (b Int)) \
             (or true (xor (xor (= a 0) (= b 0)) (forall ((c Int)) \
             (= (ite (= a 0) 0 1) (ite (= c 0) 0 1))))))) (check-sat)",
        ] {
            let mut script = axeyum_smtlib::parse_script(text).unwrap();
            let assertions = script.assertions.clone();
            let result = crate::solve(&mut script.arena, &assertions, &SolverConfig::default());
            assert!(
                !matches!(result, Ok(CheckResult::Unsat)),
                "satisfiable polarity/context near miss must not be refuted: {text}"
            );
        }
    }

    #[test]
    fn affine_growth_instantiation_refutes_repair_const_nterm() {
        let mut script = axeyum_smtlib::parse_script(include_str!(
            "../../../corpus/public-curated/quantified/LIA/cvc5-regress-clean/cli__regress1__quantifiers__repair-const-nterm.smt2"
        ))
        .unwrap();
        let assertion = script.assertions[0];
        let instances = affine_growth_instances(&mut script.arena, assertion)
            .unwrap()
            .expect("exact affine-growth shape must instantiate");
        assert_eq!(instances.len(), 2);
        assert_eq!(
            prove_quantified_unsat_via_egraph(
                &mut script.arena,
                &[assertion],
                &SolverConfig::default(),
            )
            .unwrap(),
            CheckResult::Unsat,
            "two consecutive symbolic counterexamples must refute the target"
        );
    }

    #[test]
    fn affine_growth_instantiation_declines_near_misses() {
        for text in [
            "(set-logic LIA) (declare-fun p () Int) (declare-fun a () Int) \
             (declare-fun b () Int) (assert (forall ((x Int)) \
             (not (>= (- (* 0 x) (ite (= x p) a b)) 1)))) (check-sat)",
            "(set-logic LIA) (declare-fun p () Int) (declare-fun a () Int) \
             (assert (forall ((x Int)) \
             (not (>= (- (* 3 x) (ite (= x p) a x)) 1)))) (check-sat)",
            "(set-logic LIA) (declare-fun p () Int) (declare-fun a () Int) \
             (declare-fun b () Int) (assert (forall ((x Int)) \
             (or (not (>= (- (* 3 x) (ite (= x p) a b)) 1)) true))) (check-sat)",
        ] {
            let mut script = axeyum_smtlib::parse_script(text).unwrap();
            let assertion = script.assertions[0];
            assert!(
                affine_growth_instances(&mut script.arena, assertion)
                    .unwrap()
                    .is_none()
            );
        }
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn closed_universal_with_no_trigger_is_refuted() {
        // The measured qbv-simp shape: ∀A B C D. (A=B ∧ C=D) ∨ (A=C ∧ B=D).
        // status unsat — the universal is *false* (A=0,B=1,C=0,D=0 falsifies it),
        // but its body has no function-application trigger, so the e-matching loop
        // alone returns `unknown`. Closed-universal falsification decides it.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let mk = |arena: &mut TermArena, n: &str| {
            let s = arena.declare(n, sort).unwrap();
            (s, arena.var(s))
        };
        let (a, av) = mk(&mut arena, "A");
        let (b, bv) = mk(&mut arena, "B");
        let (c, cv) = mk(&mut arena, "C");
        let (d, dv) = mk(&mut arena, "D");
        let ab = arena.eq(av, bv).unwrap();
        let cd = arena.eq(cv, dv).unwrap();
        let ac = arena.eq(av, cv).unwrap();
        let bd = arena.eq(bv, dv).unwrap();
        let left = arena.and(ab, cd).unwrap();
        let right = arena.and(ac, bd).unwrap();
        let body = arena.or(left, right).unwrap();
        // Bind innermost-first so the peeled prefix is [A, B, C, D].
        let mut forall = arena.forall(d, body).unwrap();
        forall = arena.forall(c, forall).unwrap();
        forall = arena.forall(b, forall).unwrap();
        forall = arena.forall(a, forall).unwrap();

        let result =
            prove_quantified_unsat_via_egraph(&mut arena, &[forall], &SolverConfig::default())
                .unwrap();
        assert_eq!(
            result,
            CheckResult::Unsat,
            "a false closed universal with no trigger must be refuted"
        );
    }

    #[test]
    fn valid_closed_universal_is_not_refuted() {
        // ∀x. (x = x): valid (true), must NOT be reported unsat. The falsification
        // sub-check `¬(x=x)` is unsat, so the lever declines and the loop reaches
        // its own (non-unsat) verdict.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let body = arena.eq(xv, xv).unwrap();
        let forall = arena.forall(x, body).unwrap();
        let result =
            prove_quantified_unsat_via_egraph(&mut arena, &[forall], &SolverConfig::default())
                .unwrap();
        assert_ne!(
            result,
            CheckResult::Unsat,
            "a valid closed universal must never be refuted"
        );
    }

    /// Builds the census `∀A B C D. (A=B ∧ C=D) ∨ (A=C ∧ B=D)` closed universal —
    /// a **false** sentence (A=0,B=1,C=0,D=0 falsifies it) that the closed-universal
    /// lever refutes when it is *positively* asserted. Returns the arena and the
    /// forall term, so the polarity tests can embed it in a Boolean context where
    /// refuting it would be **unsound**.
    #[allow(clippy::many_single_char_names)]
    fn false_closed_universal() -> (TermArena, TermId) {
        let mut arena = TermArena::new();
        // A narrow width so the front door's finite-domain expansion
        // (`check_with_quantifiers`, complete for `BitVec`) decides the nested-
        // polarity shapes end-to-end rather than falling through to the e-matching
        // fallback (which cannot bit-blast a residual quantifier).
        let sort = Sort::BitVec(4);
        let mk = |arena: &mut TermArena, n: &str| {
            let s = arena.declare(n, sort).unwrap();
            (s, arena.var(s))
        };
        let (a, av) = mk(&mut arena, "A");
        let (b, bv) = mk(&mut arena, "B");
        let (c, cv) = mk(&mut arena, "C");
        let (d, dv) = mk(&mut arena, "D");
        let ab = arena.eq(av, bv).unwrap();
        let cd = arena.eq(cv, dv).unwrap();
        let ac = arena.eq(av, cv).unwrap();
        let bd = arena.eq(bv, dv).unwrap();
        let left = arena.and(ab, cd).unwrap();
        let right = arena.and(ac, bd).unwrap();
        let body = arena.or(left, right).unwrap();
        // Innermost-first, so the peeled prefix is [A, B, C, D].
        let mut forall = arena.forall(d, body).unwrap();
        forall = arena.forall(c, forall).unwrap();
        forall = arena.forall(b, forall).unwrap();
        forall = arena.forall(a, forall).unwrap();
        (arena, forall)
    }

    /// DEBT 3 polarity guard — the closed-universal falsification lever must fire
    /// ONLY on a **top-level positively-asserted** universal. Here the lever's owner
    /// [`prove_quantified_unsat_via_egraph`] is handed a false `∀` buried under a
    /// top-level `or` (an `Op::Or` node, never in the `foralls` bucket): it must
    /// never forge an `unsat`, whatever the ground solver makes of the disjunction.
    /// (`(or (false ∀) …)` is TRUE, so an `unsat` would be unsound.)
    fn lever_never_forges_unsat(assertion: TermId, arena: &mut TermArena) {
        // The lever's owner: proves the lever itself never fires on the wrong
        // polarity. A ground solver that declines the embedded quantifier surfaces as
        // `Err(Unsupported)` — which is NOT an `unsat`, so the property holds.
        let via_lever =
            prove_quantified_unsat_via_egraph(arena, &[assertion], &SolverConfig::default());
        assert!(
            !matches!(via_lever, Ok(CheckResult::Unsat)),
            "closed-universal lever forged an unsat on a non-top-level universal: {via_lever:?}",
        );
    }

    #[test]
    fn forall_under_or_with_true_branch_is_not_refuted() {
        let (mut arena, forall) = false_closed_universal();
        let tru = arena.bool_const(true);
        let disj = arena.or(forall, tru).unwrap();
        // The lever must not forge an unsat.
        lever_never_forges_unsat(disj, &mut arena);
        // End-to-end: the real front door decides it correctly — `(or ∀ true)` is
        // TRUE, so `sat` (via finite BV expansion), never `unsat`.
        let end_to_end = crate::solve(&mut arena, &[disj], &SolverConfig::default()).unwrap();
        assert!(
            matches!(end_to_end, CheckResult::Sat(_)),
            "(or (false ∀) true) is TRUE — solve must return sat, got {end_to_end:?}",
        );
    }

    #[test]
    fn forall_under_or_with_sat_ground_branch_is_not_refuted() {
        let (mut arena, forall) = false_closed_universal();
        let p = arena.bool_var("p_free").unwrap(); // a free Boolean: can be true
        let disj = arena.or(forall, p).unwrap();
        lever_never_forges_unsat(disj, &mut arena);
        let end_to_end = crate::solve(&mut arena, &[disj], &SolverConfig::default()).unwrap();
        assert!(
            matches!(end_to_end, CheckResult::Sat(_)),
            "(or (false ∀) p) is satisfiable (p=true) — got {end_to_end:?}",
        );
    }

    /// DEBT 3 polarity guard: `¬(∀x⃗. body)` with a **false** body-universal is
    /// `∃x⃗. ¬body`, which is TRUE — so the assertion is satisfiable and must NOT be
    /// `unsat`. Refuting the *inner* positive `∀` (the wrong polarity) would forge an
    /// unsat here; the `not` node is not an `Op::Forall`, so the lever never fires.
    #[test]
    fn negated_false_universal_is_not_refuted() {
        let (mut arena, forall) = false_closed_universal();
        let neg = arena.not(forall).unwrap();
        lever_never_forges_unsat(neg, &mut arena);
        let end_to_end = crate::solve(&mut arena, &[neg], &SolverConfig::default()).unwrap();
        assert!(
            matches!(end_to_end, CheckResult::Sat(_)),
            "¬(false ∀) = ∃¬body is TRUE — solve must return sat, got {end_to_end:?}",
        );
    }

    /// DEBT 3 polarity guard: a false closed `∀` in the **then** branch of an `ite`
    /// whose condition can select the (true) **else** branch must NOT be `unsat`.
    #[test]
    fn forall_inside_ite_then_branch_is_not_refuted() {
        let (mut arena, forall) = false_closed_universal();
        let cond = arena.bool_var("c_free").unwrap();
        let tru = arena.bool_const(true);
        // (ite c (false ∀) true): choosing c=false yields the true else branch.
        let ite = arena.ite(cond, forall, tru).unwrap();
        lever_never_forges_unsat(ite, &mut arena);
        let end_to_end = crate::solve(&mut arena, &[ite], &SolverConfig::default()).unwrap();
        assert!(
            matches!(end_to_end, CheckResult::Sat(_)),
            "(ite c (false ∀) true) is satisfiable (c=false) — got {end_to_end:?}",
        );
    }

    /// Control: the same false closed universal asserted **positively** at top level
    /// IS refuted (by the lever), confirming the polarity tests above are non-vacuous
    /// — the universal really is false, so only its *positive* top-level assertion is
    /// unsat.
    #[test]
    fn positive_false_universal_control_is_refuted() {
        let (mut arena, forall) = false_closed_universal();
        let end_to_end = crate::solve(&mut arena, &[forall], &SolverConfig::default()).unwrap();
        assert_eq!(
            end_to_end,
            CheckResult::Unsat,
            "the positively-asserted false closed universal must be unsat (control)",
        );
    }

    #[test]
    fn open_universal_is_not_treated_as_closed() {
        // ∀x. (f x) = c has a free function symbol `f` — it is NOT a closed
        // sentence, so `body_is_closed_qf` rejects it and the falsification lever
        // does not fire (the e-matching path owns it).
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let body = arena.eq(fx, c).unwrap();
        let bound: HashSet<SymbolId> = std::iter::once(x).collect();
        assert!(
            !body_is_closed_qf(&arena, body, &bound),
            "a body mentioning a free function symbol is not closed"
        );
    }

    #[test]
    fn non_forall_or_no_trigger_yields_nothing() {
        let mut arena = TermArena::new();
        let p = arena.bool_var("p").unwrap();
        // Not a forall.
        assert!(instantiate_forall_via_egraph(&mut arena, &[p], p).is_empty());
        // A forall whose body has no unary trigger over the bound variable.
        let x = arena.declare("x", Sort::Bool).unwrap();
        let xv = arena.var(x);
        let body = arena.or(xv, p).unwrap();
        let forall = arena.forall(x, body).unwrap();
        assert!(instantiate_forall_via_egraph(&mut arena, &[p], forall).is_empty());
    }
}
