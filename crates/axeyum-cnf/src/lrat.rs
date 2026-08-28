//! An independent LRAT (clausal, hint-based) UNSAT-proof checker and a
//! DRAT→LRAT elaborator (Track 3, phase P3.1).
//!
//! Where [`crate::check_drat`] *searches* for a unit-propagation refutation of
//! each added clause, an LRAT proof carries the refutation explicitly: every
//! clause gets a numeric ID, and each addition lists the antecedent clause IDs
//! whose unit propagation drives the contradiction. The checker therefore does
//! **no search** — it just follows the hints — which makes it small, total, and
//! auditable. This is the trusted component that discharges `unsat`.
//!
//! This slice supports **RUP-only** proofs (positive hints). RAT additions
//! (negative hints) are out of scope, both in the checker and the elaborator;
//! an elaborator input that would require RAT is rejected.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Duration;

// Monotonic clock: on wasm32 the browser has no `std` clock, so use `web-time`'s
// drop-in `Instant`, exactly like `crate::proof_sat` / `crate::drat` (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use crate::drat::{DratStep, literal_from_dimacs, sorted};
use crate::{CnfFormula, CnfLit};

/// One step of an LRAT proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LratStep {
    /// Add clause `id` (strictly greater than every prior id), justified by RUP
    /// over the antecedent clauses named in `hints` (positive ids only).
    Add {
        /// Numeric id of the new clause.
        id: u64,
        /// The clause literals.
        clause: Vec<CnfLit>,
        /// Antecedent clause ids, in unit-propagation order, ending with the
        /// conflicting clause.
        hints: Vec<u64>,
    },
    /// Delete the clauses with these ids from the active set.
    Delete {
        /// Clause ids to remove.
        ids: Vec<u64>,
    },
}

/// Error from LRAT checking, elaboration, or parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LratError {
    /// An addition's hints did not produce a conflict — the step is invalid.
    StepNotVerified {
        /// Id of the failing addition.
        id: u64,
    },
    /// A hint referenced an active clause that was not unit (or was already
    /// satisfied) under the running assignment.
    BadHint {
        /// Id of the addition whose hint chain is malformed.
        id: u64,
    },
    /// A hint referenced a clause id not present in the active set.
    UnknownClause {
        /// The missing clause id.
        id: u64,
    },
    /// The proof text could not be parsed.
    Parse(String),
    /// The DRAT proof handed to [`elaborate_drat_to_lrat_backward`] does not
    /// itself check: this step is neither RUP nor RAT. There is nothing to
    /// elaborate.
    DratStepNotVerified {
        /// Zero-based index of the failing DRAT step.
        step: usize,
    },
    /// A DRAT step the refutation depends on is RAT rather than RUP, and
    /// [`LratStep`] has no room for the pivot and negative hint blocks a RAT
    /// addition needs (ADR-0382). The proof is fine; this elaborator cannot
    /// express it.
    RatNotSupported {
        /// Zero-based index of the RAT step.
        step: usize,
    },
    /// An antecedent chain recovered from the backward checker could not be
    /// replayed under this module's own semantics, so no hints were emitted for
    /// it. A guard on an internal invariant, never a statement about the input
    /// proof.
    HintChainFailed {
        /// Zero-based index of the DRAT step whose chain failed.
        step: usize,
    },
}

impl core::fmt::Display for LratError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LratError::StepNotVerified { id } => {
                write!(f, "LRAT addition {id} is not verified by its hints")
            }
            LratError::BadHint { id } => {
                write!(f, "LRAT addition {id} has a hint that is not a unit clause")
            }
            LratError::UnknownClause { id } => {
                write!(f, "LRAT hint references unknown clause {id}")
            }
            LratError::Parse(what) => write!(f, "LRAT parse error: {what}"),
            LratError::DratStepNotVerified { step } => {
                write!(f, "DRAT step {step} is neither RUP nor RAT")
            }
            LratError::RatNotSupported { step } => write!(
                f,
                "DRAT step {step} is RAT, which an LRAT step cannot express"
            ),
            LratError::HintChainFailed { step } => {
                write!(
                    f,
                    "no LRAT hint chain could be emitted for DRAT step {step}"
                )
            }
        }
    }
}

impl core::error::Error for LratError {}

/// Tri-valued status of a clause under a partial assignment, used by the
/// hint-following verifier.
enum ClauseStatus {
    /// At least one literal is true: the clause is satisfied.
    Satisfied,
    /// Every literal is false: the clause is a conflict.
    Conflict,
    /// Exactly one literal is unassigned (all others false): unit on that
    /// literal.
    Unit(CnfLit),
    /// Two or more literals are unassigned.
    Unresolved,
}

/// Classifies `clause` under `assign` (map from variable index to the value
/// that variable currently holds).
fn classify(clause: &[CnfLit], assign: &BTreeMap<usize, bool>) -> ClauseStatus {
    let mut unassigned: Option<CnfLit> = None;
    let mut unassigned_count = 0usize;
    for &lit in clause {
        if let Some(&value) = assign.get(&lit.var().index()) {
            // `lit` is true iff its assigned value disagrees with its negation
            // flag.
            if value != lit.is_negated() {
                return ClauseStatus::Satisfied;
            }
        } else {
            unassigned_count += 1;
            unassigned = Some(lit);
        }
    }
    match unassigned_count {
        0 => ClauseStatus::Conflict,
        1 => ClauseStatus::Unit(unassigned.expect("one unassigned literal")),
        _ => ClauseStatus::Unresolved,
    }
}

/// Seeds `assign` so every literal of `clause` is false. Returns `false` if the
/// clause is a tautology (contains a literal and its negation), which makes its
/// negation immediately contradictory — the step is then trivially verified.
fn assign_clause_false(clause: &[CnfLit], assign: &mut BTreeMap<usize, bool>) -> bool {
    for &lit in clause {
        // Value that makes `lit` false.
        let falsifying = lit.is_negated();
        match assign.get(&lit.var().index()) {
            Some(&prev) if prev != falsifying => return false,
            _ => {
                assign.insert(lit.var().index(), falsifying);
            }
        }
    }
    true
}

/// Verifies one addition by following its hint chain (no search).
///
/// Assigns every literal of `clause` false, then walks `hints` left-to-right:
/// every hint but the last must be unit (propagate its lone literal false), and
/// the last must be falsified (a conflict). Any deviation is a rejection.
fn verify_addition(
    active: &BTreeMap<u64, Vec<CnfLit>>,
    id: u64,
    clause: &[CnfLit],
    hints: &[u64],
) -> Result<(), LratError> {
    let mut assign: BTreeMap<usize, bool> = BTreeMap::new();
    if !assign_clause_false(clause, &mut assign) {
        // Tautological clause: its negation is contradictory, trivially RUP.
        return Ok(());
    }
    for (position, &hint_id) in hints.iter().enumerate() {
        let hinted = active
            .get(&hint_id)
            .ok_or(LratError::UnknownClause { id: hint_id })?;
        let is_last = position + 1 == hints.len();
        match classify(hinted, &assign) {
            ClauseStatus::Conflict => {
                if is_last {
                    return Ok(());
                }
                // A conflict before the chain ends is still a valid refutation,
                // but the proof claimed more steps; reject as malformed so the
                // emitted hints must be exact.
                return Err(LratError::StepNotVerified { id });
            }
            ClauseStatus::Unit(lit) => {
                if is_last {
                    // The final hint must be a conflict, not merely unit.
                    return Err(LratError::StepNotVerified { id });
                }
                // Unit propagation: assign so `lit` becomes true.
                assign.insert(lit.var().index(), !lit.is_negated());
            }
            ClauseStatus::Satisfied | ClauseStatus::Unresolved => {
                return Err(LratError::BadHint { id });
            }
        }
    }
    // The chain ended without reaching a conflict (e.g. empty hints).
    Err(LratError::StepNotVerified { id })
}

/// Verifies `proof` against `formula`.
///
/// The formula's clauses are assigned ids `1..=n` in order. Returns `Ok(true)`
/// when every step verifies and the empty clause is derived (UNSAT confirmed),
/// `Ok(false)` when every step verifies but the empty clause is never derived,
/// and `Err` when a step fails.
///
/// # Errors
///
/// Returns [`LratError::StepNotVerified`], [`LratError::BadHint`], or
/// [`LratError::UnknownClause`] for an addition whose hints do not produce a
/// conflict.
pub fn check_lrat(formula: &CnfFormula, proof: &[LratStep]) -> Result<bool, LratError> {
    let mut active: BTreeMap<u64, Vec<CnfLit>> = BTreeMap::new();
    for (index, clause) in formula.clauses().iter().enumerate() {
        let id = u64::try_from(index + 1).map_err(|_| {
            LratError::Parse(format!("formula clause index {index} does not fit in u64"))
        })?;
        active.insert(id, clause.lits().to_vec());
    }
    let mut derived_empty = false;

    for step in proof {
        match step {
            LratStep::Delete { ids } => {
                for id in ids {
                    active.remove(id);
                }
            }
            LratStep::Add { id, clause, hints } => {
                verify_addition(&active, *id, clause, hints)?;
                if clause.is_empty() {
                    derived_empty = true;
                }
                active.insert(*id, clause.clone());
            }
        }
    }
    Ok(derived_empty)
}

/// Serializes an LRAT proof to the standard textual format.
///
/// An addition is `<id> <lit ...> 0 <hintid ...> 0`; a deletion is
/// `<id> d <delid ...> 0`, where the leading id is a running step id. The
/// output round-trips through [`parse_lrat`].
pub fn write_lrat(proof: &[LratStep]) -> String {
    let mut out = String::new();
    // The deletion line carries a leading step id. LRAT conventionally reuses
    // the most recent clause id; here a monotone counter suffices and is
    // ignored on parse.
    let mut step_id: u64 = 0;
    for step in proof {
        match step {
            LratStep::Add { id, clause, hints } => {
                step_id = *id;
                out.push_str(&id.to_string());
                out.push(' ');
                for lit in clause {
                    out.push_str(&lit.dimacs().to_string());
                    out.push(' ');
                }
                out.push_str("0 ");
                for hint in hints {
                    out.push_str(&hint.to_string());
                    out.push(' ');
                }
                out.push_str("0\n");
            }
            LratStep::Delete { ids } => {
                out.push_str(&step_id.to_string());
                out.push_str(" d ");
                for id in ids {
                    out.push_str(&id.to_string());
                    out.push(' ');
                }
                out.push_str("0\n");
            }
        }
    }
    out
}

/// Parses an LRAT proof in the standard textual format.
///
/// Each non-comment line begins with a step id. A `d` after the id marks a
/// deletion line (`<id> d <delid ...> 0`); otherwise it is an addition
/// (`<id> <lit ...> 0 <hintid ...> 0`). The leading id of a deletion line is
/// ignored.
///
/// # Errors
///
/// Returns [`LratError::Parse`] for a malformed token, a missing terminator, or
/// an out-of-range variable.
pub fn parse_lrat(text: &str) -> Result<Vec<LratStep>, LratError> {
    let mut steps = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        let mut tokens = line.split_whitespace();
        let id_token = tokens
            .next()
            .ok_or_else(|| LratError::Parse("empty LRAT line".to_owned()))?;
        let id: u64 = id_token
            .parse()
            .map_err(|_| LratError::Parse(format!("invalid step id `{id_token}`")))?;
        let rest: Vec<&str> = tokens.collect();
        if rest.first() == Some(&"d") {
            // Deletion: `<id> d <delid ...> 0`.
            let mut ids = Vec::new();
            for token in &rest[1..] {
                let value: u64 = token
                    .parse()
                    .map_err(|_| LratError::Parse(format!("invalid clause id `{token}`")))?;
                if value == 0 {
                    break;
                }
                ids.push(value);
            }
            steps.push(LratStep::Delete { ids });
            continue;
        }

        // Addition: literals up to the first `0`, then hints up to the second
        // `0`.
        let mut clause = Vec::new();
        let mut iter = rest.iter();
        let mut saw_clause_terminator = false;
        for token in iter.by_ref() {
            let value: i64 = token
                .parse()
                .map_err(|_| LratError::Parse(format!("invalid literal `{token}`")))?;
            if value == 0 {
                saw_clause_terminator = true;
                break;
            }
            clause.push(
                literal_from_dimacs(value).map_err(|error| LratError::Parse(error.to_string()))?,
            );
        }
        if !saw_clause_terminator {
            return Err(LratError::Parse(format!(
                "LRAT addition {id} missing clause terminator 0"
            )));
        }
        let mut hints = Vec::new();
        let mut saw_hint_terminator = false;
        for token in iter {
            let value: u64 = token
                .parse()
                .map_err(|_| LratError::Parse(format!("invalid hint id `{token}`")))?;
            if value == 0 {
                saw_hint_terminator = true;
                break;
            }
            hints.push(value);
        }
        if !saw_hint_terminator {
            return Err(LratError::Parse(format!(
                "LRAT addition {id} missing hint terminator 0"
            )));
        }
        steps.push(LratStep::Add { id, clause, hints });
    }
    Ok(steps)
}

/// Re-derives an addition's RUP refutation over `active`, returning the
/// antecedent ids in propagation order, ending with the conflicting clause id.
///
/// Mirrors the unit-propagation of [`crate::check_drat`]'s `is_rup`, but records
/// which active clause caused each unit assignment and the final conflict. The
/// returned id list, fed back as hints, is exactly what [`check_lrat`] needs.
///
/// Returns `None` when the clause is not RUP (would need RAT). A tautological
/// clause is RUP with an empty hint chain handled by the caller.
fn rup_hints(active: &BTreeMap<u64, Vec<CnfLit>>, clause: &[CnfLit]) -> Option<Vec<u64>> {
    struct Propagation {
        clause_id: u64,
        dependencies: Vec<usize>,
    }

    fn needed_hints(
        propagations: &[Propagation],
        conflict_id: u64,
        conflict_dependencies: impl IntoIterator<Item = usize>,
    ) -> Vec<u64> {
        let mut needed = BTreeSet::new();
        let mut stack = conflict_dependencies.into_iter().collect::<Vec<_>>();
        while let Some(index) = stack.pop() {
            if needed.insert(index) {
                stack.extend(propagations[index].dependencies.iter().copied());
            }
        }
        let mut hints = propagations
            .iter()
            .enumerate()
            .filter(|(index, _)| needed.contains(index))
            .map(|(_, propagation)| propagation.clause_id)
            .collect::<Vec<_>>();
        hints.push(conflict_id);
        hints
    }

    let mut assign: BTreeMap<usize, bool> = BTreeMap::new();
    if !assign_clause_false(clause, &mut assign) {
        // Tautology: trivially refuted with no antecedents.
        return Some(Vec::new());
    }
    let mut reason_for_variable = BTreeMap::<usize, usize>::new();
    let mut propagations = Vec::<Propagation>::new();
    loop {
        let mut changed = false;
        for (&id, candidate) in active {
            match classify(candidate, &assign) {
                ClauseStatus::Conflict => {
                    let dependencies = candidate.iter().filter_map(|literal| {
                        reason_for_variable.get(&literal.var().index()).copied()
                    });
                    return Some(needed_hints(&propagations, id, dependencies));
                }
                ClauseStatus::Unit(lit) => {
                    let variable = lit.var().index();
                    let dependencies = candidate
                        .iter()
                        .filter(|literal| literal.var().index() != variable)
                        .filter_map(|literal| {
                            reason_for_variable.get(&literal.var().index()).copied()
                        })
                        .collect::<BTreeSet<_>>()
                        .into_iter()
                        .collect();
                    // Unit propagation: assign so `lit` becomes true.
                    assign.insert(variable, !lit.is_negated());
                    let index = propagations.len();
                    propagations.push(Propagation {
                        clause_id: id,
                        dependencies,
                    });
                    reason_for_variable.insert(variable, index);
                    changed = true;
                }
                ClauseStatus::Satisfied | ClauseStatus::Unresolved => {}
            }
        }
        if !changed {
            return None;
        }
    }
}

/// Elaborates a RUP-only DRAT proof into an LRAT proof with explicit hints.
///
/// The formula's clauses take ids `1..=n`; new clauses take ids from `n+1`.
/// Each [`DratStep::Add`] is re-checked by reverse unit propagation, recording
/// the antecedent ids in propagation order; the resulting [`LratStep`] sequence
/// is guaranteed to pass [`check_lrat`]. Each [`DratStep::Delete`] maps to a
/// deletion of the matching active id.
///
/// # Errors
///
/// Returns [`LratError::StepNotVerified`] when an addition is not RUP (RAT
/// elaboration is out of scope for this slice).
pub fn elaborate_drat_to_lrat(
    formula: &CnfFormula,
    drat: &[DratStep],
) -> Result<Vec<LratStep>, LratError> {
    let mut active: BTreeMap<u64, Vec<CnfLit>> = BTreeMap::new();
    for (index, clause) in formula.clauses().iter().enumerate() {
        let id = u64::try_from(index + 1).map_err(|_| {
            LratError::Parse(format!("formula clause index {index} does not fit in u64"))
        })?;
        active.insert(id, clause.lits().to_vec());
    }
    let mut next_id = u64::try_from(formula.clauses().len() + 1)
        .map_err(|_| LratError::Parse("formula clause count does not fit in u64".to_owned()))?;
    let mut out = Vec::new();

    for step in drat {
        match step {
            DratStep::Add(clause) => {
                let hints =
                    rup_hints(&active, clause).ok_or(LratError::StepNotVerified { id: next_id })?;
                out.push(LratStep::Add {
                    id: next_id,
                    clause: clause.clone(),
                    hints,
                });
                active.insert(next_id, clause.clone());
                next_id += 1;
            }
            DratStep::Delete(clause) => {
                if let Some(id) = find_active_id(&active, clause) {
                    out.push(LratStep::Delete { ids: vec![id] });
                    active.remove(&id);
                }
            }
        }
    }
    Ok(out)
}

// --- Observability and bounding for elaboration -----------------------------
//
// Same motivation and design as the checking-side hooks in `crate::drat`
// (`DratCheckProgress` / `check_drat_with_limits_and_progress`), and the
// search-side ones in `crate::proof_sat` (`ProofSearchProgress`): elaboration
// re-derives every addition's RUP hints by the same rescan-to-fixpoint
// propagation `check_drat` uses (see `elaborate_drat_to_lrat`'s doc), so on a
// large proof it is at least as expensive as checking and had exactly the same
// blind spot — no deadline, no step budget, no progress. [`elaborate_drat_to_lrat`]
// above is UNTOUCHED: the bounded engine below reuses the same `rup_hints` /
// `find_active_id` free functions and the same per-step logic, so a difference
// in behaviour between the two would be a diff in this file, not a hidden
// divergence.

/// How many processed steps elapse between wall-clock deadline reads. Smaller
/// than `crate::drat`'s analogous (private) check-side interval on purpose:
/// `rup_hints` rescans the whole active set to a fixpoint per call, so a single
/// elaboration step is typically far more expensive than a single DRAT check
/// step, and a coarser cadence would let the deadline overshoot by more wall
/// time per check.
const LRAT_ELABORATE_DEADLINE_INTERVAL: usize = 64;

/// A point-in-time, cumulative-since-start snapshot of a bounded
/// [`elaborate_drat_to_lrat_with_limits_and_progress`] run, handed to an
/// optional callback so a long-running elaboration is observable. Every field
/// is a running total, not a delta.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct LratElaborateProgress {
    /// DRAT steps (additions and deletions) processed so far.
    pub steps_processed: usize,
    /// Total steps in the input DRAT proof (always known: `drat` is a slice).
    pub steps_total: usize,
    /// Clauses in the live (post-deletion) active set right now.
    pub active_clauses: usize,
    /// LRAT steps emitted so far (one per DRAT addition; deletions that hit an
    /// already-absent clause emit nothing, so this can be slightly less than
    /// `steps_processed`).
    pub lrat_steps_emitted: usize,
    /// Wall-clock time since this elaboration began.
    pub elapsed: Duration,
}

/// Outcome of a bounded, progress-observed elaboration
/// ([`elaborate_drat_to_lrat_with_limits_and_progress`]).
///
/// [`LratElaborateOutcome::Elaborated`] carries exactly what
/// [`elaborate_drat_to_lrat`] returns on success. The two bounded variants are
/// **undecided** results, deliberately distinct: a run that hit its deadline or
/// step budget has not elaborated the whole proof, and its partial `out` is
/// discarded rather than returned as if it were complete — an incomplete
/// elaboration must never be handed to [`check_lrat`] and reported as a
/// checked certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LratElaborateOutcome {
    /// Every DRAT step elaborated; see [`elaborate_drat_to_lrat`] for what the
    /// `Vec<LratStep>` means.
    Elaborated(Vec<LratStep>),
    /// The step budget (`max_steps`) was exhausted before every step was
    /// processed. Not a complete elaboration.
    ResourceOut,
    /// The wall-clock deadline passed before every step was processed. Not a
    /// complete elaboration.
    Interrupted,
}

/// Reports one [`LratElaborateProgress`] snapshot to `progress`, if installed.
/// A no-op — one `is_none` check, nothing else — when `progress` is `None`.
fn report_lrat_elaborate_progress(
    progress: &mut Option<&mut dyn FnMut(&LratElaborateProgress)>,
    steps_processed: usize,
    steps_total: usize,
    active_clauses: usize,
    lrat_steps_emitted: usize,
    elapsed: Duration,
) {
    let Some(sink) = progress.as_mut() else {
        return;
    };
    sink(&LratElaborateProgress {
        steps_processed,
        steps_total,
        active_clauses,
        lrat_steps_emitted,
        elapsed,
    });
}

/// Like [`elaborate_drat_to_lrat`], but bounded by an optional wall-clock
/// `deadline` and an optional step budget `max_steps`, and optionally observed
/// by a `progress` sink polled every `progress_interval` processed steps (and
/// once more at the end, whichever way the run finishes).
///
/// This reuses the private `rup_hints` and `find_active_id` exactly as
/// [`elaborate_drat_to_lrat`] does — the same hint-recovery logic, called the
/// same way — so installing a deadline, a step budget, or a progress sink
/// cannot change what hints are computed, only whether/when the run gives up
/// early (see `tests::bounding_and_progress_do_not_change_the_output`).
///
/// # Errors
///
/// Returns [`LratError::StepNotVerified`] when an addition reached before a
/// bound fires is not RUP (RAT elaboration remains out of scope, exactly as in
/// [`elaborate_drat_to_lrat`]), or the same [`LratError::Parse`] this function's
/// unbounded counterpart can return for an id overflow.
pub fn elaborate_drat_to_lrat_with_limits_and_progress(
    formula: &CnfFormula,
    drat: &[DratStep],
    deadline: Option<Instant>,
    max_steps: Option<usize>,
    progress_interval: usize,
    mut progress: Option<&mut dyn FnMut(&LratElaborateProgress)>,
) -> Result<LratElaborateOutcome, LratError> {
    let progress_interval = progress_interval.max(1);
    let start = Instant::now();
    let steps_total = drat.len();
    let mut active: BTreeMap<u64, Vec<CnfLit>> = BTreeMap::new();
    for (index, clause) in formula.clauses().iter().enumerate() {
        let id = u64::try_from(index + 1).map_err(|_| {
            LratError::Parse(format!("formula clause index {index} does not fit in u64"))
        })?;
        active.insert(id, clause.lits().to_vec());
    }
    let mut next_id = u64::try_from(formula.clauses().len() + 1)
        .map_err(|_| LratError::Parse("formula clause count does not fit in u64".to_owned()))?;
    let mut out = Vec::new();
    let mut steps_processed: usize = 0;

    for step in drat {
        if let Some(limit) = max_steps
            && steps_processed >= limit
        {
            report_lrat_elaborate_progress(
                &mut progress,
                steps_processed,
                steps_total,
                active.len(),
                out.len(),
                start.elapsed(),
            );
            return Ok(LratElaborateOutcome::ResourceOut);
        }
        if let Some(deadline) = deadline
            && steps_processed.is_multiple_of(LRAT_ELABORATE_DEADLINE_INTERVAL)
            && Instant::now() >= deadline
        {
            report_lrat_elaborate_progress(
                &mut progress,
                steps_processed,
                steps_total,
                active.len(),
                out.len(),
                start.elapsed(),
            );
            return Ok(LratElaborateOutcome::Interrupted);
        }
        match step {
            DratStep::Add(clause) => {
                let hints =
                    rup_hints(&active, clause).ok_or(LratError::StepNotVerified { id: next_id })?;
                out.push(LratStep::Add {
                    id: next_id,
                    clause: clause.clone(),
                    hints,
                });
                active.insert(next_id, clause.clone());
                next_id += 1;
            }
            DratStep::Delete(clause) => {
                if let Some(id) = find_active_id(&active, clause) {
                    out.push(LratStep::Delete { ids: vec![id] });
                    active.remove(&id);
                }
            }
        }
        steps_processed += 1;
        if progress.is_some() && steps_processed.is_multiple_of(progress_interval) {
            report_lrat_elaborate_progress(
                &mut progress,
                steps_processed,
                steps_total,
                active.len(),
                out.len(),
                start.elapsed(),
            );
        }
    }
    report_lrat_elaborate_progress(
        &mut progress,
        steps_processed,
        steps_total,
        active.len(),
        out.len(),
        start.elapsed(),
    );
    Ok(LratElaborateOutcome::Elaborated(out))
}

/// Elaborates the *core* of a DRAT proof into LRAT, using the backward checker
/// as the engine (ADR-0382).
///
/// [`elaborate_drat_to_lrat`] re-derives every addition's hints with the same
/// rescan-to-fixpoint propagation [`crate::check_drat`] uses, for every line of
/// the proof. This one runs [`crate::check_drat_backward`] once and reads the
/// antecedents straight off the walk, so it does the work only for the lemmas
/// the refutation depends on, with watched-literal propagation. The output is
/// therefore also *trimmed*: it contains the core lemmas and nothing else.
///
/// Two differences from [`elaborate_drat_to_lrat`] a caller has to know about:
///
/// - **No deletion steps are emitted.** The active set only grows, which is safe
///   for a hint-checked proof — a RUP step names its antecedents, so extra
///   clauses cannot invalidate it — and it keeps the emitted ids independent of
///   the input's deletion structure. The cost is memory in [`check_lrat`].
/// - **RAT is refused, not approximated.** [`LratStep`] carries a flat list of
///   positive hints, which cannot express a RAT addition's pivot and per-
///   candidate hint blocks. A core lemma that is RAT rather than RUP produces
///   [`LratError::RatNotSupported`], naming the step. Proofs from this
///   workspace's own CDCL core are RUP-only, so this is a boundary rather than
///   a limitation in practice — but it is a hard boundary, because the
///   alternative is emitting a hint chain that does not justify its clause.
///
/// A proof with no empty-clause addition elaborates to the empty LRAT proof, on
/// which [`check_lrat`] reports `Ok(false)` — the same verdict
/// [`crate::check_drat_backward`] gives it.
///
/// # Errors
///
/// Returns [`LratError::DratStepNotVerified`] when the input proof's refutation
/// does not check, [`LratError::RatNotSupported`] when a core lemma is RAT, and
/// [`LratError::HintChainFailed`] if an internal invariant on the recovered
/// chains fails (no output is emitted in that case).
pub fn elaborate_drat_to_lrat_backward(
    formula: &CnfFormula,
    drat: &[DratStep],
) -> Result<Vec<LratStep>, LratError> {
    crate::drat_backward::elaborate_backward(formula, drat)
}

/// The outcome of certifying a DRAT refutation by way of LRAT (ADR-0613).
///
/// See [`certify_unsat_via_lrat`] for the trust argument. The two variants are
/// deliberately asymmetric: `Certified` is a positive claim about `formula`,
/// `Declined` is a claim about nothing at all.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LratCertifyOutcome {
    /// `formula` is unsatisfiable. These LRAT steps were emitted by the backward
    /// engine and **accepted by [`check_lrat`]**, which followed their hints and
    /// reached the empty clause. The verdict rests on [`check_lrat`] alone.
    Certified(Vec<LratStep>),
    /// This route declined. **Nothing is claimed about `formula`, and nothing is
    /// claimed about the input proof**: a decline is not a rejection. A caller
    /// that needs a verdict must fall back to another checker; a caller that
    /// reports "the proof is bad" from a decline is reporting a fact it does not
    /// have.
    Declined(LratDecline),
}

/// Why [`certify_unsat_via_lrat`] declined.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LratDecline {
    /// A core lemma is a RAT addition, which [`LratStep`] cannot express
    /// (ADR-0382). The proof may be perfectly good; this format cannot hint it.
    RatStep {
        /// Zero-based index of the RAT step.
        step: usize,
    },
    /// The backward engine found a core lemma that is neither RUP nor RAT, so
    /// there was nothing to elaborate.
    DratNotVerified {
        /// Zero-based index of the failing step.
        step: usize,
    },
    /// An internal invariant on the recovered hint chains failed and no hints
    /// were emitted. A guard on this crate, never a statement about the input.
    HintChainFailed {
        /// Zero-based index of the step whose chain failed.
        step: usize,
    },
    /// The elaborator emitted hints and [`check_lrat`] **rejected** them. The
    /// untrusted engine and the trusted checker disagree, so nothing is
    /// certified — this is the case the composition exists to catch.
    HintsRejected(LratError),
    /// Every emitted step verified, but the empty clause was never derived, so
    /// no refutation was established.
    NoEmptyClause,
}

impl core::fmt::Display for LratDecline {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            LratDecline::RatStep { step } => {
                write!(f, "DRAT step {step} is RAT; LRAT cannot express it")
            }
            LratDecline::DratNotVerified { step } => {
                write!(f, "DRAT step {step} is neither RUP nor RAT")
            }
            LratDecline::HintChainFailed { step } => {
                write!(f, "no hint chain could be emitted for DRAT step {step}")
            }
            LratDecline::HintsRejected(error) => {
                write!(f, "the emitted LRAT was rejected by check_lrat: {error}")
            }
            LratDecline::NoEmptyClause => {
                write!(f, "the elaborated proof never derives the empty clause")
            }
        }
    }
}

/// Certifies `formula` unsatisfiable from a DRAT refutation, cheaply, **without
/// putting any trust in the machinery that makes it cheap** (ADR-0613).
///
/// This is the composition the workspace's identity sentence describes —
/// *untrusted fast search, trusted small checking* — applied to proof checking
/// itself:
///
/// 1. [`elaborate_drat_to_lrat_backward`] runs the backward core-first engine
///    (ADR-0382) over `drat` and emits the core as LRAT with explicit antecedent
///    hints. That engine is thousands of lines of watched literals, clause
///    arenas and lifetime intervals. **It is not trusted here.** It is a
///    *producer*: its only job is to guess hints.
/// 2. [`check_lrat`] then verifies those hints against `formula` directly. It
///    seeds its active set from `formula`'s own clauses, follows each addition's
///    hint chain with no search of any kind, and reports `Ok(true)` only if the
///    empty clause is derived. It is small enough to read in one sitting, which
///    is the whole basis of the trust story for `unsat`.
///
/// So a bug anywhere in step 1 produces hints that step 2 rejects, and the
/// outcome is [`LratCertifyOutcome::Declined`] rather than a wrong `unsat`.
/// **`Certified` is discharged by [`check_lrat`] alone**; the backward engine
/// contributes speed and nothing else. In particular this does *not* move the
/// trusted base from [`crate::check_drat`] to [`crate::check_drat_backward`] —
/// the backward checker never appears in accepting position.
///
/// The asymmetry to respect at the call site: `Certified` means unsatisfiable;
/// `Declined` means **this route has no opinion**. A DRAT proof that is fine but
/// uses a RAT step declines here, and so does a proof this crate mis-elaborates.
/// Neither is evidence that the proof is bad.
#[must_use]
pub fn certify_unsat_via_lrat(formula: &CnfFormula, drat: &[DratStep]) -> LratCertifyOutcome {
    let steps = match elaborate_drat_to_lrat_backward(formula, drat) {
        Ok(steps) => steps,
        Err(LratError::RatNotSupported { step }) => {
            return LratCertifyOutcome::Declined(LratDecline::RatStep { step });
        }
        Err(LratError::DratStepNotVerified { step }) => {
            return LratCertifyOutcome::Declined(LratDecline::DratNotVerified { step });
        }
        Err(LratError::HintChainFailed { step }) => {
            return LratCertifyOutcome::Declined(LratDecline::HintChainFailed { step });
        }
        Err(other) => {
            return LratCertifyOutcome::Declined(LratDecline::HintsRejected(other));
        }
    };
    match check_lrat(formula, &steps) {
        Ok(true) => LratCertifyOutcome::Certified(steps),
        Ok(false) => LratCertifyOutcome::Declined(LratDecline::NoEmptyClause),
        Err(error) => LratCertifyOutcome::Declined(LratDecline::HintsRejected(error)),
    }
}

/// Finds the active id whose clause equals `clause` as a set.
fn find_active_id(active: &BTreeMap<u64, Vec<CnfLit>>, clause: &[CnfLit]) -> Option<u64> {
    let target = sorted(clause);
    active
        .iter()
        .find(|(_, candidate)| sorted(candidate) == target)
        .map(|(&id, _)| id)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::{
        LratError, LratStep, check_lrat, elaborate_drat_to_lrat, parse_lrat, rup_hints, write_lrat,
    };
    use crate::{
        CnfClause, CnfFormula, CnfLit, CnfVar, ProofSolveOutcome, check_drat, solve_with_drat_proof,
    };

    fn lit(value: i64) -> CnfLit {
        let var = CnfVar::new(usize::try_from(value.unsigned_abs() - 1).unwrap()).unwrap();
        if value < 0 {
            CnfLit::positive(var).negated()
        } else {
            CnfLit::positive(var)
        }
    }

    fn formula(variable_count: usize, clauses: &[&[i64]]) -> CnfFormula {
        let mut f = CnfFormula::new(variable_count);
        for clause in clauses {
            f.add_clause(CnfClause::new(clause.iter().map(|&v| lit(v)).collect()))
                .unwrap();
        }
        f
    }

    fn drat_of_unsat(f: &CnfFormula) -> Vec<crate::DratStep> {
        match solve_with_drat_proof(f) {
            ProofSolveOutcome::Unsat(proof) => {
                assert_eq!(check_drat(f, &proof), Ok(true), "DRAT proof must verify");
                proof
            }
            other => panic!("expected unsat, got {other:?}"),
        }
    }

    #[test]
    fn rup_hint_elaboration_trims_irrelevant_unit_propagations() {
        // Proving (z): under ¬z, unit b and (¬b ∨ z) conflict. Unit a is
        // encountered first but does not participate in that implication graph.
        let active = BTreeMap::from([
            (1, vec![lit(1)]),
            (2, vec![lit(2)]),
            (3, vec![lit(-2), lit(3)]),
        ]);
        assert_eq!(rup_hints(&active, &[lit(3)]), Some(vec![2, 3]));
    }

    #[test]
    fn lrat_roundtrip_parse_write() {
        let proof = vec![
            LratStep::Add {
                id: 5,
                clause: vec![lit(1), lit(-2)],
                hints: vec![1, 3, 4],
            },
            LratStep::Delete { ids: vec![1, 3] },
            LratStep::Add {
                id: 6,
                clause: vec![],
                hints: vec![5, 2],
            },
        ];
        assert_eq!(parse_lrat(&write_lrat(&proof)).unwrap(), proof);
    }

    #[test]
    fn lrat_checks_an_elaborated_drat_proof() {
        let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
        let drat = drat_of_unsat(&f);
        let lrat = elaborate_drat_to_lrat(&f, &drat).unwrap();
        assert_eq!(check_lrat(&f, &lrat), Ok(true));
        // Survives a text round-trip and still checks.
        let reparsed = parse_lrat(&write_lrat(&lrat)).unwrap();
        assert_eq!(reparsed, lrat);
        assert_eq!(check_lrat(&f, &reparsed), Ok(true));
    }

    #[test]
    fn check_lrat_rejects_a_corrupted_hint() {
        let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
        let drat = drat_of_unsat(&f);
        let mut lrat = elaborate_drat_to_lrat(&f, &drat).unwrap();
        // Drop the last hint from the first addition: the chain can no longer
        // reach a conflict.
        let corrupted = lrat
            .iter_mut()
            .find_map(|step| match step {
                LratStep::Add { hints, .. } if !hints.is_empty() => Some(hints),
                _ => None,
            })
            .expect("at least one addition with hints");
        corrupted.pop();
        let verdict = check_lrat(&f, &lrat);
        assert_ne!(verdict, Ok(true), "corrupted hint must not be accepted");
        assert!(
            matches!(
                verdict,
                Err(LratError::StepNotVerified { .. } | LratError::BadHint { .. })
            ) || verdict == Ok(false),
            "got {verdict:?}"
        );
    }

    #[test]
    fn check_lrat_rejects_a_bogus_clause() {
        // A satisfiable formula: no addition is genuinely entailed.
        let f = formula(2, &[&[1, 2]]);
        // Assert a fresh non-entailed unit with an arbitrary (real) hint.
        let proof = vec![LratStep::Add {
            id: 2,
            clause: vec![lit(1)],
            hints: vec![1],
        }];
        let verdict = check_lrat(&f, &proof);
        assert_ne!(verdict, Ok(true), "bogus clause must not be accepted");
        assert!(verdict.is_err(), "got {verdict:?}");
    }

    #[test]
    fn check_lrat_unsat_only_when_empty_clause() {
        // (x), (¬x): the unit (x) under no assignment... build a real chain that
        // derives a non-empty learned clause but never the empty one.
        let f = formula(2, &[&[1, 2], &[1, -2]]);
        // Derive (1): assign 1 false, then clauses 1 and 2 both become unit on 2
        // and ¬2 — a conflict. Hints: clause 1 makes 2, clause 2 conflicts.
        let proof = vec![LratStep::Add {
            id: 3,
            clause: vec![lit(1)],
            hints: vec![1, 2],
        }];
        assert_eq!(check_lrat(&f, &proof), Ok(false));
    }

    #[test]
    fn elaborated_lrat_matches_drat_verdict() {
        let cases = [
            formula(1, &[&[1], &[-1]]),
            formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]),
            formula(
                6,
                &[
                    &[1, 2],
                    &[3, 4],
                    &[5, 6],
                    &[-1, -3],
                    &[-1, -5],
                    &[-3, -5],
                    &[-2, -4],
                    &[-2, -6],
                    &[-4, -6],
                ],
            ),
        ];
        for f in &cases {
            let drat = drat_of_unsat(f);
            assert_eq!(check_drat(f, &drat), Ok(true));
            let lrat = elaborate_drat_to_lrat(f, &drat).unwrap();
            assert_eq!(check_lrat(f, &lrat), Ok(true));
        }
    }

    /// Differential fuzz: for many random UNSAT CNFs, the CDCL core's DRAT proof
    /// must elaborate to an LRAT proof that the (search-free) LRAT checker
    /// accepts, and the elaborated proof must survive a text round-trip.
    #[test]
    fn random_unsat_drat_proofs_elaborate_and_check() {
        let mut state = 0x0bad_c0de_dead_beefu64;
        let mut next = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        let below = |n: &mut dyn FnMut() -> u64, bound: u64| usize::try_from(n() % bound).unwrap();
        let mut checked = 0u32;
        for _ in 0..600 {
            let vars = 3 + below(&mut next, 4); // 3..=6 variables
            let clause_count = 4 + below(&mut next, 16);
            let mut f = CnfFormula::new(vars);
            let vars_bound = u64::try_from(vars).unwrap();
            for _ in 0..clause_count {
                let width = 1 + below(&mut next, 3);
                let mut lits = Vec::new();
                for _ in 0..width {
                    let v = i64::try_from(next() % vars_bound).unwrap() + 1;
                    let signed = if next() & 1 == 0 { v } else { -v };
                    lits.push(lit(signed));
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }
            // Only exercise the elaborator on genuinely UNSAT instances.
            let ProofSolveOutcome::Unsat(drat) = solve_with_drat_proof(&f) else {
                continue;
            };
            assert_eq!(check_drat(&f, &drat), Ok(true), "DRAT must verify");
            let lrat = elaborate_drat_to_lrat(&f, &drat).expect("RUP proof elaborates");
            assert_eq!(check_lrat(&f, &lrat), Ok(true), "LRAT must verify UNSAT");
            let reparsed = parse_lrat(&write_lrat(&lrat)).expect("LRAT round-trips");
            assert_eq!(reparsed, lrat, "LRAT text round-trip is lossless");
            assert_eq!(check_lrat(&f, &reparsed), Ok(true));
            checked += 1;
        }
        assert!(checked >= 20, "expected many UNSAT cases, got {checked}");
    }

    // --- elaboration progress / bounding ------------------------------------

    use super::{
        LratElaborateOutcome, LratElaborateProgress,
        elaborate_drat_to_lrat_with_limits_and_progress,
    };
    use std::time::{Duration, Instant};

    fn unsat_2x2() -> CnfFormula {
        formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]])
    }

    /// A real search proof over `unsat_2x2()`, big enough to exercise a step
    /// budget meaningfully (at least one `Add` before the empty clause).
    fn multi_step_unsat_drat() -> (CnfFormula, Vec<crate::DratStep>) {
        let f = unsat_2x2();
        let drat = drat_of_unsat(&f);
        assert!(
            drat.len() >= 2,
            "need at least one step before the final empty clause to bound meaningfully"
        );
        (f, drat)
    }

    #[test]
    fn unbounded_matches_elaborate_drat_to_lrat() {
        let (f, drat) = multi_step_unsat_drat();
        let expected = elaborate_drat_to_lrat(&f, &drat).expect("elaboration must not error");
        let bounded =
            elaborate_drat_to_lrat_with_limits_and_progress(&f, &drat, None, None, 1, None)
                .expect("elaboration must not error");
        assert_eq!(bounded, LratElaborateOutcome::Elaborated(expected));
    }

    #[test]
    fn a_step_budget_that_is_never_reached_does_not_change_the_output() {
        let (f, drat) = multi_step_unsat_drat();
        let generous = drat.len() + 10;
        let outcome = elaborate_drat_to_lrat_with_limits_and_progress(
            &f,
            &drat,
            None,
            Some(generous),
            1,
            None,
        )
        .expect("elaboration must not error");
        let expected = elaborate_drat_to_lrat(&f, &drat).expect("elaboration must not error");
        assert_eq!(outcome, LratElaborateOutcome::Elaborated(expected));
    }

    #[test]
    fn a_step_budget_smaller_than_the_proof_yields_resource_out_never_output() {
        let (f, drat) = multi_step_unsat_drat();
        let outcome =
            elaborate_drat_to_lrat_with_limits_and_progress(&f, &drat, None, Some(1), 1, None)
                .expect("a resource bound is an outcome, not an error");
        assert_eq!(
            outcome,
            LratElaborateOutcome::ResourceOut,
            "a bounded run that ran out must never be reported as Elaborated(_) — \
             a timeout is not a pass"
        );
    }

    #[test]
    fn an_already_expired_deadline_yields_interrupted_never_output() {
        let (f, drat) = multi_step_unsat_drat();
        let expired = Instant::now()
            .checked_sub(Duration::from_secs(1))
            .expect("now is well past the epoch");
        let outcome = elaborate_drat_to_lrat_with_limits_and_progress(
            &f,
            &drat,
            Some(expired),
            None,
            1,
            None,
        )
        .expect("an expired deadline is an outcome, not an error");
        assert_eq!(
            outcome,
            LratElaborateOutcome::Interrupted,
            "an expired deadline must never be reported as Elaborated(_)"
        );
    }

    #[test]
    fn a_generous_deadline_does_not_change_the_output() {
        let (f, drat) = multi_step_unsat_drat();
        let generous = Instant::now() + Duration::from_secs(60);
        let outcome = elaborate_drat_to_lrat_with_limits_and_progress(
            &f,
            &drat,
            Some(generous),
            None,
            1,
            None,
        )
        .expect("elaboration must not error");
        let expected = elaborate_drat_to_lrat(&f, &drat).expect("elaboration must not error");
        assert_eq!(outcome, LratElaborateOutcome::Elaborated(expected));
    }

    #[test]
    fn a_non_rup_addition_is_still_rejected_under_generous_bounds() {
        let f = formula(1, &[&[1]]);
        let bogus = vec![crate::DratStep::Add(vec![lit(-1), lit(-1)])]; // not RUP
        let outcome =
            elaborate_drat_to_lrat_with_limits_and_progress(&f, &bogus, None, None, 1, None);
        assert_eq!(outcome, Err(LratError::StepNotVerified { id: 2 }));
    }

    #[test]
    fn progress_sink_fires_and_reports_totals_matching_the_output() {
        let (f, drat) = multi_step_unsat_drat();
        let mut snapshots: Vec<LratElaborateProgress> = Vec::new();
        let mut record = |p: &LratElaborateProgress| snapshots.push(*p);
        let outcome = elaborate_drat_to_lrat_with_limits_and_progress(
            &f,
            &drat,
            None,
            None,
            1,
            Some(&mut record),
        )
        .expect("elaboration must not error");
        let LratElaborateOutcome::Elaborated(lrat) = outcome else {
            panic!("expected Elaborated, got {outcome:?}");
        };
        assert!(
            snapshots.len() >= drat.len(),
            "interval 1 must poll at least once per processed step"
        );
        for snapshot in &snapshots {
            assert_eq!(snapshot.steps_total, drat.len());
        }
        let last = snapshots.last().unwrap();
        assert_eq!(last.steps_processed, drat.len());
        assert_eq!(last.lrat_steps_emitted, lrat.len());
        for pair in snapshots.windows(2) {
            assert!(pair[1].steps_processed >= pair[0].steps_processed);
            assert!(pair[1].lrat_steps_emitted >= pair[0].lrat_steps_emitted);
            assert!(pair[1].elapsed >= pair[0].elapsed);
        }
    }

    #[test]
    fn progress_sink_installed_or_not_does_not_change_the_output() {
        let (f, drat) = multi_step_unsat_drat();
        let without =
            elaborate_drat_to_lrat_with_limits_and_progress(&f, &drat, None, None, 1, None)
                .expect("elaboration must not error");
        let mut ticks = 0usize;
        let mut count = |_: &LratElaborateProgress| ticks += 1;
        let with_sink = elaborate_drat_to_lrat_with_limits_and_progress(
            &f,
            &drat,
            None,
            None,
            1,
            Some(&mut count),
        )
        .expect("elaboration must not error");
        assert_eq!(
            without, with_sink,
            "installing a progress sink must not change the output"
        );
        assert!(ticks > 0, "the sink must actually have fired");
    }

    #[test]
    fn a_resource_out_still_reports_a_final_progress_snapshot() {
        let (f, drat) = multi_step_unsat_drat();
        let mut snapshots: Vec<LratElaborateProgress> = Vec::new();
        let mut record = |p: &LratElaborateProgress| snapshots.push(*p);
        let outcome = elaborate_drat_to_lrat_with_limits_and_progress(
            &f,
            &drat,
            None,
            Some(1),
            1_000_000,
            Some(&mut record),
        )
        .expect("a resource bound is an outcome, not an error");
        assert_eq!(outcome, LratElaborateOutcome::ResourceOut);
        assert_eq!(
            snapshots.len(),
            1,
            "the ResourceOut path must still report a final snapshot"
        );
        assert_eq!(snapshots[0].steps_processed, 1);
    }

    // --- certify_unsat_via_lrat (ADR-0613) ----------------------------------

    use super::{LratCertifyOutcome, LratDecline, certify_unsat_via_lrat};
    use crate::DratStep;

    /// A deterministic xorshift, so every fixture below is reproducible.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn below(&mut self, bound: u64) -> usize {
            usize::try_from(self.next() % bound).unwrap()
        }

        /// A random CNF over `vars` variables with clauses of width 1..=3.
        fn formula(&mut self, vars: usize, clause_count: usize) -> CnfFormula {
            let mut f = CnfFormula::new(vars);
            let bound = u64::try_from(vars).unwrap();
            for _ in 0..clause_count {
                let width = 1 + self.below(3);
                let mut lits = Vec::new();
                for _ in 0..width {
                    let v = i64::try_from(self.next() % bound).unwrap() + 1;
                    lits.push(lit(if self.next() & 1 == 0 { v } else { -v }));
                }
                f.add_clause(CnfClause::new(lits)).unwrap();
            }
            f
        }
    }

    fn certified(outcome: &LratCertifyOutcome) -> bool {
        matches!(outcome, LratCertifyOutcome::Certified(_))
    }

    /// THE LOAD-BEARING ADVERSARIAL FIXTURE.
    ///
    /// On an unsatisfiable formula every accepted proof is sound vacuously, so a
    /// composition that had quietly stopped checking would look perfect there. A
    /// **satisfiable** formula is the only place it shows up: nothing may ever
    /// certify one, whatever proof is attached.
    ///
    /// Three attack shapes, because they exercise different guards:
    ///
    /// - a **borrowed** proof, valid for a different formula — the backward walk
    ///   finds a real empty clause but the lemmas do not follow from *this*
    ///   formula;
    /// - a proof **truncated** before its empty clause, and one whose empty
    ///   clause is **unjustified** — this is the shape that kills a missing
    ///   `check_lrat` gate, because `elaborate_drat_to_lrat_backward` answers
    ///   `Ok(vec![])` when there is no refutation, and an empty LRAT proof is
    ///   `Ok(false)` (not an error) to the trusted checker. Returning
    ///   `Certified` on elaboration success alone would certify a satisfiable
    ///   formula from an empty proof;
    /// - a proof of **random garbage** ending in an empty clause.
    #[test]
    fn never_certifies_a_satisfiable_formula() {
        let mut rng = Rng(0x51a7_1c5e_0bad_f00d);
        // A real refutation to borrow from, over the same variable range.
        let (donor_formula, donor_proof) = multi_step_unsat_drat();
        assert!(
            certified(&certify_unsat_via_lrat(&donor_formula, &donor_proof)),
            "positive control: the donor's own proof must certify its own formula"
        );

        let mut satisfiable = 0u32;
        for _ in 0..400 {
            let vars = 3 + rng.below(4);
            let clauses = 3 + rng.below(10);
            let f = rng.formula(vars, clauses);
            if !matches!(solve_with_drat_proof(&f), ProofSolveOutcome::Sat(_)) {
                continue;
            }
            satisfiable += 1;

            // 1. Borrowed refutation.
            assert!(
                !certified(&certify_unsat_via_lrat(&f, &donor_proof)),
                "a borrowed refutation must never certify a satisfiable formula"
            );

            // 2a. Truncated: everything before the donor's empty clause.
            let truncated: Vec<DratStep> = donor_proof
                .iter()
                .take_while(|step| !matches!(step, DratStep::Add(c) if c.is_empty()))
                .cloned()
                .collect();
            assert!(
                !certified(&certify_unsat_via_lrat(&f, &truncated)),
                "a proof with no empty clause must never certify anything"
            );

            // 2b. An unjustified empty clause and nothing else. This is exactly
            //     what a missing `check_lrat` gate would wave through.
            assert!(
                !certified(&certify_unsat_via_lrat(&f, &[DratStep::Add(Vec::new())])),
                "a bare empty clause is not a refutation of a satisfiable formula"
            );

            // 3. Random garbage terminated by an empty clause.
            let mut garbage: Vec<DratStep> = Vec::new();
            for _ in 0..6 {
                let width = 1 + rng.below(3);
                let bound = u64::try_from(vars).unwrap();
                let mut lits = Vec::new();
                for _ in 0..width {
                    let v = i64::try_from(rng.next() % bound).unwrap() + 1;
                    lits.push(lit(if rng.next() & 1 == 0 { v } else { -v }));
                }
                garbage.push(DratStep::Add(lits));
            }
            garbage.push(DratStep::Add(Vec::new()));
            assert!(
                !certified(&certify_unsat_via_lrat(&f, &garbage)),
                "a random proof must never certify a satisfiable formula"
            );
        }
        assert!(
            satisfiable >= 20,
            "the fixture must actually have run on satisfiable formulas, got \
             {satisfiable} — a generator that produced none would make every \
             assertion above vacuous"
        );
    }

    /// Differential against the forward reference checker on solver-produced
    /// proofs: whatever [`check_drat`] verifies, this route must certify, and
    /// the LRAT it hands back must independently satisfy [`check_lrat`].
    ///
    /// The counter is asserted so the sweep cannot silently degenerate into "no
    /// unsat instances ran".
    #[test]
    fn certifies_exactly_what_the_reference_checker_verifies() {
        let mut rng = Rng(0x0bad_c0de_dead_beef);
        let mut unsat = 0u32;
        for _ in 0..600 {
            let vars = 3 + rng.below(4);
            let clauses = 4 + rng.below(16);
            let f = rng.formula(vars, clauses);
            let ProofSolveOutcome::Unsat(drat) = solve_with_drat_proof(&f) else {
                continue;
            };
            assert_eq!(check_drat(&f, &drat), Ok(true), "DRAT must verify");
            unsat += 1;
            match certify_unsat_via_lrat(&f, &drat) {
                LratCertifyOutcome::Certified(steps) => {
                    assert_eq!(
                        check_lrat(&f, &steps),
                        Ok(true),
                        "the returned LRAT must verify on its own"
                    );
                    let reparsed = parse_lrat(&write_lrat(&steps)).expect("LRAT round-trips");
                    assert_eq!(check_lrat(&f, &reparsed), Ok(true));
                }
                LratCertifyOutcome::Declined(reason) => panic!(
                    "the reference checker verified this proof but the LRAT route \
                     declined: {reason}"
                ),
            }
        }
        assert!(unsat >= 20, "expected many UNSAT cases, got {unsat}");
    }

    /// A decline is a statement about the ROUTE, not about the proof, and the
    /// reasons must stay distinguishable — a caller that cannot tell "this
    /// format cannot express your proof" from "your proof is broken" will report
    /// the wrong one.
    #[test]
    fn a_missing_refutation_declines_with_the_no_empty_clause_reason() {
        let f = unsat_2x2();
        let outcome = certify_unsat_via_lrat(&f, &[]);
        assert_eq!(
            outcome,
            LratCertifyOutcome::Declined(LratDecline::NoEmptyClause),
            "an empty proof establishes nothing and must say so precisely"
        );
    }

    /// Deleting the empty-clause addition from a real refutation leaves a proof
    /// that derives no contradiction. Certifying it would mean the route reports
    /// `unsat` for a proof that never says so.
    ///
    /// Deliberately *not* a literal-flip sweep: flipping a sign can produce
    /// another clause that happens to be RUP, so such a sweep asserts something
    /// that is not actually invariant. Removing the refutation is invariant.
    #[test]
    fn a_refutation_stripped_of_its_empty_clause_is_never_certified() {
        let f = unsat_2x2();
        let drat = drat_of_unsat(&f);
        assert!(
            certified(&certify_unsat_via_lrat(&f, &drat)),
            "positive control: the intact proof certifies"
        );
        let stripped: Vec<DratStep> = drat
            .iter()
            .filter(|step| !matches!(step, DratStep::Add(c) if c.is_empty()))
            .cloned()
            .collect();
        assert!(
            stripped.len() < drat.len(),
            "the fixture must actually have removed an empty clause"
        );
        assert_eq!(
            certify_unsat_via_lrat(&f, &stripped),
            LratCertifyOutcome::Declined(LratDecline::NoEmptyClause),
            "a proof that derives no empty clause must not be certified"
        );
    }
}
