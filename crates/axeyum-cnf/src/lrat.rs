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

use std::collections::BTreeMap;

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
    let mut assign: BTreeMap<usize, bool> = BTreeMap::new();
    if !assign_clause_false(clause, &mut assign) {
        // Tautology: trivially refuted with no antecedents.
        return Some(Vec::new());
    }
    let mut hints = Vec::new();
    loop {
        let mut changed = false;
        for (&id, candidate) in active {
            match classify(candidate, &assign) {
                ClauseStatus::Conflict => {
                    hints.push(id);
                    return Some(hints);
                }
                ClauseStatus::Unit(lit) => {
                    // Unit propagation: assign so `lit` becomes true.
                    assign.insert(lit.var().index(), !lit.is_negated());
                    hints.push(id);
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
    use super::{LratError, LratStep, check_lrat, elaborate_drat_to_lrat, parse_lrat, write_lrat};
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
}
