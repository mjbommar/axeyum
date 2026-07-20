//! An independent DRAT UNSAT-proof checker (ADR-0011).
//!
//! This is the trusted component that discharges `unsat`: given a CNF formula
//! and a DRAT proof (clause additions and deletions), it verifies each added
//! clause is RUP (reverse unit propagation) or RAT (resolution asymmetric
//! tautology) with respect to the current clauses, and that the empty clause is
//! derived. It depends on nothing but the formula and proof — a small, total,
//! auditable checker, independent of whatever solver produced the proof.

use std::collections::HashMap;

use crate::{CnfFormula, CnfLit, CnfVar};

/// One step of a DRAT proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DratStep {
    /// Add a clause; it must be RUP or RAT w.r.t. the current clause set.
    Add(Vec<CnfLit>),
    /// Delete a clause previously present in the clause set.
    Delete(Vec<CnfLit>),
}

/// Error from DRAT checking or parsing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DratError {
    /// An added clause is neither RUP nor RAT — the proof is invalid.
    StepNotVerified {
        /// Zero-based index of the failing proof step.
        step: usize,
    },
    /// The proof text could not be parsed.
    Parse(String),
}

impl core::fmt::Display for DratError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            DratError::StepNotVerified { step } => {
                write!(f, "DRAT step {step} is neither RUP nor RAT")
            }
            DratError::Parse(what) => write!(f, "DRAT parse error: {what}"),
        }
    }
}

impl core::error::Error for DratError {}

/// Verifies `proof` against `formula`.
///
/// Returns `Ok(true)` when every step verifies and the empty clause is derived
/// (UNSAT confirmed), `Ok(false)` when every step verifies but the empty clause
/// is never derived (UNSAT not established), and `Err` when a step fails to
/// verify.
///
/// # Errors
///
/// Returns [`DratError::StepNotVerified`] for an unjustified clause addition.
pub fn check_drat(formula: &CnfFormula, proof: &[DratStep]) -> Result<bool, DratError> {
    let mut active: Vec<Vec<CnfLit>> = formula.clauses().map(<[CnfLit]>::to_vec).collect();
    let mut derived_empty = false;

    for (step, action) in proof.iter().enumerate() {
        match action {
            DratStep::Delete(clause) => {
                if let Some(position) = position_of(&active, clause) {
                    active.swap_remove(position);
                }
            }
            DratStep::Add(clause) => {
                if !is_rup(&active, clause) && !is_rat(&active, clause) {
                    return Err(DratError::StepNotVerified { step });
                }
                if clause.is_empty() {
                    derived_empty = true;
                }
                active.push(clause.clone());
            }
        }
    }
    Ok(derived_empty)
}

/// Serializes a DRAT proof to the standard textual format: each step is a
/// `0`-terminated line of DIMACS integer literals, deletions prefixed with `d`.
/// The output is accepted by [`parse_drat`] and by external checkers such as
/// `drat-trim`, so an `unsat` proof can be exported as a checkable artifact.
pub fn write_drat(proof: &[DratStep]) -> String {
    let mut out = String::new();
    for step in proof {
        let lits = match step {
            DratStep::Add(lits) => lits,
            DratStep::Delete(lits) => {
                out.push_str("d ");
                lits
            }
        };
        for lit in lits {
            out.push_str(&lit.dimacs().to_string());
            out.push(' ');
        }
        out.push_str("0\n");
    }
    out
}

/// Parses a DRAT proof in the standard textual format (DIMACS-style integer
/// clauses terminated by `0`, optionally prefixed with `d` for deletions;
/// `c` lines are comments).
///
/// # Errors
///
/// Returns [`DratError::Parse`] for a malformed token or out-of-range variable.
pub fn parse_drat(text: &str) -> Result<Vec<DratStep>, DratError> {
    let mut steps = Vec::new();
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        let mut tokens = line.split_whitespace().peekable();
        let delete = if tokens.peek() == Some(&"d") {
            tokens.next();
            true
        } else {
            false
        };
        let mut lits = Vec::new();
        for token in tokens {
            let value: i64 = token
                .parse()
                .map_err(|_| DratError::Parse(format!("invalid literal `{token}`")))?;
            if value == 0 {
                break;
            }
            lits.push(literal_from_dimacs(value)?);
        }
        steps.push(if delete {
            DratStep::Delete(lits)
        } else {
            DratStep::Add(lits)
        });
    }
    Ok(steps)
}

pub(crate) fn literal_from_dimacs(value: i64) -> Result<CnfLit, DratError> {
    let index = usize::try_from(value.unsigned_abs() - 1)
        .map_err(|_| DratError::Parse(format!("variable {value} out of range")))?;
    let var = CnfVar::new(index).map_err(|error| DratError::Parse(error.to_string()))?;
    Ok(if value < 0 {
        CnfLit::positive(var).negated()
    } else {
        CnfLit::positive(var)
    })
}

/// Finds the index of a clause in `active` equal as a set to `clause`.
fn position_of(active: &[Vec<CnfLit>], clause: &[CnfLit]) -> Option<usize> {
    let target = sorted(clause);
    active
        .iter()
        .position(|candidate| sorted(candidate) == target)
}

pub(crate) fn sorted(clause: &[CnfLit]) -> Vec<(usize, bool)> {
    let mut key: Vec<(usize, bool)> = clause
        .iter()
        .map(|lit| (lit.var().index(), lit.is_negated()))
        .collect();
    key.sort_unstable();
    key.dedup();
    key
}

/// Reverse unit propagation: `clause` is RUP if assigning all its literals false
/// and unit-propagating over `active` yields a conflict.
fn is_rup(active: &[Vec<CnfLit>], clause: &[CnfLit]) -> bool {
    let mut assign: HashMap<usize, bool> = HashMap::new();
    for lit in clause {
        // Value that makes `lit` false.
        let falsifying = lit.is_negated();
        if let Some(&prev) = assign.get(&lit.var().index()) {
            if prev != falsifying {
                // The clause contains both a literal and its negation: falsifying
                // it is contradictory, so its negation is immediately unsat.
                return true;
            }
        } else {
            assign.insert(lit.var().index(), falsifying);
        }
    }
    propagate_to_conflict(active, &mut assign)
}

/// Unit-propagates `assign` over `active`, returning `true` on a conflict.
fn propagate_to_conflict(active: &[Vec<CnfLit>], assign: &mut HashMap<usize, bool>) -> bool {
    loop {
        let mut changed = false;
        for clause in active {
            let mut satisfied = false;
            let mut unassigned: Option<CnfLit> = None;
            let mut unassigned_count = 0usize;
            for &lit in clause {
                if let Some(&value) = assign.get(&lit.var().index()) {
                    // `lit` is true iff its value disagrees with its negation flag.
                    if value != lit.is_negated() {
                        satisfied = true;
                        break;
                    }
                } else {
                    unassigned_count += 1;
                    unassigned = Some(lit);
                }
            }
            if satisfied {
                continue;
            }
            if unassigned_count == 0 {
                return true;
            }
            if unassigned_count == 1 {
                let lit = unassigned.expect("exactly one unassigned literal");
                // Assign so `lit` becomes true.
                assign.insert(lit.var().index(), !lit.is_negated());
                changed = true;
            }
        }
        if !changed {
            return false;
        }
    }
}

/// Resolution asymmetric tautology: `clause` (non-empty) is RAT on its first
/// literal `p` if, for every active clause containing `¬p`, the resolvent
/// `clause ∪ (D \ {¬p})` is RUP.
fn is_rat(active: &[Vec<CnfLit>], clause: &[CnfLit]) -> bool {
    let Some(&pivot) = clause.first() else {
        return false;
    };
    let pivot_var = pivot.var().index();
    for d in active {
        let has_neg_pivot = d
            .iter()
            .any(|l| l.var().index() == pivot_var && l.is_negated() != pivot.is_negated());
        if !has_neg_pivot {
            continue;
        }
        let mut resolvent = clause.to_vec();
        for &l in d {
            let is_neg_pivot = l.var().index() == pivot_var && l.is_negated() != pivot.is_negated();
            if !is_neg_pivot {
                resolvent.push(l);
            }
        }
        if !is_rup(active, &resolvent) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::{DratError, DratStep, check_drat, is_rat, is_rup, parse_drat, write_drat};
    use crate::{CnfClause, CnfFormula, CnfLit, CnfVar};

    #[test]
    fn write_drat_round_trips_through_parse() {
        let proof = vec![
            DratStep::Add(vec![lit(1), lit(-2)]),
            DratStep::Delete(vec![lit(1), lit(-2)]),
            DratStep::Add(vec![]), // the empty clause
        ];
        let text = write_drat(&proof);
        assert!(text.contains("d "), "deletions are prefixed with `d`");
        assert_eq!(parse_drat(&text).unwrap(), proof);
    }

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

    #[test]
    fn rup_derives_empty_clause_for_unit_contradiction() {
        // (x) and (¬x): the empty clause is RUP.
        let f = formula(1, &[&[1], &[-1]]);
        let proof = vec![DratStep::Add(vec![])];
        assert_eq!(check_drat(&f, &proof), Ok(true));
    }

    #[test]
    fn rup_chain_proves_unsat_2x2() {
        // All four clauses over x,y: unsat. Proof learns (x) then ().
        let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
        let proof = vec![DratStep::Add(vec![lit(1)]), DratStep::Add(vec![])];
        assert_eq!(check_drat(&f, &proof), Ok(true));
    }

    #[test]
    fn blocked_clause_is_rat_but_not_rup() {
        // Over formula [(1, 2)], the clause (1) is RAT on pivot 1 (no clause has
        // ¬1) but is not RUP.
        let active = vec![vec![lit(1), lit(2)]];
        let clause = vec![lit(1)];
        assert!(!is_rup(&active, &clause));
        assert!(is_rat(&active, &clause));
    }

    #[test]
    fn unjustified_addition_is_rejected() {
        // From [(1)] alone, the empty clause is neither RUP nor RAT.
        let f = formula(1, &[&[1]]);
        let proof = vec![DratStep::Add(vec![])];
        assert_eq!(
            check_drat(&f, &proof),
            Err(DratError::StepNotVerified { step: 0 })
        );
    }

    #[test]
    fn verified_proof_without_empty_clause_is_not_unsat() {
        // A valid RAT addition that does not derive the empty clause.
        let f = formula(2, &[&[1, 2]]);
        let proof = vec![DratStep::Add(vec![lit(1)])];
        assert_eq!(check_drat(&f, &proof), Ok(false));
    }

    #[test]
    fn parse_round_trips_additions_and_deletions() {
        let text = "c a proof\n1 2 0\nd 1 2 0\n0\n";
        let steps = parse_drat(text).unwrap();
        assert_eq!(
            steps,
            vec![
                DratStep::Add(vec![lit(1), lit(2)]),
                DratStep::Delete(vec![lit(1), lit(2)]),
                DratStep::Add(vec![]),
            ]
        );
    }

    #[test]
    fn parsed_proof_checks_end_to_end() {
        let f = formula(2, &[&[1, 2], &[1, -2], &[-1, 2], &[-1, -2]]);
        let proof = parse_drat("1 0\n0\n").unwrap();
        assert_eq!(check_drat(&f, &proof), Ok(true));
    }
}
