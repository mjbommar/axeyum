//! Exportable, externally-checkable `unsat` certificates for the pure-Rust
//! `QF_BV` path (ADR-0011/0012 follow-on).
//!
//! [`export_qf_bv_unsat_proof`] bit-blasts a `QF_BV` query to CNF, runs the
//! proof-producing SAT core, and — on `unsat` — returns the CNF in **DIMACS**
//! and the refutation in standard **DRAT**, both as text. The DRAT is
//! self-verified by the in-tree [`axeyum_cnf::check_drat`] before it is
//! returned, and the same `(dimacs, drat)` pair is accepted by external checkers
//! such as `drat-trim`. This makes the trusted clausal core of an `unsat` an
//! auditable artifact a consumer can save and re-check.
//!
//! Scope: this certifies the **clausal layer** (CNF `unsat`). Certifying the
//! bit-blasting reduction itself (term → AIG → CNF) is the future "SMT-level"
//! proof step; for now the reduction provenance is recorded but the machine
//! check covers the DIMACS/DRAT pair.

use axeyum_bv::{first_unsupported_op, first_unsupported_sort, lower_terms};
use axeyum_cnf::{
    ProofSolveOutcome, check_drat, solve_with_drat_proof, tseitin_encode, write_drat,
};
use axeyum_ir::{Sort, TermArena, TermId};

use crate::backend::SolverError;

/// A checkable `unsat` certificate: the CNF and its DRAT refutation, both in
/// standard text formats.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnsatProof {
    /// The bit-blasted CNF in DIMACS format.
    pub dimacs: String,
    /// The DRAT refutation (verified by `check_drat`, accepted by `drat-trim`).
    pub drat: String,
}

/// The outcome of attempting to export an `unsat` proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnsatProofOutcome {
    /// The query is unsatisfiable with a DRAT-checked certificate.
    Proved(UnsatProof),
    /// The query is satisfiable, so there is no `unsat` proof.
    Satisfiable,
    /// The proof core exhausted its conflict budget without deciding.
    Inconclusive,
}

/// Bit-blasts a `QF_BV` conjunction and, if unsatisfiable, returns a
/// DRAT-checked, exportable `unsat` certificate.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] if the query is outside the bit-blasted
/// `QF_BV` fragment, [`SolverError::NonBooleanAssertion`] for a non-Boolean
/// assertion, or [`SolverError::Backend`] on an internal encoding failure or a
/// proof that fails to check (a soundness alarm).
pub fn export_qf_bv_unsat_proof(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<UnsatProofOutcome, SolverError> {
    for &term in assertions {
        if arena.sort_of(term) != Sort::Bool {
            return Err(SolverError::NonBooleanAssertion(term));
        }
    }
    if let Some((term, op)) = first_unsupported_op(arena, assertions) {
        return Err(SolverError::Unsupported(format!(
            "term #{} uses unsupported pure-Rust BV operator {op:?}",
            term.index()
        )));
    }
    if let Some((term, sort)) = first_unsupported_sort(arena, assertions) {
        return Err(SolverError::Unsupported(format!(
            "term #{} has sort {sort} the pure-Rust BV backend cannot bit-blast",
            term.index()
        )));
    }

    let lowering = lower_terms(arena, assertions)
        .map_err(|error| SolverError::Backend(format!("bit-blasting failed: {error}")))?;
    let roots = lowering
        .roots()
        .iter()
        .map(|root| root.bits()[0])
        .collect::<Vec<_>>();
    let encoding = tseitin_encode(lowering.aig(), &roots)
        .map_err(|error| SolverError::Backend(format!("CNF encoding failed: {error}")))?;
    let formula = encoding.formula();

    match solve_with_drat_proof(formula) {
        ProofSolveOutcome::Sat(_) => Ok(UnsatProofOutcome::Satisfiable),
        ProofSolveOutcome::ResourceOut => Ok(UnsatProofOutcome::Inconclusive),
        ProofSolveOutcome::Unsat(proof) => match check_drat(formula, &proof) {
            Ok(true) => Ok(UnsatProofOutcome::Proved(UnsatProof {
                dimacs: formula.to_dimacs(),
                drat: write_drat(&proof),
            })),
            Ok(false) => Err(SolverError::Backend(
                "exported unsat proof did not derive the empty clause".to_owned(),
            )),
            Err(error) => Err(SolverError::Backend(format!(
                "exported unsat proof failed to check: {error}"
            ))),
        },
    }
}
