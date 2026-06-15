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
use axeyum_rewrite::{
    ArrayElimError, FuncElimError, IntBlastError, blast_integers, eliminate_arrays,
    eliminate_functions, simplify_datatypes,
};

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

/// Like [`export_qf_bv_unsat_proof`] but for **`QF_ABV`** (arrays): eagerly
/// eliminates `select`/`store` to `QF_BV` (read-over-write + Ackermann,
/// ADR-0010), then exports the DRAT-checked certificate of the eliminated query.
///
/// The returned `(dimacs, drat)` is an externally-checkable (`drat-trim`) proof
/// that the *array-eliminated* CNF is `unsat`. The original `QF_ABV` query is
/// then `unsat` by the soundness of the elimination (an
/// equisatisfiability-preserving transform, ADR-0010 — the same one the
/// validated `check_with_array_elimination` solve path uses, and which a `sat`
/// model independently replays through). So the assurance is: **machine-checked
/// at the clausal layer, modulo the trusted (and replay-validatable) array
/// elimination** — strictly stronger than a bare uncertified `unsat`. Certifying
/// the elimination step itself is future SMT-level proof work.
///
/// Takes `&mut` arena because elimination introduces terms.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for constructs outside `QF_ABV`,
/// [`SolverError::NonBooleanAssertion`], or [`SolverError::Backend`] on an
/// encoding failure or a proof that fails to check.
pub fn export_qf_abv_unsat_proof(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<UnsatProofOutcome, SolverError> {
    let elimination = eliminate_arrays(arena, assertions).map_err(|error| match error {
        ArrayElimError::Unsupported(what) => SolverError::Unsupported(what),
        ArrayElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    })?;
    let eliminated = elimination.assertions().to_vec();
    export_qf_bv_unsat_proof(arena, &eliminated)
}

/// Checkable `unsat` certificate for the combined **`QF_AUFBV`** fragment
/// (arrays *and* uninterpreted functions over bit-vectors — the realistic
/// verification/symbolic-execution shape: symbolic memory plus uninterpreted
/// summaries). Eliminates arrays then functions, then exports the `QF_BV`
/// certificate. Same assurance shape as the single-reduction exporters
/// (clausal-layer checked, modulo the trusted reductions).
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for constructs outside `QF_AUFBV`,
/// [`SolverError::NonBooleanAssertion`], or [`SolverError::Backend`] on an
/// encoding failure or a proof that fails to check.
pub fn export_qf_aufbv_unsat_proof(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<UnsatProofOutcome, SolverError> {
    let array_elim = eliminate_arrays(arena, assertions).map_err(|error| match error {
        ArrayElimError::Unsupported(what) => SolverError::Unsupported(what),
        ArrayElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    })?;
    let after_arrays = array_elim.assertions().to_vec();
    let func_elim = eliminate_functions(arena, &after_arrays).map_err(|error| match error {
        FuncElimError::Unsupported(what) => SolverError::Unsupported(what),
        FuncElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    })?;
    let eliminated = func_elim.assertions().to_vec();
    export_qf_bv_unsat_proof(arena, &eliminated)
}

/// Like [`export_qf_bv_unsat_proof`] but for **`QF_UFBV`** (uninterpreted
/// functions over bit-vectors): Ackermann-reduces function applications to
/// fresh variables plus functional-consistency constraints (ADR-0013), then
/// exports the DRAT-checked certificate of the reduced `QF_BV` query.
///
/// Same assurance shape as [`export_qf_abv_unsat_proof`]: machine-checked at the
/// clausal layer, modulo the trusted (replay-validatable) Ackermann reduction.
/// Takes `&mut` arena because the reduction introduces terms.
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for constructs outside `QF_UFBV`,
/// [`SolverError::NonBooleanAssertion`], or [`SolverError::Backend`] on an
/// encoding failure or a proof that fails to check.
pub fn export_qf_uf_unsat_proof(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<UnsatProofOutcome, SolverError> {
    let elimination = eliminate_functions(arena, assertions).map_err(|error| match error {
        FuncElimError::Unsupported(what) => SolverError::Unsupported(what),
        FuncElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    })?;
    let eliminated = elimination.assertions().to_vec();
    export_qf_bv_unsat_proof(arena, &eliminated)
}

/// Checkable `unsat` certificate for **bounded `QF_LIA`**: bit-blasts integers
/// to `BitVec(int_width)` (ADR-0014) and exports the DRAT-checked certificate of
/// the resulting `QF_BV` query. The certificate refutes the query *at the chosen
/// bound* (the bound is part of the claim). If a constant does not fit
/// `int_width`, returns [`UnsatProofOutcome::Inconclusive`] (widen the bound).
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for non-`QF_LIA`/BV constructs,
/// [`SolverError::NonBooleanAssertion`], or [`SolverError::Backend`] on an
/// invalid width / encoding failure / a proof that fails to check.
pub fn export_qf_lia_unsat_proof(
    arena: &mut TermArena,
    assertions: &[TermId],
    int_width: u32,
) -> Result<UnsatProofOutcome, SolverError> {
    let blasting = match blast_integers(arena, assertions, int_width) {
        Ok(blasting) => blasting,
        Err(IntBlastError::ConstantOutOfRange { .. }) => {
            return Ok(UnsatProofOutcome::Inconclusive); // bound too small to bit-blast
        }
        Err(IntBlastError::InvalidWidth(width)) => {
            return Err(SolverError::Backend(format!(
                "invalid integer bit-blast width {width}"
            )));
        }
        Err(IntBlastError::Ir(inner)) => return Err(SolverError::Backend(inner.to_string())),
    };
    let eliminated = blasting.assertions().to_vec();
    export_qf_bv_unsat_proof(arena, &eliminated)
}

/// Checkable `unsat` certificate for **datatypes** over bit-vectors: folds
/// `select`/`is`/equality over explicit constructors ([`simplify_datatypes`],
/// ADR-0022) and exports the DRAT-checked certificate of the resulting `QF_BV`
/// query. Works when the datatypes fully fold away; a query left with free
/// datatype variables (not bit-blastable) is a clean [`SolverError::Unsupported`].
///
/// # Errors
///
/// Returns [`SolverError::Unsupported`] for residual datatype constructs,
/// [`SolverError::NonBooleanAssertion`], or [`SolverError::Backend`] on an
/// encoding failure or a proof that fails to check.
pub fn export_datatype_unsat_proof(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Result<UnsatProofOutcome, SolverError> {
    let simplified =
        simplify_datatypes(arena, assertions).map_err(|e| SolverError::Backend(e.to_string()))?;
    export_qf_bv_unsat_proof(arena, &simplified)
}
