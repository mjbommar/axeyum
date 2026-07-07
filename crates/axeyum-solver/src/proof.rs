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

use std::time::Instant;

use axeyum_bv::{first_unsupported_op, first_unsupported_sort, lower_terms};
use axeyum_cnf::{
    ProofSolveOutcome, check_drat, check_lrat, elaborate_drat_to_lrat, parse_dimacs, parse_drat,
    parse_lrat, solve_with_drat_proof_within, tseitin_encode, write_drat, write_lrat,
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
    /// The **LRAT** refutation: the same proof in the stronger clausal format with
    /// explicit antecedent hints, so it re-checks in *linear* time (follow the
    /// hints) via [`axeyum_cnf::check_lrat`] — no RUP search. `None` when the proof
    /// could not be elaborated to LRAT (e.g. it uses a RAT step, which the current
    /// elaborator does not hint); the DRAT certificate still stands in that case.
    pub lrat: Option<String>,
}

impl UnsatProof {
    /// Independently re-checks this certificate **from its text alone**: parses
    /// the DIMACS formula and the DRAT proof and confirms the refutation derives
    /// the empty clause (RUP+RAT), exactly as an external `drat-trim` run would.
    ///
    /// This is the consumer-side "trusted small checking" entry point — the DRAT
    /// analogue of [`FarkasCertificate::verify`](crate::FarkasCertificate::verify):
    /// a saved certificate can be re-validated later with no access to the solver
    /// that produced it. (The exporters already self-check on the way out; this
    /// lets a *consumer* re-check independently.)
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Backend`] if the stored DIMACS or DRAT text cannot
    /// be parsed (a malformed certificate).
    pub fn recheck(&self) -> Result<bool, SolverError> {
        let formula = parse_dimacs(&self.dimacs).map_err(|error| {
            SolverError::Backend(format!("certificate DIMACS unparseable: {error}"))
        })?;
        let proof = parse_drat(&self.drat).map_err(|error| {
            SolverError::Backend(format!("certificate DRAT unparseable: {error}"))
        })?;
        let drat_ok = check_drat(&formula, &proof).map_err(|error| {
            SolverError::Backend(format!("certificate failed to check: {error}"))
        })?;
        // When an LRAT certificate is also present, it must independently confirm
        // the same refutation; a present-but-failing LRAT is a tampered certificate,
        // so the whole certificate is rejected (never silently trusted to the DRAT).
        if let Some(lrat_text) = &self.lrat {
            let lrat = parse_lrat(lrat_text).map_err(|error| {
                SolverError::Backend(format!("certificate LRAT unparseable: {error}"))
            })?;
            let lrat_ok = check_lrat(&formula, &lrat).map_err(|error| {
                SolverError::Backend(format!("certificate LRAT failed to check: {error}"))
            })?;
            return Ok(drat_ok && lrat_ok);
        }
        Ok(drat_ok)
    }

    /// Independently re-checks **only** the LRAT certificate in *linear* time
    /// ([`axeyum_cnf::check_lrat`], following the antecedent hints — no RUP search).
    /// Returns `Ok(None)` when no LRAT certificate is attached.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::Backend`] if the stored DIMACS or LRAT text cannot be
    /// parsed.
    pub fn recheck_lrat(&self) -> Result<Option<bool>, SolverError> {
        let Some(lrat_text) = &self.lrat else {
            return Ok(None);
        };
        let formula = parse_dimacs(&self.dimacs).map_err(|error| {
            SolverError::Backend(format!("certificate DIMACS unparseable: {error}"))
        })?;
        let lrat = parse_lrat(lrat_text).map_err(|error| {
            SolverError::Backend(format!("certificate LRAT unparseable: {error}"))
        })?;
        check_lrat(&formula, &lrat).map(Some).map_err(|error| {
            SolverError::Backend(format!("certificate LRAT failed to check: {error}"))
        })
    }
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
    export_qf_bv_unsat_proof_impl(arena, assertions, None)
}

/// Like [`export_qf_bv_unsat_proof`], but the proof-producing SAT search returns
/// [`UnsatProofOutcome::Inconclusive`] when `deadline` expires.
///
/// The deadline only bounds the optional proof search. If it expires, no
/// satisfiability verdict is claimed from the exporter.
///
/// # Errors
///
/// Returns the same errors as [`export_qf_bv_unsat_proof`].
pub fn export_qf_bv_unsat_proof_within(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Result<UnsatProofOutcome, SolverError> {
    export_qf_bv_unsat_proof_impl(arena, assertions, deadline)
}

fn export_qf_bv_unsat_proof_impl(
    arena: &TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
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

    match solve_with_drat_proof_within(formula, deadline) {
        ProofSolveOutcome::Sat(_) => Ok(UnsatProofOutcome::Satisfiable),
        ProofSolveOutcome::ResourceOut | ProofSolveOutcome::Interrupted => {
            Ok(UnsatProofOutcome::Inconclusive)
        }
        ProofSolveOutcome::Unsat(proof) => match check_drat(formula, &proof) {
            Ok(true) => {
                // Elaborate the (RUP) DRAT proof to LRAT for linear re-checking; if
                // a step is not RUP-elaboratable (RAT), keep DRAT-only. The LRAT, when
                // present, is self-checked here so a stored certificate cannot carry a
                // bad LRAT past the exporter.
                let lrat = match elaborate_drat_to_lrat(formula, &proof) {
                    Ok(steps) if matches!(check_lrat(formula, &steps), Ok(true)) => {
                        Some(write_lrat(&steps))
                    }
                    _ => None,
                };
                Ok(UnsatProofOutcome::Proved(UnsatProof {
                    dimacs: formula.to_dimacs(),
                    drat: write_drat(&proof),
                    lrat,
                }))
            }
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
    export_qf_abv_unsat_proof_within(arena, assertions, None)
}

/// Like [`export_qf_abv_unsat_proof`], but the final BV proof search is bounded
/// by `deadline`.
///
/// # Errors
///
/// Returns the same errors as [`export_qf_abv_unsat_proof`].
pub fn export_qf_abv_unsat_proof_within(
    arena: &mut TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
) -> Result<UnsatProofOutcome, SolverError> {
    let elimination = eliminate_arrays(arena, assertions).map_err(|error| match error {
        ArrayElimError::Unsupported(what) => SolverError::Unsupported(what),
        ArrayElimError::Ir(inner) => SolverError::Backend(inner.to_string()),
    })?;
    let eliminated = elimination.assertions().to_vec();
    export_qf_bv_unsat_proof_within(arena, &eliminated, deadline)
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
    export_qf_aufbv_unsat_proof_within(arena, assertions, None)
}

/// Like [`export_qf_aufbv_unsat_proof`], but the final BV proof search is bounded
/// by `deadline`.
///
/// # Errors
///
/// Returns the same errors as [`export_qf_aufbv_unsat_proof`].
pub fn export_qf_aufbv_unsat_proof_within(
    arena: &mut TermArena,
    assertions: &[TermId],
    deadline: Option<Instant>,
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
    export_qf_bv_unsat_proof_within(arena, &eliminated, deadline)
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
        // No finite bit-vector encoding (e.g. `int.pow2`): no bit-blast proof here.
        Err(IntBlastError::UnsupportedOp(_)) => return Ok(UnsatProofOutcome::Inconclusive),
        Err(IntBlastError::Ir(inner)) => return Err(SolverError::Backend(inner.to_string())),
    };
    // Fail-closed against restricting guards: when the blast added any
    // no-overflow (faithful-product) side-constraints, the resulting `QF_BV`
    // query is a *strict restriction* of the original (it prunes wrapping
    // products to steer the `sat` search). A DRAT refutation of that restricted
    // query therefore does NOT establish `unsat` of the original integer
    // formula — exporting it would be a wrong `unsat` proof. So we decline to a
    // sound `Inconclusive` rather than certify a refutation we cannot transfer.
    if blasting.restricting_constraints() > 0 {
        return Ok(UnsatProofOutcome::Inconclusive);
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unsat_proof_rechecks_and_detects_tampering() {
        // x = 0 ∧ x = 1 over BV8 is unsatisfiable.
        let mut arena = TermArena::new();
        let x = arena.bv_var("x", 8).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a = arena.eq(x, zero).unwrap();
        let b = arena.eq(x, one).unwrap();

        let UnsatProofOutcome::Proved(proof) = export_qf_bv_unsat_proof(&arena, &[a, b]).unwrap()
        else {
            panic!("x=0 ∧ x=1 must be unsat with a proof");
        };
        // The exported certificate re-checks independently from its text alone.
        assert!(proof.recheck().unwrap());

        // An LRAT certificate is attached and re-checks in linear time (hints) on
        // its own.
        assert_eq!(
            proof.recheck_lrat().unwrap(),
            Some(true),
            "the exported certificate must carry a linearly-checkable LRAT proof"
        );

        // Corrupting the DRAT (drop its final empty-clause line) must fail the
        // re-check rather than pass — the checker is not fooled.
        let mut broken = proof.clone();
        broken.drat = broken
            .drat
            .lines()
            .filter(|line| line.trim() != "0")
            .collect::<Vec<_>>()
            .join("\n");
        // Either it no longer derives the empty clause (Ok(false)) or the text is
        // now unparseable (Err); both are a rejected certificate, never Ok(true).
        assert!(!matches!(broken.recheck(), Ok(true)));

        // Tampering with the LRAT alone (drop its last hint line) is likewise
        // caught: `recheck` cross-checks the LRAT and rejects the certificate.
        let mut lrat_broken = proof.clone();
        if let Some(text) = lrat_broken.lrat.take() {
            let mut lines: Vec<&str> = text.lines().collect();
            lines.pop(); // drop the final (empty-clause) addition line
            lrat_broken.lrat = Some(lines.join("\n"));
            assert!(
                !matches!(lrat_broken.recheck(), Ok(true)),
                "a tampered LRAT must fail the combined re-check"
            );
        }
    }
}
