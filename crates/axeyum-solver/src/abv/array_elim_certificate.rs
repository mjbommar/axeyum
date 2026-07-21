//! Re-checkable eager array-elimination UNSAT evidence.

use super::{
    ArrayElimination, SolverError, SymbolId, TermArena, TermId, eliminate_arrays,
    map_elim_error, select_congruence_lemma,
};

// ===========================================================================
// Eager array-elimination UNSAT CERTIFICATE (narrows the `TrustId::ArrayElim`
// hole for the eager-elimination UNSAT sub-case).
// ===========================================================================
//
// [`check_with_array_elimination`] reaches a TRUSTED `Unsat` for a `QF_ABV`
// query: it eagerly eliminates arrays ([`eliminate_arrays`], ADR-0010) to a pure
// `QF_BV` formula and refutes that. The `QF_BV` layer already carries DRAT
// (`export_qf_bv_unsat_proof` → `check_drat`), but the ABV→BV *reduction* — that
// the eliminated formula is a SOUND relaxation of the original array formula — is
// the `ArrayElim` trust hole. This certificate makes that reduction
// independently re-checkable for the eager-elimination UNSAT sub-case, mirroring
// the bounded int-blast certificate (commit 6211982) and COMPOSING the Ackermann
// select-congruence witness (commit d7394ec) — array elim's second step IS an
// Ackermann congruence reduction (over a per-array read function with a single
// index argument).
//
// SOUNDNESS DIRECTION (why `QF_BV`-UNSAT ⇒ ABV-UNSAT). `eliminate_arrays` does
// two things, each a SOUND step:
//
//   1. **Read-over-write.** It rewrites `select(store(a,i,e),j)` to
//      `ite(i=j, e, select(a,j))` and `select(ite(c,t,e),j)` to
//      `ite(c, select(t,j), select(e,j))` until every remaining `select` reads an
//      array *variable*. Each rewrite is a VALID array-theory EQUIVALENCE (the LHS
//      and RHS denote the same element in every array model), so the rewritten
//      formula is equisatisfiable with the original — no models are gained or lost.
//      The result is the `abstraction`: every `select(a, idx)` over an array
//      variable replaced by a fresh `BitVec` variable `v_{a,idx}` (consistently
//      interned: identical `(a, idx)` reads share one fresh var).
//   2. **Ackermann select-congruence.** For every pair of selects on the SAME
//      array variable it appends the constraint `(idx_i = idx_j) ⇒ (v_i = v_j)`.
//      Each such constraint is a VALID consequence of `a` being a function of its
//      index (equal indices read equal elements). Therefore EVERY model `M` of the
//      original array formula extends to a model of the eliminated `QF_BV` formula
//      (interpret each `v_{a,idx}` as `a^M[idx^M]`; the rewritten body holds
//      because read-over-write is an equivalence, and every congruence constraint
//      holds because `a^M` is a genuine function). So the eliminated formula is a
//      sound over-approximation (relaxation): if it is UNSAT, the original has no
//      model either. As with the UF Ackermann case, for the UNSAT direction even a
//      *subset* of the congruence constraints would remain sound (fewer
//      constraints only enlarge the model set) — the witness merely confirms each
//      appended constraint is a real, valid congruence, never a spurious extra
//      assertion that could make a satisfiable formula look UNSAT.
//
// The certificate's `recheck` re-runs the deterministic elimination on the
// ORIGINAL assertions, structurally re-derives the select-congruence set from the
// discovered read pairs and confirms the eliminated formula is exactly
// `abstraction ++ pairwise-congruence` (so it IS a sound relaxation, witnessed —
// not asserted), re-bit-blasts that eliminated formula and confirms the stored
// DIMACS is byte-identical (the DRAT refutes precisely THIS CNF), and re-runs
// `check_drat` over the stored DIMACS/DRAT. Trusting nothing the emitter computed.

/// Deterministic admission bound on the number of eager select-congruence pairs a
/// certificate will witness, mirroring the UF eager bound in [`crate::euf`]. Above
/// this, [`certify_array_elim_unsat`] declines (no certificate) rather than build
/// and re-derive the `O(k²)` pairing.
const MAX_ARRAY_ELIM_CONGRUENCE_PAIRS: usize = 256;

/// A re-checkable certificate that a `QF_ABV` query is `Unsat` via **eager array
/// elimination** (read-over-write + Ackermann select-congruence, ADR-0010): the
/// bit-blasted-CNF DRAT refutation of the (deterministically) array-eliminated
/// formula, plus the witnessed shape of the elimination (the per-array
/// select-congruence-pair counts) so the reduction can be re-derived and confirmed.
/// See [`ArrayElimUnsatCertificate::recheck`].
#[derive(Debug, Clone)]
pub struct ArrayElimUnsatCertificate {
    /// Per-array select-congruence-pair counts `(array, pairs)` in discovery order:
    /// `pairs = k·(k−1)/2` for an array variable read at `k` distinct sites. Purely
    /// descriptive (re-derived and confirmed by `recheck`); records the witnessed
    /// shape of the eager select-congruence (Ackermann) expansion.
    congruence_pairs_per_array: Vec<(SymbolId, usize)>,
    /// Total appended select-congruence constraints (`Σ pairs`): the size of the
    /// valid-consequence set the eliminated formula adds over the rewritten
    /// (read-over-write) abstraction. Re-derived and confirmed by `recheck`.
    congruence_constraint_count: usize,
    /// DRAT (+ DIMACS) refutation of the bit-blasted, array-eliminated `QF_BV` CNF,
    /// independently re-checkable by `check_drat`.
    bv_proof: crate::proof::UnsatProof,
}

impl ArrayElimUnsatCertificate {
    /// The per-array select-congruence-pair counts `(array, pairs)`, in discovery
    /// order.
    #[must_use]
    pub fn congruence_pairs_per_array(&self) -> &[(SymbolId, usize)] {
        &self.congruence_pairs_per_array
    }

    /// The total number of appended select-congruence constraints.
    #[must_use]
    pub fn congruence_constraint_count(&self) -> usize {
        self.congruence_constraint_count
    }

    /// The bit-blasted-CNF DRAT certificate of the array-eliminated formula.
    #[must_use]
    pub fn bv_proof(&self) -> &crate::proof::UnsatProof {
        &self.bv_proof
    }

    /// **Independently re-validates** the whole eager array-elimination reduction
    /// plus the BV refutation, from the ORIGINAL `assertions` and this
    /// certificate's stored data, trusting nothing the emitter computed:
    ///
    ///  1. re-runs the deterministic [`eliminate_arrays`] on `assertions`;
    ///  2. structurally re-derives the pairwise select-congruence set from the
    ///     discovered read sites and confirms the eliminated formula is *exactly*
    ///     `abstraction (read-over-write) ++ that-congruence-set` (so each appended
    ///     assertion is a VALID select-congruence consequence — the eliminated
    ///     formula is a sound relaxation, witnessed) and that the recorded pair
    ///     counts match;
    ///  3. re-bit-blasts the re-derived eliminated formula and confirms the stored
    ///     DIMACS is byte-identical (the DRAT refutes precisely *this* CNF);
    ///  4. re-runs `check_drat` (RUP/RAT) over the stored DIMACS/DRAT.
    ///
    /// Returns `Ok(true)` only when all four hold. With the reduction re-derived
    /// (2,3) and the refutation re-checked (4), `QF_BV`-UNSAT ⇒ ABV-UNSAT, so this
    /// `Unsat` carries no residual `ArrayElim` trust for this eager sub-case. A
    /// `false`/`Err` means the certificate does not establish the `Unsat` and must
    /// not be trusted.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError`] if the elimination/bit-blast fails or the stored
    /// DRAT/DIMACS is unparseable.
    pub fn recheck(&self, arena: &TermArena, assertions: &[TermId]) -> Result<bool, SolverError> {
        // (1) Re-run the deterministic elimination on a scratch copy of the
        //     ORIGINAL assertions. Trust nothing stored: the eliminated formula and
        //     its blast are recomputed here.
        let mut scratch = arena.clone();
        let Ok(elim) = eliminate_arrays(&mut scratch, assertions) else {
            return Ok(false);
        };
        if !elim.had_arrays() {
            // No array constructs: nothing was array-eliminated, so there is no
            // eager array-elim reduction for this certificate to stand for.
            return Ok(false);
        }

        // (2) Structurally re-derive the pairwise select-congruence set and confirm
        //     the eliminated formula is exactly `abstraction ++ congruence`.
        let Some((rederived, per_array)) = rederive_select_congruence(&mut scratch, &elim) else {
            return Ok(false);
        };
        let abstraction = elim.abstraction();
        let eliminated = elim.assertions();
        if eliminated.len() != abstraction.len() + rederived.len() {
            return Ok(false);
        }
        if eliminated[..abstraction.len()] != *abstraction {
            return Ok(false);
        }
        if eliminated[abstraction.len()..] != rederived[..] {
            return Ok(false);
        }
        if per_array != self.congruence_pairs_per_array
            || rederived.len() != self.congruence_constraint_count
        {
            return Ok(false);
        }

        // (3) Re-bit-blast the re-derived eliminated formula and confirm the stored
        //     DIMACS is byte-identical: the DRAT refutes precisely the CNF of the
        //     formula we just re-derived, not some unrelated CNF the emitter chose.
        let eliminated = eliminated.to_vec();
        match crate::proof::export_qf_bv_unsat_proof(&scratch, &eliminated)? {
            crate::proof::UnsatProofOutcome::Proved(fresh) => {
                if fresh.dimacs != self.bv_proof.dimacs {
                    return Ok(false);
                }
            }
            // The re-derived eliminated formula is SAT or undecided: the stored
            // UNSAT certificate cannot stand.
            crate::proof::UnsatProofOutcome::Satisfiable
            | crate::proof::UnsatProofOutcome::Inconclusive => return Ok(false),
        }

        // (4) Independently re-check the stored BV refutation (RUP/RAT) over the
        //     stored DIMACS/DRAT.
        self.bv_proof.recheck()
    }
}

/// The re-derived select-congruence set: the constraint terms (in eliminator-append
/// order) paired with the per-array congruence-pair counts `(array, pairs)`.
type RederivedSelectCongruence = (Vec<TermId>, Vec<(SymbolId, usize)>);

/// Structurally re-derives the eager Ackermann select-congruence constraints from
/// an elimination's discovered selects, replicating exactly what
/// [`eliminate_arrays`] appends: per array variable (discovery order), for every
/// `i < j` read pair, `(idx_i = idx_j) ⇒ (v_i = v_j)`. Returns the constraint
/// terms (in the same order the eliminator appends them) and the per-array pair
/// counts. `None` on an IR builder failure.
///
/// Because these terms are rebuilt on the SAME (post-elimination) `arena` whose
/// interning gives identity, the returned `TermId`s are directly comparable to the
/// eliminated formula's appended constraints — so a match *witnesses* that every
/// appended assertion is a genuine, valid select-congruence consequence. The build
/// (`implies(eq(idx_i, idx_j), eq(v_i, v_j))`, in array-then-pair order) mirrors
/// `Eliminator::ackermann_constraints` verbatim.
fn rederive_select_congruence(
    arena: &mut TermArena,
    elim: &ArrayElimination,
) -> Option<RederivedSelectCongruence> {
    // Snapshot the eliminated selects `(array, index, fresh)` in discovery order.
    let selects: Vec<(SymbolId, TermId, SymbolId)> = elim.selects();

    // Group select indices by array symbol, preserving discovery order — the same
    // grouping order `Eliminator::record_select` uses (linear find, no hash-map
    // iteration in any output).
    let mut groups: Vec<(SymbolId, Vec<usize>)> = Vec::new();
    for (idx, (array, _index, _fresh)) in selects.iter().enumerate() {
        if let Some((_, members)) = groups.iter_mut().find(|(a, _)| a == array) {
            members.push(idx);
        } else {
            groups.push((*array, vec![idx]));
        }
    }

    let mut constraints = Vec::new();
    let mut per_array = Vec::new();
    for (array, members) in &groups {
        let mut pairs = 0usize;
        for a in 0..members.len() {
            for b in (a + 1)..members.len() {
                let (_ai, index_i, fresh_i) = selects[members[a]];
                let (_aj, index_j, fresh_j) = selects[members[b]];
                // Same construction as `select_congruence_lemma` /
                // `Eliminator::ackermann_constraints`: `(idx_i = idx_j) ⇒ (v_i = v_j)`.
                let constraint =
                    select_congruence_lemma(arena, index_i, index_j, fresh_i, fresh_j).ok()?;
                constraints.push(constraint);
                pairs += 1;
            }
        }
        per_array.push((*array, pairs));
    }
    Some((constraints, per_array))
}

/// Counts the total eager select-congruence pairs `eliminate_arrays` would append
/// for `assertions` (`Σ_a k_a·(k_a−1)/2` over array variables read at `k_a`
/// distinct sites), without building them. Used as the deterministic admission
/// bound. `None` if elimination refuses (out of the supported array fragment).
fn array_elim_congruence_pairs(arena: &TermArena, assertions: &[TermId]) -> Option<usize> {
    let mut scratch = arena.clone();
    let elim = eliminate_arrays(&mut scratch, assertions).ok()?;
    let selects = elim.selects();
    let mut groups: Vec<(SymbolId, usize)> = Vec::new();
    for (array, _index, _fresh) in &selects {
        if let Some((_, count)) = groups.iter_mut().find(|(a, _)| a == array) {
            *count += 1;
        } else {
            groups.push((*array, 1));
        }
    }
    Some(
        groups
            .iter()
            .map(|(_, k)| k * k.saturating_sub(1) / 2)
            .sum(),
    )
}

/// Attempts to produce a fully re-checkable [`ArrayElimUnsatCertificate`] for a
/// `QF_ABV` `assertions`: eagerly eliminates arrays ([`eliminate_arrays`] —
/// read-over-write + Ackermann select-congruence), bit-blasts the eliminated
/// `QF_BV` formula, and — if that CNF is `Unsat` — emits the DRAT bundled with the
/// witnessed shape of the elimination.
///
/// Returns `Ok(None)` when there are no array constructs to eliminate (not the
/// eager array-elim fragment), the instance is over the deterministic admission
/// bound (`MAX_ARRAY_ELIM_CONGRUENCE_PAIRS` — graceful, no `O(k²)` blowup), the
/// query is outside the supported array fragment, the eliminated formula is `Sat`,
/// or the proof core stays inconclusive. The verdict path is unchanged; this only
/// adds a certificate when one cleanly exists.
///
/// This is the **certifying** entry point for eager array-elimination `QF_ABV`
/// `Unsat`: a returned certificate, re-checked by
/// [`ArrayElimUnsatCertificate::recheck`] against the same `assertions`,
/// establishes the `Unsat` with no residual `ArrayElim` trust for this
/// eager-elimination sub-case.
///
/// # Errors
///
/// Returns [`SolverError`] on an internal elimination/encoding/blast failure.
pub fn certify_array_elim_unsat(
    arena: &TermArena,
    assertions: &[TermId],
) -> Result<Option<ArrayElimUnsatCertificate>, SolverError> {
    // Deterministic admission bound: refuse the O(k²) eager congruence expansion
    // above the cap rather than build and re-derive it.
    match array_elim_congruence_pairs(arena, assertions) {
        Some(pairs) if pairs <= MAX_ARRAY_ELIM_CONGRUENCE_PAIRS => {}
        // Over the bound, or elimination refused (out-of-fragment): no certificate.
        _ => return Ok(None),
    }

    // Eliminate on a scratch arena (additive; the caller's arena is untouched).
    let mut scratch = arena.clone();
    let elim = eliminate_arrays(&mut scratch, assertions).map_err(map_elim_error)?;
    if !elim.had_arrays() {
        // No array constructs: there is no eager array-elim reduction to certify
        // here (pure QF_BV has its own exporter).
        return Ok(None);
    }

    // Witness the elimination's shape by structurally re-deriving the
    // select-congruence set; it must equal what `eliminate_arrays` appended.
    let Some((rederived, per_array)) = rederive_select_congruence(&mut scratch, &elim) else {
        return Ok(None);
    };
    let abstraction = elim.abstraction();
    let eliminated = elim.assertions();
    if eliminated.len() != abstraction.len() + rederived.len()
        || eliminated[..abstraction.len()] != *abstraction
        || eliminated[abstraction.len()..] != rederived[..]
    {
        return Ok(None);
    }
    let congruence_constraint_count = rederived.len();

    let eliminated = eliminated.to_vec();
    match crate::proof::export_qf_bv_unsat_proof(&scratch, &eliminated)? {
        crate::proof::UnsatProofOutcome::Proved(bv_proof) => Ok(Some(ArrayElimUnsatCertificate {
            congruence_pairs_per_array: per_array,
            congruence_constraint_count,
            bv_proof,
        })),
        crate::proof::UnsatProofOutcome::Satisfiable
        | crate::proof::UnsatProofOutcome::Inconclusive => Ok(None),
    }
}
