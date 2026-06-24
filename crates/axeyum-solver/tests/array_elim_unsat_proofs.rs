//! **Eager array-elimination UNSAT carries an independently-checked
//! certificate** — the Lean-parity ("every unsat carries a checkable
//! certificate") moat extension for the eager `QF_ABV` path
//! (`check_with_array_elimination`, ADR-0010), mirroring the eager-Ackermann
//! certificate (`tests/ackermann_unsat_proofs.rs`) and the bounded int-blast
//! certificate (`tests/bounded_int_blast_proofs.rs`).
//!
//! That path decides a `QF_ABV` query `Unsat` by eagerly eliminating arrays —
//! (1) **read-over-write**, a VALID array-theory equivalence rewriting
//! `select(store(a,i,e),j)` to `ite(i=j, e, select(a,j))` until every remaining
//! `select` reads an array *variable* (abstracted as a fresh `BitVec` var), then
//! (2) **Ackermann select-congruence**, asserting `(i=j) ⇒ (s_i = s_j)` for every
//! pair of reads on the same array — and refuting the resulting pure `QF_BV`
//! formula. The bit-vector layer already carries DRAT, but the ABV→BV reduction
//! (that the eliminated formula is a sound relaxation of the original) was the
//! trusted `TrustId::ArrayElim` hole.
//!
//! SOUNDNESS DIRECTION. Read-over-write is an equivalence (no models gained or
//! lost) and each select-congruence constraint is a VALID consequence of an array
//! being a function of its index, so every model of the original array formula
//! extends to a model of the eliminated `QF_BV` formula — the eliminated formula
//! is a sound over-approximation (relaxation). Hence `QF_BV`-UNSAT ⇒ ABV-UNSAT.
//! The second step IS an Ackermann congruence reduction over a per-array read
//! function, so this composes the eager-Ackermann witness.
//!
//! [`axeyum_solver::certify_array_elim_unsat`] emits an
//! [`axeyum_solver::ArrayElimUnsatCertificate`] bundling the DRAT of the
//! eliminated CNF plus the witnessed shape of the elimination (per-array
//! select-congruence-pair counts);
//! [`axeyum_solver::ArrayElimUnsatCertificate::recheck`] re-runs the elimination
//! on the ORIGINAL assertions, structurally re-derives the select-congruence set
//! (witnessing each appended assertion is a valid congruence), re-bit-blasts to
//! confirm the stored CNF, and re-runs `check_drat` — establishing the UNSAT with
//! no residual `ArrayElim` trust for this eager sub-case.
//!
//! Soundness-negative anchors confirm the certificate is never fabricated: a
//! genuinely SAT instance and an array-free query both yield `None`, and a
//! tampered certificate (corrupt DRAT / a query with a different eliminated CNF)
//! fails `recheck`.

#![allow(clippy::similar_names)]

use axeyum_ir::{TermArena, TermId};
use axeyum_solver::{ArrayElimUnsatCertificate, certify_array_elim_unsat};

/// `select(store(a, i, v), i) ≠ v` over index width 3 / element width 4: by
/// read-over-write the read at the same index `i` is exactly `v`, so the
/// disequality is UNSAT. The refutation rests purely on the read-over-write
/// equivalence (no select-congruence pair needed).
fn instance_row_same_index() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 3, 4).unwrap();
    let i = arena.bv_var("i", 3).unwrap();
    let v = arena.bv_var("v", 4).unwrap();
    let stored = arena.store(a, i, v).unwrap();
    let read = arena.select(stored, i).unwrap();
    let ne = {
        let eq = arena.eq(read, v).unwrap();
        arena.not(eq).unwrap()
    };
    (arena, vec![ne])
}

/// `i = j ∧ select(store(a, i, v), j) ≠ v` over index width 3 / element width 4:
/// read-over-write gives `ite(i=j, v, select(a,j))`, and `i = j` forces the read
/// to `v`, contradicting the disequality. UNSAT.
fn instance_row_equal_index() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 3, 4).unwrap();
    let i = arena.bv_var("i", 3).unwrap();
    let j = arena.bv_var("j", 3).unwrap();
    let v = arena.bv_var("v", 4).unwrap();
    let stored = arena.store(a, i, v).unwrap();
    let read = arena.select(stored, j).unwrap();
    let i_eq_j = arena.eq(i, j).unwrap();
    let ne = {
        let eq = arena.eq(read, v).unwrap();
        arena.not(eq).unwrap()
    };
    (arena, vec![i_eq_j, ne])
}

/// `i = j ∧ select(a, i) ≠ select(a, j)` over index width 3 / element width 4:
/// two reads of the same array variable at indices forced equal — the Ackermann
/// select-congruence constraint `(i=j) ⇒ (s_i = s_j)` clashes with the
/// disequality. UNSAT; exercises the select-congruence (Ackermann) step (one
/// congruence pair).
fn instance_select_congruence_clash() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 3, 4).unwrap();
    let i = arena.bv_var("i", 3).unwrap();
    let j = arena.bv_var("j", 3).unwrap();
    let read_i = arena.select(a, i).unwrap();
    let read_j = arena.select(a, j).unwrap();
    let i_eq_j = arena.eq(i, j).unwrap();
    let ne = {
        let eq = arena.eq(read_i, read_j).unwrap();
        arena.not(eq).unwrap()
    };
    (arena, vec![i_eq_j, ne])
}

/// Drives `certify_array_elim_unsat`, asserts a certificate is produced with a
/// non-trivial bundled DRAT that re-checks in isolation, and that the FULL
/// reduction re-validates against the ORIGINAL assertions.
fn assert_certified(
    label: &str,
    arena: &TermArena,
    asserts: &[TermId],
    nontrivial_cnf: bool,
) -> ArrayElimUnsatCertificate {
    let cert = certify_array_elim_unsat(arena, asserts)
        .unwrap_or_else(|e| panic!("{label}: certify_array_elim_unsat errored: {e}"))
        .unwrap_or_else(|| {
            panic!("{label}: expected Some(certificate) for an eager array-elim UNSAT")
        });

    // The bundled BV DRAT is itself re-checkable in isolation. For instances whose
    // eliminated formula does not collapse to a trivial unit refutation, confirm
    // the CNF is non-trivial (the refutation does real clausal work).
    let clauses = cert
        .bv_proof()
        .dimacs
        .lines()
        .filter(|l| !l.starts_with('p') && !l.starts_with('c') && !l.trim().is_empty())
        .count();
    assert!(
        clauses >= 1,
        "{label}: certificate must carry at least one clause (got {clauses})"
    );
    if nontrivial_cnf {
        assert!(
            clauses > 1,
            "{label}: certificate is over a non-trivial CNF (got {clauses} clauses)"
        );
    }
    assert_eq!(
        cert.bv_proof().recheck(),
        Ok(true),
        "{label}: bundled BV DRAT must re-check (independent check_drat, RUP/RAT)"
    );

    // The total congruence count equals the sum of the per-array pair counts.
    let total: usize = cert
        .congruence_pairs_per_array()
        .iter()
        .map(|(_, p)| *p)
        .sum();
    assert_eq!(
        total,
        cert.congruence_constraint_count(),
        "{label}: per-array pair counts must sum to the total congruence count"
    );

    // The whole ABV→BV reduction re-validates against the ORIGINAL assertions:
    // re-run elimination, re-derive select-congruence, re-blast (DIMACS match),
    // check_drat.
    assert_eq!(
        cert.recheck(arena, asserts),
        Ok(true),
        "{label}: full array-elim certificate must re-validate against the originals"
    );
    cert
}

#[test]
fn row_same_index_certificate_revalidates() {
    let (arena, asserts) = instance_row_same_index();
    // Read-over-write at the same index collapses `select(store(a,i,v),i)` to `v`,
    // so this reduces to `v ≠ v` — a trivial unit refutation. The certificate is
    // still genuinely UNSAT and re-checks; we just do not require a non-trivial CNF.
    let cert = assert_certified("select(store(a,i,v),i) ≠ v", &arena, &asserts, false);
    // Single read site (after read-over-write) on `a` — no congruence pair needed;
    // the read-over-write equivalence alone refutes it.
    assert_eq!(cert.congruence_constraint_count(), 0);
}

#[test]
fn row_equal_index_certificate_revalidates() {
    let (arena, asserts) = instance_row_equal_index();
    assert_certified("i=j ∧ select(store(a,i,v),j) ≠ v", &arena, &asserts, true);
}

#[test]
fn select_congruence_clash_certificate_revalidates() {
    let (arena, asserts) = instance_select_congruence_clash();
    let cert = assert_certified("i=j ∧ select(a,i) ≠ select(a,j)", &arena, &asserts, true);
    // One array `a` read at two distinct sites => exactly one select-congruence pair.
    assert_eq!(cert.congruence_constraint_count(), 1);
    assert_eq!(cert.congruence_pairs_per_array().len(), 1);
    assert_eq!(cert.congruence_pairs_per_array()[0].1, 1);
}

/// SOUNDNESS NEGATIVE: re-validating a certificate against a DIFFERENT formula
/// whose re-derived elimination/blast won't match the stored one must fail — the
/// re-checker re-derives everything from the originals and does not trust the
/// certificate's stored data.
#[test]
fn cert_against_different_formula_is_rejected() {
    let (arena, asserts) = instance_select_congruence_clash();
    let cert = certify_array_elim_unsat(&arena, &asserts).unwrap().unwrap();

    // A DIFFERENT (still UNSAT) instance whose eliminated CNF differs: the same
    // read-over-write-same-index refutation, which has a distinct CNF (a `store`
    // shape, no select-congruence pair).
    let (other, other_asserts) = instance_row_same_index();
    assert_eq!(
        cert.recheck(&other, &other_asserts),
        Ok(false),
        "a certificate must NOT re-validate against a query with a different eliminated CNF"
    );
}

/// SOUNDNESS NEGATIVE: corrupting the bundled DRAT defeats the re-check. The
/// certificate's `recheck` step (4) is exactly `self.bv_proof.recheck()` (an
/// independent `check_drat` over the stored DIMACS/DRAT); a DRAT that no longer
/// derives the empty clause must not re-validate.
#[test]
fn tampered_drat_breaks_the_recheck() {
    let (arena, asserts) = instance_select_congruence_clash();
    let cert = certify_array_elim_unsat(&arena, &asserts).unwrap().unwrap();
    // Control: the untampered certificate (and its bundled proof) re-validate.
    assert_eq!(cert.recheck(&arena, &asserts), Ok(true));
    assert_eq!(cert.bv_proof().recheck(), Ok(true));

    // Corrupt the bundled DRAT by dropping its final (empty-clause) line and the
    // self-consistent LRAT: the proof no longer derives the empty clause, so the
    // step-(4) re-check returns `false`/`Err`, never `Ok(true)`.
    let mut proof = cert.bv_proof().clone();
    let trimmed: String = {
        let mut lines: Vec<&str> = proof.drat.lines().collect();
        lines.pop();
        lines.join("\n")
    };
    proof.drat = trimmed;
    proof.lrat = None;
    assert_ne!(
        proof.recheck(),
        Ok(true),
        "a corrupted DRAT must not re-check — the step-(4) checker is not fooled"
    );
}

/// SOUNDNESS NEGATIVE: a genuinely SATISFIABLE array instance yields NO certificate
/// (`select(a, i) = select(a, j) ∧ i ≠ j` is satisfiable — distinct indices, no
/// congruence forced). The certifier returns `None` rather than fabricate an UNSAT.
#[test]
fn sat_instance_yields_no_certificate() {
    let mut arena = TermArena::new();
    let a = arena.array_var("a", 3, 4).unwrap();
    let i = arena.bv_var("i", 3).unwrap();
    let j = arena.bv_var("j", 3).unwrap();
    let read_i = arena.select(a, i).unwrap();
    let read_j = arena.select(a, j).unwrap();
    let eq_reads = arena.eq(read_i, read_j).unwrap();
    let i_ne_j = {
        let eq = arena.eq(i, j).unwrap();
        arena.not(eq).unwrap()
    };
    let cert = certify_array_elim_unsat(&arena, &[eq_reads, i_ne_j]).unwrap();
    assert!(
        cert.is_none(),
        "a satisfiable array instance must not yield an UNSAT certificate"
    );
}

/// SOUNDNESS NEGATIVE: an array-free `QF_BV` query is outside the eager array-elim
/// fragment — nothing is array-eliminated — so the certifier declines (the pure
/// `QF_BV` exporter is the right tool there).
#[test]
fn array_free_query_yields_no_certificate() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let a = arena.eq(x, zero).unwrap();
    let b = arena.eq(x, one).unwrap();
    // x = 0 ∧ x = 1 is UNSAT but has no array constructs.
    let cert = certify_array_elim_unsat(&arena, &[a, b]).unwrap();
    assert!(
        cert.is_none(),
        "an array-free query is not the eager array-elim fragment; no certificate"
    );
}
