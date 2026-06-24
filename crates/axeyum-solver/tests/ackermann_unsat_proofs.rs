//! **Eager Ackermann UF-elimination UNSAT carries an independently-checked
//! certificate** — the Lean-parity ("every unsat carries a checkable
//! certificate") moat extension for the eager `QF_UFBV` path
//! (`check_with_function_elimination`, ADR-0013), mirroring the bounded
//! int-blast certificate (`tests/bounded_int_blast_proofs.rs`).
//!
//! That path decides a `QF_UFBV` query `Unsat` by eagerly Ackermann-eliminating
//! the uninterpreted functions — replacing each distinct application `f(a⃗)` with
//! a fresh variable and asserting, for every same-`f` application pair, the
//! congruence constraint `(⋀ aᵢ = bᵢ) ⇒ (v_{f(a⃗)} = v_{f(b⃗)})` — then refuting
//! the resulting pure `QF_BV` formula. The bit-vector layer already carries DRAT,
//! but the UF→BV reduction (that the eliminated formula is a sound relaxation of
//! the original) was the trusted `TrustId::Ackermann` hole.
//!
//! SOUNDNESS DIRECTION. Each congruence constraint is a VALID consequence of `f`
//! being a function, so every model of the original UF formula extends to a model
//! of the eliminated `QF_BV` formula — the eliminated formula is a sound
//! over-approximation (relaxation). Hence `QF_BV`-UNSAT ⇒ UF-UNSAT.
//!
//! [`axeyum_solver::certify_ackermann_unsat`] emits an
//! [`axeyum_solver::AckermannUnsatCertificate`] bundling the DRAT of the
//! eliminated CNF plus the witnessed shape of the elimination;
//! [`axeyum_solver::AckermannUnsatCertificate::recheck`] re-runs the elimination
//! on the ORIGINAL assertions, structurally re-derives the congruence set
//! (witnessing each appended assertion is a valid congruence), re-bit-blasts to
//! confirm the stored CNF, and re-runs `check_drat` — establishing the UNSAT with
//! no residual `Ackermann` trust for this eager sub-case.
//!
//! Soundness-negative anchors confirm the certificate is never fabricated: a
//! genuinely SAT instance and a function-free query both yield `None`, and a
//! tampered certificate (corrupt congruence accounting / corrupt DRAT) fails
//! `recheck`.

#![allow(clippy::similar_names)]

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{AckermannUnsatCertificate, certify_ackermann_unsat};

/// `f(a) = 1 ∧ f(b) = 2 ∧ a = b` over `BV8`: by congruence `a = b ⇒ f(a) = f(b)`,
/// so `1 = 2` — UNSAT. The single congruence constraint is the whole refutation.
fn instance_congruence_clash() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let two = arena.bv_const(8, 2).unwrap();
    let fa_eq_1 = arena.eq(fa, one).unwrap();
    let fb_eq_2 = arena.eq(fb, two).unwrap();
    let a_eq_b = arena.eq(a, b).unwrap();
    (arena, vec![fa_eq_1, fb_eq_2, a_eq_b])
}

/// `f(f(x)) ≠ f(f(y)) ∧ x = y` over `BV8`: nested applications. With `x = y`,
/// congruence gives `f(x) = f(y)`, then `f(f(x)) = f(f(y))` — contradicting the
/// disequality. UNSAT; exercises Ackermann over nested applications (multiple
/// congruence pairs).
fn instance_nested_congruence() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let x = arena.bv_var("x", 8).unwrap();
    let y = arena.bv_var("y", 8).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let ffx = arena.apply(f, &[fx]).unwrap();
    let ffy = arena.apply(f, &[fy]).unwrap();
    let ne = {
        let eq = arena.eq(ffx, ffy).unwrap();
        arena.not(eq).unwrap()
    };
    let x_eq_y = arena.eq(x, y).unwrap();
    (arena, vec![ne, x_eq_y])
}

/// `f(a) ≠ f(b) ∧ a = b` over `BV4`: the classic single-congruence refutation.
fn instance_classic_diseq() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(4)], Sort::BitVec(4))
        .unwrap();
    let a = arena.bv_var("a", 4).unwrap();
    let b = arena.bv_var("b", 4).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let ne = {
        let eq = arena.eq(fa, fb).unwrap();
        arena.not(eq).unwrap()
    };
    let a_eq_b = arena.eq(a, b).unwrap();
    (arena, vec![ne, a_eq_b])
}

/// Drives `certify_ackermann_unsat`, asserts a certificate is produced with a
/// non-trivial bundled DRAT that re-checks in isolation, and that the FULL
/// reduction re-validates against the ORIGINAL assertions.
fn assert_certified(
    label: &str,
    arena: &TermArena,
    asserts: &[TermId],
) -> AckermannUnsatCertificate {
    let cert = certify_ackermann_unsat(arena, asserts)
        .unwrap_or_else(|e| panic!("{label}: certify_ackermann_unsat errored: {e}"))
        .unwrap_or_else(|| {
            panic!("{label}: expected Some(certificate) for an eager-Ackermann UNSAT")
        });

    assert!(
        cert.congruence_constraint_count() >= 1,
        "{label}: an eager-Ackermann UNSAT must witness at least one congruence constraint"
    );
    assert!(
        !cert.congruence_pairs_per_func().is_empty(),
        "{label}: certificate must record per-function congruence-pair counts"
    );

    // The bundled BV DRAT is itself re-checkable in isolation over a non-trivial CNF.
    let clauses = cert
        .bv_proof()
        .dimacs
        .lines()
        .filter(|l| !l.starts_with('p') && !l.starts_with('c') && !l.trim().is_empty())
        .count();
    assert!(
        clauses > 1,
        "{label}: certificate is over a non-trivial CNF (got {clauses} clauses)"
    );
    assert_eq!(
        cert.bv_proof().recheck(),
        Ok(true),
        "{label}: bundled BV DRAT must re-check (independent check_drat, RUP/RAT)"
    );

    // The whole UF→BV reduction re-validates against the ORIGINAL assertions:
    // re-run elimination, re-derive congruence, re-blast (DIMACS match), check_drat.
    assert_eq!(
        cert.recheck(arena, asserts),
        Ok(true),
        "{label}: full Ackermann certificate must re-validate against the originals"
    );
    cert
}

#[test]
fn congruence_clash_certificate_revalidates() {
    let (arena, asserts) = instance_congruence_clash();
    let cert = assert_certified("f(a)=1 ∧ f(b)=2 ∧ a=b", &arena, &asserts);
    // One function `f` with two distinct applications => exactly one congruence pair.
    assert_eq!(cert.congruence_constraint_count(), 1);
    assert_eq!(cert.congruence_pairs_per_func().len(), 1);
    assert_eq!(cert.congruence_pairs_per_func()[0].1, 1);
}

#[test]
fn nested_congruence_certificate_revalidates() {
    let (arena, asserts) = instance_nested_congruence();
    let cert = assert_certified("f(f(x))≠f(f(y)) ∧ x=y", &arena, &asserts);
    // f has four distinct applications (f(x), f(y), f(f(x)), f(f(y))) =>
    // C(4,2) = 6 congruence pairs.
    assert_eq!(cert.congruence_constraint_count(), 6);
}

#[test]
fn classic_diseq_certificate_revalidates() {
    let (arena, asserts) = instance_classic_diseq();
    assert_certified("f(a)≠f(b) ∧ a=b", &arena, &asserts);
}

/// SOUNDNESS NEGATIVE: re-validating a certificate against a DIFFERENT formula
/// whose re-derived elimination/blast won't match the stored one must fail — the
/// re-checker re-derives everything from the originals and does not trust the
/// certificate's stored data.
#[test]
fn cert_against_different_formula_is_rejected() {
    let (arena, asserts) = instance_congruence_clash();
    let cert = certify_ackermann_unsat(&arena, &asserts).unwrap().unwrap();

    // A DIFFERENT (also UNSAT) instance: `f(a)=1 ∧ f(b)=3 ∧ a=b`. Its eliminated
    // CNF differs (constant 3 vs 2), so the stored DIMACS won't match on re-blast.
    let mut other = TermArena::new();
    let f = other
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let a = other.bv_var("a", 8).unwrap();
    let b = other.bv_var("b", 8).unwrap();
    let fa = other.apply(f, &[a]).unwrap();
    let fb = other.apply(f, &[b]).unwrap();
    let one = other.bv_const(8, 1).unwrap();
    let three = other.bv_const(8, 3).unwrap();
    let fa_eq_1 = other.eq(fa, one).unwrap();
    let fb_eq_3 = other.eq(fb, three).unwrap();
    let a_eq_b = other.eq(a, b).unwrap();
    assert_eq!(
        cert.recheck(&other, &[fa_eq_1, fb_eq_3, a_eq_b]),
        Ok(false),
        "a certificate must NOT re-validate against a query with a different eliminated CNF"
    );
}

/// SOUNDNESS NEGATIVE: corrupting the bundled DRAT defeats the re-check. The
/// certificate's `recheck` step (4) is exactly `self.bv_proof.recheck()` (an
/// independent `check_drat` over the stored DIMACS/DRAT); this anchors that that
/// checker is not fooled by a DRAT that no longer derives the empty clause, so a
/// certificate carrying such a proof cannot re-validate.
#[test]
fn tampered_drat_breaks_the_recheck() {
    let (arena, asserts) = instance_congruence_clash();
    let cert = certify_ackermann_unsat(&arena, &asserts).unwrap().unwrap();
    // Control: the untampered certificate (and its bundled proof) re-validate.
    assert_eq!(cert.recheck(&arena, &asserts), Ok(true));
    assert_eq!(cert.bv_proof().recheck(), Ok(true));

    // Corrupt the bundled DRAT by dropping its final (empty-clause) line and the
    // self-consistent LRAT: the proof no longer derives the empty clause, so the
    // step-(4) re-check the certificate performs returns `false`/`Err`, never
    // `Ok(true)`.
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

/// SOUNDNESS NEGATIVE: a genuinely SATISFIABLE UF instance yields NO certificate
/// (`f(a) = 1 ∧ f(b) = 2 ∧ a ≠ b` is satisfiable — distinct args, no congruence
/// forced). The certifier returns `None` rather than fabricate an UNSAT certificate.
#[test]
fn sat_instance_yields_no_certificate() {
    let mut arena = TermArena::new();
    let f = arena
        .declare_fun("f", &[Sort::BitVec(8)], Sort::BitVec(8))
        .unwrap();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let two = arena.bv_const(8, 2).unwrap();
    let fa_eq_1 = arena.eq(fa, one).unwrap();
    let fb_eq_2 = arena.eq(fb, two).unwrap();
    let a_ne_b = {
        let eq = arena.eq(a, b).unwrap();
        arena.not(eq).unwrap()
    };
    let cert = certify_ackermann_unsat(&arena, &[fa_eq_1, fb_eq_2, a_ne_b]).unwrap();
    assert!(
        cert.is_none(),
        "a satisfiable UF instance must not yield an UNSAT certificate"
    );
}

/// SOUNDNESS NEGATIVE: a function-free `QF_BV` query is outside the
/// eager-Ackermann fragment — nothing is Ackermann-eliminated — so the certifier
/// declines (the pure `QF_BV` exporter is the right tool there).
#[test]
fn function_free_query_yields_no_certificate() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let a = arena.eq(x, zero).unwrap();
    let b = arena.eq(x, one).unwrap();
    // x = 0 ∧ x = 1 is UNSAT but has no uninterpreted functions.
    let cert = certify_ackermann_unsat(&arena, &[a, b]).unwrap();
    assert!(
        cert.is_none(),
        "a function-free query is not the eager-Ackermann fragment; no certificate"
    );
}
