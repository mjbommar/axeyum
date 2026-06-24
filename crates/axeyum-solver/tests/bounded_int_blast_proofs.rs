//! **Bounded `QF_NIA` UNSAT carries an independently-checked certificate** — the
//! Lean-parity ("every unsat carries a checkable certificate") moat extension for
//! the bounded exact int-blast added in `feat(solver): bounded QF_NIA UNSAT via
//! exact int-blast` (`decide_bounded_int_blast`).
//!
//! That path decides a bounded `QF_NIA` query `Unsat` by proving a finite integer
//! box per variable, then bit-blasting at a covering width where two's-complement
//! arithmetic is EXACT. The bit-vector layer already carries DRAT, but the Int→BV
//! reduction (the box + exact width) was the trusted `TrustId::IntBlast` hole.
//!
//! This test establishes two things:
//!
//!  * **PART 1 — the BV refutation is independently re-checked.** For each bounded
//!    UNSAT instance we drive the proof-producing path over the bit-blasted
//!    (clamped) CNF — [`axeyum_rewrite::blast_integers`] →
//!    [`axeyum_solver::export_qf_bv_unsat_proof`] → and require
//!    [`axeyum_solver::UnsatProof::recheck`] (which re-runs `axeyum_cnf::check_drat`,
//!    RUP/RAT) to return `Ok(true)` over a NON-TRIVIAL CNF. A self-asserted proof
//!    would not survive this.
//!
//!  * **PART 2 — the Int→BV reduction itself is witnessed.**
//!    [`axeyum_solver::certify_bounded_int_blast`] emits a
//!    [`axeyum_solver::BoundedIntBlastCertificate`] bundling the per-variable
//!    bounds, the covering width, and the BV DRAT;
//!    [`axeyum_solver::BoundedIntBlastCertificate::recheck`] re-derives the box +
//!    width from the ORIGINAL assertions and re-checks the DRAT — establishing the
//!    UNSAT with no residual `IntBlast` trust for this bounded sub-case.
//!
//! Soundness-negative anchors confirm the certificate is never fabricated: a
//! genuinely SAT box and an UNBOUNDED nonlinear query both yield `None`.

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_solver::{
    BoundedIntBlastCertificate, UnsatProofOutcome, certify_bounded_int_blast,
    export_qf_bv_unsat_proof,
};

/// `x*x = 2 ∧ 0 ≤ x ≤ 5`: no integer in `[0,5]` squares to 2.
fn instance_square_no_root() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let xv = arena.var(x);
    let sq = arena.int_mul(xv, xv).unwrap();
    let two = arena.int_const(2);
    let zero = arena.int_const(0);
    let five = arena.int_const(5);
    let eq = arena.eq(sq, two).unwrap();
    let lo = arena.int_ge(xv, zero).unwrap();
    let hi = arena.int_le(xv, five).unwrap();
    (arena, vec![eq, lo, hi])
}

/// `x*y = 7 ∧ 2 ≤ x,y ≤ 3`: in-range products are 4,6,9 — never 7.
fn instance_product_no_factorization() -> (TermArena, Vec<TermId>) {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let y = arena.declare("y", Sort::Int).unwrap();
    let (xv, yv) = (arena.var(x), arena.var(y));
    let prod = arena.int_mul(xv, yv).unwrap();
    let seven = arena.int_const(7);
    let two = arena.int_const(2);
    let three = arena.int_const(3);
    let eq = arena.eq(prod, seven).unwrap();
    let xlo = arena.int_ge(xv, two).unwrap();
    let xhi = arena.int_le(xv, three).unwrap();
    let ylo = arena.int_ge(yv, two).unwrap();
    let yhi = arena.int_le(yv, three).unwrap();
    (arena, vec![eq, xlo, xhi, ylo, yhi])
}

/// `x*x = m·t + r ∧ 0 ≤ x < N·m ∧ t ≥ 0` with `(m,r,N) = (3,2,2)`: `2` is a
/// quadratic non-residue mod 3, so this `no-square-mod` shape is unsat — and the
/// bound on `t` is DERIVED from `x`'s via the equality (exercises that path too).
#[allow(clippy::many_single_char_names)]
fn instance_no_square_mod() -> (TermArena, Vec<TermId>) {
    let (m, r, n) = (3i128, 2i128, 2i128);
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let t = arena.declare("t", Sort::Int).unwrap();
    let (xv, tv) = (arena.var(x), arena.var(t));
    let xsq = arena.int_mul(xv, xv).unwrap();
    let m_c = arena.int_const(m);
    let mt = arena.int_mul(m_c, tv).unwrap();
    let r_c = arena.int_const(r);
    let rhs = arena.int_add(mt, r_c).unwrap();
    let eq = arena.eq(xsq, rhs).unwrap();
    let zero = arena.int_const(0);
    let upper = arena.int_const(n * m);
    let xlo = arena.int_ge(xv, zero).unwrap();
    let xhi = arena.int_lt(xv, upper).unwrap();
    let tlo = arena.int_ge(tv, zero).unwrap();
    (arena, vec![eq, xlo, xhi, tlo])
}

/// PART 1: drive the bounded UNSAT instance through the proof-producing bit-vector
/// path and assert that `check_drat` (RUP/RAT) **independently accepts** the DRAT
/// refutation of the bit-blasted (clamped) CNF, over a NON-TRIVIAL CNF.
///
/// This mirrors what `decide_bounded_int_blast` does to reach its trusted `Unsat`
/// (prove the box → clamp → blast at the covering width), then runs the
/// proof-emitting export over the very same blasted CNF. Returns the
/// independently-rechecked clause count for the report.
fn assert_part1_rechecked_drat(
    label: &str,
    width: u32,
    mut arena: TermArena,
    asserts: &[TermId],
) -> usize {
    // Clamp variables to their (known, for these fixtures) box and blast at the
    // covering width — exactly the bit-blasted CNF the trusted path refutes.
    let blast = axeyum_rewrite::blast_integers(&mut arena, asserts, width)
        .unwrap_or_else(|e| panic!("{label}: blast_integers failed: {e}"));
    let bv_assertions = blast.assertions().to_vec();

    let proof = match export_qf_bv_unsat_proof(&arena, &bv_assertions) {
        Ok(UnsatProofOutcome::Proved(proof)) => proof,
        other => panic!("{label}: expected a DRAT UNSAT proof from the blasted CNF, got {other:?}"),
    };
    let clauses = proof
        .dimacs
        .lines()
        .filter(|l| !l.starts_with('p') && !l.starts_with('c') && !l.trim().is_empty())
        .count();
    assert!(
        clauses > 1,
        "{label}: certificate is over a non-trivial CNF (got {clauses} clauses)"
    );
    assert_eq!(
        proof.recheck(),
        Ok(true),
        "{label}: independent check_drat (RUP/RAT) must accept the DRAT refutation"
    );
    clauses
}

#[test]
fn part1_bounded_square_no_root_carries_rechecked_drat() {
    let (arena, asserts) = instance_square_no_root();
    // max_abs = 25, covering width = bit_len(25)+1 = 5+1 = 6.
    let clauses = assert_part1_rechecked_drat("x*x=2 in [0,5]", 6, arena, &asserts);
    assert!(clauses > 1);
}

#[test]
fn part1_bounded_product_no_factorization_carries_rechecked_drat() {
    let (arena, asserts) = instance_product_no_factorization();
    // max_abs = 9, covering width = bit_len(9)+1 = 4+1 = 5.
    assert_part1_rechecked_drat("x*y=7 in [2,3]", 5, arena, &asserts);
}

#[test]
fn part1_no_square_mod_carries_rechecked_drat() {
    let (arena, asserts) = instance_no_square_mod();
    // x in [0,5] ⇒ x*x ≤ 25; t derived ≤ ~7 ⇒ 3*t ≤ ~25. max_abs ≈ 25 ⇒ width 6.
    assert_part1_rechecked_drat("no-square-mod (3,2,2)", 6, arena, &asserts);
}

/// PART 2: `certify_bounded_int_blast` emits a `BoundedIntBlastCertificate`, and
/// `recheck` (re-deriving the box + width from the ORIGINAL assertions, then
/// re-running `check_drat`) returns `Ok(true)` — witnessing the Int→BV reduction
/// step, not just the BV layer.
fn assert_part2_certified(
    label: &str,
    arena: &TermArena,
    asserts: &[TermId],
) -> BoundedIntBlastCertificate {
    let cert = certify_bounded_int_blast(arena, asserts)
        .unwrap_or_else(|e| panic!("{label}: certify_bounded_int_blast errored: {e}"))
        .unwrap_or_else(|| panic!("{label}: expected a Some(certificate) for a bounded UNSAT"));
    assert!(
        !cert.per_var_bounds().is_empty(),
        "{label}: certificate must record per-variable bounds"
    );
    assert!(
        cert.covering_width() >= 1,
        "{label}: covering width must be positive"
    );
    // The bundled BV proof is itself re-checkable in isolation.
    assert_eq!(
        cert.bv_proof().recheck(),
        Ok(true),
        "{label}: bundled BV DRAT must re-check"
    );
    // The whole reduction re-validates against the ORIGINAL assertions.
    assert_eq!(
        cert.recheck(arena, asserts),
        Ok(true),
        "{label}: full bound-coverage certificate must re-validate against the originals"
    );
    cert
}

#[test]
fn part2_square_no_root_certificate_revalidates() {
    let (arena, asserts) = instance_square_no_root();
    let cert = assert_part2_certified("x*x=2 in [0,5]", &arena, &asserts);
    // The witnessed box is exactly x ∈ [0,5].
    assert_eq!(cert.per_var_bounds().len(), 1);
    let (_, lo, hi) = cert.per_var_bounds()[0];
    assert_eq!((lo, hi), (0, 5));
    assert_eq!(
        cert.covering_width(),
        6,
        "width covers |x*x| ≤ 25 (bit_len 5 + sign)"
    );
}

#[test]
fn part2_product_no_factorization_certificate_revalidates() {
    let (arena, asserts) = instance_product_no_factorization();
    assert_part2_certified("x*y=7 in [2,3]", &arena, &asserts);
}

#[test]
fn part2_no_square_mod_certificate_revalidates() {
    let (arena, asserts) = instance_no_square_mod();
    assert_part2_certified("no-square-mod (3,2,2)", &arena, &asserts);
}

/// SOUNDNESS NEGATIVE: tampering with a stored bound makes `recheck` reject — the
/// re-checker re-derives the box from the originals and does not trust the
/// certificate's claimed bounds. (Guards against a forged/loosened box.)
#[test]
fn part2_tampered_bound_is_rejected() {
    let (arena, asserts) = instance_square_no_root();
    let cert = certify_bounded_int_blast(&arena, &asserts)
        .unwrap()
        .unwrap();
    // Re-validating against a DIFFERENT formula whose re-derived box won't match
    // the stored one must fail: build `x*x = 2 ∧ 0 ≤ x ≤ 9` (box [0,9] ≠ [0,5]).
    let mut other = TermArena::new();
    let x = other.declare("x", Sort::Int).unwrap();
    let xv = other.var(x);
    let sq = other.int_mul(xv, xv).unwrap();
    let two = other.int_const(2);
    let zero = other.int_const(0);
    let nine = other.int_const(9);
    let eq = other.eq(sq, two).unwrap();
    let lo = other.int_ge(xv, zero).unwrap();
    let hi = other.int_le(xv, nine).unwrap();
    assert_eq!(
        cert.recheck(&other, &[eq, lo, hi]),
        Ok(false),
        "a certificate must NOT re-validate against a query with a different proven box"
    );
}

/// SOUNDNESS NEGATIVE: a genuinely SATISFIABLE bounded box yields NO certificate
/// (`x*y = 6 ∧ 1 ≤ x,y ≤ 6` has the model 2·3). The certifier returns `None`
/// rather than fabricate an UNSAT certificate.
#[test]
fn sat_box_yields_no_certificate() {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let y = arena.declare("y", Sort::Int).unwrap();
    let (xv, yv) = (arena.var(x), arena.var(y));
    let prod = arena.int_mul(xv, yv).unwrap();
    let six = arena.int_const(6);
    let one = arena.int_const(1);
    let eq = arena.eq(prod, six).unwrap();
    let xlo = arena.int_ge(xv, one).unwrap();
    let xhi = arena.int_le(xv, six).unwrap();
    let ylo = arena.int_ge(yv, one).unwrap();
    let yhi = arena.int_le(yv, six).unwrap();
    let cert = certify_bounded_int_blast(&arena, &[eq, xlo, xhi, ylo, yhi]).unwrap();
    assert!(
        cert.is_none(),
        "a satisfiable box must not yield an UNSAT certificate"
    );
}

/// SOUNDNESS NEGATIVE: an UNBOUNDED nonlinear query (`x² = 2y² ∧ x,y ≥ 1`, no
/// upper bound) cannot have a finite box proven, so the certifier declines —
/// never a fabricated certificate for an undecided query.
#[test]
fn unbounded_nonlinear_yields_no_certificate() {
    let mut arena = TermArena::new();
    let x = arena.declare("x", Sort::Int).unwrap();
    let y = arena.declare("y", Sort::Int).unwrap();
    let (xv, yv) = (arena.var(x), arena.var(y));
    let xsq = arena.int_mul(xv, xv).unwrap();
    let ysq = arena.int_mul(yv, yv).unwrap();
    let two = arena.int_const(2);
    let two_ysq = arena.int_mul(two, ysq).unwrap();
    let eq = arena.eq(xsq, two_ysq).unwrap();
    let one = arena.int_const(1);
    let xlo = arena.int_ge(xv, one).unwrap();
    let ylo = arena.int_ge(yv, one).unwrap();
    let cert = certify_bounded_int_blast(&arena, &[eq, xlo, ylo]).unwrap();
    assert!(
        cert.is_none(),
        "an unbounded nonlinear query must not yield a certificate"
    );
}
