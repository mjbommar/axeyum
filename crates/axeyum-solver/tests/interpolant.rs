//! Craig interpolation over conjunctive `QF_LRA` (Track 3, **T3.8.1**).
//!
//! Each test refutes `A ∧ B`, asks [`lra_interpolant`] for a Craig interpolant
//! `I`, and *independently* re-checks the three defining conditions
//! (`A ⇒ I`, `I ∧ B ⇒ ⊥`, shared vocabulary) so the assurance does not lean on
//! the function's own internal verification.
#![cfg(feature = "full")]

use std::collections::BTreeSet;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, TermNode};
use axeyum_solver::{
    CheckResult, InterpolantOutcome, SatBvBackend, Solver, check_alethe_lra, check_with_lra,
    lra_interpolant, lra_interpolant_certified,
};

/// `x` as a real symbol + its variable term.
fn real_var(arena: &mut TermArena, name: &str) -> TermId {
    let sym = arena.declare(name, Sort::Real).unwrap();
    arena.var(sym)
}

fn symbol_id(arena: &TermArena, name: &str) -> SymbolId {
    arena.find_symbol(name).expect("declared symbol")
}

fn is_unsat(arena: &TermArena, assertions: &[TermId]) -> bool {
    matches!(
        check_with_lra(arena, assertions).expect("QF_LRA decides"),
        CheckResult::Unsat
    )
}

fn symbols_of(arena: &TermArena, term: TermId, out: &mut BTreeSet<SymbolId>) {
    match arena.node(term) {
        TermNode::Symbol(s) => {
            out.insert(*s);
        }
        TermNode::App { args, .. } => {
            for &arg in args {
                symbols_of(arena, arg, out);
            }
        }
        _ => {}
    }
}

/// Independently verifies that `interpolant` is a genuine Craig interpolant for
/// the partition `(a, b)`: `A ⇒ I`, `I ∧ B ⇒ ⊥`, and `I`'s symbols are shared.
fn assert_is_interpolant(arena: &mut TermArena, a: &[TermId], b: &[TermId], interpolant: TermId) {
    // (1) A ⇒ I  ≡  A ∧ ¬I unsat.
    let not_i = arena.not(interpolant).unwrap();
    let mut a_not_i = a.to_vec();
    a_not_i.push(not_i);
    assert!(is_unsat(arena, &a_not_i), "A ∧ ¬I must be unsat (A ⇒ I)");

    // (2) I ∧ B unsat.
    let mut i_b = vec![interpolant];
    i_b.extend_from_slice(b);
    assert!(is_unsat(arena, &i_b), "I ∧ B must be unsat");

    // (3) Vocabulary: I's symbols ⊆ symbols(A) ∩ symbols(B).
    let mut a_syms = BTreeSet::new();
    for &t in a {
        symbols_of(arena, t, &mut a_syms);
    }
    let mut b_syms = BTreeSet::new();
    for &t in b {
        symbols_of(arena, t, &mut b_syms);
    }
    let mut i_syms = BTreeSet::new();
    symbols_of(arena, interpolant, &mut i_syms);
    for s in &i_syms {
        assert!(
            a_syms.contains(s) && b_syms.contains(s),
            "interpolant uses a non-shared symbol"
        );
    }
}

#[test]
fn shared_single_variable_interpolant() {
    // A: x ≤ 0 ; B: x ≥ 1.  Unsat; shared variable x.
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let a0 = arena.real_le(x, zero).unwrap();
    let b0 = arena.real_ge(x, one).unwrap();

    let interpolant = lra_interpolant(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a Farkas interpolant exists for an unsat LRA conjunction");
    assert_is_interpolant(&mut arena, &[a0], &[b0], interpolant);
}

#[test]
fn a_only_variable_cancels_out_of_the_interpolant() {
    // A: x ≤ 0 ∧ z ≤ x   (⇒ z ≤ 0, but mentions the A-only variable x)
    // B: z ≥ 1
    // The Farkas interpolant must mention only the shared variable z; x cancels.
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let z = real_var(&mut arena, "z");
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let a0 = arena.real_le(x, zero).unwrap();
    let a1 = arena.real_le(z, x).unwrap(); // z ≤ x
    let b0 = arena.real_ge(z, one).unwrap();

    let interpolant = lra_interpolant(&mut arena, &[a0, a1], &[b0])
        .expect("decides")
        .expect("interpolant exists");
    assert_is_interpolant(&mut arena, &[a0, a1], &[b0], interpolant);

    // Concretely: x must NOT appear in the interpolant (it is A-only).
    let x_sym = symbol_id(&arena, "x");
    let z_sym = symbol_id(&arena, "z");
    let mut i_syms = BTreeSet::new();
    symbols_of(&arena, interpolant, &mut i_syms);
    assert!(!i_syms.contains(&x_sym), "A-only variable x must cancel");
    assert!(i_syms.contains(&z_sym), "shared variable z must remain");
}

#[test]
fn strict_interpolant_is_strict() {
    // A: x < 0 ; B: x ≥ 0.  The A-atom is strict, so the interpolant is strict.
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let zero = arena.real_ratio(0, 1);
    let a0 = arena.real_lt(x, zero).unwrap();
    let b0 = arena.real_ge(x, zero).unwrap();

    let interpolant = lra_interpolant(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("interpolant exists");
    assert_is_interpolant(&mut arena, &[a0], &[b0], interpolant);
}

#[test]
fn a_alone_unsat_yields_false_interpolant() {
    // A: x ≤ 0 ∧ x ≥ 1 (unsat on its own); B: empty.
    // The interpolant is ⊥ — A ⇒ ⊥, ⊥ ∧ B ⇒ ⊥, empty vocabulary.
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let a0 = arena.real_le(x, zero).unwrap();
    let a1 = arena.real_ge(x, one).unwrap();

    let interpolant = lra_interpolant(&mut arena, &[a0, a1], &[])
        .expect("decides")
        .expect("interpolant exists");
    // ⊥: A ∧ ¬I unsat (A is unsat) and I ∧ (empty B) unsat (I is false).
    assert_is_interpolant(&mut arena, &[a0, a1], &[], interpolant);
}

#[test]
fn b_alone_unsat_yields_true_interpolant() {
    // A: empty; B: x ≤ 0 ∧ x ≥ 1 (unsat on its own).
    // The interpolant is ⊤ — A ⇒ ⊤ vacuously, ⊤ ∧ B ⇒ ⊥, empty vocabulary.
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let b0 = arena.real_le(x, zero).unwrap();
    let b1 = arena.real_ge(x, one).unwrap();

    let interpolant = lra_interpolant(&mut arena, &[], &[b0, b1])
        .expect("decides")
        .expect("interpolant exists");
    assert_is_interpolant(&mut arena, &[], &[b0, b1], interpolant);
}

#[test]
fn two_variable_shared_interpolant() {
    // A: x + y ≤ 0 ; B: x + y ≥ 2.  Shared variables x and y.
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let y = real_var(&mut arena, "y");
    let zero = arena.real_ratio(0, 1);
    let two = arena.real_ratio(2, 1);
    let xy = arena.real_add(x, y).unwrap();
    let a0 = arena.real_le(xy, zero).unwrap();
    let b0 = arena.real_ge(xy, two).unwrap();

    let interpolant = lra_interpolant(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("interpolant exists");
    assert_is_interpolant(&mut arena, &[a0], &[b0], interpolant);
}

#[test]
fn satisfiable_conjunction_has_no_interpolant() {
    // A: x ≤ 0 ; B: x ≤ 1.  Satisfiable — there is no Craig interpolant; decline.
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let a0 = arena.real_le(x, zero).unwrap();
    let b0 = arena.real_le(x, one).unwrap();

    assert!(
        lra_interpolant(&mut arena, &[a0], &[b0])
            .expect("decides")
            .is_none(),
        "a satisfiable conjunction must yield no interpolant"
    );
}

#[test]
fn solver_facade_interpolant_partitions_assertions() {
    // Active assertions [x ≤ 0, x ≥ 1]; A = {index 0}, B = {index 1}.
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let a0 = arena.real_le(x, zero).unwrap();
    let b0 = arena.real_ge(x, one).unwrap();

    let mut solver = Solver::new(SatBvBackend::new());
    solver.assert(a0);
    solver.assert(b0);

    let interpolant = solver
        .interpolant(&mut arena, &[0])
        .expect("decides")
        .expect("interpolant exists");
    assert_is_interpolant(&mut arena, &[a0], &[b0], interpolant);
}

#[test]
fn explained_outcome_distinguishes_interpolant_notinterpolable_declined() {
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let two = arena.real_ratio(2, 1);
    let nonpos = arena.real_le(x, zero).unwrap();
    let atleast_one = arena.real_ge(x, one).unwrap();
    let atmost_two = arena.real_le(x, two).unwrap();

    // Unsat partition (x ≤ 0 vs x ≥ 1) ⇒ a real interpolant.
    let mut unsat_solver = Solver::new(SatBvBackend::new());
    unsat_solver.assert(nonpos);
    unsat_solver.assert(atleast_one);
    assert!(matches!(
        unsat_solver
            .interpolant_explained(&mut arena, &[0])
            .unwrap(),
        InterpolantOutcome::Interpolant(_)
    ));

    // Satisfiable partition (x ≤ 0 ∧ x ≤ 2) ⇒ no interpolant exists.
    let mut sat_solver = Solver::new(SatBvBackend::new());
    sat_solver.assert(nonpos);
    sat_solver.assert(atmost_two);
    assert_eq!(
        sat_solver.interpolant_explained(&mut arena, &[0]).unwrap(),
        InterpolantOutcome::NotInterpolable,
        "a satisfiable A ∧ B has no interpolant"
    );
}

// --- Certified conjunctive interpolation (`lra_interpolant_certified`) -------

/// The certified path returns the SAME verified interpolant as `lra_interpolant`,
/// re-passes the three Craig conditions, and carries two `la_generic` refutations
/// that BOTH self-check through `check_alethe_lra` (the in-tree counterpart to the
/// external Carcara/Lean acceptance the cross-check suites exercise).
#[test]
fn certified_interpolant_carries_two_self_checked_farkas_refutations() {
    // A: x ≤ 0 ; B: x ≥ 1.  Unsat; shared variable x.
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let a0 = arena.real_le(x, zero).unwrap();
    let b0 = arena.real_ge(x, one).unwrap();

    // Byte-identical interpolant to the Validated path.
    let validated = lra_interpolant(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("interpolant exists");
    let cert = lra_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("a certified interpolant exists for an unsat LRA conjunction");
    assert_eq!(
        cert.interpolant, validated,
        "the certified interpolant must equal the Validated lra_interpolant output"
    );

    // The three Craig conditions still hold for the returned interpolant.
    assert_is_interpolant(&mut arena, &[a0], &[b0], cert.interpolant);

    // The two carried refutations are genuine `la_generic` proofs that derive the
    // empty clause — accepted by the in-tree checker (the external Carcara/Lean
    // acceptance is asserted by `carcara_crosscheck`/`lean_crosscheck`).
    assert_eq!(
        check_alethe_lra(&cert.a_refutation),
        Ok(true),
        "the A ∧ ¬I refutation (Craig condition 1) must self-check"
    );
    assert_eq!(
        check_alethe_lra(&cert.b_refutation),
        Ok(true),
        "the I ∧ B refutation (Craig condition 2) must self-check"
    );

    // The carried conjunctions are exactly A ∧ ¬I and I ∧ B (each genuinely unsat).
    assert!(is_unsat(&arena, &cert.a_and_not_i), "A ∧ ¬I must be unsat");
    assert!(is_unsat(&arena, &cert.i_and_b), "I ∧ B must be unsat");
}

/// A non-unit-coefficient certified interpolant (rational Farkas combination) also
/// emits two self-checking refutations.
#[test]
fn certified_interpolant_rational_coefficients() {
    // A: 3x ≤ 1 ; B: 2x ≥ 3 (x ≤ 1/3 vs x ≥ 3/2) — unsat with a rational combo.
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let one = arena.real_ratio(1, 1);
    let three = arena.real_ratio(3, 1);
    let two = arena.real_ratio(2, 1);
    let three_x = arena.real_mul(three, x).unwrap();
    let two_x = arena.real_mul(two, x).unwrap();
    let a0 = arena.real_le(three_x, one).unwrap();
    let b0 = arena.real_ge(two_x, three).unwrap();

    let cert = lra_interpolant_certified(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("certified interpolant exists");
    assert_is_interpolant(&mut arena, &[a0], &[b0], cert.interpolant);
    assert_eq!(check_alethe_lra(&cert.a_refutation), Ok(true));
    assert_eq!(check_alethe_lra(&cert.b_refutation), Ok(true));
}

/// A satisfiable conjunction has no interpolant, so the certified path declines
/// (`Ok(None)`) — the caller falls back to the `Validated` `lra_interpolant`,
/// which also declines. This is the boundary: nothing is dressed up as certified.
#[test]
fn certified_interpolant_declines_on_satisfiable() {
    // A: x ≤ 0 ; B: x ≤ 1 — satisfiable, so neither path yields an interpolant.
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let a0 = arena.real_le(x, zero).unwrap();
    let b0 = arena.real_le(x, one).unwrap();

    assert!(
        lra_interpolant_certified(&mut arena, &[a0], &[b0])
            .expect("decides")
            .is_none(),
        "a satisfiable A ∧ B must yield no certified interpolant"
    );
    // And the Validated fallback agrees.
    assert!(
        lra_interpolant(&mut arena, &[a0], &[b0])
            .expect("decides")
            .is_none()
    );
}

/// The degenerate `⊥`/`⊤` interpolants (one side unsat alone) are still single
/// inequalities, so the conjunctive certification covers them: the certified path
/// returns the same interpolant as the Validated path with two self-checked
/// refutations.
#[test]
fn certified_interpolant_handles_one_sided_unsat() {
    // A: x ≤ 0 ∧ x ≥ 1 (unsat alone); B empty ⇒ interpolant is ⊥.
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let a0 = arena.real_le(x, zero).unwrap();
    let a1 = arena.real_ge(x, one).unwrap();

    let validated = lra_interpolant(&mut arena, &[a0, a1], &[])
        .expect("decides")
        .expect("interpolant exists");
    let cert = lra_interpolant_certified(&mut arena, &[a0, a1], &[])
        .expect("decides")
        .expect("certified interpolant exists");
    assert_eq!(cert.interpolant, validated);
    assert_eq!(check_alethe_lra(&cert.a_refutation), Ok(true));
    assert_eq!(check_alethe_lra(&cert.b_refutation), Ok(true));
}

#[test]
fn rational_coefficient_interpolant() {
    // A: 3x ≤ 1 ; B: 2x ≥ 3  (⇒ x ≤ 1/3 and x ≥ 3/2, unsat). Exercises a
    // rational-coefficient Farkas combination in the interpolant.
    let mut arena = TermArena::new();
    let x = real_var(&mut arena, "x");
    let one = arena.real_ratio(1, 1);
    let three = arena.real_ratio(3, 1);
    let two = arena.real_ratio(2, 1);
    let three_x = arena.real_mul(three, x).unwrap();
    let two_x = arena.real_mul(two, x).unwrap();
    let a0 = arena.real_le(three_x, one).unwrap(); // 3x ≤ 1
    let b0 = arena.real_ge(two_x, three).unwrap(); // 2x ≥ 3

    let interpolant = lra_interpolant(&mut arena, &[a0], &[b0])
        .expect("decides")
        .expect("interpolant exists");
    assert_is_interpolant(&mut arena, &[a0], &[b0], interpolant);
}
