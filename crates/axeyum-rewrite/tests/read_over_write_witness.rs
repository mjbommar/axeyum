//! The read-over-write faithfulness witness (ADR-1721 §7).
//!
//! `eliminate_arrays` does two things and they owe different evidence. The
//! **Ackermann** half *adds* constraints, so it can only break `unsat`, and
//! `ArrayElimUnsatCertificate::recheck` already discharges it: the appended
//! congruence set is rebuilt by an independent implementation of one schema, so
//! a spurious extra constraint is caught. The **read-over-write** half is a
//! *replacement*, so it can break both directions — and `recheck` only
//! re-derives it, by re-running the same `resolve_select` on the same input.
//!
//! Measured 2026-09-06 on this lane's isolated worktree: with the `Op::Store`
//! arm's `ite` branches swapped, `recheck` returns `Ok(true)` over the
//! satisfiable query `i ≠ j ∧ select(store(a,i,e),j) ≠ e`, which the mutation
//! turns into `e ≠ e`. Three of eight tests in
//! `crates/axeyum-solver/tests/array_elim_unsat_proofs.rs` died, and only one of
//! the three — the anchor added for that measurement — exhibited the dangerous
//! direction (a wrong `unsat` with a passing certificate); the other two failed
//! because the producer stopped producing on genuinely-`unsat` fixtures.
//!
//! [`witness_read_over_write`] is the independent reference that closes it. It
//! does not re-run the transform. It interprets both sides under one concrete
//! assignment — arrays as real `ArrayValue` maps, each abstracted select symbol
//! bound to the element the sampled array holds at the evaluated index — and
//! compares the values. The original assertion is evaluated by the ground
//! evaluator's array semantics, which never touch `resolve_select`. That is the
//! same shape as `crates/axeyum-fp/tests/fpa2bv_faithfulness.rs`, the pattern
//! this repository already proved on this defect class.

use axeyum_ir::{TermArena, TermId};
use axeyum_rewrite::{READ_OVER_WRITE_WITNESS_SAMPLES, eliminate_arrays, witness_read_over_write};

/// `i = j ∧ select(store(a, i, e), j) ≠ e` — the shape whose read-over-write is
/// load-bearing (the rewrite is what makes it refutable at all).
fn store_select_query(arena: &mut TermArena) -> Vec<TermId> {
    let a = arena.array_var("a", 3, 4).unwrap();
    let i = arena.bv_var("i", 3).unwrap();
    let j = arena.bv_var("j", 3).unwrap();
    let e = arena.bv_var("e", 4).unwrap();
    let stored = arena.store(a, i, e).unwrap();
    let read = arena.select(stored, j).unwrap();
    let i_eq_j = arena.eq(i, j).unwrap();
    let read_ne_e = {
        let eq = arena.eq(read, e).unwrap();
        arena.not(eq).unwrap()
    };
    vec![i_eq_j, read_ne_e]
}

/// POSITIVE CONTROL. The shipped read-over-write is faithful, and the witness
/// says so having actually examined something — `compared` is the number of
/// `(sample, assertion)` pairs it evaluated, and the assertion below pins it to
/// the full grid rather than accepting a run that quietly examined nothing.
#[test]
fn witness_accepts_the_shipped_read_over_write() {
    let mut arena = TermArena::new();
    let assertions = store_select_query(&mut arena);
    let elim = eliminate_arrays(&mut arena, &assertions).unwrap();
    assert!(elim.had_arrays());

    let witness =
        witness_read_over_write(&arena, &assertions, &elim, READ_OVER_WRITE_WITNESS_SAMPLES);

    assert_eq!(
        witness.disagreement, None,
        "the shipped read-over-write must be faithful"
    );
    assert_eq!(
        witness.compared,
        READ_OVER_WRITE_WITNESS_SAMPLES * assertions.len(),
        "every (sample, assertion) pair must be compared, not skipped"
    );
    assert_eq!(witness.unavailable, 0);
    assert!(witness.is_faithful());
}

/// NEGATIVE CONTROL — the witness can reach `Disagreed`.
///
/// A witness that structurally cannot report a disagreement would pass the test
/// above forever, so this hands it an original whose meaning is the *negation*
/// of what the elimination abstracted. Both sides evaluate; they must differ.
/// This is the analogue of `cert_against_different_formula_is_rejected` in the
/// solver's certificate suite: the checker is confirmed to compare the two sides
/// rather than to agree by construction.
#[test]
fn witness_rejects_an_original_that_is_not_what_was_abstracted() {
    let mut arena = TermArena::new();
    let assertions = store_select_query(&mut arena);
    // A second "original" of the same length whose second assertion is the
    // negation of the real one. Built before elimination so its `TermId`s are
    // valid in the same arena.
    let negated = arena.not(assertions[1]).unwrap();
    let mismatched = vec![assertions[0], negated];

    let elim = eliminate_arrays(&mut arena, &assertions).unwrap();
    let witness =
        witness_read_over_write(&arena, &mismatched, &elim, READ_OVER_WRITE_WITNESS_SAMPLES);

    let disagreement = witness
        .disagreement
        .as_ref()
        .expect("a negated original must disagree with the abstraction");
    assert_eq!(
        disagreement.assertion, 1,
        "the disagreement must be reported at the assertion that was negated"
    );
    assert_ne!(disagreement.original, disagreement.abstracted);
    assert!(!witness.is_faithful());
}

/// VACUITY CONTROL. An array-free query gives the witness nothing to examine,
/// and `compared == 0` must NOT read as a pass — otherwise every query outside
/// the fragment would silently "witness" faithfulness.
#[test]
fn an_empty_witness_is_not_a_pass() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let assertions = vec![arena.eq(x, zero).unwrap()];
    let elim = eliminate_arrays(&mut arena, &assertions).unwrap();
    assert!(!elim.had_arrays());

    let witness =
        witness_read_over_write(&arena, &assertions, &elim, READ_OVER_WRITE_WITNESS_SAMPLES);

    assert_eq!(witness.compared, 0);
    assert_eq!(witness.disagreement, None);
    assert!(
        !witness.is_faithful(),
        "a witness that examined nothing has not witnessed anything"
    );
}

/// The sample sequence is a public API promise (determinism), so two runs over
/// the same query must produce byte-identical witnesses.
#[test]
fn the_witness_is_deterministic() {
    let mut first_arena = TermArena::new();
    let first_assertions = store_select_query(&mut first_arena);
    let first_elim = eliminate_arrays(&mut first_arena, &first_assertions).unwrap();
    let first = witness_read_over_write(
        &first_arena,
        &first_assertions,
        &first_elim,
        READ_OVER_WRITE_WITNESS_SAMPLES,
    );

    let mut second_arena = TermArena::new();
    let second_assertions = store_select_query(&mut second_arena);
    let second_elim = eliminate_arrays(&mut second_arena, &second_assertions).unwrap();
    let second = witness_read_over_write(
        &second_arena,
        &second_assertions,
        &second_elim,
        READ_OVER_WRITE_WITNESS_SAMPLES,
    );

    assert_eq!(first, second);
}
