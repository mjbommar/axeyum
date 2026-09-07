//! The Ackermann-abstraction faithfulness witness (ADR-1721 §7), ported from
//! `read_over_write_witness.rs` onto `eliminate_functions`.
//!
//! `eliminate_functions` does two things and they owe different evidence. The
//! **congruence** half only *adds* constraints, so it can break `unsat` alone,
//! and `AckermannUnsatCertificate::recheck` already discharges it: the appended
//! pairwise set is rebuilt from an independent implementation of one schema, so
//! a spurious extra constraint is caught. The **abstraction** half -- each
//! application `f(a…)` replaced by a fresh result-sort symbol -- is a
//! *replacement*, so it can break both directions, and `recheck` only
//! re-derives it by re-running the same producer on the same input.
//!
//! [`witness_function_abstraction`] is the independent reference that closes
//! it. It does not re-run the transform. It interprets both sides under one
//! concrete assignment -- each function given a real [`FuncValue`]
//! interpretation, each fresh symbol bound to what that interpretation returns
//! at the application's evaluated arguments -- and compares the values. The
//! original assertion is evaluated by the ground evaluator's `Op::Apply` arm,
//! which never touches this pass.

#![allow(clippy::many_single_char_names)]

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_rewrite::{
    FUNCTION_ABSTRACTION_WITNESS_SAMPLES, eliminate_functions, witness_function_abstraction,
};

/// The default must exceed the two corner samples, or
/// `the_two_corner_samples_alone_cannot_distinguish_applications` below is
/// comparing the default against itself. Checked at COMPILE time: as a runtime
/// `assert!` it is a constant expression, which clippy rejects and which would
/// be no weaker written this way.
const _: () = assert!(FUNCTION_ABSTRACTION_WITNESS_SAMPLES > 2);

/// `f(x) = c0 ∧ f(y) = c1 ∧ x = y` over 4-bit vectors — the shape whose
/// abstraction is load-bearing: it is refutable only through the fresh symbols
/// and the congruence between them.
fn uf_query(arena: &mut TermArena) -> Vec<TermId> {
    let bv4 = Sort::BitVec(4);
    let f = arena
        .declare_fun("f", &[bv4], bv4)
        .expect("declare function");
    let x = arena.bv_var("x", 4).unwrap();
    let y = arena.bv_var("y", 4).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let one = arena.bv_const(4, 1).unwrap();
    let two = arena.bv_const(4, 2).unwrap();
    let a = arena.eq(fx, one).unwrap();
    let b = arena.eq(fy, two).unwrap();
    let c = arena.eq(x, y).unwrap();
    vec![a, b, c]
}

/// POSITIVE CONTROL. The shipped abstraction is faithful, and the witness says
/// so having actually examined something -- `compared` is the number of
/// `(sample, assertion)` pairs it evaluated, pinned to the full grid so a run
/// that quietly examined nothing cannot pass as a run that agreed.
#[test]
fn witness_accepts_the_shipped_function_abstraction() {
    let mut arena = TermArena::new();
    let assertions = uf_query(&mut arena);
    let elim = eliminate_functions(&mut arena, &assertions).unwrap();
    assert!(elim.had_functions());

    let witness = witness_function_abstraction(
        &arena,
        &assertions,
        &elim,
        FUNCTION_ABSTRACTION_WITNESS_SAMPLES,
    );

    assert_eq!(
        witness.disagreement, None,
        "the shipped function abstraction must be faithful"
    );
    assert_eq!(
        witness.compared,
        FUNCTION_ABSTRACTION_WITNESS_SAMPLES * assertions.len(),
        "every (sample, assertion) pair must be compared, not skipped"
    );
    assert_eq!(witness.unavailable, 0);
    assert!(witness.is_faithful());
}

/// NEGATIVE CONTROL — the witness can reach a disagreement.
///
/// A witness that structurally cannot report one would pass the test above
/// forever, so this hands it an original whose meaning is the *negation* of
/// what the elimination abstracted. Both sides evaluate; they must differ.
#[test]
fn witness_rejects_an_original_that_is_not_what_was_abstracted() {
    let mut arena = TermArena::new();
    let assertions = uf_query(&mut arena);
    // A second "original" of the same length whose FIRST assertion is the
    // negation of the real one. Built before elimination so its `TermId`s are
    // valid in the same arena.
    let negated = arena.not(assertions[0]).unwrap();
    let mismatched = vec![negated, assertions[1], assertions[2]];

    let elim = eliminate_functions(&mut arena, &assertions).unwrap();
    let witness = witness_function_abstraction(
        &arena,
        &mismatched,
        &elim,
        FUNCTION_ABSTRACTION_WITNESS_SAMPLES,
    );

    let disagreement = witness
        .disagreement
        .as_ref()
        .expect("a negated original must disagree with the abstraction");
    assert_eq!(
        disagreement.assertion, 0,
        "the disagreement must be reported at the assertion that was negated"
    );
    assert_ne!(disagreement.original, disagreement.abstracted);
    assert!(!witness.is_faithful());
}

/// The witness must be sensitive to the abstraction CONFUSING two applications
/// of one function, which is the defect class `recheck`'s re-derivation cannot
/// see: a producer that bound `f(x)` and `f(y)` to ONE fresh symbol re-derives
/// to itself perfectly.
///
/// The fixture is `f(x) = f(y)`, whose abstraction is `fresh_fx = fresh_fy`.
/// Standing in for the mutation, the ORIGINAL handed to the witness is
/// `f(x) = f(x)` — what the query would mean if the two applications had been
/// confused. That is a tautology, while the abstraction holds only when the
/// sampled `f` happens to agree at `x` and at `y`. A witness blind to the
/// argument would report faithful.
///
/// Note the shape this fixes. An earlier version compared `f(y) = 2` against
/// `f(x) = 2` and PASSED WRONGLY: at most samples both sides are simply
/// `false`, and a disagreement needs the two BOOLEANS to differ, not the two
/// function values. A negative control can fail by being vacuous as easily as
/// by being inverted, and this one was vacuous until it was run.
#[test]
fn witness_is_sensitive_to_confusing_two_applications_of_one_function() {
    let mut arena = TermArena::new();
    let bv4 = Sort::BitVec(4);
    let f = arena.declare_fun("f", &[bv4], bv4).unwrap();
    let x = arena.bv_var("x", 4).unwrap();
    let y = arena.bv_var("y", 4).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let real = arena.eq(fx, fy).unwrap();
    let confused = arena.eq(fx, fx).unwrap();

    let assertions = vec![real];
    let elim = eliminate_functions(&mut arena, &assertions).unwrap();
    let witness = witness_function_abstraction(
        &arena,
        &[confused],
        &elim,
        FUNCTION_ABSTRACTION_WITNESS_SAMPLES,
    );
    assert!(
        witness.disagreement.is_some(),
        "an abstraction that named the wrong application must be caught"
    );
    assert!(!witness.is_faithful());
}

/// VACUITY CONTROL. A function-free query gives the witness nothing to examine,
/// and `compared == 0` must NOT read as a pass — otherwise every query outside
/// the fragment would silently "witness" faithfulness.
#[test]
fn an_empty_witness_is_not_a_pass() {
    let mut arena = TermArena::new();
    let x = arena.bv_var("x", 8).unwrap();
    let zero = arena.bv_const(8, 0).unwrap();
    let assertions = vec![arena.eq(x, zero).unwrap()];
    let elim = eliminate_functions(&mut arena, &assertions).unwrap();
    assert!(!elim.had_functions());

    let witness = witness_function_abstraction(
        &arena,
        &assertions,
        &elim,
        FUNCTION_ABSTRACTION_WITNESS_SAMPLES,
    );
    assert_eq!(witness.compared, 0);
    assert_eq!(witness.disagreement, None);
    assert!(
        !witness.is_faithful(),
        "an empty witness has witnessed nothing and must not report faithful"
    );
}

/// COVERAGE CONTROL for the sample count: the default is not a round number
/// chosen by taste.
///
/// Samples 0 and 1 are the all-zero and all-ones corners. There every symbol
/// holds the same value, so `x` and `y` are equal, so `f` is asked at ONE key
/// and the confused original agrees with the abstraction. A witness given only
/// those two samples reports faithful over a real defect. This test measures
/// that gap rather than asserting the constant is "enough".
#[test]
fn the_two_corner_samples_alone_cannot_distinguish_applications() {
    let mut arena = TermArena::new();
    let bv4 = Sort::BitVec(4);
    let f = arena.declare_fun("f", &[bv4], bv4).unwrap();
    let x = arena.bv_var("x", 4).unwrap();
    let y = arena.bv_var("y", 4).unwrap();
    let fx = arena.apply(f, &[x]).unwrap();
    let fy = arena.apply(f, &[y]).unwrap();
    let real = arena.eq(fx, fy).unwrap();
    let confused = arena.eq(fx, fx).unwrap();

    let assertions = vec![real];
    let elim = eliminate_functions(&mut arena, &assertions).unwrap();

    let corners = witness_function_abstraction(&arena, &[confused], &elim, 2);
    assert_eq!(corners.compared, 2, "both corner samples must be evaluated");
    assert!(
        corners.disagreement.is_none(),
        "the corners agree by construction -- this is the blind spot the default \
         sample count exists to cover"
    );

    let full = witness_function_abstraction(
        &arena,
        &[confused],
        &elim,
        FUNCTION_ABSTRACTION_WITNESS_SAMPLES,
    );
    assert!(
        full.disagreement.is_some(),
        "the pseudorandom samples are what give the witness teeth"
    );
}

/// The STRUCTURAL half: an original application the abstraction never named.
///
/// This exists because the value comparison alone was MEASURED to miss the
/// defect that matters most. With `eliminate_functions` mutated so every
/// application of one function shares one fresh symbol, the satisfiable
/// `f(a) = 1 & f(b) = 2` becomes a wrong `unsat` and
/// `AckermannUnsatCertificate::recheck` returned `Ok(true)` over it -- because
/// the two sides are compared as BOOLEANS, and `f(b) = 2` and `f(a) = 2` are
/// both simply `false` at almost every sample. Agreement on `false` is not
/// agreement, and a probabilistic check cannot be relied on to notice it.
///
/// The structural check does not depend on luck: a merged or dropped
/// application leaves an original `Op::Apply` with no entry at its evaluated
/// arguments. Here the abstraction is built from `f(a) = 1` alone while the
/// original also mentions `f(b)`, which is the shape the mutation produces.
#[test]
fn an_application_the_abstraction_never_named_is_a_finding() {
    let mut arena = TermArena::new();
    let bv8 = Sort::BitVec(8);
    let f = arena.declare_fun("f", &[bv8], bv8).unwrap();
    let a = arena.bv_var("a", 8).unwrap();
    let b = arena.bv_var("b", 8).unwrap();
    let fa = arena.apply(f, &[a]).unwrap();
    let fb = arena.apply(f, &[b]).unwrap();
    let one = arena.bv_const(8, 1).unwrap();
    let two = arena.bv_const(8, 2).unwrap();
    let named = arena.eq(fa, one).unwrap();
    let unnamed = arena.eq(fb, two).unwrap();

    // The elimination sees only the first assertion, so only `f(a)` is named.
    let elim = eliminate_functions(&mut arena, &[named]).unwrap();
    // The witness is handed an original that also mentions `f(b)`.
    let witness = witness_function_abstraction(
        &arena,
        &[unnamed],
        &elim,
        FUNCTION_ABSTRACTION_WITNESS_SAMPLES,
    );

    assert!(
        witness.unnamed_applications > 0,
        "an original application absent from the abstraction's own list must be counted"
    );
    assert!(
        !witness.is_faithful(),
        "is_faithful must fold in the structural count, not only the value comparison"
    );

    // CONTROL: the same elimination against the original it was actually built
    // from names every application, so the count above is about the missing
    // application and not about this check firing on everything.
    let clean = witness_function_abstraction(
        &arena,
        &[named],
        &elim,
        FUNCTION_ABSTRACTION_WITNESS_SAMPLES,
    );
    assert_eq!(clean.unnamed_applications, 0);
    assert!(clean.is_faithful());
}
