//! What it would take to let a `> i128` witness out of the simplex — measured,
//! not argued (roadmap item 2.3,
//! `docs/solver-comparison-2026-09/11-roadmap-and-plan.md`).
//!
//! `simplex.rs`'s `narrow` refuses to hand back a feasible point when any
//! coordinate has been promoted past `i128`, and the query then answers
//! `unknown` even though a model exists. Yices2, `OpenSMT` and `SMTInterpol` all
//! keep growing the number instead
//! (`docs/solver-comparison-2026-09/05-yices-opensmt-smtinterpol.md`), so the
//! boundary is a genuine capability gap and the roadmap asks for it to be
//! opened. The decline itself is pinned next to the code, in `simplex.rs`'s
//! `the_witness_boundary_discards_an_exact_model_that_exceeds_i128`.
//!
//! This file pins the two things that must be true DOWNSTREAM before that
//! boundary can be opened, and neither is true today:
//!
//! 1. the ground evaluator — the trust anchor every `sat` replays through —
//!    must be able to evaluate the original assertions under a wide model. It
//!    cannot: `Rational`'s declining `checked_*` family computes exactly and
//!    then demotes, so it returns `None` for **any** result outside `i128`,
//!    even `x + 0` when `x` is promoted;
//! 2. no consumer of the model may call `Rational::numerator()` /
//!    `denominator()`, which panic on a promoted value. `auto.rs`'s `milp_bnb`
//!    does (`:2537`, `:2570`) and so does `smtlib_value_text`
//!    (`smtlib.rs:3904`), which is the `get-model` / `get-value` path — so
//!    today a wide model could not even be printed.
//!
//! Each test below FAILS when its blocker is removed. That is deliberate: this
//! file is the trip-wire saying item 2.3 has become landable, and the lane that
//! lands it updates these tests together with the boundary.

#![cfg(feature = "full")]

use axeyum_ir::{Assignment, IrError, Rational, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, check_with_lra};

/// `x_i = 2 * x_{i+1}` for `i` in `0..n-1`, plus `x_{n-1} >= 1`.
///
/// Satisfiable, with the unique vertex `x_j = 2^(n-1-j)`. Every coefficient and
/// constant in the query is a small integer, so nothing about the INPUT is out
/// of range — only the answer is. This is the same system the `simplex.rs` unit
/// test builds directly against the tableau.
fn doubling_chain(n: usize) -> (TermArena, Vec<SymbolId>, Vec<TermId>) {
    let mut arena = TermArena::new();
    let syms: Vec<SymbolId> = (0..n)
        .map(|i| {
            arena
                .declare(&format!("x{i}"), Sort::Real)
                .expect("fresh symbol")
        })
        .collect();
    let vars: Vec<TermId> = syms.iter().map(|&s| arena.var(s)).collect();
    let two = arena.real_ratio(2, 1);
    let one = arena.real_ratio(1, 1);
    let mut assertions = Vec::with_capacity(n);
    for i in 0..(n - 1) {
        let doubled = arena.real_mul(two, vars[i + 1]).expect("linear product");
        assertions.push(arena.eq(vars[i], doubled).expect("real equality"));
    }
    assertions.push(arena.real_ge(vars[n - 1], one).expect("real bound"));
    (arena, syms, assertions)
}

/// `2^k` as an exact rational, built by the promoting family so the fixture
/// itself never depends on `i128` range.
fn pow2(k: u32) -> Rational {
    let mut acc = Rational::integer(1);
    for _ in 0..k {
        acc = acc.wide_add(acc).expect("big-rational pool has room");
    }
    acc
}

/// **Blocker 1.** The evaluator cannot replay a wide-real model, so opening the
/// simplex boundary on its own would turn one `unknown` into a different one.
///
/// The assignment here is the exact vertex the tableau finds. Assertion 0 is
/// `x_0 = 2 * x_1` with `x_1 = 2^129`; the product `2^130` does not fit `i128`,
/// so `Rational::checked_mul` declines and `eval` reports `ArithmeticOverflow`
/// rather than a Boolean.
///
/// The bound is checked first on purpose. It replays fine, because `checked_cmp`
/// IS exact on promoted values — so this test cannot be read as "wide rationals
/// are unusable"; the gap is specifically arithmetic, and specifically the
/// declining family's demote-or-`None` contract.
#[test]
fn the_evaluator_declines_a_wide_real_model_it_should_be_able_to_replay() {
    const N: usize = 131;
    let (arena, syms, assertions) = doubling_chain(N);

    let mut assignment = Assignment::new();
    for (i, &s) in syms.iter().enumerate() {
        let exponent = u32::try_from(N - 1 - i).expect("exponent fits u32");
        assignment.set(s, Value::Real(pow2(exponent)));
    }

    assert_eq!(
        eval(&arena, assertions[N - 1], &assignment),
        Ok(Value::Bool(true)),
        "comparison is exact on promoted values, so `x_130 >= 1` must replay"
    );

    match eval(&arena, assertions[0], &assignment) {
        Err(IrError::ArithmeticOverflow { op }) => assert_eq!(
            op, "real_mul",
            "the decline must come from the product 2 * 2^129, not from elsewhere"
        ),
        other => panic!(
            "blocker 1 is gone: the evaluator replayed a wide-real model ({other:?}). \
             Roadmap item 2.3 is now landable on this axis — open `narrow` in \
             `simplex.rs` for the witness path and update this test."
        ),
    }
}

/// The negative control for blocker 1, and a finding in its own right: **the
/// `sat` replay cannot currently tell a correct wide witness from a corrupt
/// one.** It rejects both, with the identical error.
///
/// The obvious way to test a widened model path is to corrupt a coordinate and
/// watch the replay catch it. Run today, that check is vacuous: `eval` declines
/// on the arithmetic before it ever compares anything, so a *correct* `2^130`
/// and a deliberately wrong `2^131` produce the same
/// `ArithmeticOverflow { op: "real_mul" }`. That is sound — a decline is
/// `unknown`, never a wrong `sat` — but it means the replay contributes **no**
/// discrimination on this axis, and any future "the replay catches a corrupted
/// wide witness" claim must be re-measured after the evaluator is widened, not
/// inherited from here.
///
/// When blocker 1 is removed this test fails, and the assertion that replaces
/// it is the one that matters: correct ⇒ `Bool(true)`, corrupt ⇒ `Bool(false)`.
#[test]
fn the_replay_check_cannot_distinguish_a_correct_wide_witness_from_a_corrupt_one() {
    const N: usize = 131;
    let (arena, syms, assertions) = doubling_chain(N);

    let mut correct = Assignment::new();
    for (i, &s) in syms.iter().enumerate() {
        let exponent = u32::try_from(N - 1 - i).expect("exponent fits u32");
        correct.set(s, Value::Real(pow2(exponent)));
    }

    // Same vertex with `x_0` doubled: `x_0 = 2 * x_1` is now FALSE.
    let mut corrupt = correct.clone();
    corrupt.set(syms[0], Value::Real(pow2(131)));

    let on_correct = eval(&arena, assertions[0], &correct);
    let on_corrupt = eval(&arena, assertions[0], &corrupt);
    assert_eq!(
        on_correct, on_corrupt,
        "if these now differ, the replay has gained discrimination on wide \
         witnesses — that is the good outcome; assert `Bool(true)` vs \
         `Bool(false)` here instead"
    );
    assert_eq!(
        on_correct,
        Err(IrError::ArithmeticOverflow { op: "real_mul" }),
        "and today both are the same decline, so the guard is blind, not strict"
    );
}

/// **Blocker 2.** A model consumer that reads `numerator()` panics on exactly
/// the value the simplex would hand out.
///
/// Three shipped call sites have this shape on values taken straight from an
/// LRA model: `auto.rs:2537` (`q.numerator().div_euclid(q.denominator())`),
/// `auto.rs:2570` (`Value::Int(q.numerator())`) and `smtlib.rs:3904`
/// (`smtlib_value_text`, the `get-model` / `get-value` path). All three belong
/// to other lanes, so the hazard is pinned here rather than fixed there.
///
/// The `is_integer()` line is the load-bearing one: `auto.rs:2570` guards on it
/// and the guard PASSES for a promoted integer, so it protects nothing.
#[test]
#[should_panic(expected = "rational numerator exceeds i128")]
fn a_model_consumer_that_reads_numerator_panics_on_the_witness() {
    let witness = pow2(130);
    assert!(witness.is_big(), "2^130 is outside the i128 fast path");
    assert!(
        witness.is_integer(),
        "and `is_integer()` is true, so the `milp_bnb` guard does not stop it"
    );
    let _ = witness.numerator();
}

/// The end-to-end consequence today: a satisfiable query answers `unknown`.
///
/// Item 2.3's exit criterion inverts this — it asks for `sat` with a model that
/// replays. Note the reported reason is Fourier–Motzkin's budget, not the
/// simplex's: on a 131-variable system the elimination also gives up, and its
/// refusal is the one `lra::decide_within` reports last. So this test pins the
/// user-visible verdict, and the `simplex.rs` unit test pins the `narrow`
/// decline that sits behind it. Neither substitutes for the other.
#[test]
fn the_front_door_answers_unknown_on_a_satisfiable_wide_witness_query() {
    const N: usize = 131;
    let (arena, _syms, assertions) = doubling_chain(N);
    match check_with_lra(&arena, &assertions) {
        Ok(CheckResult::Unknown(reason)) => {
            eprintln!("check_with_lra -> unknown: {reason:?}");
        }
        other => panic!(
            "the wide-witness query no longer answers `unknown` ({other:?}). \
             If it is now `sat`, confirm the model replays against the ORIGINAL \
             assertions before believing it, and update roadmap item 2.3."
        ),
    }
}
