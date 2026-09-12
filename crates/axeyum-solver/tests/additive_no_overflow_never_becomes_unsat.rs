//! Soundness-negative for the ADDITIVE no-overflow side-constraint (ADR-1937).
//!
//! `blast_integers` may be armed
//! (`AXEYUM_INT_BLAST_ADDITIVE_NO_OVERFLOW=1`, or explicitly through
//! `blast_integers_with_additive_no_overflow`) to conjoin a no-overflow
//! constraint onto every `int_add`/`int_sub`/`int_neg`, the way it already does
//! for `int_mul`. That is a **strengthening** of the bit-vector query, and a
//! strengthened query can be UNSAT where the original integer problem is SAT.
//!
//! So the whole soundness of arming it rests on one property of the consumer:
//! **a bit-vector `Unsat` with integers present must be reported as `unknown`,
//! never as an integer `unsat`.**
//!
//! The two tests here are the two halves of that, and neither is worth anything
//! without the other:
//!
//! 1. the hazard is REAL — the armed encoding genuinely refutes, at width 6, a
//!    query that is satisfiable over the integers, and the unarmed encoding does
//!    not. A "never transfers" test over a refutation nothing produces cannot
//!    fail.
//! 2. the consumer NEVER transfers such a refutation.
//!
//! # No environment variable anywhere in this file
//!
//! The lever resolves once per process through a `OnceLock`
//! (`axeyum_ir::cap_lever!`), so a test that sets it is a test of whichever test
//! read it first — and `unsafe_code` is denied workspace-wide, so a test cannot
//! set it at all. Both tests therefore drive
//! `blast_integers_with_additive_no_overflow`, which takes the flag as an
//! argument. That entry point exists for exactly this reason.
//!
//! `check_with_all_theories` is exported only under `full`, so this suite is
//! gated on it. CONFIRM A NONZERO TEST COUNT (2) when running it: without the
//! feature this file compiles to an empty binary that prints
//! "running 0 tests ... ok" and exits 0.
#![cfg(feature = "full")]

use axeyum_ir::{Sort, TermArena, TermId};
use axeyum_rewrite::blast_integers_with_additive_no_overflow;
use axeyum_solver::{
    CheckResult, SatBvBackend, SolverBackend, SolverConfig, check_with_all_theories,
};

/// The bit-blast width every test here uses. Signed range `[-32, 31]`, chosen
/// so every CONSTANT in the fixtures fits (a constant that does not is a hard
/// `ConstantOutOfRange` before any solving happens) while the SUMS and PRODUCTS
/// do not — which is the whole point.
const W: u32 = 6;

/// `x > 20 ∧ y > 20 ∧ x + y ≠ 0` — satisfiable over the integers at
/// `x = y = 21` (sum 42), and purely ADDITIVE, so the shipped (`int_mul`-only)
/// blaster constrains nothing in it. At width 6 every admissible sum (42..=62)
/// wraps to a NEGATIVE value, which is still non-zero, so the unarmed blast is
/// satisfiable and the armed one is not.
fn additive_and_satisfiable(arena: &mut TermArena) -> Vec<TermId> {
    let xs = arena.declare("x", Sort::Int).unwrap();
    let ys = arena.declare("y", Sort::Int).unwrap();
    let (x, y) = (arena.var(xs), arena.var(ys));
    let twenty = arena.int_const(20);
    let zero = arena.int_const(0);
    let sum = arena.int_add(x, y).unwrap();
    let is_zero = arena.eq(sum, zero).unwrap();
    vec![
        arena.int_gt(x, twenty).unwrap(),
        arena.int_gt(y, twenty).unwrap(),
        arena.not(is_zero).unwrap(),
    ]
}

/// `x > 5 ∧ y > 5 ∧ x * y ≠ 0` — satisfiable over the integers at `x = y = 6`
/// (product 36), and refuted at width 6 by the no-overflow constraint the
/// blaster has ALWAYS emitted for `int_mul`. The consumer property is tested on
/// this one so it holds for the SHIPPED path, not only for an armed one.
fn multiplicative_and_satisfiable(arena: &mut TermArena) -> Vec<TermId> {
    let xs = arena.declare("x", Sort::Int).unwrap();
    let ys = arena.declare("y", Sort::Int).unwrap();
    let (x, y) = (arena.var(xs), arena.var(ys));
    let five = arena.int_const(5);
    let zero = arena.int_const(0);
    let prod = arena.int_mul(x, y).unwrap();
    let is_zero = arena.eq(prod, zero).unwrap();
    vec![
        arena.int_gt(x, five).unwrap(),
        arena.int_gt(y, five).unwrap(),
        arena.not(is_zero).unwrap(),
    ]
}

fn solve_blasted(arena: &mut TermArena, assertions: &[TermId], additive: bool) -> CheckResult {
    let blast = blast_integers_with_additive_no_overflow(arena, assertions, W, additive).unwrap();
    let blasted = blast.assertions().to_vec();
    let mut backend = SatBvBackend::new();
    backend
        .check(arena, &blasted, &SolverConfig::default())
        .unwrap()
}

/// Half one: the hazard is real. Arming the additive constraint turns a
/// bit-vector query that WAS satisfiable at width 6 into one that is not, for
/// an integer query that is satisfiable over the integers.
///
/// Without this, the "never transfers" test below would be a claim about a
/// refutation nothing produces.
#[test]
fn arming_the_additive_constraint_refutes_a_satisfiable_integer_query_at_width_6() {
    let mut arena = TermArena::new();
    let assertions = additive_and_satisfiable(&mut arena);

    let unarmed = solve_blasted(&mut arena, &assertions, false);
    assert!(
        matches!(unarmed, CheckResult::Sat(_)),
        "control: without the additive constraint the width-6 blast is satisfiable \
         (x = y = 21, the sum wraps to a negative value); got {unarmed:?}",
    );

    let armed = solve_blasted(&mut arena, &assertions, true);
    assert!(
        matches!(armed, CheckResult::Unsat),
        "the additive constraint must forbid the wrapping sum at width 6; got {armed:?}",
    );
}

/// Half two: the consumer never turns a bounded bit-vector refutation into an
/// integer `unsat`. Deleting the `has_integers` arm in `combined.rs` makes this
/// answer `unsat` to a query that is satisfiable over the integers.
#[test]
fn a_bounded_bit_vector_refutation_is_reported_unknown_and_never_unsat() {
    let mut arena = TermArena::new();
    let assertions = multiplicative_and_satisfiable(&mut arena);

    // Control: the width-6 bit-vector query really is refuted, so the arm under
    // test is actually reached.
    let raw = solve_blasted(&mut arena, &assertions, false);
    assert!(
        matches!(raw, CheckResult::Unsat),
        "control: the shipped `int_mul` no-overflow constraint must refute this at \
         width 6, or the consumer arm below is never entered; got {raw:?}",
    );

    let mut backend = SatBvBackend::new();
    let result = check_with_all_theories(
        &mut backend,
        &mut arena,
        &assertions,
        W,
        &SolverConfig::default(),
    )
    .unwrap();
    match result {
        CheckResult::Unsat => panic!(
            "WRONG UNSAT: `x > 5 and y > 5 and x * y != 0` is satisfiable over the integers \
             (x = y = 6). A bounded bit-vector refutation — especially one produced by a \
             STRENGTHENING no-overflow side-constraint — must never transfer.",
        ),
        CheckResult::Unknown(reason) => assert!(
            reason.detail.contains("bounded integer width"),
            "the decline must name the bound it could not see past: {reason:?}",
        ),
        CheckResult::Sat(model) => panic!(
            "unexpected `sat` at width 6 for a query the bit-vector layer refutes: {model:?}",
        ),
    }
}
