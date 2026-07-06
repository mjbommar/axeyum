//! A3 (direction A frontier): **MIR-text reflection prototype**. Parse the real
//! compiled MIR of a Rust function into an `axeyum-ir` term over symbolic inputs,
//! and exhaustively cross-check that the reflected term computes the *same*
//! function as the real Rust — i.e. we reflected the *compiled* semantics (what
//! the CPU runs) into the solver's IR, faithfully.
//!
//! Design + feasibility: `docs/consumer-track/verify/real-rust-frontend.md`.
//! The reflector itself lives in `axeyum_verify::reflect::mir` — the same one the
//! cross-IR equivalence suite uses (`cross_ir_equivalence.rs`), over the same op
//! vocabulary as the LLVM front end. This file is the MIR-side fixtures + the
//! reflect-then-{enumerate,prove} tests.
//!
//! **Prototype scope, honestly:** the MIR comes from a *committed fixture*
//! (captured once via `rustc --crate-type=lib -Zunpretty=mir`, rustc 1.96-nightly)
//! — NOT invoked at test time, because `-Zunpretty` is nightly-only and CI runs
//! stable/MSRV; a fixture keeps this test toolchain-independent. The MIR text
//! format is explicitly unstable (rustc prints that warning) — regenerate the
//! fixture if it drifts. This is a proof-of-concept that the MIR pipeline is
//! real, not a maintained front end (that is the deferred `stable_mir` path).

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, Value};
use axeyum_solver::ProofOutcome;

use axeyum_verify::reflect::mir::reflect_mir_unary;
use axeyum_verify::reflect::{eval_bv, is_proved, prove_goal};

/// The real Rust function. Its compiled MIR (below) is what we reflect; the
/// function itself is the reference oracle for the exhaustive cross-check.
fn lut(x: u8) -> u8 {
    match x {
        0 => 5,
        1 => 7,
        _ => 0,
    }
}

/// Committed `rustc --crate-type=lib -Zunpretty=mir lut.rs` output (rustc 1.96).
const LUT_MIR: &str = r"
fn lut(_1: u8) -> u8 {
    debug x => _1;
    let mut _0: u8;

    bb0: {
        switchInt(copy _1) -> [0: bb3, 1: bb2, otherwise: bb1];
    }

    bb1: {
        _0 = const 0_u8;
        goto -> bb4;
    }

    bb2: {
        _0 = const 7_u8;
        goto -> bb4;
    }

    bb3: {
        _0 = const 5_u8;
        goto -> bb4;
    }

    bb4: {
        return;
    }
}
";

/// A wider real function: `fn lut32(u32)->u32` with five arms. Exhaustive
/// evaluation over its 2^32 inputs is infeasible — but the reflected term is
/// proven symbolically. Committed `-Zunpretty=mir` output (rustc 1.96).
const LUT32_MIR: &str = r"
fn lut32(_1: u32) -> u32 {
    debug x => _1;
    let mut _0: u32;

    bb0: {
        switchInt(copy _1) -> [0: bb5, 1: bb4, 100: bb3, 65535: bb2, otherwise: bb1];
    }

    bb1: {
        _0 = const 0_u32;
        goto -> bb6;
    }

    bb2: {
        _0 = const 3_u32;
        goto -> bb6;
    }

    bb3: {
        _0 = const 9_u32;
        goto -> bb6;
    }

    bb4: {
        _0 = const 7_u32;
        goto -> bb6;
    }

    bb5: {
        _0 = const 5_u32;
        goto -> bb6;
    }

    bb6: {
        return;
    }
}
";

/// Reflect a fixture into a fresh arena over a symbolic input `x` of the given
/// width, via the **shared** `axeyum_verify::reflect::mir` reflector.
fn reflect_mir(mir: &str, in_w: u32) -> (TermArena, SymbolId, TermId) {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(in_w)).unwrap();
    let x = arena.var(x_sym);
    let term = reflect_mir_unary(&mut arena, x, mir);
    (arena, x_sym, term)
}

/// Evaluate the reflected term `T(x)` at a concrete `a`.
fn eval_at(arena: &TermArena, sym: SymbolId, term: TermId, a: u8) -> u128 {
    let mut asg = Assignment::new();
    asg.set(
        sym,
        Value::Bv {
            width: 8,
            value: u128::from(a),
        },
    );
    eval_bv(arena, term, &asg)
}

/// The term reflected from `lut`'s real compiled MIR computes **exactly** `lut`
/// on all 256 inputs — the reflection of the compiled semantics into the IR is
/// faithful (verified by exhaustive evaluation against the real Rust oracle).
#[test]
fn mir_reflected_term_matches_real_rust_on_all_inputs() {
    let (arena, sym, term) = reflect_mir(LUT_MIR, 8);
    for a in 0..=u8::MAX {
        assert_eq!(
            eval_at(&arena, sym, term, a),
            u128::from(lut(a)),
            "MIR-reflected term diverged from real Rust at x={a}"
        );
    }
}

/// A property of the reflected real-compiled code, established over the full
/// domain by the same exhaustive evaluation: `lut`'s result is always one of
/// {0,5,7} — in particular `<= 7`. (For this tiny prototype, exhaustive eval *is*
/// the all-inputs proof; larger functions are the symbolic-solver path.)
#[test]
fn mir_reflected_term_satisfies_a_range_property() {
    let (arena, sym, term) = reflect_mir(LUT_MIR, 8);
    for a in 0..=u8::MAX {
        assert!(
            eval_at(&arena, sym, term, a) <= 7,
            "reflected lut exceeded its range at x={a}"
        );
    }
}

/// Scale past enumeration: reflect the `u32` lookup (2^32 inputs — exhaustive
/// eval is infeasible) and **prove symbolically** that its result is always
/// `<= 9`, for ALL inputs, via the solver. This is the payoff of
/// reflect-then-prove over reflect-then-enumerate, on real compiled Rust.
#[test]
fn mir_reflected_u32_term_proved_symbolically() {
    let (mut arena, _sym, term) = reflect_mir(LUT32_MIR, 32);
    let bound = arena.bv_const(32, 9).unwrap();
    let goal = arena.bv_ule(term, bound).unwrap(); // T(x) <= 9
    assert!(
        is_proved(&mut arena, goal),
        "lut32(x) <= 9 must hold for ALL u32 inputs"
    );
}

/// The verifier catches a *false* claim about real compiled code: `lut32(x) <= 8`
/// is false (the `x == 100` arm returns 9), so the solver returns a `Disproved`
/// countermodel rather than a bogus proof.
#[test]
fn mir_reflected_u32_false_property_is_disproved() {
    let (mut arena, _sym, term) = reflect_mir(LUT32_MIR, 32);
    let bound = arena.bv_const(32, 8).unwrap();
    let goal = arena.bv_ule(term, bound).unwrap(); // T(x) <= 8  — FALSE (9 at x=100)
    let outcome = prove_goal(&mut arena, goal);
    assert!(
        matches!(outcome, ProofOutcome::Disproved(_)),
        "lut32(x) <= 8 is false (9 at x=100); expected Disproved, got {outcome:?}"
    );
}

/// Both oracles agree on the `u8` lookup: exhaustive evaluation (above) and the
/// symbolic solver proof reach the same conclusion (`lut(x) <= 7` for all x) —
/// enumeration and proof corroborate on the small case where both are feasible.
#[test]
fn mir_reflected_u8_eval_and_proof_agree() {
    let (mut arena, _sym, term) = reflect_mir(LUT_MIR, 8);
    let bound = arena.bv_const(8, 7).unwrap();
    let goal = arena.bv_ule(term, bound).unwrap();
    assert!(
        is_proved(&mut arena, goal),
        "lut(x) <= 7 must be proven (matching the exhaustive eval)"
    );
}
