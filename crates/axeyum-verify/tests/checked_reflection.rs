//! **Panic-freedom from debug-profile MIR** — the symbolic-fuzzing story.
//!
//! Debug MIR carries rustc's own overflow checks (`AddWithOverflow` + `assert`).
//! The shared reflector (`reflect_common::mir::reflect_mir_into_checked`) turns
//! them into a Bool *panic-condition term*, so:
//!
//! - proving `panic == false` is a **panic-freedom proof** over ALL inputs —
//!   what a fuzzer approximates by sampling, discharged exactly;
//! - a `Disproved` countermodel is a **concrete panicking input**, found in
//!   milliseconds — and it is *replayed against the real compiled Rust function*
//!   (`catch_unwind`), closing the loop the way a fuzzer's crash repro does;
//! - conditioned on `¬panic`, the debug-MIR value can be proved equal to the
//!   **release LLVM** value — translation-validation *across profiles*.
//!
//! Fixtures are committed debug-MIR text (`rustc -Zunpretty=mir`, checks ON) and
//! release LLVM; not invoked at test time.

use axeyum_ir::{Sort, TermArena, Value};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

mod reflect_common;
use reflect_common::llvm::reflect_unary_into;
use reflect_common::mir::reflect_mir_into_checked;

// ---- the real Rust functions (the replay oracles) --------------------------------

/// Panics at `u32::MAX` when overflow checks are on (debug test profile).
fn inc(x: u32) -> u32 {
    x + 1
}

/// Never panics: the guard keeps the add far from the overflow boundary.
fn inc_guarded(x: u32) -> u32 {
    if x < 1000 { x + 1 } else { 0 }
}

// ---- committed debug-MIR fixtures (overflow checks present) ----------------------

const INC_MIR: &str = r#"
fn inc(_1: u32) -> u32 {
    debug x => _1;
    let mut _0: u32;
    let mut _2: (u32, bool);

    bb0: {
        _2 = AddWithOverflow(copy _1, const 1_u32);
        assert(!move (_2.1: bool), "attempt to compute `{} + {}`, which would overflow", copy _1, const 1_u32) -> [success: bb1, unwind continue];
    }

    bb1: {
        _0 = move (_2.0: u32);
        return;
    }
}
"#;

const INC_GUARDED_MIR: &str = r#"
fn inc_guarded(_1: u32) -> u32 {
    debug x => _1;
    let mut _0: u32;
    let mut _2: bool;
    let mut _3: (u32, bool);

    bb0: {
        StorageLive(_2);
        _2 = Lt(copy _1, const 1000_u32);
        switchInt(move _2) -> [0: bb3, otherwise: bb1];
    }

    bb1: {
        _3 = AddWithOverflow(copy _1, const 1_u32);
        assert(!move (_3.1: bool), "attempt to compute `{} + {}`, which would overflow", copy _1, const 1_u32) -> [success: bb2, unwind continue];
    }

    bb2: {
        _0 = move (_3.0: u32);
        goto -> bb4;
    }

    bb3: {
        _0 = const 0_u32;
        goto -> bb4;
    }

    bb4: {
        StorageDead(_2);
        return;
    }
}
"#;

/// The **release** LLVM of `inc` — no check, just the add (`-O`).
const INC_RELEASE_LL: &str = r"
define noundef i32 @inc(i32 noundef %x) unnamed_addr {
start:
  %_0 = add i32 %x, 1
  ret i32 %_0
}
";

fn reflect_checked(
    mir: &str,
) -> (
    TermArena,
    axeyum_ir::SymbolId,
    axeyum_ir::TermId,
    axeyum_ir::TermId,
) {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(32)).unwrap();
    let x = arena.var(x_sym);
    let (value, panic) = reflect_mir_into_checked(&mut arena, &[x], mir);
    (arena, x_sym, value, panic)
}

/// The guard keeps `x + 1` from overflowing on every reachable path: the
/// reflected panic condition is **provably false for ALL u32** — a
/// panic-freedom proof over the whole input space, from the compiler's own
/// debug-profile checks.
#[test]
fn guarded_increment_proved_panic_free() {
    let (mut arena, _x, _value, panic) = reflect_checked(INC_GUARDED_MIR);
    let no_panic = arena.not(panic).unwrap();
    let outcome = prove(&mut arena, &[], no_panic, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "inc_guarded must be panic-free for all u32, got {outcome:?}"
    );
    // The real function agrees at the guard boundary (concrete oracle).
    assert_eq!(inc_guarded(999), 1000);
    assert_eq!(inc_guarded(1000), 0);
    assert_eq!(inc_guarded(u32::MAX), 0);
}

/// The guarded function's *total* behavior is provable too (it cannot panic, so
/// the value spec holds unconditionally): `inc_guarded(x) == if x<1000 {x+1} else {0}`.
#[test]
fn guarded_increment_value_spec_proved() {
    let (mut arena, x_sym, value, _panic) = reflect_checked(INC_GUARDED_MIR);
    let x = arena.var(x_sym);
    let thousand = arena.bv_const(32, 1000).unwrap();
    let one = arena.bv_const(32, 1).unwrap();
    let zero = arena.bv_const(32, 0).unwrap();
    let lt = arena.bv_ult(x, thousand).unwrap();
    let xp1 = arena.bv_add(x, one).unwrap();
    let spec = arena.ite(lt, xp1, zero).unwrap();
    let goal = arena.eq(value, spec).unwrap();
    let outcome = prove(&mut arena, &[], goal, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "inc_guarded value spec must hold for all u32, got {outcome:?}"
    );
}

/// The unguarded `x + 1` is NOT panic-free: the solver *finds the panicking
/// input* (`u32::MAX` — the only one), and the witness is **replayed against
/// the real compiled Rust function**, which really panics there and really
/// doesn't at a neighboring input. This is the fuzzing loop — search, crash,
/// repro — discharged symbolically in milliseconds.
#[test]
fn unguarded_increment_panic_witness_found_and_reproduced() {
    let (mut arena, x_sym, _value, panic) = reflect_checked(INC_MIR);
    let no_panic = arena.not(panic).unwrap();
    let outcome = prove(&mut arena, &[], no_panic, &SolverConfig::default())
        .expect("solver should not hard-error");
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("inc must have a panicking input, got {outcome:?}");
    };
    let witness = match model.get(x_sym) {
        Some(Value::Bv { width: 32, value }) => u32::try_from(value).unwrap(),
        other => panic!("countermodel has no u32 for x: {other:?}"),
    };
    assert_eq!(witness, u32::MAX, "x+1 overflows only at u32::MAX");

    // Replay the witness against the REAL Rust `inc` (overflow checks are on in
    // the debug test profile — the same checks the reflected MIR carries).
    if cfg!(debug_assertions) {
        let crashed = std::panic::catch_unwind(|| inc(witness)).is_err();
        assert!(crashed, "real inc({witness}) must panic in debug profile");
        let fine = std::panic::catch_unwind(|| inc(witness - 1)).is_ok();
        assert!(fine, "real inc({}) must not panic", witness - 1);
    }
}

/// Across profiles: on every input where the **debug** MIR does not panic, its
/// value equals the **release** LLVM's value — `panic ∨ (mir == llvm)` proved
/// for all u32. Release code is faithful to debug semantics wherever debug
/// semantics is defined: conditional translation-validation.
#[test]
fn debug_mir_equals_release_llvm_where_not_panicking() {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(32)).unwrap();
    let x = arena.var(x_sym);
    let (mir_value, panic) = reflect_mir_into_checked(&mut arena, &[x], INC_MIR);
    let llvm_value = reflect_unary_into(&mut arena, x, INC_RELEASE_LL);
    let eq = arena.eq(mir_value, llvm_value).unwrap();
    let goal = arena.or(panic, eq).unwrap();
    let outcome = prove(&mut arena, &[], goal, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "debug MIR and release LLVM must agree wherever the check passes, got {outcome:?}"
    );
}
