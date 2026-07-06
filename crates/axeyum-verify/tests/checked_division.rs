//! **Checked division, both platforms** — the panic that survives release mode.
//!
//! Rust guards every division: debug *and* release insert the `b == 0` check
//! (and, for signed division, the `i32::MIN / -1` overflow check). So this is
//! the sharpest panic-reflection case: the MIR carries `assert`s, and even the
//! `-O` LLVM carries a real `br` to a panic block (`call core::panicking::panic`
//! + `unreachable`).
//!
//! Proved here:
//! - the **exact panic specification**: unsigned `div` panics iff `b == 0`;
//!   signed `sdiv` panics iff `b == 0 ∨ (a == i32::MIN ∧ b == -1)` — two
//!   accumulated asserts captured precisely;
//! - witnesses replayed against the **real** Rust functions (`catch_unwind`) —
//!   and unlike overflow, division panics in EVERY profile, so the replay is
//!   unconditional;
//! - conditional cross-IR: wherever the MIR does not panic, its value equals
//!   the release LLVM's `udiv` (whose panic arm the reflector treats as the
//!   don't-care `unreachable` path it is).

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

use axeyum_verify::reflect::llvm::reflect_into;
use axeyum_verify::reflect::mir::reflect_mir_into_checked;

// ---- the real Rust functions (replay oracles; division checks are unconditional) --

fn div(a: u32, b: u32) -> u32 {
    a / b
}

fn sdiv(a: i32, b: i32) -> i32 {
    a / b
}

// ---- committed MIR fixtures (the checks rustc inserts) ----------------------------

const DIV_MIR: &str = r#"
fn div(_1: u32, _2: u32) -> u32 {
    debug a => _1;
    debug b => _2;
    let mut _0: u32;
    let mut _3: bool;

    bb0: {
        _3 = Eq(copy _2, const 0_u32);
        assert(!move _3, "attempt to divide `{}` by zero", copy _1) -> [success: bb1, unwind continue];
    }

    bb1: {
        _0 = Div(copy _1, copy _2);
        return;
    }
}
"#;

const SDIV_MIR: &str = r#"
fn sdiv(_1: i32, _2: i32) -> i32 {
    debug a => _1;
    debug b => _2;
    let mut _0: i32;
    let mut _3: bool;
    let mut _4: bool;
    let mut _5: bool;
    let mut _6: bool;

    bb0: {
        _3 = Eq(copy _2, const 0_i32);
        assert(!move _3, "attempt to divide `{}` by zero", copy _1) -> [success: bb1, unwind continue];
    }

    bb1: {
        _4 = Eq(copy _2, const -1_i32);
        _5 = Eq(copy _1, const -2147483648_i32);
        _6 = BitAnd(move _4, move _5);
        assert(!move _6, "attempt to compute `{} / {}`, which would overflow", copy _1, copy _2) -> [success: bb2, unwind continue];
    }

    bb2: {
        _0 = Div(copy _1, copy _2);
        return;
    }
}
"#;

/// Release LLVM of `div`: the zero check is a real branch to a panic block —
/// which the reflector treats as the `unreachable` don't-care path it is.
const DIV_RELEASE_LL: &str = r"
define noundef i32 @div(i32 noundef %a, i32 noundef %b) unnamed_addr {
start:
  %_3 = icmp eq i32 %b, 0
  br i1 %_3, label %panic, label %bb1

panic:                                            ; preds = %start
  tail call void @_ZN4core9panicking14panic_div_by_zero(ptr align 8 @anon)
  unreachable

bb1:                                              ; preds = %start
  %_0 = udiv i32 %a, %b
  ret i32 %_0
}
";

fn reflect_two(mir: &str) -> (TermArena, SymbolId, SymbolId, TermId, TermId) {
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(32)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(32)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let (value, panic) = reflect_mir_into_checked(&mut arena, &[a, b], mir);
    (arena, a_sym, b_sym, value, panic)
}

fn proved(arena: &mut TermArena, goal: TermId) -> bool {
    matches!(
        prove(arena, &[], goal, &SolverConfig::default()).expect("solver should not hard-error"),
        ProofOutcome::Proved(_)
    )
}

/// The exact panic specification of unsigned division: `panic ⟺ b == 0`,
/// proved for ALL (u32, u32).
#[test]
fn unsigned_division_panic_spec_exact() {
    let (mut arena, _a, b_sym, _value, panic) = reflect_two(DIV_MIR);
    let b = arena.var(b_sym);
    let zero = arena.bv_const(32, 0).unwrap();
    let b_is_zero = arena.eq(b, zero).unwrap();
    let goal = arena.eq(panic, b_is_zero).unwrap();
    assert!(
        proved(&mut arena, goal),
        "div must panic exactly when b == 0"
    );
}

/// The panic witness is found and replayed: real `a / b` panics at the model's
/// `b == 0` (in every profile — division checks are unconditional) and not at
/// `b == 1`.
#[test]
fn unsigned_division_witness_replayed() {
    let (mut arena, a_sym, b_sym, _value, panic) = reflect_two(DIV_MIR);
    let no_panic = arena.not(panic).unwrap();
    let outcome = prove(&mut arena, &[], no_panic, &SolverConfig::default())
        .expect("solver should not hard-error");
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("div must have a panicking input, got {outcome:?}");
    };
    let get = |sym| match model.get(sym) {
        Some(Value::Bv { value, .. }) => u32::try_from(value).unwrap(),
        other => panic!("no u32 in countermodel: {other:?}"),
    };
    let (wa, wb) = (get(a_sym), get(b_sym));
    assert_eq!(wb, 0, "the only panic cause is b == 0");
    assert!(
        std::panic::catch_unwind(|| div(wa, wb)).is_err(),
        "real div({wa}, {wb}) must panic"
    );
    assert!(
        std::panic::catch_unwind(|| div(wa, 1)).is_ok(),
        "real div({wa}, 1) must not panic"
    );
}

/// Conditional cross-IR: wherever the checked MIR does not panic, its value
/// equals the release LLVM's `udiv` — `panic ∨ (mir == llvm)` for all inputs.
#[test]
fn division_mir_equals_release_llvm_where_defined() {
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(32)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(32)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let (mir_value, panic) = reflect_mir_into_checked(&mut arena, &[a, b], DIV_MIR);
    let llvm_value = reflect_into(&mut arena, &[a, b], DIV_RELEASE_LL);
    let eq = arena.eq(mir_value, llvm_value).unwrap();
    let goal = arena.or(panic, eq).unwrap();
    assert!(
        proved(&mut arena, goal),
        "MIR and release LLVM division must agree wherever defined"
    );
}

/// The exact panic specification of **signed** division — TWO accumulated
/// asserts: `panic ⟺ b == 0 ∨ (a == i32::MIN ∧ b == -1)`, for ALL (i32, i32).
#[test]
fn signed_division_panic_spec_exact() {
    let (mut arena, a_sym, b_sym, _value, panic) = reflect_two(SDIV_MIR);
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let zero = arena.bv_const(32, 0).unwrap();
    let minus_one = arena.bv_const(32, 0xffff_ffff).unwrap();
    let min = arena.bv_const(32, 0x8000_0000).unwrap();
    let b_zero = arena.eq(b, zero).unwrap();
    let b_m1 = arena.eq(b, minus_one).unwrap();
    let a_min = arena.eq(a, min).unwrap();
    let ovf = arena.and(a_min, b_m1).unwrap();
    let spec = arena.or(b_zero, ovf).unwrap();
    let goal = arena.eq(panic, spec).unwrap();
    assert!(
        proved(&mut arena, goal),
        "sdiv must panic exactly on b==0 or i32::MIN / -1"
    );
}

/// The MIN/-1 corner reproduces on the real function: with `b == 0` excluded
/// as a hypothesis, the solver's witness must be exactly (`i32::MIN`, -1), and
/// the real `a / b` panics there (in every profile).
#[test]
fn signed_division_overflow_witness_replayed() {
    let (mut arena, a_sym, b_sym, _value, panic) = reflect_two(SDIV_MIR);
    let b = arena.var(b_sym);
    let zero = arena.bv_const(32, 0).unwrap();
    let b_zero = arena.eq(b, zero).unwrap();
    let b_nonzero = arena.not(b_zero).unwrap();
    let no_panic = arena.not(panic).unwrap();
    let outcome = prove(&mut arena, &[b_nonzero], no_panic, &SolverConfig::default())
        .expect("solver should not hard-error");
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("sdiv must still panic somewhere with b != 0, got {outcome:?}");
    };
    let get = |sym| match model.get(sym) {
        Some(Value::Bv { value, .. }) => u32::try_from(value).unwrap().cast_signed(),
        other => panic!("no value in countermodel: {other:?}"),
    };
    let (wa, wb) = (get(a_sym), get(b_sym));
    assert_eq!((wa, wb), (i32::MIN, -1), "the only b!=0 panic is MIN / -1");
    assert!(
        std::panic::catch_unwind(|| sdiv(wa, wb)).is_err(),
        "real sdiv(i32::MIN, -1) must panic"
    );
    assert!(
        std::panic::catch_unwind(|| sdiv(wa, -2)).is_ok(),
        "real sdiv(i32::MIN, -2) must not panic"
    );
}
