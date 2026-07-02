//! Cross-IR equivalence: reflect the **same source function** from *both* its
//! rustc **MIR** and its **LLVM IR**, lower both into one `axeyum-ir` arena over a
//! shared input symbol, and **prove them equal for every input**. This is
//! translation-validation of rustc's own MIR→LLVM lowering, and the sharpest
//! demonstration that both front ends land in one term algebra: the proof is
//! `∀x. mir_reflect(f)(x) == llvm_reflect(f)(x)`, discharged by the solver.
//!
//! Both reflectors come from `reflect_common` (the MIR and LLVM parsers over the
//! *shared* op vocabulary), so this file is only fixtures + the equivalence
//! assertions — the DRY payoff realized.
//!
//! Fixtures are committed IR text (captured once from `rustc -Zunpretty=mir` and
//! `rustc -O --emit=llvm-ir`); not invoked at test time, so this is CI-robust.

use axeyum_ir::{Assignment, Sort, TermArena, Value, eval};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

mod reflect_common;
use reflect_common::llvm::reflect_unary_into;
use reflect_common::mir::reflect_mir_unary;

// ---- `masked(x) = (x & 0xff) | 0x100` : straight-line BitAnd/BitOr ~ and/or -----

const MASKED_MIR: &str = r"
fn masked(_1: u32) -> u32 {
    bb0: {
        _2 = BitAnd(copy _1, const 255_u32);
        _0 = BitOr(move _2, const 256_u32);
        return;
    }
}
";

const MASKED_LL: &str = r"
define noundef range(i32 256, 512) i32 @masked(i32 noundef %x) unnamed_addr {
start:
  %_2 = and i32 %x, 255
  %_0 = or disjoint i32 %_2, 256
  ret i32 %_0
}
";

// ---- `lut(x) = match x { 0=>5, 1=>7, _=>0 }` : switchInt ~ icmp+select -----------

const LUT_MIR: &str = r"
fn lut(_1: u8) -> u8 {
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

/// The `-O` if-converted form: two chained `select`s (equivalent to the match).
const LUT_LL: &str = r"
define noundef i8 @lut(i8 noundef %x) unnamed_addr {
start:
  %c1 = icmp eq i8 %x, 1
  %s1 = select i1 %c1, i8 7, i8 0
  %c0 = icmp eq i8 %x, 0
  %_0 = select i1 %c0, i8 5, i8 %s1
  ret i8 %_0
}
";

/// Prove `mir(f) == llvm(f)` for all inputs, and separately exhaustively/fuzz the
/// two reflected terms agree — belt and suspenders across proof and execution.
fn assert_equivalent(width: u32, mir: &str, ll: &str, samples: &[u128]) {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);

    let from_mir = reflect_mir_unary(&mut arena, x, mir);
    let from_llvm = reflect_unary_into(&mut arena, x, ll);

    // Symbolic: ∀x. mir(x) == llvm(x).
    let eq = arena.eq(from_mir, from_llvm).unwrap();
    let outcome =
        prove(&mut arena, &[], eq, &SolverConfig::default()).expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "MIR and LLVM reflections must be provably equal for all {width}-bit inputs, got {outcome:?}"
    );

    // Concrete cross-check at chosen samples (independent of the proof).
    for &v in samples {
        let mut asg = Assignment::new();
        asg.set(x_sym, Value::Bv { width, value: v });
        let m = match eval(&arena, from_mir, &asg).unwrap() {
            Value::Bv { value, .. } => value,
            other => panic!("mir eval not BV: {other:?}"),
        };
        let l = match eval(&arena, from_llvm, &asg).unwrap() {
            Value::Bv { value, .. } => value,
            other => panic!("llvm eval not BV: {other:?}"),
        };
        assert_eq!(m, l, "mir/llvm disagree at x={v}");
    }
}

/// `masked`: straight-line MIR `BitAnd`/`BitOr` == LLVM `and`/`or`, for all `u32`.
/// The MIR side exercises the new shared straight-line `BinaryOp` path, routing
/// `BitAnd`/`BitOr` through the *same* `binop` vocabulary the LLVM side uses.
#[test]
fn masked_mir_equals_llvm() {
    assert_equivalent(
        32,
        MASKED_MIR,
        MASKED_LL,
        &[0, 1, 0xff, 0x100, 0xdead_beef, u128::from(u32::MAX)],
    );
}

/// `lut`: MIR `switchInt` dispatch == LLVM if-converted `icmp`+`select`, for all
/// `u8` — proving rustc's two representations of a match compute one function.
#[test]
fn lut_mir_equals_llvm() {
    assert_equivalent(8, LUT_MIR, LUT_LL, &(0u128..=255).collect::<Vec<_>>());
}

/// A negative control: `masked` MIR must **not** be equivalent to `lut` LLVM — the
/// equivalence prover is discriminating, not vacuously accepting. (Widths differ,
/// so compare each against a deliberately-wrong same-width partner instead.)
#[test]
fn distinct_functions_are_not_equivalent() {
    // masked vs a shifted-mask variant: (x & 0xff) | 0x100  vs  (x & 0xff) | 0x200.
    const MASKED2_LL: &str = r"
define i32 @masked2(i32 %x) {
start:
  %_2 = and i32 %x, 255
  %_0 = or i32 %_2, 512
  ret i32 %_0
}
";
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(32)).unwrap();
    let x = arena.var(x_sym);
    let a = reflect_mir_unary(&mut arena, x, MASKED_MIR);
    let b = reflect_unary_into(&mut arena, x, MASKED2_LL);
    let eq = arena.eq(a, b).unwrap();
    let outcome =
        prove(&mut arena, &[], eq, &SolverConfig::default()).expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Disproved(_)),
        "masked (|0x100) and masked2 (|0x200) must be refuted as unequal, got {outcome:?}"
    );
}
