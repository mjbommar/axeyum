//! The **wrong-transform corpus**: hand-broken compiler-optimization pairs the
//! cross-IR equivalence prover must *refute*. Each case pairs a correct MIR
//! reflection with a plausible-but-wrong LLVM "optimization" (off-by-one shift,
//! `lshr` for `ashr`, flipped select arms, a dropped mask, an unsigned compare
//! of signed values) — the classic miscompile shapes.
//!
//! Discipline (`untrusted fast search, trusted small checking`): a `Disproved`
//! verdict is not taken on faith — the countermodel is **replay-checked** by
//! evaluating both reflected terms at the model's input and asserting they
//! really differ. A refuter that returned bogus countermodels would fail here.
//!
//! This is the negative half of `cross_ir_equivalence.rs`: together they show
//! the prover is *discriminating* — it accepts exactly the correct transforms.

use axeyum_ir::{Assignment, Sort, TermArena, Value, eval};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

mod reflect_common;
use reflect_common::llvm::reflect_unary_into;
use reflect_common::mir::reflect_mir_unary;

/// Reflect both sides over one symbol, require `Disproved`, then replay-check
/// the countermodel: the two terms must evaluate to *different* values at the
/// model's input (and the returned input must be a well-formed width-`width` BV).
fn assert_refuted(width: u32, mir: &str, ll: &str, what: &str) {
    let mut arena = TermArena::new();
    let x_sym = arena.declare("x", Sort::BitVec(width)).unwrap();
    let x = arena.var(x_sym);
    let from_mir = reflect_mir_unary(&mut arena, x, mir);
    let from_llvm = reflect_unary_into(&mut arena, x, ll);
    let eq = arena.eq(from_mir, from_llvm).unwrap();
    let outcome =
        prove(&mut arena, &[], eq, &SolverConfig::default()).expect("solver should not hard-error");
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("{what}: the broken transform must be REFUTED, got {outcome:?}");
    };

    // Replay-check the countermodel against both reflections.
    let cx = match model.get(x_sym) {
        Some(Value::Bv { width: w, value }) => {
            assert_eq!(w, width, "{what}: countermodel width mismatch");
            value
        }
        other => panic!("{what}: countermodel has no BV value for x, got {other:?}"),
    };
    let mut asg = Assignment::new();
    asg.set(x_sym, Value::Bv { width, value: cx });
    let m = match eval(&arena, from_mir, &asg).unwrap() {
        Value::Bv { value, .. } => value,
        other => panic!("{what}: mir eval not BV: {other:?}"),
    };
    let l = match eval(&arena, from_llvm, &asg).unwrap() {
        Value::Bv { value, .. } => value,
        other => panic!("{what}: llvm eval not BV: {other:?}"),
    };
    assert_ne!(
        m, l,
        "{what}: countermodel x={cx} does not actually distinguish the two sides"
    );
}

// ---- 1. off-by-one strength reduction: x*4 + 1 vs (x<<3) + 1 ---------------------

const SCALE_MIR: &str = r"
fn scale(_1: u32) -> u32 {
    bb0: {
        _2 = Mul(copy _1, const 4_u32);
        _0 = Add(move _2, const 1_u32);
        return;
    }
}
";

/// WRONG: shifts by 3 (`*8`), not 2 (`*4`).
const SCALE_BROKEN_LL: &str = r"
define i32 @scale(i32 %x) unnamed_addr {
start:
  %m = shl i32 %x, 3
  %_0 = add i32 %m, 1
  ret i32 %_0
}
";

#[test]
fn off_by_one_strength_reduction_refuted() {
    assert_refuted(32, SCALE_MIR, SCALE_BROKEN_LL, "x*4 -> x<<3");
}

// ---- 2. logical shift for arithmetic: i32 >> 4 via lshr --------------------------

const SAR_MIR: &str = r"
fn sar(_1: i32) -> i32 {
    debug x => _1;
    let mut _0: i32;

    bb0: {
        _0 = Shr(copy _1, const 4_i32);
        return;
    }
}
";

/// WRONG: `lshr` zero-fills the sign bits; differs at every negative input.
const SAR_BROKEN_LL: &str = r"
define i32 @sar(i32 %x) unnamed_addr {
start:
  %_0 = lshr i32 %x, 4
  ret i32 %_0
}
";

#[test]
fn lshr_for_ashr_refuted() {
    assert_refuted(32, SAR_MIR, SAR_BROKEN_LL, "signed >> via lshr");
}

// ---- 3. flipped select polarity ---------------------------------------------------

const SEL_MIR: &str = r"
fn sel(_1: u32) -> u32 {
    debug x => _1;
    let mut _0: u32;
    let mut _2: bool;

    bb0: {
        StorageLive(_2);
        _2 = Gt(copy _1, const 100_u32);
        switchInt(move _2) -> [0: bb2, otherwise: bb1];
    }

    bb1: {
        _0 = BitAnd(copy _1, const 255_u32);
        goto -> bb3;
    }

    bb2: {
        _0 = BitOr(copy _1, const 1_u32);
        goto -> bb3;
    }

    bb3: {
        StorageDead(_2);
        return;
    }
}
";

/// WRONG: the select arms are swapped relative to the branch.
const SEL_FLIPPED_LL: &str = r"
define i32 @sel(i32 %x) unnamed_addr {
start:
  %c = icmp ugt i32 %x, 100
  %a = and i32 %x, 255
  %b = or i32 %x, 1
  %_0 = select i1 %c, i32 %b, i32 %a
  ret i32 %_0
}
";

#[test]
fn flipped_select_polarity_refuted() {
    assert_refuted(32, SEL_MIR, SEL_FLIPPED_LL, "select arms swapped");
}

// ---- 4. dropped mask ---------------------------------------------------------------

const MASKED_MIR: &str = r"
fn masked(_1: u32) -> u32 {
    bb0: {
        _2 = BitAnd(copy _1, const 255_u32);
        _0 = BitOr(move _2, const 256_u32);
        return;
    }
}
";

/// WRONG: the `& 0xff` was "optimized away".
const MASKED_UNMASKED_LL: &str = r"
define i32 @masked(i32 %x) unnamed_addr {
start:
  %_0 = or i32 %x, 256
  ret i32 %_0
}
";

#[test]
fn dropped_mask_refuted() {
    assert_refuted(32, MASKED_MIR, MASKED_UNMASKED_LL, "mask dropped");
}

// ---- 5. sign-confused compare: (x < 0) via unsigned ult ---------------------------

const IS_NEG_MIR: &str = r"
fn is_neg(_1: i32) -> u32 {
    debug x => _1;
    let mut _0: u32;
    let mut _2: bool;

    bb0: {
        _2 = Lt(copy _1, const 0_i32);
        switchInt(move _2) -> [0: bb2, otherwise: bb1];
    }

    bb1: {
        _0 = const 1_u32;
        goto -> bb3;
    }

    bb2: {
        _0 = const 0_u32;
        goto -> bb3;
    }

    bb3: {
        return;
    }
}
";

/// WRONG: `ult %x, 0` is never true — unsigned compare of a signed test, the
/// classic sign-confusion miscompile (collapses to constant 0).
const IS_NEG_UNSIGNED_LL: &str = r"
define i32 @is_neg(i32 %x) unnamed_addr {
start:
  %c = icmp ult i32 %x, 0
  %_0 = select i1 %c, i32 1, i32 0
  ret i32 %_0
}
";

#[test]
fn unsigned_compare_of_signed_test_refuted() {
    assert_refuted(32, IS_NEG_MIR, IS_NEG_UNSIGNED_LL, "x<0 via ult");
}
