//! A **micro-module end-to-end**, both platforms: the Internet-checksum add
//! step (`sum16`: one's-complement 16-bit addition via a u32 widen + fold) and
//! the header-checksum finalizer (`cksum_pair = !sum16`). Two functions, two
//! parameters each, reflected from paired committed MIR and LLVM fixtures.
//!
//! What gets proved, per platform and across them:
//! - `sum16` and `cksum_pair`: MIR == LLVM for **all** `(u16, u16)` — the
//!   translation-validation baseline, now at module scale;
//! - **composition**: `cksum_pair == ¬sum16` — rustc's MIR inliner composed the
//!   two functions; the proof validates the inlined body against the pieces;
//! - the **receiver property**: `sum16(a,b) + cksum_pair(a,b) == 0xffff` for
//!   all inputs — the actual protocol-level reason the checksum verifies —
//!   proved over the *reflected compiled code*, not the source.
//!
//! This is the shape a network-stack verification takes: reflect the leaf
//! functions the compiler produced, prove the per-function contracts and the
//! protocol identities over them.

use axeyum_ir::{Assignment, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

mod reflect_common;
use reflect_common::llvm::reflect_into;
use reflect_common::mir::reflect_mir_into;

// ---- the real Rust module (concrete oracle) ---------------------------------------

#[allow(clippy::cast_possible_truncation)] // the fold keeps the sum within 16 bits
fn sum16(a: u16, b: u16) -> u16 {
    let s = u32::from(a) + u32::from(b);
    ((s & 0xffff) + (s >> 16)) as u16
}

fn cksum_pair(a: u16, b: u16) -> u16 {
    !sum16(a, b)
}

// ---- committed release-MIR fixtures ------------------------------------------------

const SUM16_MIR: &str = r"
fn sum16(_1: u16, _2: u16) -> u16 {
    debug a => _1;
    debug b => _2;
    let mut _0: u16;
    let mut _3: u32;
    let mut _4: u32;
    let mut _5: u32;
    let mut _6: u32;
    let mut _7: u32;

    bb0: {
        _3 = copy _1 as u32 (IntToInt);
        _4 = copy _2 as u32 (IntToInt);
        _5 = Add(move _3, move _4);
        _6 = BitAnd(copy _5, const 65535_u32);
        _7 = Shr(copy _5, const 16_i32);
        _5 = Add(move _6, move _7);
        _0 = copy _5 as u16 (IntToInt);
        return;
    }
}
";

/// `cksum_pair` after the MIR inliner: `sum16`'s body inlined, then `Not`.
const CKSUM_MIR: &str = r"
fn cksum_pair(_1: u16, _2: u16) -> u16 {
    debug a => _1;
    debug b => _2;
    let mut _0: u16;
    let mut _3: u32;
    let mut _4: u32;
    let mut _5: u32;
    let mut _6: u32;
    let mut _7: u32;
    let mut _8: u16;

    bb0: {
        _3 = copy _1 as u32 (IntToInt);
        _4 = copy _2 as u32 (IntToInt);
        _5 = Add(move _3, move _4);
        _6 = BitAnd(copy _5, const 65535_u32);
        _7 = Shr(copy _5, const 16_i32);
        _5 = Add(move _6, move _7);
        _8 = copy _5 as u16 (IntToInt);
        _0 = Not(move _8);
        return;
    }
}
";

// ---- committed release-LLVM fixtures -----------------------------------------------

const SUM16_LL: &str = r"
define noundef i16 @sum16(i16 noundef %a, i16 noundef %b) unnamed_addr {
start:
  %_3 = zext i16 %a to i32
  %_4 = zext i16 %b to i32
  %s = add nuw nsw i32 %_3, %_4
  %lo = and i32 %s, 65535
  %hi = lshr i32 %s, 16
  %f = add nuw nsw i32 %lo, %hi
  %_0 = trunc i32 %f to i16
  ret i16 %_0
}
";

const CKSUM_LL: &str = r"
define noundef i16 @cksum_pair(i16 noundef %a, i16 noundef %b) unnamed_addr {
start:
  %_3 = zext i16 %a to i32
  %_4 = zext i16 %b to i32
  %s = add nuw nsw i32 %_3, %_4
  %lo = and i32 %s, 65535
  %hi = lshr i32 %s, 16
  %f = add nuw nsw i32 %lo, %hi
  %t = trunc i32 %f to i16
  %_0 = xor i16 %t, -1
  ret i16 %_0
}
";

/// One arena with `(a, b)` symbols and all four reflections over them.
struct Module {
    arena: TermArena,
    a_sym: SymbolId,
    b_sym: SymbolId,
    sum_mir: TermId,
    sum_llvm: TermId,
    cksum_mir: TermId,
    cksum_llvm: TermId,
}

fn reflect_module() -> Module {
    let mut arena = TermArena::new();
    let a_sym = arena.declare("a", Sort::BitVec(16)).unwrap();
    let b_sym = arena.declare("b", Sort::BitVec(16)).unwrap();
    let a = arena.var(a_sym);
    let b = arena.var(b_sym);
    let sum_mir = reflect_mir_into(&mut arena, &[a, b], SUM16_MIR);
    let sum_llvm = reflect_into(&mut arena, &[a, b], SUM16_LL);
    let cksum_mir = reflect_mir_into(&mut arena, &[a, b], CKSUM_MIR);
    let cksum_llvm = reflect_into(&mut arena, &[a, b], CKSUM_LL);
    Module {
        arena,
        a_sym,
        b_sym,
        sum_mir,
        sum_llvm,
        cksum_mir,
        cksum_llvm,
    }
}

fn proved(arena: &mut TermArena, goal: TermId) -> bool {
    matches!(
        prove(arena, &[], goal, &SolverConfig::default()).expect("solver should not hard-error"),
        ProofOutcome::Proved(_)
    )
}

/// Per-function translation validation at module scale: both functions' MIR
/// and LLVM reflections are equal for ALL `(u16, u16)`.
#[test]
fn module_functions_mir_equal_llvm() {
    let mut m = reflect_module();
    let eq_sum = m.arena.eq(m.sum_mir, m.sum_llvm).unwrap();
    assert!(
        proved(&mut m.arena, eq_sum),
        "sum16: MIR and LLVM must be equal for all (u16,u16)"
    );
    let eq_cksum = m.arena.eq(m.cksum_mir, m.cksum_llvm).unwrap();
    assert!(
        proved(&mut m.arena, eq_cksum),
        "cksum_pair: MIR and LLVM must be equal for all (u16,u16)"
    );
}

/// Composition, validating the MIR inliner: the inlined `cksum_pair` is exactly
/// `¬sum16` — on both platforms.
#[test]
fn module_composition_cksum_is_not_sum() {
    let mut m = reflect_module();
    let not_sum_mir = m.arena.bv_not(m.sum_mir).unwrap();
    let goal_mir = m.arena.eq(m.cksum_mir, not_sum_mir).unwrap();
    assert!(
        proved(&mut m.arena, goal_mir),
        "MIR: cksum_pair must equal !sum16"
    );
    let not_sum_llvm = m.arena.bv_not(m.sum_llvm).unwrap();
    let goal_llvm = m.arena.eq(m.cksum_llvm, not_sum_llvm).unwrap();
    assert!(
        proved(&mut m.arena, goal_llvm),
        "LLVM: cksum_pair must equal !sum16"
    );
}

/// The protocol-level receiver property, on the reflected compiled code:
/// `sum16(a,b) + cksum_pair(a,b) == 0xffff` for ALL inputs — why a receiver
/// that re-sums a checksummed header gets all-ones. Proved on both platforms.
#[test]
fn module_receiver_property_sum_plus_cksum_is_all_ones() {
    let mut m = reflect_module();
    let all_ones = m.arena.bv_const(16, 0xffff).unwrap();
    let total_mir = m.arena.bv_add(m.sum_mir, m.cksum_mir).unwrap();
    let goal_mir = m.arena.eq(total_mir, all_ones).unwrap();
    assert!(
        proved(&mut m.arena, goal_mir),
        "MIR: sum16 + cksum_pair must be 0xffff for all inputs"
    );
    let total_llvm = m.arena.bv_add(m.sum_llvm, m.cksum_llvm).unwrap();
    let goal_llvm = m.arena.eq(total_llvm, all_ones).unwrap();
    assert!(
        proved(&mut m.arena, goal_llvm),
        "LLVM: sum16 + cksum_pair must be 0xffff for all inputs"
    );
}

/// Concrete oracle: all four reflections match the real Rust module on a
/// deterministic sample of input pairs (independent of the proofs).
#[test]
fn module_reflections_match_real_rust() {
    let m = reflect_module();
    let mut state = 0x00DD_BA11_u64;
    let mut lcg = move || {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        u16::try_from((state >> 40) & 0xffff).unwrap()
    };
    let eval_at = |term: TermId, a: u16, b: u16| -> u16 {
        let mut asg = Assignment::new();
        asg.set(
            m.a_sym,
            Value::Bv {
                width: 16,
                value: u128::from(a),
            },
        );
        asg.set(
            m.b_sym,
            Value::Bv {
                width: 16,
                value: u128::from(b),
            },
        );
        match eval(&m.arena, term, &asg).unwrap() {
            Value::Bv { value, .. } => u16::try_from(value).unwrap(),
            other => panic!("expected BV, got {other:?}"),
        }
    };
    let mut corners = vec![(0, 0), (0xffff, 0xffff), (0xffff, 1), (0x8000, 0x8000)];
    for _ in 0..2000 {
        corners.push((lcg(), lcg()));
    }
    for (a, b) in corners {
        assert_eq!(
            eval_at(m.sum_mir, a, b),
            sum16(a, b),
            "sum_mir at ({a},{b})"
        );
        assert_eq!(
            eval_at(m.sum_llvm, a, b),
            sum16(a, b),
            "sum_llvm at ({a},{b})"
        );
        assert_eq!(
            eval_at(m.cksum_mir, a, b),
            cksum_pair(a, b),
            "cksum_mir at ({a},{b})"
        );
        assert_eq!(
            eval_at(m.cksum_llvm, a, b),
            cksum_pair(a, b),
            "cksum_llvm at ({a},{b})"
        );
    }
}
