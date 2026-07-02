//! Shared, IR-agnostic reflection core used by **both** the MIR and LLVM
//! front-end test suites (`mir_reflection.rs`, `llvm_reflection.rs`). The parsers
//! differ per platform; the op vocabulary and the proof/eval harness are one
//! thing — here — so a fix or a new op benefits both platforms at once, and the
//! same harness proves the two reflections of one function equivalent.
//!
//! (Included via `mod reflect_common;` — the `subdir/mod.rs` form, so cargo does
//! not compile it as its own test binary. Each test crate compiles its own copy;
//! this is source-level DRY, not a public API.)
#![allow(dead_code)] // each front end uses a subset of the shared vocabulary.

/// The single-block LLVM-IR reflector (parse `define … ret` → term).
pub mod llvm;
/// The `switchInt` / straight-line `BinaryOp` MIR reflector.
pub mod mir;

use axeyum_ir::{Assignment, TermArena, TermId, Value, eval};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

/// Width of an `iN`/`uN` type token (`i8`, `i32`, `u64`, …).
pub fn width_of(ty: &str) -> u32 {
    ty.trim_start_matches(['i', 'u'])
        .trim_end_matches(|c: char| !c.is_ascii_digit())
        .parse()
        .expect("iN/uN width")
}

/// Whether `tok` is an integer type token.
pub fn is_int_ty(tok: &str) -> bool {
    (tok.starts_with('i') || tok.starts_with('u'))
        && tok.len() > 1
        && tok[1..].chars().all(|c| c.is_ascii_digit())
}

/// The binary-op → arena BV-op map, keyed by **both** LLVM and MIR spellings —
/// the DRY vocabulary. (`Shr` maps to logical shift: correct for MIR's unsigned
/// `Shr`; a signed `Shr` on `iN` would need `ashr`, added when a case needs it.)
pub fn binop(arena: &mut TermArena, op: &str, a: TermId, b: TermId) -> TermId {
    match op {
        "and" | "BitAnd" => arena.bv_and(a, b),
        "or" | "BitOr" => arena.bv_or(a, b),
        "xor" | "BitXor" => arena.bv_xor(a, b),
        "add" | "Add" => arena.bv_add(a, b),
        "sub" | "Sub" => arena.bv_sub(a, b),
        "mul" | "Mul" => arena.bv_mul(a, b),
        "shl" | "Shl" => arena.bv_shl(a, b),
        "lshr" | "Shr" => arena.bv_lshr(a, b),
        "ashr" => arena.bv_ashr(a, b),
        other => panic!("unsupported binop {other}"),
    }
    .unwrap()
}

/// The comparison-predicate → arena BV-compare map (LLVM `icmp` predicates).
pub fn compare(arena: &mut TermArena, pred: &str, a: TermId, b: TermId) -> TermId {
    match pred {
        "eq" => arena.eq(a, b),
        "ne" => {
            let e = arena.eq(a, b).unwrap();
            return arena.not(e).unwrap();
        }
        "ult" => arena.bv_ult(a, b),
        "ule" => arena.bv_ule(a, b),
        "ugt" => arena.bv_ugt(a, b),
        "uge" => arena.bv_uge(a, b),
        "slt" => arena.bv_slt(a, b),
        "sle" => arena.bv_sle(a, b),
        "sgt" => arena.bv_sgt(a, b),
        "sge" => arena.bv_sge(a, b),
        other => panic!("unsupported icmp predicate {other}"),
    }
    .unwrap()
}

// ---- the proof / eval harness (identical across front ends) --------------------

/// Prove `goal` for all inputs (no hypotheses).
pub fn prove_goal(arena: &mut TermArena, goal: TermId) -> ProofOutcome {
    prove(arena, &[], goal, &SolverConfig::default()).expect("solver should not hard-error")
}

/// `goal` holds for every input (a re-checked refutation of `¬goal`).
pub fn is_proved(arena: &mut TermArena, goal: TermId) -> bool {
    matches!(prove_goal(arena, goal), ProofOutcome::Proved(_))
}

/// `goal` is refuted — there is a countermodel.
pub fn is_disproved(arena: &mut TermArena, goal: TermId) -> bool {
    matches!(prove_goal(arena, goal), ProofOutcome::Disproved(_))
}

/// Evaluate a BV-valued term under an assignment (the fuzz/eval reader).
pub fn eval_bv(arena: &TermArena, term: TermId, asg: &Assignment) -> u128 {
    match eval(arena, term, asg).unwrap() {
        Value::Bv { value, .. } => value,
        other => panic!("expected a BV value, got {other:?}"),
    }
}
