//! **Bounds-check panic-freedom** — memory safety from debug-profile MIR.
//!
//! Rust guards every array read with a bounds `assert` in debug MIR. Reflecting
//! `[u8; N]` parameters as one symbol per element and the read as an ite table
//! turns that guard into the same Bool panic-condition the overflow checks use:
//!
//! - a **clamped** read (`buf[i & 3]`) is proved panic-free for **every**
//!   index (all 2^64 of them) and every buffer content — a memory-safety proof
//!   over the compiled function's own check;
//! - an **unguarded** read (`buf[i]`) is refuted: the solver hands back an
//!   out-of-bounds index, which is replayed against the real Rust function
//!   (`catch_unwind` sees the index-out-of-bounds panic; in-bounds neighbors
//!   don't panic);
//! - the read **value** is cross-checked concretely against the real function
//!   on every in-bounds index for sampled buffer contents.
//!
//! This is the buffer half of the sel4-direction story: the same machinery that
//! proves an overflow check unreachable proves an OOB access unreachable.

use axeyum_ir::{Assignment, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{ProofOutcome, SolverConfig, prove};

use axeyum_verify::reflect::mir::checked::{MirMemoryConfig, reflect_bounded_memory_checked};

// ---- the real Rust functions (replay oracles) -------------------------------------

fn get(buf: [u8; 4], i: usize) -> u8 {
    buf[i]
}

fn get_clamped(buf: [u8; 4], i: usize) -> u8 {
    buf[i & 3]
}

// ---- authenticated compiler MIR fixture (bounds asserts present) -----------------

const COMPILER_MIR: &str = include_str!("fixtures/mir/rustc197-debug.mir");

struct Reflection {
    arena: TermArena,
    byte_syms: Vec<SymbolId>,
    idx_sym: SymbolId,
    value: TermId,
    panic: TermId,
}

fn reflect(function: &str) -> Reflection {
    let reflected =
        reflect_bounded_memory_checked(COMPILER_MIR, &MirMemoryConfig::new(function, 64)).unwrap();
    let idx_sym = reflected
        .params
        .iter()
        .find(|parameter| parameter.local == 2)
        .unwrap()
        .symbol;
    Reflection {
        arena: reflected.arena,
        byte_syms: reflected.region.input,
        idx_sym,
        value: reflected.result.value,
        panic: reflected.panic,
    }
}

/// The clamped read is memory-safe for EVERY 64-bit index and every buffer
/// content: the compiled bounds check is proved unreachable.
#[test]
fn clamped_read_proved_panic_free_for_all_indices() {
    let mut r = reflect("clamped_read");
    let no_panic = r.arena.not(r.panic).unwrap();
    let outcome = prove(&mut r.arena, &[], no_panic, &SolverConfig::default())
        .expect("solver should not hard-error");
    assert!(
        matches!(outcome, ProofOutcome::Proved(_)),
        "get_clamped must be panic-free for all (buf, i), got {outcome:?}"
    );
}

/// The unguarded read is NOT memory-safe: the solver finds an out-of-bounds
/// index, and the real compiled Rust function panics exactly there.
#[test]
fn unguarded_read_oob_witness_found_and_reproduced() {
    let mut r = reflect("checked_read");
    let no_panic = r.arena.not(r.panic).unwrap();
    let outcome = prove(&mut r.arena, &[], no_panic, &SolverConfig::default())
        .expect("solver should not hard-error");
    let ProofOutcome::Disproved(model) = outcome else {
        panic!("get must have an out-of-bounds input, got {outcome:?}");
    };
    let witness = match model.get(r.idx_sym) {
        Some(Value::Bv { width: 64, value }) => u64::try_from(value).unwrap(),
        other => panic!("countermodel has no index: {other:?}"),
    };
    assert!(witness >= 4, "the witness index must be out of bounds");

    let buf = [1u8, 2, 3, 4];
    let idx = usize::try_from(witness).expect("witness fits usize on this platform");
    assert!(
        std::panic::catch_unwind(move || get(buf, idx)).is_err(),
        "real get(buf, {witness}) must panic with index-out-of-bounds"
    );
    assert!(
        std::panic::catch_unwind(move || get(buf, 3)).is_ok(),
        "real get(buf, 3) must not panic"
    );
}

/// Value faithfulness, concretely: on every in-bounds index and sampled buffer
/// contents, the reflected read equals the real Rust read (both variants).
#[test]
fn read_values_match_real_rust_in_bounds() {
    let r_get = reflect("checked_read");
    let r_clamp = reflect("clamped_read");
    let bufs = [[0u8, 0, 0, 0], [1, 2, 3, 4], [0xff, 0x80, 0x7f, 1]];
    for buf in bufs {
        for i in 0..4u64 {
            let eval_at = |r: &Reflection| -> u8 {
                let mut asg = Assignment::new();
                for (k, &sym) in r.byte_syms.iter().enumerate() {
                    asg.set(
                        sym,
                        Value::Bv {
                            width: 8,
                            value: u128::from(buf[k]),
                        },
                    );
                }
                asg.set(
                    r.idx_sym,
                    Value::Bv {
                        width: 64,
                        value: u128::from(i),
                    },
                );
                match eval(&r.arena, r.value, &asg).unwrap() {
                    Value::Bv { value, .. } => u8::try_from(value).unwrap(),
                    other => panic!("expected a byte, got {other:?}"),
                }
            };
            let idx = usize::try_from(i).unwrap();
            assert_eq!(eval_at(&r_get), get(buf, idx), "get at {buf:?}[{i}]");
            assert_eq!(
                eval_at(&r_clamp),
                get_clamped(buf, idx),
                "get_clamped at {buf:?}[{i}]"
            );
        }
    }
}
