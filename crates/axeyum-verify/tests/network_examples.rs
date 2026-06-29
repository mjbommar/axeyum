//! Block A of the *verified systems & protocols* backlog
//! ([`docs/consumer-track/verify/verified-systems-and-protocols.md`]) — worked
//! examples driving the real `#[axeyum::verify]` macro on **network-protocol**
//! code, demonstrating two rungs that need *no new macro features*:
//!
//! - **Rung 1 — spec/impl equivalence.** `assert_eq!(impl(x), spec(x))` inside a
//!   `#[verify]` fn turns equivalence into a reachable-mismatch query: `Verified`
//!   means the two are bit-equal for all inputs in the modeled domain (a bounded
//!   equivalence proof, Lean-eligible); a counterexample is a concrete divergence.
//! - **Rung 0/2 — panic-freedom & postconditions.** The classic overflow defect a
//!   wrapping formulation avoids shows up as a reachable `add overflow`.
//!
//! Each safe fn's generated `#[test] axeyum_verify_<fn>` asserts it VERIFIES;
//! each `#[verify(expect_bug)]` fn's test asserts a counterexample is FOUND and —
//! the soundness floor — that the witness re-panics in the *original* fn
//! (DISAGREE = 0). Headline cases additionally inspect the verdict directly.
//!
//! Domain note: preconditions are encoded by *masking inputs into range* (the
//! fragment has no `requires`); variable `as` casts are deliberately avoided
//! (Phase-1 supports literal casts only), so every example stays single-width.

#![allow(clippy::similar_names)]

use axeyum_verify::{Verdict, Witness, verify};

// ---- Rung 1: Internet checksum end-around-carry fold equivalence (RFC 1071) ----

/// Two idioms for the 16-bit ones-complement *end-around carry* fold of a sum of
/// two 16-bit words must be bit-equal:
///   A: `(s & 0xffff) + (s >> 16)`            (add the carry back in)
///   B: `if s > 0xffff { s - 0xffff } else s` (subtract 0xffff == +1 with wrap)
/// For `s = x16 + y16 <= 0x1fffe` these coincide. The "untrusted fast fold,
/// trusted small check" demo: `Verified` is a bounded equivalence proof.
#[verify]
fn ic_carry_fold_equiv(x: u32, y: u32) -> u32 {
    let x16: u32 = x & 0xffff;
    let y16: u32 = y & 0xffff;
    let s: u32 = x16 + y16; // <= 0x1fffe, no overflow
    let method_a: u32 = (s & 0xffff) + (s >> 16);
    let mut method_b: u32 = s;
    if s > 0xffff {
        method_b = s - 0xffff;
    }
    assert_eq!(method_a, method_b);
    method_a
}

#[test]
fn ic_carry_fold_equiv_is_certified() {
    match ic_carry_fold_equiv__axeyum_verdict() {
        Verdict::Verified { .. } => {}
        other => panic!("the carry-fold idioms must be proven equivalent, got {other:?}"),
    }
}

/// BUG: a fold that simply masks (`s & 0xffff`) and *forgets the end-around
/// carry* diverges from the correct fold whenever `s > 0xffff`. The equivalence
/// `assert_eq!` is then reachable-false → a concrete colliding witness.
#[verify(expect_bug)]
fn ic_missing_carry_bug(x: u32, y: u32) -> u32 {
    let x16: u32 = x & 0xffff;
    let y16: u32 = y & 0xffff;
    let s: u32 = x16 + y16;
    let correct: u32 = (s & 0xffff) + (s >> 16);
    let buggy: u32 = s & 0xffff; // dropped the carry
    assert_eq!(correct, buggy);
    correct
}

#[test]
fn ic_missing_carry_witness_reproduces() {
    let Verdict::Counterexample { class, inputs } = ic_missing_carry_bug__axeyum_verdict() else {
        panic!("dropping the end-around carry must be a reachable mismatch");
    };
    // `assert_eq!(a, b)` desugars to `assert!(a == b)`, so the class is the
    // generic assert label.
    assert_eq!(class, "assert! violated");
    let x = int_bits(&inputs, "x");
    let y = int_bits(&inputs, "y");
    assert!(
        axeyum_verify::reproduce::panics_on(move || {
            let _ = ic_missing_carry_bug(x as u32, y as u32);
        }),
        "witness ({x},{y}) must trip the assert_eq! in the original fn"
    );
}

// ---- Rung 1: big-endian 16-bit header field parse∘serialize round-trip --------

/// Serialize two header bytes into a big-endian 16-bit word, then parse them back
/// out: the round-trip is the identity. A wire-format faithfulness proof. (All
/// `u16` with masked inputs — no variable casts.)
#[verify]
fn be16_field_roundtrip(hi: u16, lo: u16) -> u16 {
    let hi8: u16 = hi & 0x00ff;
    let lo8: u16 = lo & 0x00ff;
    let word: u16 = (hi8 << 8) | lo8; // serialize, big-endian
    let back_hi: u16 = word >> 8; // parse
    let back_lo: u16 = word & 0x00ff;
    assert_eq!(back_hi, hi8);
    assert_eq!(back_lo, lo8);
    word
}

// ---- Rung 1: TCP sequence-number algebra under mod-2^32 wraparound ------------

/// Advancing a sequence number by `n` and then retreating by `n` returns the
/// original, for ALL `seq`, `n` — the wraparound round-trip identity at the heart
/// of RFC-1982-style serial-number arithmetic. `wrapping_*` is exact modular BV.
///
/// Modeled at 8-bit width: the identity is width-agnostic, but the `(a+n)-n == a`
/// carry-chain equivalence *miter + certificate* grows steeply with width (a
/// measured perf note for the scoreboard — see the horizon doc §5, not a
/// soundness issue). 8-bit keeps the bounded UNSAT proof fast.
#[verify]
fn seq_advance_roundtrip(seq: u8, n: u8) -> u8 {
    let advanced: u8 = seq.wrapping_add(n);
    let back: u8 = advanced.wrapping_sub(n);
    assert_eq!(back, seq);
    seq
}

/// Window membership via wrapping subtraction (`seq - start < len`) is invariant
/// under translating both `seq` and `start` by the same offset `d` — because
// NOTE (measured perf wall, 2026-06-29): the window *offset shift-invariance*
// lemma `(seq - start) == ((seq + d) - (start + d))` — two wrapping subtractions
// over the same `d` — is deliberately NOT committed as a live example. Although
// structurally close to `seq_advance_roundtrip` (which proves in ~2.4 s at u8),
// its equivalence-miter + certificate did not finish within minutes even at u8,
// while a `Sat` bug witness over the same shape is instant. The asymmetry
// (cheap cancellation `(a+n)-n` vs. cross-cancellation `(a+d)-(b+d)`) is a
// concrete demand-pull finding for the verify/solver lane: the bit-blast +
// proof-producing route on chained modular subtractions is the bottleneck, not
// the IR or the fragment. `seq_advance_roundtrip` above carries the
// modular-algebra demonstration; see the horizon doc §7 (honest limits).

/// BUG: the *naive* (non-wrapping) window upper bound `start + len` overflows
/// `u32` for large `start`/`len` — the classic defect the wrapping formulation
/// above avoids. A reachable `add overflow`.
#[verify(expect_bug)]
fn naive_window_upper_overflows(start: u32, len: u32) -> u32 {
    let upper: u32 = start + len; // overflow witness
    upper
}

#[test]
fn naive_window_overflow_reproduces() {
    let Verdict::Counterexample { class, inputs } = naive_window_upper_overflows__axeyum_verdict()
    else {
        panic!("the naive window upper bound must be able to overflow");
    };
    assert_eq!(class, "add overflow");
    let start = int_bits(&inputs, "start");
    let len = int_bits(&inputs, "len");
    assert!(
        axeyum_verify::reproduce::panics_on(move || {
            let _ = naive_window_upper_overflows(start as u32, len as u32);
        }),
        "witness start={start}, len={len} must overflow-panic in the original fn"
    );
}

// ---- helper --------------------------------------------------------------------

fn int_bits(inputs: &[Witness], name: &str) -> u128 {
    inputs
        .iter()
        .find_map(|w| match w {
            Witness::Int { name: n, bits, .. } if n == name => Some(*bits),
            _ => None,
        })
        .unwrap_or_else(|| panic!("no int witness `{name}` in {inputs:?}"))
}
