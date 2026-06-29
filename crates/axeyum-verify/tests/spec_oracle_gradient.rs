//! The **fuzz ↔ proof gradient** (spec-as-oracle) for the verified systems &
//! protocols backlog ([`docs/consumer-track/verify/verified-systems-and-protocols.md`]
//! §5). The *same* reference spec drives two ends of one dial:
//!
//! - **Cheap end (here):** ordinary executable Rust. A reference `*_spec` and a
//!   fast `*_fast` impl are checked to agree by a deterministic differential
//!   sweep (and the spec catches a buggy impl) — always-on, sub-millisecond, no
//!   solver, no new dependency.
//! - **Expensive end:** the `#[axeyum::verify]` equivalence proof over the same
//!   property (`network_examples::ic_carry_fold_equiv`, `seq_advance_roundtrip`)
//!   discharges it for *all* inputs with a re-checked certificate.
//!
//! The point: "verified" becomes a dial you turn up locally rather than a heroic
//! one-off. These functions are plain Rust (the "two readings" — they also happen
//! to be in the `#[verify]` fragment), so `as` casts etc. are unrestricted here.

#![allow(clippy::unreadable_literal)]

// ---- reference spec + impls (ordinary Rust) ------------------------------------

/// Reference: 16-bit ones-complement end-around-carry fold, carry added back in.
fn ic_fold_spec(x: u16, y: u16) -> u32 {
    let s: u32 = u32::from(x) + u32::from(y);
    (s & 0xffff) + (s >> 16)
}

/// Fast impl: end-around carry as a conditional subtract of `0xffff`.
fn ic_fold_fast(x: u16, y: u16) -> u32 {
    let s: u32 = u32::from(x) + u32::from(y);
    if s > 0xffff { s - 0xffff } else { s }
}

/// Buggy impl: drops the end-around carry (just masks).
fn ic_fold_buggy(x: u16, y: u16) -> u32 {
    let s: u32 = u32::from(x) + u32::from(y);
    s & 0xffff
}

/// Deterministic LCG (no `rand` dependency) so the sweep is reproducible.
fn lcg(state: &mut u32) -> u16 {
    *state = state.wrapping_mul(1664525).wrapping_add(1013904223);
    (*state >> 16) as u16
}

// ---- cheap end: the spec as a differential oracle ------------------------------

/// The fast fold agrees with the reference spec across a large deterministic
/// sample — the cheap, always-on mirror of `ic_carry_fold_equiv`'s exhaustive
/// `#[verify]` proof.
#[test]
fn ic_fold_fast_matches_spec_under_sampling() {
    let mut st: u32 = 0x1234_5678;
    for _ in 0..200_000 {
        let x = lcg(&mut st);
        let y = lcg(&mut st);
        assert_eq!(
            ic_fold_fast(x, y),
            ic_fold_spec(x, y),
            "fast fold diverged from spec at x={x:#06x}, y={y:#06x}"
        );
    }
}

/// The same cheap oracle has real *detection* power: it finds an `(x, y)` where
/// the carry-dropping impl diverges from the spec — the cheap mirror of the
/// `#[verify]` counterexample in `ic_missing_carry_bug`.
#[test]
fn ic_fold_oracle_catches_missing_carry() {
    let mut st: u32 = 0x1;
    let mut diverged = None;
    for _ in 0..200_000 {
        let x = lcg(&mut st);
        let y = lcg(&mut st);
        if ic_fold_buggy(x, y) != ic_fold_spec(x, y) {
            diverged = Some((x, y));
            break;
        }
    }
    let (x, y) = diverged.expect("the oracle must catch the dropped-carry divergence");
    // Confirm the witness genuinely diverges (the cheap-end soundness floor).
    assert_ne!(ic_fold_buggy(x, y), ic_fold_spec(x, y));
}

/// Sequence-number wraparound roundtrip, checked **exhaustively** at `u8`
/// (65 536 pairs, sub-millisecond) — the exhaustive cheap end that the `#[verify]`
/// proof generalizes to all inputs symbolically.
#[test]
fn seq_advance_roundtrip_exhaustive_u8() {
    for seq in 0u8..=u8::MAX {
        for n in 0u8..=u8::MAX {
            assert_eq!(seq.wrapping_add(n).wrapping_sub(n), seq);
        }
    }
}
