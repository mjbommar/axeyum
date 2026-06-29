//! Block B of the *verified systems & protocols* backlog
//! ([`docs/consumer-track/verify/verified-systems-and-protocols.md`]) — worked
//! examples driving the real `#[axeyum::verify]` macro on **systems** code with
//! fixed arrays + `#[unwind(K)]`-bounded loops (rung 3). The recurring property
//! is *memory safety of index arithmetic over attacker-influenced inputs* — the
//! seL4-flavored core: ring buffers, capability/slot indexing, length-guarded
//! copies.
//!
//! Safe fns' generated tests assert `Verified` (no out-of-bounds reachable within
//! the unwind bound); `#[verify(expect_bug)]` fns assert a counterexample is found
//! and that the witness re-panics in the original fn (DISAGREE = 0). Guarantees
//! are **bounded** (fixed array sizes, fixed `#[unwind(K)]`).
//!
//! Preconditions are encoded by masking inputs into range (no `requires`); indices
//! are `usize` (modeled at 64-bit).

#![allow(clippy::similar_names)]

use axeyum_verify::{Verdict, Witness, verify};

// ---- Ring buffer: wrapped slot indexing stays in bounds (seL4-IPC flavored) ----

/// Sum every slot of a capacity-4 ring buffer starting at `start`, wrapping the
/// index modulo the capacity. Masking `start` into `[0,4)` and adding `i < 4`
/// keeps `s + i < 8` (no `usize` overflow) and `% 4` keeps every access in bounds
/// — so the indexing is proven memory-safe for all `start`.
#[verify]
#[axeyum_verify::unwind(5)]
fn ring_wrapped_read_safe(buf: [u8; 4], start: usize) -> u8 {
    let s: usize = start % 4; // s in [0, 4)
    let mut acc: u8 = 0;
    let mut i: usize = 0;
    while i < 4 {
        let idx: usize = (s + i) % 4; // s<4, i<4 => sum<8, no overflow; idx<4
        acc = acc.wrapping_add(buf[idx]);
        i += 1;
    }
    acc
}

/// BUG: the same loop with the `% 4` wrap *dropped* — a classic off-by-wrap. The
/// raw index `s + i` reaches 6, so `buf[idx]` goes out of bounds.
#[verify(expect_bug)]
#[axeyum_verify::unwind(5)]
fn ring_unwrapped_read_oob(buf: [u8; 4], start: usize) -> u8 {
    let s: usize = start % 4;
    let mut acc: u8 = 0;
    let mut i: usize = 0;
    while i < 4 {
        let idx: usize = s + i; // BUG: forgot `% 4`; idx can reach 6
        acc = acc.wrapping_add(buf[idx]); // out of bounds when idx >= 4
        i += 1;
    }
    acc
}

#[test]
fn ring_unwrapped_oob_reproduces() {
    let Verdict::Counterexample { class, inputs } = ring_unwrapped_read_oob__axeyum_verdict()
    else {
        panic!("dropping the modular wrap must reach an out-of-bounds index");
    };
    assert_eq!(class, "index out of bounds");
    let start = int_bits(&inputs, "start") as usize;
    assert!(
        axeyum_verify::reproduce::panics_on(move || {
            let _ = ring_unwrapped_read_oob([0u8; 4], start);
        }),
        "witness start={start} must index-panic in the original fn"
    );
}

// ---- Length-guarded buffer read (a Heartbleed-shaped bounds check) -------------

/// Read `len` bytes from a 4-byte buffer, but *clamp* the attacker-supplied length
/// to the buffer size first (`len.min(4)`). The clamp is the fix: `i < n <= 4`
/// keeps every access in bounds, proven for all `len`.
#[verify]
#[axeyum_verify::unwind(5)]
fn bounded_read_safe(src: [u8; 4], len: usize) -> u8 {
    let n: usize = len.min(4); // the guard
    let mut acc: u8 = 0;
    let mut i: usize = 0;
    while i < n {
        acc = acc.wrapping_add(src[i]); // i < n <= 4 => in bounds
        i += 1;
    }
    acc
}

/// BUG: trusting the attacker-supplied `len` without clamping it to the buffer
/// size — the Heartbleed shape. For `len >= 5` the read walks off the 4-byte
/// buffer within the unwind bound.
#[verify(expect_bug)]
#[axeyum_verify::unwind(5)]
fn unbounded_read_oob(src: [u8; 4], len: usize) -> u8 {
    let n: usize = len; // BUG: no `.min(4)` clamp
    let mut acc: u8 = 0;
    let mut i: usize = 0;
    while i < n {
        acc = acc.wrapping_add(src[i]); // out of bounds once i >= 4
        i += 1;
    }
    acc
}

#[test]
fn unbounded_read_oob_reproduces() {
    let Verdict::Counterexample { class, inputs } = unbounded_read_oob__axeyum_verdict() else {
        panic!("an unclamped length must read past the buffer");
    };
    assert_eq!(class, "index out of bounds");
    let len = int_bits(&inputs, "len") as usize;
    assert!(
        len >= 4,
        "OOB witness len={len} must reach index >= buffer len 4"
    );
    assert!(
        axeyum_verify::reproduce::panics_on(move || {
            let _ = unbounded_read_oob([0u8; 4], len);
        }),
        "witness len={len} must index-panic in the original fn"
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
