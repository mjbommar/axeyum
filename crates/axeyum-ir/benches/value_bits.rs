//! Micro-benchmarks for the LSB-first value/bit conversion helpers —
//! [`value_to_lsb_bits`] and [`lsb_bits_to_value`].
//!
//! # What real workload this is a proxy for
//!
//! Model lifting on the BV route. Measured 2026-09-07, the non-test callers of
//! these two functions outside this crate are `axeyum-bv`'s
//! `BitLowering::input_values` / `evaluate_root` / `evaluate_roots` /
//! `root_value_from_aig_values` / `root_values_from_aig_values` /
//! `assignment_from_aig_node_values`, plus the Python bindings. That is the
//! path `CLAUDE.md`'s hard rule makes mandatory on every `sat` result: the
//! lifted model has to be turned back into bits and the AIG's answer back into
//! a `Value`.
//!
//! It is a **partial** proxy and the split matters. `input_values` calls
//! `value_to_lsb_bits` once per *symbol bit* rather than once per symbol, so a
//! `w`-bit symbol pays `w` calls, each allocating a `w`-element `Vec<bool>`.
//! That interaction is measured where it lives, in `axeyum-bv`'s
//! `model_replay_input_values` group; this file measures only the primitive,
//! so the two together separate "the conversion is slow" from "the caller
//! calls it too often". Neither number alone answers the question.
//!
//! # The data-structure question the width sweep asks
//!
//! Both directions represent a bit string as `Vec<bool>` — one **byte** per
//! bit, heap-allocated per call. The sweep over 8 / 32 / 64 / 128 shows
//! whether the cost is dominated by the per-call allocation (flat until the
//! allocation stops fitting a size class) or by the per-bit loop (linear in
//! the width). Those two shapes call for opposite fixes, which is why the
//! sweep exists rather than one number at one width.
//!
//! `Value` is not `Copy` (it carries array/function/algebraic variants), so
//! the timed loop clones the `Value::Bv` it converts. That clone is a ~24-byte
//! memcpy of a stack enum with no heap traffic for this variant, and it is
//! present in **both** directions' loops, so it does not distort the width
//! comparison the sweep exists to make. It is named here rather than left for
//! a reader to discover from the code.
//!
//! Fixed widths and fixed payloads; no RNG, no seed to pin.

#![allow(missing_docs)] // criterion_group!/criterion_main! expand to undocumented items; see module doc.

use std::hint::black_box;

use axeyum_ir::{Sort, Value, lsb_bits_to_value, value_to_lsb_bits};
use criterion::{Criterion, criterion_group, criterion_main};

/// Widths spanning the `u128`-backed `Value::Bv` range. 128 is the largest
/// width `bv_value_to_lsb_bits` accepts before the `WideUint` path takes over.
const WIDTHS: &[u32] = &[8, 32, 64, 128];

/// A fixed payload that fits `width` and has bits set across the whole range,
/// so neither direction can shortcut on a mostly-zero value.
fn payload(width: u32) -> u128 {
    // Alternating nibble pattern, masked to the width. Deterministic and
    // dense: for every width at least a quarter of the bits are set.
    let full = 0x5A5A_5A5A_5A5A_5A5A_5A5A_5A5A_5A5A_5A5Au128;
    if width >= 128 {
        full
    } else {
        full & ((1u128 << width) - 1)
    }
}

fn bench_value_to_bits(c: &mut Criterion) {
    let mut group = c.benchmark_group("value_to_lsb_bits");
    for &width in WIDTHS {
        let value = Value::Bv {
            width,
            value: payload(width),
        };
        group.bench_function(format!("w{width}"), |b| {
            b.iter(|| {
                let bits = value_to_lsb_bits(value.clone()).expect("a well-formed Bv converts");
                assert_eq!(
                    bits.len(),
                    width as usize,
                    "the conversion must produce one bool per bit; a different \
                     length means the fixture stopped measuring the real path"
                );
                black_box(bits);
            });
        });
    }
    group.finish();
}

fn bench_bits_to_value(c: &mut Criterion) {
    let mut group = c.benchmark_group("lsb_bits_to_value");
    for &width in WIDTHS {
        let value = Value::Bv {
            width,
            value: payload(width),
        };
        let bits = value_to_lsb_bits(value.clone()).expect("a well-formed Bv converts");
        group.bench_function(format!("w{width}"), |b| {
            b.iter(|| {
                let restored = lsb_bits_to_value(Sort::BitVec(width), &bits)
                    .expect("bits produced by the forward direction convert back");
                assert_eq!(
                    restored, value,
                    "the round trip must be the identity; a mismatch means the \
                     fixture is measuring a wrong answer"
                );
                black_box(restored);
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_value_to_bits, bench_bits_to_value);
criterion_main!(benches);
