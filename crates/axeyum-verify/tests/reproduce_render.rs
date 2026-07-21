//! Rendering a counterexample to a committed regression `#[test]` via the shared
//! `axeyum-property` reproduction layer (App C ↔ App B alignment).

use axeyum_verify::reproduce::render_counterexample_test;
use axeyum_verify::{Witness, signed_value};

const I128_MIN_LITERAL: i128 = -170_141_183_460_469_231_731_687_303_715_884_105_728_i128;
const I128_EDGE_ARRAY: [i128; 4] = [
    -170_141_183_460_469_231_731_687_303_715_884_105_728_i128,
    -1i128,
    0i128,
    170_141_183_460_469_231_731_687_303_715_884_105_727_i128,
];

#[test]
fn renders_scalar_counterexample_test() {
    // The u8-add-overflow witness (a=200, b=100).
    let inputs = vec![
        Witness::Int {
            name: "a".into(),
            width: 8,
            signed: false,
            bits: 200,
        },
        Witness::Int {
            name: "b".into(),
            width: 8,
            signed: false,
            bits: 100,
        },
    ];
    let src =
        render_counterexample_test("add_overflow_repro", "add", "a, b", "add overflow", &inputs);
    // Shared format: a `#[test]` with typed `let` bindings, then a panic assert.
    assert!(src.contains("#[test]"));
    assert!(src.contains("fn add_overflow_repro()"));
    assert!(src.contains("let a: u8 = 200u8;"));
    assert!(src.contains("let b: u8 = 100u8;"));
    assert!(src.contains("let _ = add(a, b);"));
    assert!(src.contains("add overflow"));
}

#[test]
fn renders_array_counterexample_test() {
    let inputs = vec![
        Witness::Array {
            name: "buf".into(),
            width: 8,
            signed: false,
            ints: vec![1, 2, 3, 4],
        },
        Witness::Int {
            name: "i".into(),
            width: 64,
            signed: false,
            bits: 9,
        },
    ];
    let src =
        render_counterexample_test("oob_repro", "get", "buf, i", "index out of bounds", &inputs);
    assert!(src.contains("let buf: [u8; 4] = [1u8, 2u8, 3u8, 4u8];"));
    assert!(src.contains("let i: u64 = 9u64;"));
    assert!(src.contains("let _ = get(buf, i);"));
}

#[test]
fn renders_signed_counterexample_test() {
    // i8 = -128 (bit-pattern 0x80) must render as the signed decimal.
    let inputs = vec![Witness::Int {
        name: "x".into(),
        width: 8,
        signed: true,
        bits: 0x80,
    }];
    let src = render_counterexample_test("neg_repro", "neg", "x", "negation overflow", &inputs);
    assert!(src.contains("let x: i8 = -128i8;"), "got: {src}");
}

#[test]
fn signed_values_reinterpret_every_width_exactly() {
    let mut state = 0x5eed_cafe_dead_beef_0123_4567_89ab_cdef_u128;
    for width in 1..=128 {
        let mask = if width == 128 {
            u128::MAX
        } else {
            (1_u128 << width) - 1
        };
        let sign = 1_u128 << (width - 1);
        for bits in [0, 1, sign - 1, sign, mask] {
            let shifted = (bits & mask) << (128 - width);
            let expected = shifted.cast_signed() >> (128 - width);
            assert_eq!(
                signed_value(width, bits),
                expected,
                "width={width} bits={bits}"
            );
        }
        for _ in 0..16 {
            state = state
                .wrapping_mul(0xda94_2042_e4dd_58b5_8b5a_d4ce_2f53_6e6d)
                .wrapping_add(1);
            let bits = state & mask;
            let shifted = bits << (128 - width);
            let expected = shifted.cast_signed() >> (128 - width);
            assert_eq!(
                signed_value(width, bits),
                expected,
                "width={width} bits={bits}"
            );
        }
    }
}

#[test]
fn renders_signed_i128_boundaries_for_scalars_and_arrays() {
    assert_eq!(I128_MIN_LITERAL, i128::MIN);
    assert_eq!(I128_EDGE_ARRAY, [i128::MIN, -1, 0, i128::MAX]);
    let inputs = vec![
        Witness::Int {
            name: "minimum".into(),
            width: 128,
            signed: true,
            bits: i128::MIN.cast_unsigned(),
        },
        Witness::Int {
            name: "maximum".into(),
            width: 128,
            signed: true,
            bits: i128::MAX.cast_unsigned(),
        },
        Witness::Array {
            name: "edges".into(),
            width: 128,
            signed: true,
            ints: vec![
                i128::MIN.cast_unsigned(),
                u128::MAX,
                0,
                i128::MAX.cast_unsigned(),
            ],
        },
    ];
    let src = render_counterexample_test(
        "i128_edges_repro",
        "consume_i128_edges",
        "minimum, maximum, edges",
        "signed boundary",
        &inputs,
    );
    assert!(
        src.contains("let minimum: i128 = -170141183460469231731687303715884105728i128;"),
        "got: {src}"
    );
    assert!(
        src.contains("let maximum: i128 = 170141183460469231731687303715884105727i128;"),
        "got: {src}"
    );
    assert!(
        src.contains(
            "let edges: [i128; 4] = [-170141183460469231731687303715884105728i128, -1i128, 0i128, 170141183460469231731687303715884105727i128];"
        ),
        "got: {src}"
    );
}
