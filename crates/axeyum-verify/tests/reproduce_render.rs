//! Rendering a counterexample to a committed regression `#[test]` via the shared
//! `axeyum-property` reproduction layer (App C ↔ App B alignment).

use axeyum_verify::Witness;
use axeyum_verify::reproduce::render_counterexample_test;

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
