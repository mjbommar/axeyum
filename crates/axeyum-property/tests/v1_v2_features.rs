//! v1/v2 feature tests: `#[derive(Symbolic)]` (structs beyond arity 3),
//! `Bounded<LO, HI>` (auto-emitted range assume), fixed `BvArray<EW, N>`
//! (symbolic arrays + in-bounds indexing), and the counterexample → `#[test]`
//! reproduction layer.

use axeyum_property::{
    Bounded, Bv, BvArray, Ctx, Int, Outcome, Reproduction, Symbolic, Witness, WitnessBinding,
    property, render_reproduction_test,
};

/// A derived 4-field struct (beyond the arity-3 tuple ceiling). The companion
/// `Quad4Concrete` carries the counterexample.
#[derive(Symbolic, Clone, Copy)]
struct Quad4<'c> {
    a: Bv<'c, 8>,
    b: Bv<'c, 8>,
    c: Bv<'c, 8>,
    d: Bv<'c, 8>,
}

/// `#[derive(Symbolic)]` proves a 4-field struct property: `(a^b)^(c^d)` equals
/// `(a^c)^(b^d)` (XOR associativity/commutativity), all 8-bit.
#[test]
fn derive_struct_proves_xor_rearrange() {
    let ctx = Ctx::new();
    let outcome = property()
        .forall::<Quad4>(&ctx)
        .check(|q| ((q.a ^ q.b) ^ (q.c ^ q.d)).equals((q.a ^ q.c) ^ (q.b ^ q.d)))
        .expect("solver did not error");
    assert!(
        matches!(outcome, Outcome::Proved(_)),
        "expected Proved, got {outcome:?}"
    );
}

/// A derived struct with a deliberately-false property yields a typed concrete
/// counterexample (the generated `Quad4Concrete`).
#[test]
fn derive_struct_counterexample_is_typed() {
    let ctx = Ctx::new();
    let outcome = property()
        .forall::<Quad4>(&ctx)
        // False: a + b + c + d == 0 does not hold for all 8-bit inputs.
        .check(|q| (q.a + q.b + q.c + q.d).equals(Bv::lit(&ctx, 0)))
        .expect("solver did not error");
    match outcome {
        Outcome::Counterexample(ce) => {
            let sum = (ce
                .a
                .wrapping_add(ce.b)
                .wrapping_add(ce.c)
                .wrapping_add(ce.d))
                & 0xff;
            assert!(sum != 0, "counterexample must violate sum == 0, got {ce:?}");
        }
        other => panic!("expected Counterexample, got {other:?}"),
    }
}

/// `Bounded<LO, HI>` emits its own range assume: `|x| >= 0` proves over
/// `[-1000, 1000]` with NO manual `.assuming(..)`.
#[test]
fn bounded_emits_range_assume_and_proves() {
    let ctx = Ctx::new();
    let outcome = property()
        .forall::<Bounded<-1000, 1000>>(&ctx)
        .check(|x| x.value().abs().ge(Int::lit(&ctx, 0)))
        .expect("solver did not error");
    assert!(
        matches!(outcome, Outcome::Proved(_)),
        "expected Proved, got {outcome:?}"
    );
}

/// The `Bounded` range is a real constraint: `x < 10` over `[0, 10]` finds the
/// off-by-one counterexample `x = 10` (inside the auto-assumed range).
#[test]
fn bounded_range_is_a_real_constraint() {
    let ctx = Ctx::new();
    let outcome = property()
        .forall::<Bounded<0, 10>>(&ctx)
        .check(|x| x.value().lt(Int::lit(&ctx, 10)))
        .expect("solver did not error");
    match outcome {
        Outcome::Counterexample(x) => {
            assert_eq!(x, 10, "the only in-range counterexample is x = 10");
        }
        other => panic!("expected Counterexample x=10, got {other:?}"),
    }
}

/// A `Bounded` whose bound makes the property true everywhere in range still
/// proves: for `x in [0, 100]`, `x + 1 > x` (no integer overflow in `Sort::Int`).
#[test]
fn bounded_proves_in_range_identity() {
    let ctx = Ctx::new();
    let outcome = property()
        .forall::<Bounded<0, 100>>(&ctx)
        .check(|x| (x.value() + Int::lit(&ctx, 1)).gt(x.value()))
        .expect("solver did not error");
    assert!(
        matches!(outcome, Outcome::Proved(_)),
        "expected Proved, got {outcome:?}"
    );
}

/// Fixed `BvArray<8, 4>`: a store-then-select round-trips. For a symbolic array
/// `arr`, value `v`, and in-bounds index `i`, `store(arr, i, v).select(i) == v`
/// (the read-over-write axiom `select(store(a,i,v),i) == v`). Proves.
#[test]
fn array_store_select_roundtrip_proves() {
    let ctx = Ctx::new();
    let outcome = property()
        .forall::<(BvArray<8, 4>, Bv<32>, Bv<8>)>(&ctx)
        .check(|(arr, i, v)| arr.store(i, v).select(i).equals(v))
        .expect("solver did not error");
    assert!(
        matches!(outcome, Outcome::Proved(_)),
        "expected Proved, got {outcome:?}"
    );
}

/// A false array property finds a typed `[u128; 4]` counterexample: not every
/// symbolic 4-element array has element 0 equal to element 1.
#[test]
fn array_counterexample_lifts_to_fixed_array() {
    let ctx = Ctx::new();
    let outcome = property()
        .forall::<BvArray<8, 4>>(&ctx)
        .check(|arr| arr.get(0).equals(arr.get(1)))
        .expect("solver did not error");
    match outcome {
        Outcome::Counterexample(elems) => {
            assert_eq!(elems.len(), 4, "must lift to a 4-element array");
            assert_ne!(
                elems[0], elems[1],
                "counterexample must have distinct elements 0 and 1, got {elems:?}"
            );
        }
        other => panic!("expected Counterexample, got {other:?}"),
    }
}

/// The reproduction layer renders a runnable `#[test]` from raw bindings.
#[test]
fn reproduction_renders_runnable_test() {
    let bindings = vec![
        WitnessBinding::new("a", "u8", "1u8"),
        WitnessBinding::new("b", "u8", "255u8"),
    ];
    let src = render_reproduction_test(
        &Reproduction::new("bv8_add_wraps", bindings).body("assert!(a.checked_add(b).is_none());"),
    );
    assert!(src.contains("#[test]"));
    assert!(src.contains("fn bv8_add_wraps()"));
    assert!(src.contains("    let a: u8 = 1u8;"));
    assert!(src.contains("    let b: u8 = 255u8;"));
    assert!(src.contains("    assert!(a.checked_add(b).is_none());"));
}

/// An app's witness type implements `Witness`; `Reproduction::from_witness`
/// renders it (the shared A/C path — verify-args here, calldata for EVM).
#[test]
fn reproduction_from_witness_trait() {
    struct ArgsWitness {
        a: u64,
        b: u64,
    }
    impl Witness for ArgsWitness {
        fn bindings(&self) -> Vec<WitnessBinding> {
            vec![
                WitnessBinding::new("a", "u64", format!("{}u64", self.a)),
                WitnessBinding::new("b", "u64", format!("{}u64", self.b)),
            ]
        }
    }
    let w = ArgsWitness { a: 7, b: 9 };
    let src = render_reproduction_test(
        &Reproduction::from_witness("repro_args", &w).body("assert_eq!(add(a, b), 16);"),
    );
    assert!(src.contains("let a: u64 = 7u64;"));
    assert!(src.contains("let b: u64 = 9u64;"));
    assert!(src.contains("assert_eq!(add(a, b), 16);"));
}
