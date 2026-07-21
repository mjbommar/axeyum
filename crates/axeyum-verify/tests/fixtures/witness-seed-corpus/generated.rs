#[test]
fn equivalence_refutation_repro() {
    let x: u8 = 0u8;

    assert_ne!(corpus_reference(x), corpus_mutated(x), "wrong transform must remain distinguishable");
}

#[test]
fn overflow_panic_repro() {
    let x: u8 = 255u8;

    // class: add overflow — the original function panics on this input.
    let reproduces = std::panic::catch_unwind(|| {
        let _ = corpus_overflow(x);
    })
    .is_err();
    assert!(reproduces, "expected `corpus_overflow` to panic (add overflow)");
}

#[test]
fn postcondition_violation_repro() {
    let x: u8 = 0u8;

    let result = corpus_contract(x);
    assert!(x < 255);
    assert_ne!(result, x, "normally returned result must violate the postcondition");
}
