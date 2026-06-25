//! v0 worked examples: a proved bit-vector property (with a re-checked
//! certificate), a proved bounded-integer property, and a deliberately-false
//! property whose concrete counterexample is asserted on.

use axeyum_property::{Bv, Ctx, Int, Outcome, property};

/// Overflow-safe add: for all 32-bit `a, b` with `a, b < 2^31`, `a + b` does not
/// wrap below `a` (i.e. `a + b >= a` unsigned). Proves, and the certificate
/// re-checks. With `certificate(true)` it may also emit a Lean module.
#[test]
fn overflow_safe_add_proves_with_certificate() {
    let ctx = Ctx::new();
    let half: u128 = 1 << 31;
    let outcome = property()
        .certificate(true)
        .forall::<(Bv<32>, Bv<32>)>(&ctx)
        .assuming(|(a, b)| a.ult(Bv::lit(&ctx, half)) & b.ult(Bv::lit(&ctx, half)))
        .check(|(a, b)| (a + b).uge(a))
        .expect("solver did not error");

    match outcome {
        Outcome::Proved(cert) => {
            assert!(cert.verify().expect("certificate re-check did not error"));
            // Lean module is best-effort; QF_BV is in the reconstructable fragment,
            // but we do not require it to be present.
            let _ = cert.to_lean_module();
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

/// A small `QF_BV` theorem in the Lean-reconstructable fragment: for 2-bit
/// `a, b`, it is never the case that both `a <= b` and `b < a`. Proves, and with
/// `certificate(true)` the certificate carries a standalone Lean module (the
/// differentiator) — the negated goal flattens to the two conjuncts
/// `[a <= b, b < a]`, the shape the `QF_BV` reconstructor recognizes.
#[test]
fn bv_comparison_proves_with_lean_certificate() {
    let ctx = Ctx::new();
    let outcome = property()
        .certificate(true)
        .forall::<(Bv<2>, Bv<2>)>(&ctx)
        .check(|(a, b)| (a.ule(b) & b.ult(a)).negate())
        .expect("solver did not error");
    match outcome {
        Outcome::Proved(cert) => {
            assert!(cert.verify().expect("certificate re-check did not error"));
            let lean = cert
                .to_lean_module()
                .expect("QF_BV comparison is in the Lean-reconstructable fragment");
            assert!(
                lean.contains("axeyum_refutation") && lean.contains("False"),
                "Lean module should prove the refutation to False"
            );
        }
        other => panic!("expected Proved, got {other:?}"),
    }
}

/// `|x| >= 0` over bounded integers (`-1000 <= x <= 1000`): proves.
#[test]
fn abs_is_nonnegative_proves() {
    let ctx = Ctx::new();
    let outcome = property()
        .forall::<Int>(&ctx)
        .assuming(|x| x.ge(Int::lit(&ctx, -1000)) & x.le(Int::lit(&ctx, 1000)))
        .check(|x| x.abs().ge(Int::lit(&ctx, 0)))
        .expect("solver did not error");
    assert!(
        matches!(outcome, Outcome::Proved(_)),
        "expected Proved, got {outcome:?}"
    );
}

/// A deliberately-false property: unrestricted 8-bit `a + b >= a` is NOT a
/// theorem (it wraps). Expect a concrete counterexample that actually wraps.
#[test]
fn unrestricted_add_yields_counterexample() {
    let ctx = Ctx::new();
    let outcome = property()
        .forall::<(Bv<8>, Bv<8>)>(&ctx)
        .check(|(a, b)| (a + b).uge(a))
        .expect("solver did not error");

    match outcome {
        Outcome::Counterexample((a, b)) => {
            // The reported pair must genuinely violate `a + b >= a` over 8 bits.
            let sum = (a + b) & 0xff;
            assert!(
                sum < a,
                "counterexample a={a}, b={b} should wrap: (a+b)&0xff = {sum} < a"
            );
        }
        other => panic!("expected Counterexample, got {other:?}"),
    }
}

/// A false bounded-integer property: `x > 0` does not hold for all `x` in
/// `[-5, 5]`. Expect a concrete `x <= 0`.
#[test]
fn false_int_property_yields_counterexample() {
    let ctx = Ctx::new();
    let outcome = property()
        .forall::<Int>(&ctx)
        .assuming(|x| x.ge(Int::lit(&ctx, -5)) & x.le(Int::lit(&ctx, 5)))
        .check(|x| x.gt(Int::lit(&ctx, 0)))
        .expect("solver did not error");

    match outcome {
        Outcome::Counterexample(x) => {
            assert!(x <= 0, "counterexample x={x} should violate x > 0");
            assert!(
                (-5..=5).contains(&x),
                "counterexample x={x} must satisfy the precondition"
            );
        }
        other => panic!("expected Counterexample, got {other:?}"),
    }
}
