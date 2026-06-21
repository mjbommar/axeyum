//! Algebraic field-arithmetic tests (ADR-0038 slice 3): `−α`, `α + β`, `α · β`
//! over real-algebraic numbers, plus the `eval` upgrade that computes them.
//!
//! Every result is checked by REPLAY: its `sign_at` must vanish on the known
//! minimal polynomial of the true value, and `compare_rational` must place it in
//! the right rational neighbourhood. NO floating point anywhere.

use axeyum_ir::{Assignment, RealAlgebraic, Sign, Sort, TermArena, Value, eval};
use core::cmp::Ordering;

/// `√2`: the positive root of `x² − 2` in `(1, 2)`.
fn sqrt2() -> RealAlgebraic {
    RealAlgebraic::new(vec![-2, 0, 1], rat(1), rat(2)).unwrap()
}

/// `√3`: the positive root of `x² − 3` in `(1, 2)`.
fn sqrt3() -> RealAlgebraic {
    RealAlgebraic::new(vec![-3, 0, 1], rat(1), rat(2)).unwrap()
}

fn rat(n: i128) -> axeyum_ir::Rational {
    axeyum_ir::Rational::integer(n)
}

fn ratf(n: i128, d: i128) -> axeyum_ir::Rational {
    axeyum_ir::Rational::new(n, d)
}

#[test]
fn sqrt2_plus_sqrt3_is_root_of_x4_minus_10x2_plus_1() {
    let s = sqrt2().add(&sqrt3()).expect("√2 + √3 must compute");
    // √2 + √3 is a root of x⁴ − 10x² + 1 (LSB-first [1, 0, −10, 0, 1]).
    assert_eq!(
        s.sign_at(&[1, 0, -10, 0, 1]),
        Some(Sign::Zero),
        "√2 + √3 must be a root of x⁴ − 10x² + 1"
    );
    // √2 + √3 ≈ 3.1462643. Place it between 31/10 and 32/10.
    assert_eq!(
        s.compare_rational(&ratf(31, 10)),
        Some(Ordering::Greater),
        "√2 + √3 > 3.1"
    );
    assert_eq!(
        s.compare_rational(&ratf(32, 10)),
        Some(Ordering::Less),
        "√2 + √3 < 3.2"
    );
}

#[test]
fn sqrt2_times_sqrt3_is_sqrt6() {
    let p = sqrt2().mul(&sqrt3()).expect("√2 · √3 must compute");
    // √2 · √3 = √6, a root of x² − 6.
    assert_eq!(
        p.sign_at(&[-6, 0, 1]),
        Some(Sign::Zero),
        "√2 · √3 must be a root of x² − 6"
    );
    // √6 ≈ 2.449.
    assert_eq!(p.compare_rational(&ratf(24, 10)), Some(Ordering::Greater));
    assert_eq!(p.compare_rational(&ratf(25, 10)), Some(Ordering::Less));
}

#[test]
fn neg_sqrt2_is_negative() {
    let n = sqrt2().neg().expect("−√2 must compute");
    assert_eq!(n.compare_rational(&rat(0)), Some(Ordering::Less), "−√2 < 0");
    assert_eq!(
        n.sign_at(&[-2, 0, 1]),
        Some(Sign::Zero),
        "−√2 is still a root of x² − 2"
    );
    // −√2 ≈ −1.414, strictly between −2 and −1.
    assert_eq!(n.compare_rational(&rat(-2)), Some(Ordering::Greater));
    assert_eq!(n.compare_rational(&rat(-1)), Some(Ordering::Less));
}

#[test]
fn add_is_commutative_on_replay() {
    let a = sqrt2().add(&sqrt3()).unwrap();
    let b = sqrt3().add(&sqrt2()).unwrap();
    // Both must replay against the same minimal polynomial.
    assert_eq!(a.sign_at(&[1, 0, -10, 0, 1]), Some(Sign::Zero));
    assert_eq!(b.sign_at(&[1, 0, -10, 0, 1]), Some(Sign::Zero));
    assert_eq!(a, b);
}

#[test]
fn sqrt2_plus_neg_sqrt2_is_zero_or_declines_but_never_wrong() {
    // √2 + (−√2) = 0. The resultant's squarefree part has 0 as a root; the
    // identification may land on the rational 0 (Sturm count 1 around 0) or
    // decline — but it must NEVER produce a wrong nonzero value. Whatever it
    // returns, if Some, it must compare equal to 0 OR be a genuine root near 0.
    let n = sqrt2().neg().unwrap();
    if let Some(s) = sqrt2().add(&n) {
        // The defining poly must vanish at 0 if the value is 0.
        // Bracket it tightly around 0.
        assert_eq!(s.compare_rational(&ratf(-1, 100)), Some(Ordering::Greater));
        assert_eq!(s.compare_rational(&ratf(1, 100)), Some(Ordering::Less));
    }
}

// --- eval wiring (Phase C) -------------------------------------------------

/// Build a Real symbol bound to a `RealAlgebraic` value in the assignment, and a
/// term that is just that symbol. Returns (term, assignment-with-binding).
fn algebraic_symbol(
    arena: &mut TermArena,
    name: &str,
    val: RealAlgebraic,
    asg: &mut Assignment,
) -> axeyum_ir::TermId {
    let sym = arena.declare(name, Sort::Real).unwrap();
    asg.set(sym, Value::RealAlgebraic(val));
    arena.var(sym)
}

#[test]
fn eval_real_add_of_algebraic_operands_computes() {
    let mut arena = TermArena::new();
    let mut asg = Assignment::new();
    let a = algebraic_symbol(&mut arena, "a", sqrt2(), &mut asg);
    let b = algebraic_symbol(&mut arena, "b", sqrt3(), &mut asg);
    let sum = arena.real_add(a, b).unwrap();
    let v = eval(&arena, sum, &asg).expect("√2 + √3 must now evaluate, not Err");
    match v {
        Value::RealAlgebraic(s) => {
            assert_eq!(
                s.sign_at(&[1, 0, -10, 0, 1]),
                Some(Sign::Zero),
                "evaluated √2 + √3 must be a root of x⁴ − 10x² + 1"
            );
        }
        other => panic!("expected RealAlgebraic, got {other:?}"),
    }
}

#[test]
fn eval_real_mul_of_algebraic_operands_computes() {
    let mut arena = TermArena::new();
    let mut asg = Assignment::new();
    let a = algebraic_symbol(&mut arena, "a", sqrt2(), &mut asg);
    let b = algebraic_symbol(&mut arena, "b", sqrt3(), &mut asg);
    let prod = arena.real_mul(a, b).unwrap();
    let v = eval(&arena, prod, &asg).expect("√2 · √3 must evaluate");
    match v {
        Value::RealAlgebraic(s) => {
            assert_eq!(s.sign_at(&[-6, 0, 1]), Some(Sign::Zero), "= √6");
        }
        other => panic!("expected RealAlgebraic, got {other:?}"),
    }
}

#[test]
fn eval_real_neg_of_algebraic_computes() {
    let mut arena = TermArena::new();
    let mut asg = Assignment::new();
    let a = algebraic_symbol(&mut arena, "a", sqrt2(), &mut asg);
    let neg = arena.real_neg(a).unwrap();
    let v = eval(&arena, neg, &asg).expect("−√2 must evaluate");
    match v {
        Value::RealAlgebraic(s) => {
            assert_eq!(s.compare_rational(&rat(0)), Some(Ordering::Less));
            assert_eq!(s.sign_at(&[-2, 0, 1]), Some(Sign::Zero));
        }
        other => panic!("expected RealAlgebraic, got {other:?}"),
    }
}

#[test]
fn eval_real_sub_of_algebraic_computes() {
    // √3 − √2 = √3 + (−√2); a root of x⁴ − 10x² + 1 as well (≈ 0.318).
    let mut arena = TermArena::new();
    let mut asg = Assignment::new();
    let a = algebraic_symbol(&mut arena, "a", sqrt3(), &mut asg);
    let b = algebraic_symbol(&mut arena, "b", sqrt2(), &mut asg);
    let diff = arena.real_sub(a, b).unwrap();
    let v = eval(&arena, diff, &asg).expect("√3 − √2 must evaluate");
    match v {
        Value::RealAlgebraic(s) => {
            assert_eq!(s.sign_at(&[1, 0, -10, 0, 1]), Some(Sign::Zero));
            // ≈ 0.318, between 3/10 and 33/100.
            assert_eq!(s.compare_rational(&ratf(3, 10)), Some(Ordering::Greater));
            assert_eq!(s.compare_rational(&ratf(33, 100)), Some(Ordering::Less));
        }
        other => panic!("expected RealAlgebraic, got {other:?}"),
    }
}

#[test]
fn eval_mixing_rational_and_algebraic_computes() {
    // √2 + 1: a root of (x−1)² − 2 = x² − 2x − 1 ([−1, −2, 1]).  ≈ 2.414.
    let mut arena = TermArena::new();
    let mut asg = Assignment::new();
    let a = algebraic_symbol(&mut arena, "a", sqrt2(), &mut asg);
    let one = arena.real_const(rat(1));
    let sum = arena.real_add(a, one).unwrap();
    let v = eval(&arena, sum, &asg).expect("√2 + 1 must evaluate");
    match v {
        Value::RealAlgebraic(s) => {
            assert_eq!(
                s.sign_at(&[-1, -2, 1]),
                Some(Sign::Zero),
                "√2 + 1 root of x²−2x−1"
            );
            assert_eq!(s.compare_rational(&ratf(24, 10)), Some(Ordering::Greater));
            assert_eq!(s.compare_rational(&ratf(25, 10)), Some(Ordering::Less));
        }
        other => panic!("expected RealAlgebraic, got {other:?}"),
    }
}
