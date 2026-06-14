//! IEEE 754 floating-point predicates/comparisons as bit-vector formulas.
//! Concrete bit patterns are checked through the ground evaluator (the semantic
//! reference); a symbolic irreflexivity query goes through the solver.

use axeyum_ir::{Assignment, TermArena, Value, eval};
use axeyum_solver::fp::{self, FloatFormat};
use axeyum_solver::{CheckResult, SolverConfig, solve};

const F32: FloatFormat = FloatFormat::F32;

// Single-precision bit patterns.
const NAN: u128 = 0x7FC0_0000;
const INF: u128 = 0x7F80_0000;
const POS0: u128 = 0x0000_0000;
const NEG0: u128 = 0x8000_0000;
const ONE: u128 = 0x3F80_0000;
const TWO: u128 = 0x4000_0000;
const NEG_TWO: u128 = 0xC000_0000;

fn c(arena: &mut TermArena, bits: u128) -> axeyum_ir::TermId {
    arena.bv_const(32, bits).unwrap()
}

fn eval_bool(arena: &TermArena, term: axeyum_ir::TermId) -> bool {
    match eval(arena, term, &Assignment::new()) {
        Ok(Value::Bool(b)) => b,
        other => panic!("expected Bool, got {other:?}"),
    }
}

#[test]
fn classification() {
    let mut a = TermArena::new();

    let nan = c(&mut a, NAN);
    let t = fp::is_nan(&mut a, F32, nan).unwrap();
    assert!(eval_bool(&a, t), "0x7FC00000 is NaN");
    let one = c(&mut a, ONE);
    let t = fp::is_nan(&mut a, F32, one).unwrap();
    assert!(!eval_bool(&a, t), "1.0 is not NaN");

    let inf = c(&mut a, INF);
    let t = fp::is_infinite(&mut a, F32, inf).unwrap();
    assert!(eval_bool(&a, t), "0x7F800000 is +inf");
    let t = fp::is_infinite(&mut a, F32, nan).unwrap();
    assert!(!eval_bool(&a, t), "NaN is not infinite");

    for z in [POS0, NEG0] {
        let zt = c(&mut a, z);
        let t = fp::is_zero(&mut a, F32, zt).unwrap();
        assert!(eval_bool(&a, t), "{z:#x} is zero");
    }
    let t = fp::is_zero(&mut a, F32, one).unwrap();
    assert!(!eval_bool(&a, t), "1.0 is not zero");
}

#[test]
fn sign_predicates() {
    let mut a = TermArena::new();
    let neg_two = c(&mut a, NEG_TWO);
    let pos_two = c(&mut a, TWO);
    let neg0 = c(&mut a, NEG0);
    let nan = c(&mut a, NAN);

    let t = fp::is_negative(&mut a, F32, neg_two).unwrap();
    assert!(eval_bool(&a, t), "-2.0 is negative");
    let t = fp::is_negative(&mut a, F32, pos_two).unwrap();
    assert!(!eval_bool(&a, t), "+2.0 is not negative");
    let t = fp::is_negative(&mut a, F32, neg0).unwrap();
    assert!(!eval_bool(&a, t), "-0.0 is not negative (it is a zero)");
    let t = fp::is_negative(&mut a, F32, nan).unwrap();
    assert!(!eval_bool(&a, t), "NaN is not negative");

    let t = fp::is_positive(&mut a, F32, pos_two).unwrap();
    assert!(eval_bool(&a, t), "+2.0 is positive");
    let t = fp::is_positive(&mut a, F32, nan).unwrap();
    assert!(!eval_bool(&a, t), "NaN is not positive");
}

#[test]
fn abs_and_neg() {
    let mut a = TermArena::new();
    let neg_two = c(&mut a, NEG_TWO);
    let two = c(&mut a, TWO);

    let abs = fp::abs(&mut a, F32, neg_two).unwrap();
    let same = a.eq(abs, two).unwrap();
    assert!(eval_bool(&a, same), "abs(-2.0) == 2.0 (bitwise)");

    let neg = fp::neg(&mut a, F32, two).unwrap();
    let nt = c(&mut a, NEG_TWO);
    let same = a.eq(neg, nt).unwrap();
    assert!(eval_bool(&a, same), "neg(2.0) == -2.0 (bitwise)");
}

#[test]
fn ieee_equality() {
    let mut a = TermArena::new();
    let pos0 = c(&mut a, POS0);
    let neg0 = c(&mut a, NEG0);
    let nan = c(&mut a, NAN);
    let one = c(&mut a, ONE);

    let t = fp::eq(&mut a, F32, pos0, neg0).unwrap();
    assert!(eval_bool(&a, t), "+0 == -0");
    let t = fp::eq(&mut a, F32, nan, nan).unwrap();
    assert!(!eval_bool(&a, t), "NaN != NaN");
    let t = fp::eq(&mut a, F32, one, one).unwrap();
    assert!(eval_bool(&a, t), "1.0 == 1.0");
}

#[test]
fn ordering() {
    let mut a = TermArena::new();
    let one = c(&mut a, ONE);
    let two = c(&mut a, TWO);
    let neg_two = c(&mut a, NEG_TWO);
    let pos0 = c(&mut a, POS0);
    let neg0 = c(&mut a, NEG0);
    let nan = c(&mut a, NAN);

    let t = fp::lt(&mut a, F32, one, two).unwrap();
    assert!(eval_bool(&a, t), "1.0 < 2.0");
    let t = fp::lt(&mut a, F32, two, one).unwrap();
    assert!(!eval_bool(&a, t), "not 2.0 < 1.0");
    let t = fp::lt(&mut a, F32, neg_two, one).unwrap();
    assert!(eval_bool(&a, t), "-2.0 < 1.0");
    let t = fp::lt(&mut a, F32, neg0, pos0).unwrap();
    assert!(!eval_bool(&a, t), "not -0 < +0 (they are equal)");
    let t = fp::lt(&mut a, F32, nan, one).unwrap();
    assert!(!eval_bool(&a, t), "NaN unordered");

    let t = fp::leq(&mut a, F32, pos0, neg0).unwrap();
    assert!(eval_bool(&a, t), "+0 <= -0");
    let t = fp::geq(&mut a, F32, two, one).unwrap();
    assert!(eval_bool(&a, t), "2.0 >= 1.0");
}

#[test]
fn min_max() {
    let mut a = TermArena::new();
    let one = c(&mut a, ONE);
    let two = c(&mut a, TWO);
    let neg_two = c(&mut a, NEG_TWO);
    let nan = c(&mut a, NAN);

    let bits_eq = |a: &TermArena, t: axeyum_ir::TermId, bits: u128| {
        matches!(eval(a, t, &Assignment::new()), Ok(Value::Bv { value, .. }) if value == bits)
    };

    let m = fp::min(&mut a, F32, one, two).unwrap();
    assert!(bits_eq(&a, m, ONE), "min(1,2) = 1");
    let m = fp::max(&mut a, F32, one, two).unwrap();
    assert!(bits_eq(&a, m, TWO), "max(1,2) = 2");
    let m = fp::min(&mut a, F32, neg_two, one).unwrap();
    assert!(bits_eq(&a, m, NEG_TWO), "min(-2,1) = -2");
    let m = fp::max(&mut a, F32, neg_two, one).unwrap();
    assert!(bits_eq(&a, m, ONE), "max(-2,1) = 1");

    // NaN propagates the other operand.
    let m = fp::min(&mut a, F32, nan, one).unwrap();
    assert!(bits_eq(&a, m, ONE), "min(NaN,1) = 1");
    let m = fp::max(&mut a, F32, two, nan).unwrap();
    assert!(bits_eq(&a, m, TWO), "max(2,NaN) = 2");
}

#[test]
fn constant_arithmetic_folds_round_nearest_even() {
    let mut a = TermArena::new();
    let one = c(&mut a, ONE);
    let two = c(&mut a, TWO);
    let four = c(&mut a, 0x4080_0000); // 4.0
    let half = 0x3F00_0000u128; // 0.5
    let three = 0x4040_0000u128; // 3.0
    let six = 0x40C0_0000u128; // 6.0

    let bits = |a: &TermArena, t: Option<axeyum_ir::TermId>, want: u128, what: &str| {
        let t = t.unwrap_or_else(|| panic!("{what}: expected a folded constant"));
        assert!(
            matches!(eval(a, t, &Assignment::new()), Ok(Value::Bv { value, .. }) if value == want),
            "{what}"
        );
    };

    let r = fp::add_rne(&mut a, F32, one, two).unwrap();
    bits(&a, r, three, "1.0 + 2.0 == 3.0");
    let r = fp::sub_rne(&mut a, F32, two, one).unwrap();
    bits(&a, r, ONE, "2.0 - 1.0 == 1.0");
    let r = fp::mul_rne(&mut a, F32, two, four).unwrap();
    bits(&a, r, 0x4100_0000, "2.0 * 4.0 == 8.0");
    let three_c = c(&mut a, three);
    let r = fp::mul_rne(&mut a, F32, two, three_c).unwrap();
    bits(&a, r, six, "2.0 * 3.0 == 6.0");
    let r = fp::div_rne(&mut a, F32, one, two).unwrap();
    bits(&a, r, half, "1.0 / 2.0 == 0.5");
    let r = fp::sqrt_rne(&mut a, F32, four).unwrap();
    bits(&a, r, TWO, "sqrt(4.0) == 2.0");

    // F64 (1.0 + 2.0 == 3.0).
    let d1 = a.bv_const(64, 0x3FF0_0000_0000_0000).unwrap();
    let d2 = a.bv_const(64, 0x4000_0000_0000_0000).unwrap();
    let r = fp::add_rne(&mut a, FloatFormat::F64, d1, d2).unwrap();
    bits(&a, r, 0x4008_0000_0000_0000, "1.0 + 2.0 == 3.0 (f64)");

    // Non-constant operand: not folded.
    let xs = a.declare("x", axeyum_ir::Sort::BitVec(32)).unwrap();
    let x = a.var(xs);
    assert!(
        fp::add_rne(&mut a, F32, x, one).unwrap().is_none(),
        "symbolic operand is not folded"
    );
}

#[test]
fn fma_and_round_to_integral_fold() {
    use axeyum_solver::fp::RoundingMode;
    let mut a = TermArena::new();

    let mk = |arena: &mut TermArena, val: f32| arena.bv_const(32, u128::from(val.to_bits())).unwrap();
    let is = |arena: &TermArena, term: Option<axeyum_ir::TermId>, want: f32, what: &str| {
        let term = term.unwrap_or_else(|| panic!("{what}: expected fold"));
        let want = u128::from(want.to_bits());
        assert!(
            matches!(eval(arena, term, &Assignment::new()), Ok(Value::Bv { value, .. }) if value == want),
            "{what}"
        );
    };

    // fma: 2*3 + 1 = 7.
    let (fx, fy, fz) = (mk(&mut a, 2.0), mk(&mut a, 3.0), mk(&mut a, 1.0));
    let r = fp::fma_rne(&mut a, F32, fx, fy, fz).unwrap();
    is(&a, r, 7.0, "fma(2,3,1) == 7");

    // roundToIntegral per mode.
    let v = mk(&mut a, 2.7);
    let r = fp::round_to_integral(&mut a, F32, RoundingMode::TowardZero, v).unwrap();
    is(&a, r, 2.0, "trunc(2.7) == 2");
    let v = mk(&mut a, 2.1);
    let r = fp::round_to_integral(&mut a, F32, RoundingMode::TowardPositive, v).unwrap();
    is(&a, r, 3.0, "ceil(2.1) == 3");
    let v = mk(&mut a, -2.1);
    let r = fp::round_to_integral(&mut a, F32, RoundingMode::TowardNegative, v).unwrap();
    is(&a, r, -3.0, "floor(-2.1) == -3");
    let v = mk(&mut a, 2.5);
    let r = fp::round_to_integral(&mut a, F32, RoundingMode::NearestEven, v).unwrap();
    is(&a, r, 2.0, "round_ties_even(2.5) == 2");
    let v = mk(&mut a, 2.5);
    let r = fp::round_to_integral(&mut a, F32, RoundingMode::NearestAway, v).unwrap();
    is(&a, r, 3.0, "round_ties_away(2.5) == 3");
}

#[test]
fn int_to_fp_conversions_fold() {
    let mut a = TermArena::new();
    let want = |a: &TermArena, t: Option<axeyum_ir::TermId>, v: f32, what: &str| {
        let t = t.unwrap_or_else(|| panic!("{what}: expected fold"));
        let want = u128::from(v.to_bits());
        assert!(
            matches!(eval(a, t, &Assignment::new()), Ok(Value::Bv { value, .. }) if value == want),
            "{what}"
        );
    };

    let five = a.bv_const(32, 5).unwrap();
    let r = fp::ubv_to_fp(&mut a, F32, five).unwrap();
    want(&a, r, 5.0, "ubv 5 -> 5.0");

    // 8-bit 0xFF = -1 as signed.
    let neg_one = a.bv_const(8, 0xFF).unwrap();
    let r = fp::sbv_to_fp(&mut a, F32, neg_one).unwrap();
    want(&a, r, -1.0, "sbv 0xFF (8-bit) -> -1.0");
    // ...but unsigned it is 255.
    let r = fp::ubv_to_fp(&mut a, F32, neg_one).unwrap();
    want(&a, r, 255.0, "ubv 0xFF (8-bit) -> 255.0");

    // Precision loss: 2^24 + 1 rounds to 2^24 in f32.
    let big = a.bv_const(32, (1u128 << 24) + 1).unwrap();
    let r = fp::ubv_to_fp(&mut a, F32, big).unwrap();
    want(&a, r, 16_777_216.0, "ubv 2^24+1 rounds to 2^24");
}

#[test]
fn folded_arithmetic_composes_with_symbolic_predicates() {
    // fp.lt(1.0 + 2.0, x) with x symbolic: the add folds to 3.0, leaving a
    // symbolic comparison -> sat (e.g. x = 4.0).
    let mut a = TermArena::new();
    let one = c(&mut a, ONE);
    let two = c(&mut a, TWO);
    let three = fp::add_rne(&mut a, F32, one, two).unwrap().unwrap();
    let xs = a.declare("x", axeyum_ir::Sort::BitVec(32)).unwrap();
    let x = a.var(xs);
    let lt = fp::lt(&mut a, F32, three, x).unwrap();

    let result = solve(&mut a, &[lt], &SolverConfig::default()).unwrap();
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "3.0 < x is satisfiable; got {result:?}"
    );
}

#[test]
fn lt_is_irreflexive_symbolically() {
    // For every (non-NaN or NaN) x, fp.lt(x, x) is false -> asserting it is unsat.
    // This goes through the bit-vector solver over a free 32-bit `x`.
    let mut a = TermArena::new();
    let xs = a.declare("x", axeyum_ir::Sort::BitVec(32)).unwrap();
    let x = a.var(xs);
    let lt_xx = fp::lt(&mut a, F32, x, x).unwrap();

    let result = solve(&mut a, &[lt_xx], &SolverConfig::default()).unwrap();
    assert!(
        matches!(result, CheckResult::Unsat),
        "fp.lt(x, x) is never true, so asserting it must be unsat; got {result:?}"
    );
}

#[test]
fn nan_is_not_less_than_itself_but_neither_is_anything_symbolic() {
    // A satisfiable symbolic query: there exists x with 1.0 < x (e.g. x = 2.0).
    let mut a = TermArena::new();
    let xs = a.declare("x", axeyum_ir::Sort::BitVec(32)).unwrap();
    let x = a.var(xs);
    let one = c(&mut a, ONE);
    let one_lt_x = fp::lt(&mut a, F32, one, x).unwrap();

    let result = solve(&mut a, &[one_lt_x], &SolverConfig::default()).unwrap();
    assert!(
        matches!(result, CheckResult::Sat(_)),
        "there is a float greater than 1.0; got {result:?}"
    );
}
