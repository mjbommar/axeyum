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
    let r = fp::ubv_to_fp(&mut a, F32, five, fp::RoundingMode::NearestEven).unwrap();
    want(&a, r, 5.0, "ubv 5 -> 5.0");

    // 8-bit 0xFF = -1 as signed.
    let neg_one = a.bv_const(8, 0xFF).unwrap();
    let r = fp::sbv_to_fp(&mut a, F32, neg_one, fp::RoundingMode::NearestEven).unwrap();
    want(&a, r, -1.0, "sbv 0xFF (8-bit) -> -1.0");
    // ...but unsigned it is 255.
    let r = fp::ubv_to_fp(&mut a, F32, neg_one, fp::RoundingMode::NearestEven).unwrap();
    want(&a, r, 255.0, "ubv 0xFF (8-bit) -> 255.0");

    // Precision loss: 2^24 + 1 rounds to 2^24 in f32.
    let big = a.bv_const(32, (1u128 << 24) + 1).unwrap();
    let r = fp::ubv_to_fp(&mut a, F32, big, fp::RoundingMode::NearestEven).unwrap();
    want(&a, r, 16_777_216.0, "ubv 2^24+1 rounds to 2^24");
}

#[test]
fn fp_to_int_conversions_fold_when_defined() {
    use axeyum_solver::fp::RoundingMode::TowardZero;
    let mut a = TermArena::new();
    let mk = |a: &mut TermArena, val: f32| a.bv_const(32, u128::from(val.to_bits())).unwrap();
    let ubv = |a: &TermArena, t: Option<axeyum_ir::TermId>, want: u128, what: &str| {
        let t = t.unwrap_or_else(|| panic!("{what}: expected fold"));
        assert!(
            matches!(eval(a, t, &Assignment::new()), Ok(Value::Bv { value, .. }) if value == want),
            "{what}"
        );
    };

    // Well-defined folds.
    let v = mk(&mut a, 2.7);
    let r = fp::to_ubv(&mut a, F32, TowardZero, v, 8).unwrap();
    ubv(&a, r, 2, "to_ubv(trunc, 2.7) == 2");
    let v = mk(&mut a, -2.7);
    let r = fp::to_sbv(&mut a, F32, TowardZero, v, 8).unwrap();
    ubv(&a, r, 0xFE, "to_sbv(trunc, -2.7) == -2 (0xFE)");
    let v = mk(&mut a, 5.0);
    let r = fp::to_sbv(&mut a, F32, TowardZero, v, 8).unwrap();
    ubv(&a, r, 5, "to_sbv(5.0) == 5");

    // Undefined cases are not folded (None).
    let nan = c(&mut a, NAN);
    assert!(fp::to_ubv(&mut a, F32, TowardZero, nan, 8).unwrap().is_none(), "NaN -> None");
    let inf = c(&mut a, INF);
    assert!(fp::to_sbv(&mut a, F32, TowardZero, inf, 8).unwrap().is_none(), "inf -> None");
    let big = mk(&mut a, 300.0);
    assert!(fp::to_ubv(&mut a, F32, TowardZero, big, 8).unwrap().is_none(), "300 out of u8 range -> None");
    let neg = mk(&mut a, -1.0);
    assert!(fp::to_ubv(&mut a, F32, TowardZero, neg, 8).unwrap().is_none(), "-1 out of unsigned range -> None");
}

#[test]
fn isqrt_matches_native() {
    // floor-sqrt + remainder must match u128::isqrt over a battery of widths.
    let mut a = TermArena::new();
    for w in [8u32, 16, 32, 64] {
        let mut samples = vec![0u128, 1, 2, 3, 4, 15, 16, 17, (1u128 << w) - 1];
        let mut state: u64 = 0x51ed_0000_beef_0001 ^ u64::from(w);
        for _ in 0..40 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            samples.push(u128::from(state) & ((1u128 << w) - 1));
        }
        for n in samples {
            let nt = a.bv_const(w, n).unwrap();
            let (root_t, rem_t) = fp::isqrt(&mut a, nt).unwrap();
            let want_root = n.isqrt();
            let want_rem = n - want_root * want_root;
            let got_root = match eval(&a, root_t, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("expected Bv, got {other:?}"),
            };
            let got_rem = match eval(&a, rem_t, &Assignment::new()) {
                Ok(Value::Bv { value, .. }) => value,
                other => panic!("expected Bv, got {other:?}"),
            };
            assert_eq!(got_root, want_root, "isqrt_{w}({n}) root");
            assert_eq!(got_rem, want_rem, "isqrt_{w}({n}) rem");
        }
    }
}

#[test]
fn round_variable_matches_reference() {
    use axeyum_solver::fp::RoundingMode;
    // Variable-drop rounding must match a direct reference for ALL five rounding
    // modes over a battery of (m, drop) at several widths.
    fn ref_round(m: u128, drop: u128, mode: RoundingMode, negative: bool) -> u128 {
        if drop == 0 {
            return m;
        }
        let shifted = m >> drop;
        let dropped = m & ((1u128 << drop) - 1);
        let half = 1u128 << (drop - 1);
        let up = match mode {
            RoundingMode::NearestEven => dropped > half || (dropped == half && shifted & 1 == 1),
            RoundingMode::NearestAway => dropped >= half,
            RoundingMode::TowardZero => false,
            RoundingMode::TowardPositive => dropped != 0 && !negative,
            RoundingMode::TowardNegative => dropped != 0 && negative,
        };
        if up { shifted + 1 } else { shifted }
    }

    let modes = [
        RoundingMode::NearestEven,
        RoundingMode::NearestAway,
        RoundingMode::TowardZero,
        RoundingMode::TowardPositive,
        RoundingMode::TowardNegative,
    ];
    let mut a = TermArena::new();
    let mut state: u64 = 0xfeed_face_dead_beef;
    for n in [8u32, 16, 24] {
        for drop in 0u128..u128::from(n.min(12)) {
            let mut samples = vec![0u128, 1, 2, 3, (1u128 << (n - 1)), (1u128 << n) - 1];
            for _ in 0..32 {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                samples.push(u128::from(state) & ((1u128 << n) - 1));
            }
            for m in samples {
                for &mode in &modes {
                    for negative in [false, true] {
                        let mt = a.bv_const(n, m).unwrap();
                        let dt = a.bv_const(n, drop).unwrap();
                        let neg_t = a.bool_const(negative);
                        let r = fp::round_variable(&mut a, mt, dt, mode, neg_t).unwrap();
                        let want = ref_round(m, drop, mode, negative) & ((1u128 << n) - 1);
                        assert!(
                            matches!(eval(&a, r, &Assignment::new()), Ok(Value::Bv { value, .. }) if value == want),
                            "round_variable(n={n}, m={m:#x}, drop={drop}, {mode:?}, neg={negative}) want {want:#x}"
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn round_significand_matches_grs_reference() {
    // The symbolic RNE rounding circuit must match a direct guard/round/sticky
    // reference over a battery of significands and (n, keep) shapes.
    fn grs_ref(sig: u128, n: u32, keep: u32) -> u128 {
        if keep >= n {
            return sig;
        }
        let drop = n - keep;
        let kept = sig >> drop;
        let guard = (sig >> (drop - 1)) & 1;
        let sticky = drop >= 2 && (sig & ((1u128 << (drop - 1)) - 1)) != 0;
        let lsb = kept & 1;
        if guard == 1 && (sticky || lsb == 1) {
            kept + 1
        } else {
            kept
        }
    }

    let mut a = TermArena::new();
    let mut state: u64 = 0xc0ff_eeee_1234_5678;
    for n in [8u32, 16, 24, 28] {
        for keep in [1u32, 2, 4, 8, 12] {
            if keep >= n {
                continue;
            }
            // structured + pseudo-random significands within n bits
            let mut samples = vec![0u128, 1, 2, 3, (1u128 << n) - 1, 1u128 << (n - 1)];
            for _ in 0..64 {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                samples.push(u128::from(state) & ((1u128 << n) - 1));
            }
            for sig in samples {
                let st = a.bv_const(n, sig).unwrap();
                let r = fp::round_significand(&mut a, st, keep).unwrap();
                let want = grs_ref(sig, n, keep);
                assert!(
                    matches!(eval(&a, r, &Assignment::new()), Ok(Value::Bv { value, .. }) if value == want),
                    "round_significand(n={n}, keep={keep}, sig={sig:#x}) expected {want:#x}"
                );
            }
        }
    }
}

#[test]
fn count_leading_zeros_matches_native() {
    // Symbolic clz over concrete constants must match the native leading-zero
    // count for the given width (w for zero).
    let mut a = TermArena::new();
    for w in [1u32, 4, 8, 16, 24, 32] {
        for v in [0u128, 1, 2, 3, 7, 8, 255, 256, 1u128 << (w - 1)] {
            if w < 128 && v >= (1u128 << w) {
                continue; // not representable in w bits
            }
            let x = a.bv_const(w, v).unwrap();
            let clz = fp::count_leading_zeros(&mut a, x).unwrap();
            let want = if v == 0 {
                u128::from(w)
            } else {
                u128::from(w) - (128 - u128::from(v.leading_zeros()))
            };
            assert!(
                matches!(eval(&a, clz, &Assignment::new()), Ok(Value::Bv { value, .. }) if value == want),
                "clz_{w}({v}) expected {want}"
            );
        }
    }
}

#[test]
fn count_leading_zeros_is_symbolically_sound() {
    // For a free 8-bit x, clz(x) <= 8 always -> asserting clz(x) >= 9 is unsat.
    let mut a = TermArena::new();
    let xs = a.declare("x", axeyum_ir::Sort::BitVec(8)).unwrap();
    let x = a.var(xs);
    let clz = fp::count_leading_zeros(&mut a, x).unwrap();
    let nine = a.bv_const(8, 9).unwrap();
    let gt = a.bv_uge(clz, nine).unwrap();
    let r = solve(&mut a, &[gt], &SolverConfig::default()).unwrap();
    assert!(matches!(r, CheckResult::Unsat), "clz(x) is never > 8; got {r:?}");
}

#[test]
#[allow(clippy::cast_precision_loss, clippy::cast_possible_truncation)] // reference uses native casts
fn round_to_format_matches_native_f32() {
    // The rounding keystone: round_to_format(8, 24, v) must equal native
    // (v as f32) — which is round-nearest-even f64->f32 — for every f64 v.
    // Validated over specials, a wide structured battery, and a deterministic
    // pseudo-random sweep of f64 bit patterns (incl. subnormals, ties, overflow).
    let check = |v: f64| {
        let got = fp::round_to_format(8, 24, v, fp::RoundingMode::NearestEven);
        let want = u128::from((v as f32).to_bits());
        assert_eq!(
            got, want,
            "round_to_format(8,24,{v:?})={got:#x} but (v as f32)={want:#x}"
        );
    };

    // Specials and exact values.
    for v in [
        0.0f64, -0.0, 1.0, -1.0, 2.0, 0.5, 3.0, 1.5, 0.1, -0.1,
        f64::INFINITY, f64::NEG_INFINITY, f64::NAN,
        f64::from(f32::MIN_POSITIVE), // smallest normal f32
        f64::from(f32::MAX),
        1e38, 1e39, // near/over f32 overflow
        1e-40, 1e-45, 1e-50, // f32 subnormal range and below
    ] {
        check(v);
    }

    // Structured: i/j fractions exercise rounding/ties across many magnitudes.
    for i in 0i64..200 {
        for j in 1i64..200 {
            check(i as f64 / j as f64);
            check(-(i as f64) / j as f64);
            check((i as f64) * 1e30 / j as f64);
            check((i as f64) * 1e-30 / j as f64);
        }
    }

    // Deterministic pseudo-random sweep of f64 bit patterns (LCG).
    let mut state: u64 = 0x1234_5678_9abc_def0;
    for _ in 0..200_000 {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let v = f64::from_bits(state);
        if v.is_nan() {
            continue; // NaN payloads differ; covered by the explicit NAN case
        }
        check(v);
    }
}

#[test]
fn fp_to_real_folds_exactly() {
    use axeyum_ir::Rational;
    let mut a = TermArena::new();
    let real = |a: &TermArena, t: Option<axeyum_ir::TermId>, want: Rational, what: &str| {
        let t = t.unwrap_or_else(|| panic!("{what}: expected fold"));
        match eval(a, t, &Assignment::new()) {
            Ok(Value::Real(r)) => assert_eq!(r, want, "{what}"),
            other => panic!("{what}: expected Real, got {other:?}"),
        }
    };

    let v = c(&mut a, 0x3FC0_0000); // 1.5
    let r = fp::to_real(&mut a, F32, v).unwrap();
    real(&a, r, Rational::new(3, 2), "1.5 -> 3/2");
    let v = c(&mut a, 0x3F00_0000); // 0.5
    let r = fp::to_real(&mut a, F32, v).unwrap();
    real(&a, r, Rational::new(1, 2), "0.5 -> 1/2");
    let v = c(&mut a, NEG_TWO); // -2.0
    let r = fp::to_real(&mut a, F32, v).unwrap();
    real(&a, r, Rational::integer(-2), "-2.0 -> -2");
    let v = c(&mut a, POS0);
    let r = fp::to_real(&mut a, F32, v).unwrap();
    real(&a, r, Rational::integer(0), "+0 -> 0");

    // Not real / does not fit -> None.
    let nan = c(&mut a, NAN);
    assert!(fp::to_real(&mut a, F32, nan).unwrap().is_none(), "NaN -> None");
    let inf = c(&mut a, INF);
    assert!(fp::to_real(&mut a, F32, inf).unwrap().is_none(), "inf -> None");
    let tiny = c(&mut a, 0x0000_0001); // smallest subnormal f32 = 2^-149
    assert!(fp::to_real(&mut a, F32, tiny).unwrap().is_none(), "2^-149 exceeds i128 rational -> None");
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
