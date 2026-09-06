//! Seeded differential fuzz for integer evaluation **across the `i128`
//! boundary** (ADR-1702 slice 2).
//!
//! # Why this is the fuzz, and not a wide-literal seed in a z3 differential
//!
//! The obvious move was to add `2^127 - 1`, `2^127`, `2^128`, `2^256` seeds to an
//! existing z3 integer differential fuzz (`qf_nia_divmod_const_...` and
//! friends). Those *are* expressible on the z3 side — the fuzz builds z3 `Int`
//! ASTs, and z3 integers are unbounded. **But axeyum declines every query
//! carrying a wide literal** (`wide_int_admission`, because no route has opted
//! in), and every one of those fuzzes treats an axeyum `Unknown` as allowed.
//! A wide-literal seed there therefore could not fail, whatever the code did:
//! it would raise the seed count and check nothing. That is the shape of gate
//! this repository has been burned by, so it is not what was added.
//!
//! What *can* fail is the **evaluator**, which computes on wide integers
//! exactly and is the path every `sat` is replayed through. So the oracle here
//! is an independent reference interpreter over `num_bigint::BigInt`, written
//! against the SMT-LIB rules directly and walking the generated tree rather than
//! the arena — the same discipline ADR-1702 used for `Rational::wide_*`.
//!
//! # The rule this fuzz pins, which its first run corrected
//!
//! Promotion is decided **per node, from the operand values** — not per query
//! and not from whether a wide literal appears anywhere in the tree. At each
//! application:
//!
//! - **both operands fit `i128`** → the pre-ADR-1702 narrow rule, unchanged:
//!   checked arithmetic, and an out-of-range result is
//!   `IrError::ArithmeticOverflow`, never a promotion and never a wrapped value.
//!   So `(+ 170141183460469231731687303715884105727 1)` still DECLINES even
//!   inside a query that carries `2^256` elsewhere.
//! - **any operand is wide** → exact `BigInt`, and the result demotes back to
//!   `Value::Int` whenever it fits.
//!
//! The first version of this fuzz assumed the narrow rule applied only when
//! *every leaf in the whole expression* was narrow, and it failed on seed 7 —
//! correctly. The rule above is the contract; keeping it per-node is what makes
//! `axeyum-cas`'s use of `i128` exhaustion as a termination bound survive slice
//! 2, exactly as ADR-1702's measurement required for `Rational`.
//!
//! # What each instance checks
//!
//! - **Exactness and the decline, together.** The reference interpreter models
//!   the per-node rule above and returns *either* a value or an overflow, and
//!   `eval` must agree on which. A patch making narrow arithmetic promote
//!   returns `Ok` where the reference says overflow; a patch making the wide
//!   path decline returns `Err` where the reference has a value.
//! - **Canonicality.** A result inside `i128` comes back as `Value::Int`, never
//!   as a `Value::WideInt` holding a small number.
//! - **The degenerate argument.** `div`/`mod` by a **constant zero** is emitted
//!   deliberately, at wide magnitude too, per the partial-operator hard rule —
//!   a fuzz that avoids the corner is not a soundness gate.

use axeyum_ir::{Assignment, IrError, TermArena, TermId, Value, WideInt, eval};
use num_bigint::BigInt;

/// Instances per boundary family.
const INSTANCES: u64 = 400;

/// A deterministic linear-congruential generator (no external dependency).
struct Lcg(u64);

impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 ^ (self.0 >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }
}

/// The generated expression, kept separately from the arena so the reference
/// interpreter cannot accidentally share the code under test.
#[derive(Clone, Debug)]
enum Expr {
    Lit(BigInt),
    Neg(Box<Expr>),
    Abs(Box<Expr>),
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),
    Mod(Box<Expr>, Box<Expr>),
}

fn two_pow(n: u32) -> BigInt {
    let mut value = BigInt::from(1u8);
    for _ in 0..n {
        value *= 2;
    }
    value
}

/// The literal pool, deliberately straddling `i128` in both directions.
///
/// `i128::MAX`, `i128::MAX + 1` (= `2^127`), `2^128` and `2^256` are the four
/// magnitudes the brief names; their negatives, `i128::MIN` and small values are
/// here so the fuzz also exercises the narrow path and the sign boundary.
fn literal_pool() -> Vec<BigInt> {
    vec![
        BigInt::from(0),
        BigInt::from(1),
        BigInt::from(-1),
        BigInt::from(2),
        BigInt::from(-7),
        BigInt::from(i128::MAX),
        BigInt::from(i128::MIN),
        two_pow(127),
        -two_pow(127) - 1,
        two_pow(128),
        -two_pow(128),
        two_pow(256),
        -two_pow(256),
        two_pow(256) - 1,
        two_pow(512),
    ]
}

fn generate(rng: &mut Lcg, depth: u32, pool: &[BigInt], zero_divisor: &mut bool) -> Expr {
    if depth == 0 {
        let index = rng.below(pool.len() as u64) as usize;
        return Expr::Lit(pool[index].clone());
    }
    match rng.below(8) {
        0 => Expr::Neg(Box::new(generate(rng, depth - 1, pool, zero_divisor))),
        1 => Expr::Abs(Box::new(generate(rng, depth - 1, pool, zero_divisor))),
        2 => Expr::Add(
            Box::new(generate(rng, depth - 1, pool, zero_divisor)),
            Box::new(generate(rng, depth - 1, pool, zero_divisor)),
        ),
        3 => Expr::Sub(
            Box::new(generate(rng, depth - 1, pool, zero_divisor)),
            Box::new(generate(rng, depth - 1, pool, zero_divisor)),
        ),
        4 => Expr::Mul(
            Box::new(generate(rng, depth - 1, pool, zero_divisor)),
            Box::new(generate(rng, depth - 1, pool, zero_divisor)),
        ),
        5 | 6 => {
            // Every third divisor is a CONSTANT ZERO, at whatever magnitude the
            // dividend has. `div a 0 = 0` and `mod a 0 = a` are SMT-LIB's fixed
            // conventions, and a wrong-unsat has shipped in this repository
            // (`a946f925`) precisely because a fuzz could not generate this.
            let left = Box::new(generate(rng, depth - 1, pool, zero_divisor));
            let right = if rng.below(3) == 0 {
                *zero_divisor = true;
                Box::new(Expr::Lit(BigInt::from(0)))
            } else {
                Box::new(generate(rng, depth - 1, pool, zero_divisor))
            };
            if rng.below(2) == 0 {
                Expr::Div(left, right)
            } else {
                Expr::Mod(left, right)
            }
        }
        _ => {
            let index = rng.below(pool.len() as u64) as usize;
            Expr::Lit(pool[index].clone())
        }
    }
}

/// Euclidean quotient/remainder: remainder in `0..|b|`. Written here from the
/// SMT-LIB rule rather than reusing `WideInt`'s, so the two are independent.
fn euclid(a: &BigInt, b: &BigInt) -> (BigInt, BigInt) {
    use num_traits::Signed;
    let mut q = a / b;
    let mut r = a - &q * b;
    if r.is_negative() {
        if b.is_positive() {
            q -= 1;
            r += b;
        } else {
            q += 1;
            r -= b;
        }
    }
    (q, r)
}

/// The reference interpreter, modelling the per-node promotion rule the module
/// docs state. `Err(Overflow)` means the evaluator must decline.
///
/// Written from the SMT-LIB rules and the ADR-1702 contract directly, over the
/// generated tree rather than the arena, so it shares no code with what it
/// checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Overflow;

fn narrow(value: &BigInt) -> bool {
    use num_traits::ToPrimitive;
    value.to_i128().is_some()
}

fn reference(expr: &Expr) -> Result<BigInt, Overflow> {
    use num_traits::{Signed, Zero};

    /// Applies a binary rule: exact when either operand is wide, otherwise the
    /// narrow rule, which declines when the exact result leaves `i128`.
    fn binary(
        a: &Expr,
        b: &Expr,
        exact: impl Fn(&BigInt, &BigInt) -> BigInt,
    ) -> Result<BigInt, Overflow> {
        let (x, y) = (reference(a)?, reference(b)?);
        let value = exact(&x, &y);
        if narrow(&x) && narrow(&y) && !narrow(&value) {
            return Err(Overflow);
        }
        Ok(value)
    }

    match expr {
        Expr::Lit(value) => Ok(value.clone()),
        Expr::Neg(inner) => {
            let x = reference(inner)?;
            let value = -&x;
            if narrow(&x) && !narrow(&value) {
                return Err(Overflow);
            }
            Ok(value)
        }
        Expr::Abs(inner) => {
            let x = reference(inner)?;
            let value = x.abs();
            if narrow(&x) && !narrow(&value) {
                return Err(Overflow);
            }
            Ok(value)
        }
        Expr::Add(a, b) => binary(a, b, |x, y| x + y),
        Expr::Sub(a, b) => binary(a, b, |x, y| x - y),
        Expr::Mul(a, b) => binary(a, b, |x, y| x * y),
        // `div a 0 = 0` and `mod a 0 = a` are SMT-LIB's fixed conventions and
        // cannot overflow. `i128::MIN / -1` is the one narrow division that can.
        Expr::Div(a, b) => {
            let (x, y) = (reference(a)?, reference(b)?);
            if y.is_zero() {
                return Ok(BigInt::from(0));
            }
            let value = euclid(&x, &y).0;
            if narrow(&x) && narrow(&y) && !narrow(&value) {
                return Err(Overflow);
            }
            Ok(value)
        }
        Expr::Mod(a, b) => {
            let (x, y) = (reference(a)?, reference(b)?);
            if y.is_zero() {
                return Ok(x);
            }
            Ok(euclid(&x, &y).1)
        }
    }
}

fn build(arena: &mut TermArena, expr: &Expr) -> TermId {
    match expr {
        Expr::Lit(value) => arena.int_const_big(WideInt::from_big(value.clone())),
        Expr::Neg(inner) => {
            let a = build(arena, inner);
            arena.int_neg(a).expect("int_neg builds")
        }
        Expr::Abs(inner) => {
            let a = build(arena, inner);
            arena.int_abs(a).expect("int_abs builds")
        }
        Expr::Add(x, y) => {
            let (a, b) = (build(arena, x), build(arena, y));
            arena.int_add(a, b).expect("int_add builds")
        }
        Expr::Sub(x, y) => {
            let (a, b) = (build(arena, x), build(arena, y));
            arena.int_sub(a, b).expect("int_sub builds")
        }
        Expr::Mul(x, y) => {
            let (a, b) = (build(arena, x), build(arena, y));
            arena.int_mul(a, b).expect("int_mul builds")
        }
        Expr::Div(x, y) => {
            let (a, b) = (build(arena, x), build(arena, y));
            arena.int_div(a, b).expect("int_div builds")
        }
        Expr::Mod(x, y) => {
            let (a, b) = (build(arena, x), build(arena, y));
            arena.int_mod(a, b).expect("int_mod builds")
        }
    }
}

#[test]
fn integer_evaluation_matches_a_bigint_reference_across_the_i128_boundary() {
    use num_traits::ToPrimitive;

    let pool = literal_pool();
    let mut agreed_value = 0u64;
    let mut agreed_overflow = 0u64;
    let mut wide_results = 0u64;
    let mut demotions = 0u64;
    let mut zero_divisors = 0u64;

    for seed in 0..INSTANCES {
        for depth in 1u32..=3 {
            let mut rng = Lcg(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ u64::from(depth));
            let mut saw_zero_divisor = false;
            let expr = generate(&mut rng, depth, &pool, &mut saw_zero_divisor);
            if saw_zero_divisor {
                zero_divisors += 1;
            }
            let expected = reference(&expr);

            let mut arena = TermArena::new();
            let term = build(&mut arena, &expr);
            let got = eval(&arena, term, &Assignment::new());

            match (expected, got) {
                (Err(Overflow), Err(IrError::ArithmeticOverflow { .. })) => agreed_overflow += 1,
                (Err(Overflow), Ok(value)) => panic!(
                    "seed {seed} depth {depth}: narrow arithmetic must DECLINE out of range, \
                     got {value:?} — {expr:?}"
                ),
                (Err(Overflow), Err(error)) => panic!(
                    "seed {seed} depth {depth}: expected an arithmetic overflow, \
                     got {error:?} — {expr:?}"
                ),
                (Ok(value), Err(error)) => panic!(
                    "seed {seed} depth {depth}: must evaluate to {value} exactly, \
                     got {error:?} — {expr:?}"
                ),
                (Ok(value), Ok(actual)) => {
                    agreed_value += 1;
                    match value.to_i128() {
                        // Canonicality: a result inside `i128` is the NARROW
                        // variant, so each integer keeps one representation.
                        Some(small) => {
                            if !narrow_expr_only(&expr) {
                                demotions += 1;
                            }
                            assert_eq!(
                                actual,
                                Value::Int(small),
                                "seed {seed} depth {depth}: {expr:?}"
                            );
                        }
                        None => {
                            wide_results += 1;
                            assert_eq!(
                                actual,
                                Value::WideInt(WideInt::from_big(value.clone())),
                                "seed {seed} depth {depth}: {expr:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    // Coverage, asserted rather than assumed: an empty family would make the run
    // vacuous, and the counts are printed so a generator change that silently
    // stops producing one is visible.
    eprintln!(
        "[wide-int-eval-fuzz] values={agreed_value} overflows={agreed_overflow} \
         wide_results={wide_results} demotions={demotions} zero_divisors={zero_divisors}"
    );
    assert!(agreed_value > 0, "no instance produced a value");
    assert!(
        agreed_overflow > 0,
        "no instance exercised the narrow overflow decline — the contract that \
         `axeyum-cas` depends on would be untested"
    );
    assert!(
        wide_results > 0,
        "no instance produced an out-of-i128 result"
    );
    assert!(
        demotions > 0,
        "no wide-bearing expression evaluated back into i128 — demotion is untested"
    );
    assert!(
        zero_divisors > 0,
        "no constant-zero divisor was generated — the degenerate argument is \
         exactly where a partial operator's soundness is most fragile"
    );
}

/// Whether the expression contains no out-of-`i128` literal at all.
fn narrow_expr_only(expr: &Expr) -> bool {
    match expr {
        Expr::Lit(value) => narrow(value),
        Expr::Neg(inner) | Expr::Abs(inner) => narrow_expr_only(inner),
        Expr::Add(a, b) | Expr::Sub(a, b) | Expr::Mul(a, b) | Expr::Div(a, b) | Expr::Mod(a, b) => {
            narrow_expr_only(a) && narrow_expr_only(b)
        }
    }
}

/// The four boundary magnitudes the brief names, checked directly rather than
/// only through the random pool, so a generator change cannot silently drop
/// them. The `i128::MAX` row is the discriminating one: `x + 1` there has two
/// NARROW operands, so it declines — the per-node rule, pinned.
#[test]
fn the_four_named_boundary_magnitudes_follow_the_per_node_rule() {
    let cases = [
        (BigInt::from(i128::MAX), false), // 2^127 - 1: narrow, so `+ 1` declines
        (two_pow(127), true),             // i128::MAX + 1: wide operand, exact
        (two_pow(128), true),
        (two_pow(256), true),
    ];
    for (value, exact_round_trip) in cases {
        let mut arena = TermArena::new();
        let term = arena.int_const_big(WideInt::from_big(value.clone()));
        let one = arena.int_const(1);
        let up = arena.int_add(term, one).expect("builds");
        let back = arena.int_sub(up, one).expect("builds");
        let got = eval(&arena, back, &Assignment::new());
        if exact_round_trip {
            assert_eq!(
                got.expect("a wide operand makes the whole chain exact"),
                Value::WideInt(WideInt::from_big(value.clone())),
                "round trip at {value}"
            );
        } else {
            assert!(
                matches!(got, Err(IrError::ArithmeticOverflow { op: "int_add" })),
                "two narrow operands must still decline at {value}, got {got:?}"
            );
        }
    }
}
