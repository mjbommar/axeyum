//! Validated numerics — rational interval enclosures carrying a checkable
//! certificate (math-department file 13, Next Ten item **2**).
//!
//! [`evalf`](crate::evalf) answers "what is this expression, roughly?" with an
//! `f64`. It is fast, it is the right tool for a display string, and it proves
//! nothing: a double carries no statement about its own error. This module is
//! the certified route beside it. [`enclose`] answers "what is this expression,
//! *provably*?" with a closed interval of exact rational endpoints that is
//! guaranteed to contain the true real value, together with the evidence that
//! produced the bound. `evalf` is untouched.
//!
//! # The certificate
//!
//! An [`Enclosure`] is an interval, a requested `precision`, and a `Vec<Step>`
//! of evidence — one [`Step`] per node of the expression tree, in post-order.
//! Each step records its head, the sub-intervals that entered it, the
//! truncation order of the series used, and the remainder bound charged for
//! that truncation. [`Enclosure::verify`] re-walks the expression and
//! **recomputes** every step from `(head, inputs, order)` alone: it trusts no
//! recorded number, only re-derives and compares. The guards are listed on
//! [`Enclosure::verify`]; each one has a test that dies when the guard is
//! deleted.
//!
//! # Arithmetic
//!
//! Endpoints are `BigRational`, not [`axeyum_ir::Rational`]: the crate's
//! `i128` rational overflows long before precision 100, and an overflow inside
//! a certified path is exactly the failure mode this module exists to remove.
//! There is no `f64` anywhere below this line.
//!
//! [`BigInterval`] is the `BigRational` lift of
//! [`Interval`](crate::interval_arith::Interval), with the same operation set
//! and the same enclosure contract (`f(X) ⊇ { f(x) : x ∈ X }`);
//! [`BigInterval::from_interval`] converts, and the public binding API of
//! [`enclose`] takes the `i128` `Interval` so callers keep the existing type.
//! The `i128` module is neither forked nor modified.
//!
//! # Methods used
//!
//! | head | method | remainder bound |
//! |---|---|---|
//! | `+ − × ÷ ^n` | exact interval arithmetic | none (exact) |
//! | `sqrt` | Newton from above on rationals; `[p/xk, xk]` brackets the root by AM–GM | `(xk − p/xk)/2` |
//! | `exp` | halve to `abs(y) <= 1/2`, Taylor, then square back | `2·abs(y)^(n+1)/(n+1)!` |
//! | `ln` | `p = 2^k·t`, `t` in `[1,2)`, `ln t = 2·atanh((t−1)/(t+1))`, `ln 2 = 2·atanh(1/3)` | geometric tail of the `atanh` series |
//! | `atan` | `abs(z) <= 1/2` alternating series; `pi/4 + atan((p−1)/(p+1))` for `abs(p) <= 1`; `±pi/2 − atan(1/p)` beyond | `abs(z)^(2n+3)/(2n+3)` (alternating) |
//! | `sin`, `cos` | reduce by an integer multiple of a certified `2·pi`, then Taylor about `0` | Lagrange `abs(t)^(k+2)/(k+2)!` |
//! | `pi` | Machin: `pi = 16·atan(1/5) − 4·atan(1/239)` | the two `atan` tails |
//!
//! The remainder a step records is defined uniformly as the **half-width of the
//! head re-evaluated at each endpoint of its input as a degenerate interval**,
//! maximised over the endpoints. That is the numerical error the method itself
//! introduces, separated from the width the input already had, and it is
//! computable identically by the producer and by the verifier.
//!
//! # Cost
//!
//! Wall clock for [`enclose_constant`]`("pi", …)` plus its
//! [`Enclosure::verify`], under `--release`, from the prebuilt test binary, one
//! run each. **Advisory only, not a baseline**: the host was shared with other
//! lanes during the measurement, and this is a single unpinned run.
//!
//! | precision | wall clock |
//! |---|---|
//! | 10 | see `cost_table_pi` |
//! | 50 | see `cost_table_pi` |
//! | 100 | see `cost_table_pi` |
//! | 200 | see `cost_table_pi` |
//! | 500 | see `cost_table_pi` |
//!
//! # Out of scope
//!
//! Deliberately **not** handled here, and not silently approximated either —
//! each declines with a reason:
//!
//! - **multivariate root enclosures** ([`enclose_root`] is univariate only);
//! - **`pow` with a non-integer exponent** (`CasExpr::Pow` carries a `u32`, and
//!   `x^q` for rational `q` is not routed through `exp`/`ln` here);
//! - **`gamma`, the Bessel functions, `erf`** and the rest of the
//!   special-function heads — they have no remainder bound in this module and
//!   [`enclose`] declines with [`DeclineReason::UnsupportedHead`];
//! - **the `f64` [`evalf`](crate::evalf) itself**, which is unchanged. This
//!   module adds a route; it does not replace one.

use crate::interval_arith::Interval;
use crate::{CasExpr, UnaryFunc};
use axeyum_ir::Rational;
use core::fmt;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::collections::BTreeMap;

/// The ladder of truncation orders tried, in order, when a head needs a series.
///
/// Deterministic and shared by every head: the producer takes the first order
/// whose remainder meets the step budget and records it, so the verifier
/// recomputes exactly one evaluation per step.
const ORDERS: [u32; 9] = [4, 8, 16, 32, 64, 128, 256, 512, 1024];

/// Cap on the halvings/doublings an argument reduction may perform before the
/// module declines rather than grinding.
const REDUCTION_CAP: i64 = 4096;

// ---------------------------------------------------------------------------
// BigInterval — the BigRational lift of `interval_arith::Interval`.
// ---------------------------------------------------------------------------

/// A closed interval `[lo, hi]` of exact `BigRational` endpoints, `lo <= hi`.
///
/// The arbitrary-precision counterpart of
/// [`Interval`](crate::interval_arith::Interval), with the same contract: every
/// operation returns an interval that **contains** the true image of the
/// operation applied pointwise to the operands. Unlike the `i128` version there
/// is no overflow, so no operation fails for arithmetic reasons; the only
/// `None` results are genuine mathematical declines (an empty interval, a
/// divisor straddling zero).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BigInterval {
    lo: BigRational,
    hi: BigRational,
}

impl BigInterval {
    /// The interval `[a, b]`, or `None` when `a > b`.
    pub fn new(a: BigRational, b: BigRational) -> Option<BigInterval> {
        if a > b {
            None
        } else {
            Some(BigInterval { lo: a, hi: b })
        }
    }

    /// The degenerate (point) interval `[a, a]`.
    pub fn point(a: BigRational) -> BigInterval {
        BigInterval {
            lo: a.clone(),
            hi: a,
        }
    }

    /// The interval `[c − |r|, c + |r|]`.
    ///
    /// The constructor used by every series evaluation: `c` is the truncated
    /// sum and `r` the remainder bound, so the invariant `lo <= hi` holds by
    /// construction and no fallible path is needed.
    pub fn center_radius(c: &BigRational, r: &BigRational) -> BigInterval {
        let radius = r.abs();
        BigInterval {
            lo: c - &radius,
            hi: c + &radius,
        }
    }

    /// The `i128`-rational interval lifted to `BigRational` endpoints.
    pub fn from_interval(iv: &Interval) -> BigInterval {
        BigInterval {
            lo: from_rational(iv.lower()),
            hi: from_rational(iv.upper()),
        }
    }

    /// The lower endpoint.
    pub fn lo(&self) -> &BigRational {
        &self.lo
    }

    /// The upper endpoint.
    pub fn hi(&self) -> &BigRational {
        &self.hi
    }

    /// The width `hi − lo` (always `>= 0`).
    pub fn width(&self) -> BigRational {
        &self.hi - &self.lo
    }

    /// Half the width — the radius of the enclosure.
    pub fn radius(&self) -> BigRational {
        self.width() / BigRational::from(BigInt::from(2))
    }

    /// The midpoint `(lo + hi)/2`.
    pub fn midpoint(&self) -> BigRational {
        (&self.lo + &self.hi) / BigRational::from(BigInt::from(2))
    }

    /// Returns `true` when `x` lies in `[lo, hi]`.
    pub fn contains(&self, x: &BigRational) -> bool {
        &self.lo <= x && x <= &self.hi
    }

    /// Returns `true` when `other` is entirely contained in `self`.
    pub fn contains_interval(&self, other: &BigInterval) -> bool {
        self.lo <= other.lo && other.hi <= self.hi
    }

    /// The sum `self + other`.
    pub fn add(&self, other: &BigInterval) -> BigInterval {
        BigInterval {
            lo: &self.lo + &other.lo,
            hi: &self.hi + &other.hi,
        }
    }

    /// The difference `self − other`.
    pub fn sub(&self, other: &BigInterval) -> BigInterval {
        BigInterval {
            lo: &self.lo - &other.hi,
            hi: &self.hi - &other.lo,
        }
    }

    /// The negation `−self`.
    pub fn negate(&self) -> BigInterval {
        BigInterval {
            lo: -self.hi.clone(),
            hi: -self.lo.clone(),
        }
    }

    /// The product `self · other`, by the four-endpoint-products rule.
    pub fn mul(&self, other: &BigInterval) -> BigInterval {
        let products = [
            &self.lo * &other.lo,
            &self.lo * &other.hi,
            &self.hi * &other.lo,
            &self.hi * &other.hi,
        ];
        let mut lo = products[0].clone();
        let mut hi = products[0].clone();
        for candidate in &products[1..] {
            if *candidate < lo {
                lo = candidate.clone();
            }
            if *candidate > hi {
                hi = candidate.clone();
            }
        }
        BigInterval { lo, hi }
    }

    /// The quotient `self / other`, or `None` when `other` contains `0`.
    pub fn div(&self, other: &BigInterval) -> Option<BigInterval> {
        if other.contains(&BigRational::zero()) {
            return None;
        }
        let recip = BigInterval {
            lo: BigRational::one() / &other.hi,
            hi: BigRational::one() / &other.lo,
        };
        Some(self.mul(&recip))
    }

    /// The `n`-th power; `pow(0)` is the point interval `[1, 1]`.
    pub fn pow(&self, n: u32) -> BigInterval {
        if n == 0 {
            return BigInterval::point(BigRational::one());
        }
        let lo_pow = ratpow(&self.lo, n);
        let hi_pow = ratpow(&self.hi, n);
        let zero = BigRational::zero();
        let straddles = self.lo <= zero && zero <= self.hi;
        if n % 2 == 0 && straddles {
            let hi = if lo_pow > hi_pow { lo_pow } else { hi_pow };
            BigInterval { lo: zero, hi }
        } else if lo_pow <= hi_pow {
            BigInterval {
                lo: lo_pow,
                hi: hi_pow,
            }
        } else {
            BigInterval {
                lo: hi_pow,
                hi: lo_pow,
            }
        }
    }

    /// The scalar multiple `c · self` (endpoints swap when `c < 0`).
    pub fn scale(&self, c: &BigRational) -> BigInterval {
        let a = &self.lo * c;
        let b = &self.hi * c;
        if a <= b {
            BigInterval { lo: a, hi: b }
        } else {
            BigInterval { lo: b, hi: a }
        }
    }

    /// The convex hull of `self` and `other`.
    pub fn hull(&self, other: &BigInterval) -> BigInterval {
        BigInterval {
            lo: if self.lo <= other.lo {
                self.lo.clone()
            } else {
                other.lo.clone()
            },
            hi: if self.hi >= other.hi {
                self.hi.clone()
            } else {
                other.hi.clone()
            },
        }
    }

    /// Clamp both endpoints into `[lo_bound, hi_bound]`.
    ///
    /// Sound only when the true value is known a priori to lie in the bound —
    /// used for `exp > 0` and `|sin| <= 1`, never to hide an error.
    fn clamp(&self, lo_bound: &BigRational, hi_bound: &BigRational) -> BigInterval {
        let lo = if self.lo < *lo_bound {
            lo_bound.clone()
        } else {
            self.lo.clone()
        };
        let hi = if self.hi > *hi_bound {
            hi_bound.clone()
        } else {
            self.hi.clone()
        };
        if lo > hi {
            BigInterval {
                lo: lo.clone(),
                hi: lo,
            }
        } else {
            BigInterval { lo, hi }
        }
    }

    /// A decimal rendering `[lower, upper]` to `digits` places, both endpoints
    /// rounded **outward** so the printed interval still encloses the value.
    pub fn decimal(&self, digits: u32) -> String {
        format!(
            "[{}, {}]",
            decimal_round(&self.lo, digits, false),
            decimal_round(&self.hi, digits, true)
        )
    }
}

impl fmt::Display for BigInterval {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.decimal(20))
    }
}

// ---------------------------------------------------------------------------
// Small BigRational helpers.
// ---------------------------------------------------------------------------

/// `n/d` as a `BigRational`.
fn br(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

/// `n` as a `BigRational`.
fn bi(n: i64) -> BigRational {
    BigRational::from(BigInt::from(n))
}

/// The crate's `i128` rational lifted to a `BigRational`.
fn from_rational(r: Rational) -> BigRational {
    BigRational::new(BigInt::from(r.numerator()), BigInt::from(r.denominator()))
}

/// `2^k` for any `i32` exponent, positive or negative.
fn pow2(k: i32) -> BigRational {
    let magnitude = BigInt::from(2u32).pow(k.unsigned_abs());
    if k >= 0 {
        BigRational::from(magnitude)
    } else {
        BigRational::new(BigInt::one(), magnitude)
    }
}

/// `x^n` for a `BigRational` base and `u32` exponent (binary exponentiation).
fn ratpow(x: &BigRational, n: u32) -> BigRational {
    let mut result = BigRational::one();
    let mut base = x.clone();
    let mut exponent = n;
    while exponent > 0 {
        if exponent & 1 == 1 {
            result *= &base;
        }
        base = &base * &base;
        exponent >>= 1;
    }
    result
}

/// The larger of two `BigRational`s.
fn rmax(a: BigRational, b: BigRational) -> BigRational {
    if a >= b { a } else { b }
}

/// The smaller of two `BigRational`s.
fn rmin(a: BigRational, b: BigRational) -> BigRational {
    if a <= b { a } else { b }
}

/// `floor(q)` as a `BigInt`.
fn rat_floor(q: &BigRational) -> BigInt {
    let (num, den) = (q.numer(), q.denom());
    let quotient = num / den;
    if num < &BigInt::zero() && &(&quotient * den) != num {
        quotient - BigInt::one()
    } else {
        quotient
    }
}

/// The nearest integer to `q` (ties round up), as a `BigInt`.
fn rat_round(q: &BigRational) -> BigInt {
    rat_floor(&(q + br(1, 2)))
}

/// `q` rendered with `digits` decimal places, rounded down (`up = false`) or up
/// (`up = true`) so a pair of them still brackets the value.
fn decimal_round(q: &BigRational, digits: u32, up: bool) -> String {
    let scale = BigInt::from(10u32).pow(digits);
    let scaled = q * BigRational::from(scale.clone());
    let mut integral = rat_floor(&scaled);
    if up && BigRational::from(integral.clone()) != scaled {
        integral += BigInt::one();
    }
    let negative = integral < BigInt::zero();
    let magnitude = if negative {
        -integral.clone()
    } else {
        integral.clone()
    };
    let whole = &magnitude / &scale;
    let fraction = &magnitude % &scale;
    let sign = if negative { "-" } else { "" };
    if digits == 0 {
        format!("{sign}{whole}")
    } else {
        let width = digits as usize;
        format!("{sign}{whole}.{fraction:0width$}")
    }
}

// ---------------------------------------------------------------------------
// Decline reasons.
// ---------------------------------------------------------------------------

/// Why [`enclose`] or [`enclose_root`] refused to produce a certificate.
///
/// A decline is never an error and never an approximation: the module either
/// returns an enclosure it can defend or says which obstacle it hit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclineReason {
    /// A free variable of the expression has no interval binding.
    UnboundVariable(String),
    /// A division whose divisor interval contains `0` — the quotient is
    /// unbounded, so no finite interval encloses it.
    DivisorContainsZero,
    /// A head with no certified route in this module (`gamma`, `erf`, the
    /// Bessel family, …). The name is the head as written.
    UnsupportedHead(String),
    /// The argument left the function's domain over the whole binding box —
    /// `ln` of an interval reaching `0` or below, `sqrt` of a negative.
    DomainError(String),
    /// No order on the [`ORDERS`] ladder, at any slack, produced a final width
    /// within `2^(−precision)`. Widening a binding box or lowering the
    /// requested precision is the fix; this is not a soundness failure.
    PrecisionUnreachable,
    /// An argument reduction would need more than [`REDUCTION_CAP`] steps, or
    /// a bisection more than its cap.
    ResourceLimit,
    /// The isolating interval handed to [`enclose_root`] does not contain
    /// exactly one root by Sturm's theorem, or the polynomial was rejected.
    NotIsolating,
}

impl fmt::Display for DeclineReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DeclineReason::UnboundVariable(name) => write!(f, "unbound variable `{name}`"),
            DeclineReason::DivisorContainsZero => {
                write!(f, "divisor interval contains 0")
            }
            DeclineReason::UnsupportedHead(head) => {
                write!(f, "no certified route for head `{head}`")
            }
            DeclineReason::DomainError(detail) => write!(f, "domain error: {detail}"),
            DeclineReason::PrecisionUnreachable => {
                write!(f, "requested precision not reachable")
            }
            DeclineReason::ResourceLimit => write!(f, "resource limit reached"),
            DeclineReason::NotIsolating => {
                write!(f, "the interval does not isolate exactly one root")
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Evidence.
// ---------------------------------------------------------------------------

/// The head of one evidence [`Step`] — what operation the step performed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepHead {
    /// A rational literal.
    Const,
    /// A bound variable, named.
    Var(String),
    /// The reserved constant `pi`, enclosed by Machin's formula.
    Pi,
    /// An n-ary sum.
    Add,
    /// An n-ary product.
    Mul,
    /// Arithmetic negation.
    Neg,
    /// A quotient.
    Div,
    /// A non-negative integer power, with the exponent.
    Pow(u32),
    /// `exp`.
    Exp,
    /// `ln`.
    Ln,
    /// `sin`.
    Sin,
    /// `cos`.
    Cos,
    /// `atan`.
    Atan,
    /// Principal square root.
    Sqrt,
    /// A bisection-refined root of a univariate polynomial.
    Root,
}

impl StepHead {
    /// Whether the head introduces a truncation error (and so needs an order).
    fn is_series(&self) -> bool {
        matches!(
            self,
            StepHead::Pi
                | StepHead::Exp
                | StepHead::Ln
                | StepHead::Sin
                | StepHead::Cos
                | StepHead::Atan
                | StepHead::Sqrt
        )
    }
}

/// One line of an [`Enclosure`]'s evidence: a head, what went in, at what
/// truncation order, with what remainder bound, and what came out.
///
/// The evidence is the certificate. [`Enclosure::verify`] never reads `output`
/// or `remainder` as an answer — it recomputes both from `head`, `inputs` and
/// `order`, and compares.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Step {
    /// The operation this step performed.
    pub head: StepHead,
    /// The enclosures of the operands, in argument order.
    pub inputs: Vec<BigInterval>,
    /// The truncation order used (the position on the series, the number of
    /// Newton iterations, or the number of bisections); `0` for exact heads.
    pub order: u32,
    /// The bound charged for the method's own numerical error: the half-width
    /// of this head re-evaluated at each endpoint of its input as a degenerate
    /// interval, maximised. `0` for exact heads.
    pub remainder: BigRational,
    /// The enclosure this step claims for its output.
    pub output: BigInterval,
    /// For a [`StepHead::Root`] step, the sign of the polynomial at the lower
    /// and upper endpoint of `output` (`-1`, `0`, or `1`). `None` otherwise.
    pub signs: Option<(i8, i8)>,
}

/// A rational interval enclosing a real value, plus the evidence that produced
/// it.
///
/// Produced by [`enclose`], [`enclose_root`] and [`enclose_constant`]; checked
/// by [`Enclosure::verify`] and [`Enclosure::verify_root`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Enclosure {
    /// The interval. Guaranteed to contain the true value, with width at most
    /// `2^(−precision)`.
    pub interval: BigInterval,
    /// The requested precision: the width bound is `2^(−precision)`.
    pub precision: u32,
    /// One step per node of the subject, in post-order.
    pub evidence: Vec<Step>,
}

/// The per-step numerical-error budget a verifier will accept.
///
/// `2^(−precision) / (4 · steps)`. The producer may (and usually does) work to a
/// tighter budget; the verifier uses this loosest form, so a producer that met a
/// tighter one also passes. This is a **discipline** bound — the binding
/// guarantee on the answer is the final-width guard plus per-step containment.
fn step_tolerance(precision: u32, steps: usize) -> BigRational {
    let steps = BigInt::from(steps.max(1));
    pow2(-i32::try_from(precision.min(1_000_000)).unwrap_or(i32::MAX))
        / BigRational::from(steps * BigInt::from(4u32))
}

/// The number of nodes in the expression tree — the number of evidence steps a
/// valid certificate must carry.
fn node_count(expr: &CasExpr) -> usize {
    match expr {
        CasExpr::Const(_) | CasExpr::Var(_) => 1,
        CasExpr::Add(parts) | CasExpr::Mul(parts) => {
            1 + parts.iter().map(node_count).sum::<usize>()
        }
        CasExpr::Neg(inner) | CasExpr::Pow(inner, _) | CasExpr::Unary(_, inner) => {
            1 + node_count(inner)
        }
        CasExpr::Div(numerator, denominator) => 1 + node_count(numerator) + node_count(denominator),
    }
}

// ---------------------------------------------------------------------------
// Series kernels. Every one is deterministic in (argument, order).
// ---------------------------------------------------------------------------

/// `atanh(z)` for `|z| <= 1/2`, truncated after `order + 1` terms.
///
/// `atanh(z) = sum_i z^(2i+1)/(2i+1)`; the tail past term `n` is bounded by the
/// geometric majorant `|z|^(2n+3)/((2n+3)·(1 − z²))`.
fn atanh_small(z: &BigRational, order: u32) -> Option<BigInterval> {
    if z.abs() > br(1, 2) {
        return None;
    }
    let z2 = z * z;
    let mut power = z.clone();
    let mut sum = z.clone();
    let mut denominator: u64 = 1;
    for _ in 1..=order {
        power *= &z2;
        denominator += 2;
        sum += &power / bi(i64::try_from(denominator).ok()?);
    }
    let next_power = &power * &z2;
    let next_denominator = bi(i64::try_from(denominator + 2).ok()?);
    let geometric = BigRational::one() / (BigRational::one() - &z2);
    let remainder = (next_power / next_denominator).abs() * geometric;
    Some(BigInterval::center_radius(&sum, &remainder))
}

/// `atan(z)` for `|z| <= 1/2` by the alternating series.
///
/// The terms decrease in magnitude for `|z| <= 1`, so the alternating-series
/// bound `|R| <= |z|^(2n+3)/(2n+3)` is exact and needs no majorant.
fn atan_small(z: &BigRational, order: u32) -> Option<BigInterval> {
    if z.abs() > br(1, 2) {
        return None;
    }
    let z2 = z * z;
    let mut power = z.clone();
    let mut sum = z.clone();
    let mut denominator: u64 = 1;
    let mut sign = -1i64;
    for _ in 1..=order {
        power *= &z2;
        denominator += 2;
        sum += bi(sign) * &power / bi(i64::try_from(denominator).ok()?);
        sign = -sign;
    }
    let next_power = &power * &z2;
    let next_denominator = bi(i64::try_from(denominator + 2).ok()?);
    let remainder = (next_power / next_denominator).abs();
    Some(BigInterval::center_radius(&sum, &remainder))
}

/// A certified enclosure of `pi` by Machin's formula,
/// `pi = 16·atan(1/5) − 4·atan(1/239)`, both `atan`s at `order`.
///
/// Machin's identity is exact; the only error is the two series tails, each of
/// which carries its own alternating bound. `1/5` and `1/239` are both below
/// `1/2`, so neither `atan` needs `pi` itself — the recursion is well founded.
fn pi_enclosure(order: u32) -> Option<BigInterval> {
    let a = atan_small(&br(1, 5), order)?;
    let b = atan_small(&br(1, 239), order)?;
    Some(a.scale(&bi(16)).sub(&b.scale(&bi(4))))
}

/// `exp(p)` for a rational `p`: halve until `|y| <= 1/2`, Taylor to `order`,
/// then square back.
///
/// For `|y| <= 1/2` the tail past term `n` is at most
/// `2·|y|^(n+1)/(n+1)!` (the geometric majorant with ratio `1/2`). Squaring an
/// interval with a non-negative lower endpoint is monotone in both endpoints,
/// so the enclosure property survives the unwinding.
fn exp_point(p: &BigRational, order: u32) -> Option<BigInterval> {
    let half = br(1, 2);
    let two = bi(2);
    let mut y = p.clone();
    let mut halvings: i64 = 0;
    while y.abs() > half {
        y /= &two;
        halvings += 1;
        if halvings > REDUCTION_CAP {
            return None;
        }
    }
    let mut term = BigRational::one();
    let mut sum = BigRational::one();
    for index in 1..=order {
        term = &term * &y / bi(i64::from(index));
        sum += &term;
    }
    let next = (&term * &y / bi(i64::from(order) + 1)).abs();
    let remainder = next * two.clone();
    // `exp` is strictly positive, so a lower endpoint the truncation pushed
    // below zero can be raised to zero without losing the enclosure — and the
    // squaring below needs a non-negative lower endpoint to stay monotone.
    let candidate = BigInterval::center_radius(&sum, &remainder);
    let mut enclosure = BigInterval {
        lo: rmax(candidate.lo, BigRational::zero()),
        hi: candidate.hi,
    };
    for _ in 0..halvings {
        enclosure = BigInterval {
            lo: &enclosure.lo * &enclosure.lo,
            hi: &enclosure.hi * &enclosure.hi,
        };
    }
    Some(enclosure)
}

/// A crude but finite upper bound used only as the high side of an `exp` clamp.
fn enormous() -> BigRational {
    pow2(1 << 20)
}

/// `ln(p)` for a rational `p > 0`.
///
/// Writes `p = 2^k·t` with `t` in `[1, 2)`, then
/// `ln p = k·ln 2 + 2·atanh((t−1)/(t+1))` with `ln 2 = 2·atanh(1/3)`. Both
/// `atanh` arguments are at most `1/3`, so the series converges at a fixed rate
/// independent of `p`.
fn ln_point(p: &BigRational, order: u32) -> Option<BigInterval> {
    if !p.is_positive() {
        return None;
    }
    let one = BigRational::one();
    let two = bi(2);
    let mut t = p.clone();
    let mut exponent: i64 = 0;
    while t >= two {
        t /= &two;
        exponent += 1;
        if exponent > REDUCTION_CAP {
            return None;
        }
    }
    while t < one {
        t *= &two;
        exponent -= 1;
        if exponent < -REDUCTION_CAP {
            return None;
        }
    }
    let z = (&t - &one) / (&t + &one);
    let ln_t = atanh_small(&z, order)?.scale(&two);
    let ln_two = atanh_small(&br(1, 3), order)?.scale(&two);
    Some(ln_t.add(&ln_two.scale(&bi(exponent))))
}

/// `sqrt(p)` for a rational `p >= 0` by Newton iteration from above.
///
/// From any `x0 >= sqrt(p) > 0` the iteration `x <- (x + p/x)/2` stays at or
/// above `sqrt(p)` (AM–GM), so `p/x <= sqrt(p) <= x` brackets the root exactly
/// at every step — no error analysis is needed, the bracket *is* the
/// certificate. `order` is the iteration cap; the loop also stops once the
/// bracket is narrower than `2^(−2048)`, which keeps the denominators finite
/// and is deterministic in the value, not in the schedule.
fn sqrt_point(p: &BigRational, order: u32) -> Option<BigInterval> {
    if p.is_negative() {
        return None;
    }
    if p.is_zero() {
        return Some(BigInterval::point(BigRational::zero()));
    }
    let one = BigRational::one();
    let two = bi(2);
    let mut x = if *p > one { p.clone() } else { one.clone() };
    let floor = pow2(-2048);
    for _ in 0..order.max(1) {
        let lower = p / &x;
        if &x - &lower <= floor {
            break;
        }
        x = (&x + &lower) / &two;
    }
    let lower = p / &x;
    BigInterval::new(lower, x)
}

/// `sin(t)` for a rational `t`, Taylor about `0` truncated after the
/// `t^(2·order+1)` term.
///
/// The Lagrange remainder after degree `k` is `f^(k+1)(xi)·t^(k+1)/(k+1)!` with
/// `|f^(k+1)| <= 1`; the degree-`(k+1)` term of `sin` vanishes, so the sharper
/// `|t|^(k+2)/(k+2)!` also holds. That bound is unconditional — it does not
/// need the series to be alternating-with-decreasing-terms, so it stays valid
/// for the `|t|` up to `pi` that reduction leaves behind.
fn sin_point(t: &BigRational, order: u32) -> BigInterval {
    let t2 = t * t;
    let mut term = t.clone();
    let mut sum = t.clone();
    let mut degree: u64 = 1;
    for _ in 1..=order {
        let factor = bi_u64((degree + 1) * (degree + 2));
        term = -(&term * &t2) / factor;
        degree += 2;
        sum += &term;
    }
    let remainder = (&term * &t2 / bi_u64((degree + 1) * (degree + 2))).abs();
    BigInterval::center_radius(&sum, &remainder).clamp(&-BigRational::one(), &BigRational::one())
}

/// `cos(t)` for a rational `t`, Taylor about `0` truncated after the
/// `t^(2·order)` term, with the same Lagrange bound as [`sin_point`].
fn cos_point(t: &BigRational, order: u32) -> BigInterval {
    let t2 = t * t;
    let mut term = BigRational::one();
    let mut sum = BigRational::one();
    let mut degree: u64 = 0;
    for _ in 1..=order {
        let factor = bi_u64((degree + 1) * (degree + 2));
        term = -(&term * &t2) / factor;
        degree += 2;
        sum += &term;
    }
    let remainder = (&term * &t2 / bi_u64((degree + 1) * (degree + 2))).abs();
    BigInterval::center_radius(&sum, &remainder).clamp(&-BigRational::one(), &BigRational::one())
}

/// A `u64` as a `BigRational`.
fn bi_u64(n: u64) -> BigRational {
    BigRational::from(BigInt::from(n))
}

/// `atan(p)` for any rational `p`, by rational range reduction onto `|z| <= 1/2`.
///
/// - `|p| <= 1/2`: the series directly.
/// - `1/2 < |p| <= 1`: `atan(p) = pi/4 + atan((p−1)/(p+1))`, whose argument lies
///   in `(−1/3, 0]`.
/// - `|p| > 1`: `atan(p) = sign(p)·pi/2 − atan(1/p)`, reducing to the cases
///   above.
///
/// The `pi` enclosure comes from Machin, which uses only `atan(1/5)` and
/// `atan(1/239)` — both in the direct case — so there is no circularity.
fn atan_point(p: &BigRational, order: u32) -> Option<BigInterval> {
    let one = BigRational::one();
    let magnitude = p.abs();
    if magnitude <= br(1, 2) {
        return atan_small(p, order);
    }
    let pi = pi_enclosure(order)?;
    if magnitude <= one {
        let reduced = (&magnitude - &one) / (&magnitude + &one);
        let positive = pi.scale(&br(1, 4)).add(&atan_small(&reduced, order)?);
        return Some(if p.is_negative() {
            positive.negate()
        } else {
            positive
        });
    }
    let inner = atan_point(&(BigRational::one() / &magnitude), order)?;
    let positive = pi.scale(&br(1, 2)).sub(&inner);
    Some(if p.is_negative() {
        positive.negate()
    } else {
        positive
    })
}

/// Reduce an interval by an integer multiple of a certified `2·pi`, returning
/// the reduced interval and the `pi` enclosure used.
///
/// The multiple is chosen from the midpoint, so a point argument lands in
/// roughly `[−pi, pi]`; the returned interval carries the `pi` uncertainty
/// scaled by the multiple, which is why a large argument needs a higher order.
fn reduce_mod_two_pi(x: &BigInterval, order: u32) -> Option<(BigInterval, BigInterval)> {
    let pi = pi_enclosure(order)?;
    let two_pi = pi.scale(&bi(2));
    let multiple = rat_round(&(x.midpoint() / two_pi.midpoint()));
    if multiple.magnitude() > BigInt::from(1_000_000u32).magnitude() {
        return None;
    }
    let shift = two_pi.scale(&BigRational::from(multiple));
    Some((x.sub(&shift), pi))
}

/// `sin` over an interval, by reduction plus endpoint evaluation with explicit
/// handling of the two critical points that can fall inside the reduced range.
///
/// When the reduced interval is too wide to place the critical points, the
/// method falls back to the exact-but-useless `[−1, 1]`, which is sound; the
/// caller's precision guard then declines.
fn sin_interval(x: &BigInterval, order: u32) -> Option<BigInterval> {
    let (r, pi) = reduce_mod_two_pi(x, order)?;
    let unit = BigInterval::new(-BigRational::one(), BigRational::one())?;
    if r.lo < -pi.hi.clone() || r.hi > pi.hi {
        return Some(unit);
    }
    let half_lo = &pi.lo / bi(2);
    let half_hi = &pi.hi / bi(2);
    let at_lo = sin_point(&r.lo, order);
    let at_hi = sin_point(&r.hi, order);
    let mut lo = rmin(at_lo.lo.clone(), at_hi.lo.clone());
    let mut hi = rmax(at_lo.hi.clone(), at_hi.hi.clone());
    // The maximum +1 sits at pi/2, the minimum −1 at −pi/2; a reduced interval
    // that overlaps the enclosure of either takes the extreme value there.
    if r.lo <= half_hi && r.hi >= half_lo {
        hi = BigRational::one();
    }
    if r.lo <= -half_lo.clone() && r.hi >= -half_hi {
        lo = -BigRational::one();
    }
    BigInterval::new(lo, hi).map(|iv| iv.clamp(&-BigRational::one(), &BigRational::one()))
}

/// `cos` over an interval, by the same reduction as [`sin_interval`]; the
/// critical points inside the reduced range are `0` (maximum `+1`) and `±pi`
/// (minimum `−1`).
fn cos_interval(x: &BigInterval, order: u32) -> Option<BigInterval> {
    let (r, pi) = reduce_mod_two_pi(x, order)?;
    let unit = BigInterval::new(-BigRational::one(), BigRational::one())?;
    if r.lo < -pi.hi.clone() || r.hi > pi.hi {
        return Some(unit);
    }
    let at_lo = cos_point(&r.lo, order);
    let at_hi = cos_point(&r.hi, order);
    let mut lo = rmin(at_lo.lo.clone(), at_hi.lo.clone());
    let mut hi = rmax(at_lo.hi.clone(), at_hi.hi.clone());
    if r.lo <= BigRational::zero() && r.hi >= BigRational::zero() {
        hi = BigRational::one();
    }
    if r.hi >= pi.lo || r.lo <= -pi.lo.clone() {
        lo = -BigRational::one();
    }
    BigInterval::new(lo, hi).map(|iv| iv.clamp(&-BigRational::one(), &BigRational::one()))
}

// ---------------------------------------------------------------------------
// The head evaluator — one deterministic function of (head, inputs, order).
// ---------------------------------------------------------------------------

/// Evaluate one head at one order, returning only the enclosure.
///
/// Shared verbatim by the producer and the verifier; nothing about it depends
/// on how the order was chosen.
fn eval_head_raw(
    head: &StepHead,
    inputs: &[BigInterval],
    order: u32,
) -> Result<BigInterval, DeclineReason> {
    let unary = |slot: usize| -> Result<&BigInterval, DeclineReason> {
        inputs
            .get(slot)
            .ok_or_else(|| DeclineReason::UnsupportedHead("arity mismatch".to_string()))
    };
    match head {
        StepHead::Const | StepHead::Var(_) | StepHead::Root => Err(DeclineReason::UnsupportedHead(
            "leaf head has no evaluator".to_string(),
        )),
        StepHead::Pi => pi_enclosure(order).ok_or(DeclineReason::ResourceLimit),
        StepHead::Add => {
            let mut acc = BigInterval::point(BigRational::zero());
            for input in inputs {
                acc = acc.add(input);
            }
            Ok(acc)
        }
        StepHead::Mul => {
            let mut acc = BigInterval::point(BigRational::one());
            for input in inputs {
                acc = acc.mul(input);
            }
            Ok(acc)
        }
        StepHead::Neg => Ok(unary(0)?.negate()),
        StepHead::Div => {
            let numerator = unary(0)?;
            let denominator = unary(1)?;
            numerator
                .div(denominator)
                .ok_or(DeclineReason::DivisorContainsZero)
        }
        StepHead::Pow(exponent) => Ok(unary(0)?.pow(*exponent)),
        StepHead::Exp => {
            let x = unary(0)?;
            // exp is increasing, so the image of [a, b] is [exp a, exp b].
            let lo = exp_point(&x.lo, order).ok_or(DeclineReason::ResourceLimit)?;
            let hi = exp_point(&x.hi, order).ok_or(DeclineReason::ResourceLimit)?;
            BigInterval::new(lo.lo, hi.hi).ok_or(DeclineReason::PrecisionUnreachable)
        }
        StepHead::Ln => {
            let x = unary(0)?;
            if !x.lo.is_positive() {
                return Err(DeclineReason::DomainError(
                    "ln of an interval reaching 0 or below".to_string(),
                ));
            }
            let lo = ln_point(&x.lo, order).ok_or(DeclineReason::ResourceLimit)?;
            let hi = ln_point(&x.hi, order).ok_or(DeclineReason::ResourceLimit)?;
            BigInterval::new(lo.lo, hi.hi).ok_or(DeclineReason::PrecisionUnreachable)
        }
        StepHead::Atan => {
            let x = unary(0)?;
            let lo = atan_point(&x.lo, order).ok_or(DeclineReason::ResourceLimit)?;
            let hi = atan_point(&x.hi, order).ok_or(DeclineReason::ResourceLimit)?;
            BigInterval::new(lo.lo, hi.hi).ok_or(DeclineReason::PrecisionUnreachable)
        }
        StepHead::Sqrt => {
            let x = unary(0)?;
            if x.lo.is_negative() {
                return Err(DeclineReason::DomainError(
                    "sqrt of an interval reaching below 0".to_string(),
                ));
            }
            let lo = sqrt_point(&x.lo, order).ok_or(DeclineReason::ResourceLimit)?;
            let hi = sqrt_point(&x.hi, order).ok_or(DeclineReason::ResourceLimit)?;
            BigInterval::new(lo.lo, hi.hi).ok_or(DeclineReason::PrecisionUnreachable)
        }
        StepHead::Sin => sin_interval(unary(0)?, order).ok_or(DeclineReason::ResourceLimit),
        StepHead::Cos => cos_interval(unary(0)?, order).ok_or(DeclineReason::ResourceLimit),
    }
}

/// Evaluate one head at one order, returning the enclosure **and** the
/// remainder the method itself contributed.
///
/// The remainder is the half-width of the head re-evaluated at each endpoint of
/// each input as a degenerate interval, maximised — the numerical error with the
/// input's own width factored out. Exact heads report `0`.
fn eval_head(
    head: &StepHead,
    inputs: &[BigInterval],
    order: u32,
) -> Result<(BigInterval, BigRational), DeclineReason> {
    let output = eval_head_raw(head, inputs, order)?;
    if !head.is_series() {
        return Ok((output, BigRational::zero()));
    }
    let mut remainder = BigRational::zero();
    if inputs.is_empty() {
        // A nullary series head (`pi`): its own radius is the whole error.
        remainder = output.radius();
    }
    for input in inputs {
        for endpoint in [&input.lo, &input.hi] {
            let degenerate = [BigInterval::point(endpoint.clone())];
            let at_point = eval_head_raw(head, &degenerate, order)?;
            remainder = rmax(remainder, at_point.radius());
        }
    }
    Ok((output, remainder))
}

/// Find the first order on the ladder whose remainder meets `tolerance`.
///
/// Returns the enclosure, the remainder, and the order actually used. A head
/// that never meets the budget declines with
/// [`DeclineReason::PrecisionUnreachable`] rather than returning a bound it
/// cannot defend.
fn adaptive(
    head: &StepHead,
    inputs: &[BigInterval],
    tolerance: &BigRational,
) -> Result<(BigInterval, BigRational, u32), DeclineReason> {
    for order in ORDERS {
        let (output, remainder) = eval_head(head, inputs, order)?;
        if remainder <= *tolerance {
            return Ok((output, remainder, order));
        }
    }
    Err(DeclineReason::PrecisionUnreachable)
}

// ---------------------------------------------------------------------------
// The producer.
// ---------------------------------------------------------------------------

/// Map a `CasExpr` unary head to a certified [`StepHead`], or decline.
fn step_head_for(func: UnaryFunc) -> Result<StepHead, DeclineReason> {
    match func {
        UnaryFunc::Exp => Ok(StepHead::Exp),
        UnaryFunc::Ln => Ok(StepHead::Ln),
        UnaryFunc::Sin => Ok(StepHead::Sin),
        UnaryFunc::Cos => Ok(StepHead::Cos),
        UnaryFunc::Atan => Ok(StepHead::Atan),
        UnaryFunc::Sqrt => Ok(StepHead::Sqrt),
        other => Err(DeclineReason::UnsupportedHead(format!("{other:?}"))),
    }
}

/// Post-order walk producing one evidence step per node.
fn build(
    expr: &CasExpr,
    bindings: &BTreeMap<String, BigInterval>,
    tolerance: &BigRational,
    evidence: &mut Vec<Step>,
) -> Result<BigInterval, DeclineReason> {
    let leaf = |head: StepHead, output: BigInterval, evidence: &mut Vec<Step>| {
        evidence.push(Step {
            head,
            inputs: Vec::new(),
            order: 0,
            remainder: BigRational::zero(),
            output: output.clone(),
            signs: None,
        });
        output
    };
    match expr {
        CasExpr::Const(value) => Ok(leaf(
            StepHead::Const,
            BigInterval::point(from_rational(*value)),
            evidence,
        )),
        CasExpr::Var(name) => {
            if let Some(bound) = bindings.get(name) {
                Ok(leaf(StepHead::Var(name.clone()), bound.clone(), evidence))
            } else if name == "pi" {
                let (output, remainder, order) = adaptive(&StepHead::Pi, &[], tolerance)?;
                evidence.push(Step {
                    head: StepHead::Pi,
                    inputs: Vec::new(),
                    order,
                    remainder,
                    output: output.clone(),
                    signs: None,
                });
                Ok(output)
            } else {
                Err(DeclineReason::UnboundVariable(name.clone()))
            }
        }
        CasExpr::Add(parts) | CasExpr::Mul(parts) => {
            let head = if matches!(expr, CasExpr::Add(_)) {
                StepHead::Add
            } else {
                StepHead::Mul
            };
            let mut inputs = Vec::with_capacity(parts.len());
            for part in parts {
                inputs.push(build(part, bindings, tolerance, evidence)?);
            }
            push_step(head, inputs, tolerance, evidence)
        }
        CasExpr::Neg(inner) => {
            let input = build(inner, bindings, tolerance, evidence)?;
            push_step(StepHead::Neg, vec![input], tolerance, evidence)
        }
        CasExpr::Div(numerator, denominator) => {
            let a = build(numerator, bindings, tolerance, evidence)?;
            let b = build(denominator, bindings, tolerance, evidence)?;
            push_step(StepHead::Div, vec![a, b], tolerance, evidence)
        }
        CasExpr::Pow(base, exponent) => {
            let input = build(base, bindings, tolerance, evidence)?;
            push_step(StepHead::Pow(*exponent), vec![input], tolerance, evidence)
        }
        CasExpr::Unary(func, argument) => {
            let head = step_head_for(*func)?;
            let input = build(argument, bindings, tolerance, evidence)?;
            push_step(head, vec![input], tolerance, evidence)
        }
    }
}

/// Evaluate a non-leaf head adaptively and append its evidence step.
fn push_step(
    head: StepHead,
    inputs: Vec<BigInterval>,
    tolerance: &BigRational,
    evidence: &mut Vec<Step>,
) -> Result<BigInterval, DeclineReason> {
    let (output, remainder, order) = adaptive(&head, &inputs, tolerance)?;
    evidence.push(Step {
        head,
        inputs,
        order,
        remainder,
        output: output.clone(),
        signs: None,
    });
    Ok(output)
}

/// Build the binding map, rejecting nothing: later bindings for the same name
/// win, matching `evalf`'s first-match-wins only in that both are total.
fn binding_map(bindings: &[(&str, Interval)]) -> BTreeMap<String, BigInterval> {
    let mut map = BTreeMap::new();
    for (name, interval) in bindings {
        map.insert((*name).to_string(), BigInterval::from_interval(interval));
    }
    map
}

/// A rational interval enclosing the value of `expr` over the binding box, of
/// width at most `2^(−precision)`, with the evidence that produced it.
///
/// Every point of every binding interval is covered: the returned interval
/// contains `expr(x)` for **every** `x` in the box, not merely at its midpoint.
/// Returns `None` when no certificate could be produced; use
/// [`enclose_with_reason`] for the obstacle.
///
/// ```
/// use axeyum_cas::CasExpr;
/// use axeyum_cas::enclosure::enclose;
/// let e = enclose(&CasExpr::int(1).exp(), &[], 30).unwrap();
/// assert!(e.verify(&CasExpr::int(1).exp(), &[]).is_ok());
/// ```
pub fn enclose(expr: &CasExpr, bindings: &[(&str, Interval)], precision: u32) -> Option<Enclosure> {
    enclose_with_reason(expr, bindings, precision).ok()
}

/// [`enclose`], reporting the obstacle when it declines.
///
/// # Errors
///
/// Returns the [`DeclineReason`] describing why no certificate was produced —
/// an unbound variable, a divisor straddling zero, an unsupported head, a
/// domain violation, an unreachable precision, or a resource cap.
pub fn enclose_with_reason(
    expr: &CasExpr,
    bindings: &[(&str, Interval)],
    precision: u32,
) -> Result<Enclosure, DeclineReason> {
    let map = binding_map(bindings);
    let steps = node_count(expr);
    let target = pow2(-i32::try_from(precision.min(1_000_000)).unwrap_or(i32::MAX));
    let mut last = DeclineReason::PrecisionUnreachable;
    for slack in [0u32, 8, 24, 56, 120] {
        let tolerance = step_tolerance(precision.saturating_add(slack), steps);
        let mut evidence = Vec::with_capacity(steps);
        match build(expr, &map, &tolerance, &mut evidence) {
            Ok(interval) => {
                if interval.width() <= target {
                    return Ok(Enclosure {
                        interval,
                        precision,
                        evidence,
                    });
                }
                last = DeclineReason::PrecisionUnreachable;
            }
            // Only a budget failure can improve with more slack; a domain
            // error, an unbound variable or an unsupported head never will.
            Err(reason @ (DeclineReason::PrecisionUnreachable | DeclineReason::ResourceLimit)) => {
                last = reason;
            }
            Err(reason) => return Err(reason),
        }
    }
    Err(last)
}

// ---------------------------------------------------------------------------
// The verifier.
// ---------------------------------------------------------------------------

impl Enclosure {
    /// Re-derive every step of the evidence and refuse anything that does not
    /// hold up.
    ///
    /// The verifier reads `head`, `inputs` and `order` from each step and
    /// recomputes the enclosure and the remainder itself; it treats the
    /// recorded `output` and `remainder` as claims to be checked, never as
    /// answers. The guards, each with its own message and its own test:
    ///
    /// 1. **step count** — the evidence must have exactly one step per node of
    ///    `expr`, and every step must be consumed;
    /// 2. **head mismatch** — step `i`'s head must be the head of node `i` in
    ///    post-order;
    /// 3. **input mismatch** — a step's recorded inputs must be exactly the
    ///    outputs its children recorded, so a forger cannot feed a step a
    ///    narrower operand than the tree supplies;
    /// 4. **remainder understated** — the recorded remainder must be at least
    ///    the recomputed one;
    /// 5. **order too small** — the recomputed remainder must fit the per-step
    ///    budget for the claimed precision;
    /// 6. **containment** — the recorded output must contain the recomputed
    ///    enclosure;
    /// 7. **final width** — the enclosure's width must not exceed
    ///    `2^(−precision)`;
    /// 8. **root output** — the last step's output must be the enclosure's own
    ///    interval.
    ///
    /// # Errors
    ///
    /// Returns a message naming the guard that fired and the step it fired on.
    pub fn verify(&self, expr: &CasExpr, bindings: &[(&str, Interval)]) -> Result<(), String> {
        let map = binding_map(bindings);
        let steps = node_count(expr);
        // Guard 1: step count.
        if self.evidence.len() != steps {
            return Err(format!(
                "evidence covers {} steps but the expression has {steps} nodes",
                self.evidence.len()
            ));
        }
        let tolerance = step_tolerance(self.precision, steps);
        let mut cursor = 0usize;
        let output = self.verify_node(expr, &map, &tolerance, &mut cursor)?;
        if cursor != self.evidence.len() {
            return Err(format!(
                "evidence has {} steps but the walk consumed {cursor}",
                self.evidence.len()
            ));
        }
        // Guard 8: the last step is the answer.
        if output != self.interval {
            return Err("the final evidence step does not produce the enclosure interval".into());
        }
        // Guard 7: final width.
        let target = pow2(-i32::try_from(self.precision.min(1_000_000)).unwrap_or(i32::MAX));
        if self.interval.width() > target {
            return Err(format!(
                "final width {} exceeds 2^-{}",
                self.interval.width(),
                self.precision
            ));
        }
        Ok(())
    }

    /// One node of the post-order walk: recurse into the children, then check
    /// this node's step.
    fn verify_node(
        &self,
        expr: &CasExpr,
        bindings: &BTreeMap<String, BigInterval>,
        tolerance: &BigRational,
        cursor: &mut usize,
    ) -> Result<BigInterval, String> {
        let children: Vec<BigInterval> = match expr {
            CasExpr::Const(_) | CasExpr::Var(_) => Vec::new(),
            CasExpr::Add(parts) | CasExpr::Mul(parts) => {
                let mut out = Vec::with_capacity(parts.len());
                for part in parts {
                    out.push(self.verify_node(part, bindings, tolerance, cursor)?);
                }
                out
            }
            CasExpr::Neg(inner) | CasExpr::Pow(inner, _) | CasExpr::Unary(_, inner) => {
                vec![self.verify_node(inner, bindings, tolerance, cursor)?]
            }
            CasExpr::Div(numerator, denominator) => {
                let a = self.verify_node(numerator, bindings, tolerance, cursor)?;
                let b = self.verify_node(denominator, bindings, tolerance, cursor)?;
                vec![a, b]
            }
        };
        let index = *cursor;
        let step = self
            .evidence
            .get(index)
            .ok_or_else(|| format!("evidence step {index} is missing"))?;
        *cursor += 1;
        let expected = expected_head(expr, bindings)?;
        // Guard 2: head mismatch.
        if step.head != expected {
            return Err(format!(
                "step {index} records head {:?} but the node is {expected:?}",
                step.head
            ));
        }
        // Leaves carry their value directly; there is nothing to re-derive but
        // the value itself.
        match expr {
            CasExpr::Const(value) => {
                let want = BigInterval::point(from_rational(*value));
                if step.output != want {
                    return Err(format!("step {index} misreports the constant"));
                }
                return Ok(step.output.clone());
            }
            CasExpr::Var(name) if bindings.contains_key(name) => {
                let want = &bindings[name];
                if step.output != *want {
                    return Err(format!("step {index} misreports the binding for `{name}`"));
                }
                return Ok(step.output.clone());
            }
            _ => {}
        }
        // Guard 3: input mismatch.
        if step.inputs != children {
            return Err(format!(
                "step {index} records inputs that are not the outputs of its children"
            ));
        }
        let (recomputed, remainder) = eval_head(&step.head, &step.inputs, step.order)
            .map_err(|reason| format!("step {index} does not re-evaluate: {reason}"))?;
        // Guard 4: remainder understated.
        if step.remainder < remainder {
            return Err(format!(
                "step {index} records remainder {} but the recomputed bound is {remainder}",
                step.remainder
            ));
        }
        // Guard 5: order too small for the claimed precision.
        if remainder > *tolerance {
            return Err(format!(
                "step {index} uses order {} whose remainder {remainder} exceeds the per-step budget {tolerance}",
                step.order
            ));
        }
        // Guard 6: containment.
        if !step.output.contains_interval(&recomputed) {
            return Err(format!(
                "step {index} claims an interval that does not contain the recomputed enclosure"
            ));
        }
        Ok(step.output.clone())
    }
}

/// The head a node must have recorded.
fn expected_head(
    expr: &CasExpr,
    bindings: &BTreeMap<String, BigInterval>,
) -> Result<StepHead, String> {
    Ok(match expr {
        CasExpr::Const(_) => StepHead::Const,
        CasExpr::Var(name) => {
            if bindings.contains_key(name) {
                StepHead::Var(name.clone())
            } else if name == "pi" {
                StepHead::Pi
            } else {
                return Err(format!("unbound variable `{name}`"));
            }
        }
        CasExpr::Add(_) => StepHead::Add,
        CasExpr::Mul(_) => StepHead::Mul,
        CasExpr::Neg(_) => StepHead::Neg,
        CasExpr::Div(_, _) => StepHead::Div,
        CasExpr::Pow(_, exponent) => StepHead::Pow(*exponent),
        CasExpr::Unary(func, _) => step_head_for(*func).map_err(|reason| reason.to_string())?,
    })
}

// ---------------------------------------------------------------------------
// Root enclosures.
// ---------------------------------------------------------------------------

/// Cap on bisection steps, so a pathological request declines rather than
/// grinding.
const BISECTION_CAP: u32 = 4096;

/// Exact Horner evaluation of an LSB-first rational polynomial at a
/// `BigRational` point.
fn horner(p: &[Rational], x: &BigRational) -> BigRational {
    let mut acc = BigRational::zero();
    for coefficient in p.iter().rev() {
        acc = acc * x + from_rational(*coefficient);
    }
    acc
}

/// The sign of a `BigRational` as `-1`, `0` or `1`.
fn sign_of(x: &BigRational) -> i8 {
    if x.is_zero() {
        0
    } else if x.is_negative() {
        -1
    } else {
        1
    }
}

/// Refine an isolating interval from [`crate::sturm::isolate_real_roots`] to a
/// certified enclosure of the single real root it contains.
///
/// Bisection with exact rational sign tests: the midpoint is evaluated exactly,
/// and the half whose endpoints still bracket a sign change is kept. The
/// certificate is one [`StepHead::Root`] step recording the final endpoints and
/// the sign of `p` at each; [`Enclosure::verify_root`] re-evaluates `p` there
/// and re-runs the Sturm count, so it never inspects the bisection path.
///
/// Returns `None` when the interval does not isolate exactly one root, when the
/// polynomial is rejected by Sturm, or when the width cannot be reached inside
/// [`BISECTION_CAP`] steps.
pub fn enclose_root(
    p: &[Rational],
    isolating: (Rational, Rational),
    precision: u32,
) -> Option<Enclosure> {
    enclose_root_with_reason(p, isolating, precision).ok()
}

/// [`enclose_root`], reporting the obstacle when it declines.
///
/// # Errors
///
/// Returns [`DeclineReason::NotIsolating`] when Sturm does not certify exactly
/// one root in the interval, or [`DeclineReason::ResourceLimit`] when the
/// requested width needs more than [`BISECTION_CAP`] bisections.
pub fn enclose_root_with_reason(
    p: &[Rational],
    isolating: (Rational, Rational),
    precision: u32,
) -> Result<Enclosure, DeclineReason> {
    let count = crate::sturm::count_real_roots_in(p, isolating.0, isolating.1)
        .ok_or(DeclineReason::NotIsolating)?;
    if count != 1 {
        return Err(DeclineReason::NotIsolating);
    }
    let start = BigInterval::new(from_rational(isolating.0), from_rational(isolating.1))
        .ok_or(DeclineReason::NotIsolating)?;
    let target = pow2(-i32::try_from(precision.min(1_000_000)).unwrap_or(i32::MAX));
    let mut lo = start.lo.clone();
    let mut hi = start.hi.clone();
    let mut lo_value = horner(p, &lo);
    let mut hi_value = horner(p, &hi);
    // Sturm counts roots in a half-open interval, so the lower endpoint may sit
    // exactly on the root only when the root is the upper endpoint; either way a
    // zero endpoint is an exact answer.
    let mut steps = 0u32;
    while &hi - &lo > target {
        if lo_value.is_zero() || hi_value.is_zero() {
            break;
        }
        if steps >= BISECTION_CAP {
            return Err(DeclineReason::ResourceLimit);
        }
        steps += 1;
        let mid = (&lo + &hi) / bi(2);
        let mid_value = horner(p, &mid);
        if mid_value.is_zero() {
            lo = mid.clone();
            hi = mid;
            lo_value = BigRational::zero();
            hi_value = BigRational::zero();
            break;
        }
        if sign_of(&mid_value) == sign_of(&lo_value) {
            lo = mid;
            lo_value = mid_value;
        } else {
            hi = mid;
            hi_value = mid_value;
        }
    }
    let interval = BigInterval::new(lo, hi).ok_or(DeclineReason::ResourceLimit)?;
    if interval.width() > target {
        return Err(DeclineReason::PrecisionUnreachable);
    }
    let step = Step {
        head: StepHead::Root,
        inputs: vec![start],
        order: steps,
        remainder: BigRational::zero(),
        output: interval.clone(),
        signs: Some((sign_of(&lo_value), sign_of(&hi_value))),
    };
    Ok(Enclosure {
        interval,
        precision,
        evidence: vec![step],
    })
}

impl Enclosure {
    /// Check a root certificate against the polynomial and the isolating
    /// interval it claims to refine.
    ///
    /// This never looks at the bisection path. It re-evaluates `p` exactly at
    /// the two recorded endpoints and re-runs Sturm on the isolating interval;
    /// a sign change on a continuous function is the whole argument, and the
    /// Sturm count is what ties it to the root the caller meant. The guards:
    ///
    /// 1. **shape** — exactly one step, with head [`StepHead::Root`] and
    ///    recorded signs;
    /// 2. **containment** — the refined interval must lie inside the isolating
    ///    one;
    /// 3. **sign mismatch** — the recomputed sign at each endpoint must equal
    ///    the recorded one;
    /// 4. **no sign change** — the endpoint signs must bracket a root (opposite
    ///    signs, or an endpoint exactly on it);
    /// 5. **width** — the width must not exceed `2^(−precision)`;
    /// 6. **isolation** — Sturm must count exactly one root in the isolating
    ///    interval.
    ///
    /// # Errors
    ///
    /// Returns a message naming the guard that fired.
    pub fn verify_root(
        &self,
        p: &[Rational],
        isolating: (Rational, Rational),
    ) -> Result<(), String> {
        // Guard 1: shape.
        let [step] = &self.evidence[..] else {
            return Err(format!(
                "a root certificate carries exactly one step, found {}",
                self.evidence.len()
            ));
        };
        if step.head != StepHead::Root {
            return Err(format!("step records head {:?}, not Root", step.head));
        }
        let Some((recorded_lo, recorded_hi)) = step.signs else {
            return Err("root step records no endpoint signs".into());
        };
        let start = BigInterval::new(from_rational(isolating.0), from_rational(isolating.1))
            .ok_or("the isolating interval is empty")?;
        // Guard 2: containment in the isolating interval.
        if !start.contains_interval(&self.interval) {
            return Err("the refined interval is not inside the isolating interval".into());
        }
        let lo_value = horner(p, &self.interval.lo);
        let hi_value = horner(p, &self.interval.hi);
        // Guard 3: recorded signs.
        if sign_of(&lo_value) != recorded_lo || sign_of(&hi_value) != recorded_hi {
            return Err(format!(
                "recorded endpoint signs ({recorded_lo}, {recorded_hi}) do not match the recomputed ({}, {})",
                sign_of(&lo_value),
                sign_of(&hi_value)
            ));
        }
        // Guard 4: the sign change that proves a root is bracketed.
        if recorded_lo != 0 && recorded_hi != 0 && recorded_lo == recorded_hi {
            return Err("the endpoints do not bracket a sign change".into());
        }
        // Guard 5: width.
        let target = pow2(-i32::try_from(self.precision.min(1_000_000)).unwrap_or(i32::MAX));
        if self.interval.width() > target {
            return Err(format!(
                "final width {} exceeds 2^-{}",
                self.interval.width(),
                self.precision
            ));
        }
        // Guard 6: Sturm isolation.
        match crate::sturm::count_real_roots_in(p, isolating.0, isolating.1) {
            Some(1) => Ok(()),
            Some(other) => Err(format!(
                "Sturm counts {other} roots in the isolating interval, not 1"
            )),
            None => Err("Sturm declined the polynomial".into()),
        }
    }
}

// ---------------------------------------------------------------------------
// Named constants.
// ---------------------------------------------------------------------------

/// A certified enclosure of a named real constant to the requested precision.
///
/// Recognised names: `"pi"`, `"e"`, `"ln2"` (also `"ln 2"`), `"sqrt2"` (also
/// `"sqrt 2"`). Each is a thin wrapper: `pi`, `e` and `ln 2` go through
/// [`enclose`] on the corresponding `CasExpr`, `sqrt 2` through
/// [`enclose_root`] on `x² − 2` over `[1, 2]`, so they inherit the same
/// evidence and the same verifier as everything else.
///
/// ```
/// use axeyum_cas::enclosure::enclose_constant;
/// let pi = enclose_constant("pi", 40).unwrap();
/// assert!(pi.interval.decimal(6).starts_with("[3.141592"));
/// ```
pub fn enclose_constant(name: &str, precision: u32) -> Option<Enclosure> {
    match name {
        "pi" => enclose(&CasExpr::var("pi"), &[], precision),
        "e" => enclose(&CasExpr::int(1).exp(), &[], precision),
        "ln2" | "ln 2" => enclose(&CasExpr::int(2).ln(), &[], precision),
        "sqrt2" | "sqrt 2" => enclose_root(
            &[
                Rational::integer(-2),
                Rational::zero(),
                Rational::integer(1),
            ],
            (Rational::integer(1), Rational::integer(2)),
            precision,
        ),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A decimal literal as an exact rational — used only to state a cited
    /// digit string, never to compute.
    fn decimal_to_rational(text: &str) -> BigRational {
        let (negative, body) = match text.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, text),
        };
        let (whole, fraction) = body.split_once('.').unwrap_or((body, ""));
        let digits = format!("{whole}{fraction}");
        let numerator: BigInt = digits.parse().expect("decimal digits");
        let denominator = BigInt::from(10u32).pow(u32::try_from(fraction.len()).unwrap());
        let value = BigRational::new(numerator, denominator);
        if negative { -value } else { value }
    }

    /// The 30-decimal truncations, from OEIS: A000796 (pi), A001113 (e),
    /// A002162 (ln 2), A002193 (sqrt 2). A mismatch against these means the
    /// **enclosure** is wrong; the digit strings are the cited authority.
    const PI_30: &str = "3.141592653589793238462643383279";
    const E_30: &str = "2.718281828459045235360287471352";
    const LN2_30: &str = "0.693147180559945309417232121458";
    const SQRT2_30: &str = "1.414213562373095048801688724209";

    /// The band `[d, d + 10^-30]` a value truncated to 30 decimals must lie in.
    fn digit_band(truncated: &str) -> BigInterval {
        let lo = decimal_to_rational(truncated);
        let step = BigRational::new(BigInt::one(), BigInt::from(10u32).pow(30));
        BigInterval::new(lo.clone(), lo + step).expect("band")
    }

    fn interval(lo: i128, hi: i128) -> Interval {
        Interval::new(Rational::integer(lo), Rational::integer(hi)).expect("interval")
    }

    /// Assert that the whole enclosure sits within `10^-tolerance` of the cited
    /// decimal — a two-sided band, so it does not depend on which way the cited
    /// string was rounded. Fails if the enclosure is wider than the band, which
    /// is the point: it checks the digits *and* the width at once.
    fn assert_near(enclosure: &BigInterval, cited: &str, tolerance: u32) {
        let centre = decimal_to_rational(cited);
        let epsilon = BigRational::new(BigInt::one(), BigInt::from(10u32).pow(tolerance));
        let band = BigInterval::new(&centre - &epsilon, &centre + &epsilon).expect("band");
        assert!(
            band.contains_interval(enclosure),
            "enclosure {} is not within 1e-{tolerance} of {cited}",
            enclosure.decimal(tolerance + 4)
        );
    }

    // -- BigInterval: the enclosure property ------------------------------

    #[test]
    fn big_interval_operations_enclose_sampled_points() {
        let a = BigInterval::new(br(-3, 2), br(5, 4)).unwrap();
        let b = BigInterval::new(br(1, 3), bi(2)).unwrap();
        for i in -6..=5i64 {
            for j in 1..=6i64 {
                let x = br(i, 4);
                let y = br(j, 3);
                if !a.contains(&x) || !b.contains(&y) {
                    continue;
                }
                assert!(a.add(&b).contains(&(&x + &y)));
                assert!(a.sub(&b).contains(&(&x - &y)));
                assert!(a.mul(&b).contains(&(&x * &y)));
                assert!(a.div(&b).unwrap().contains(&(&x / &y)));
                assert!(a.pow(3).contains(&ratpow(&x, 3)));
                assert!(a.pow(2).contains(&ratpow(&x, 2)));
                assert!(a.negate().contains(&-x));
            }
        }
    }

    #[test]
    fn big_interval_division_by_a_straddling_interval_is_none() {
        let a = BigInterval::point(BigRational::one());
        let straddling = BigInterval::new(bi(-1), bi(1)).unwrap();
        assert!(a.div(&straddling).is_none());
    }

    #[test]
    fn even_power_of_a_straddling_interval_has_zero_as_its_floor() {
        let a = BigInterval::new(bi(-3), bi(2)).unwrap();
        assert_eq!(*a.pow(2).lo(), BigRational::zero());
        assert_eq!(*a.pow(2).hi(), bi(9));
    }

    // -- The named constants: width and digits ----------------------------

    #[test]
    fn pi_meets_its_width_bound_and_the_cited_digits() {
        for precision in [10u32, 50, 100, 200] {
            let e = enclose_constant("pi", precision).expect("pi enclosure");
            assert!(
                e.interval.width() <= pow2(-i32::try_from(precision).unwrap()),
                "pi at precision {precision}: width {} exceeds the bound",
                e.interval.width()
            );
            e.verify(&CasExpr::var("pi"), &[]).expect("pi verifies");
        }
        let tight = enclose_constant("pi", 130).expect("pi at 130");
        assert!(
            digit_band(PI_30).contains_interval(&tight.interval),
            "pi enclosure {} is outside the cited 30 digits",
            tight.interval.decimal(32)
        );
    }

    #[test]
    fn e_meets_its_width_bound_and_the_cited_digits() {
        let expr = CasExpr::int(1).exp();
        for precision in [10u32, 50, 100, 200] {
            let e = enclose_constant("e", precision).expect("e enclosure");
            assert!(e.interval.width() <= pow2(-i32::try_from(precision).unwrap()));
            e.verify(&expr, &[]).expect("e verifies");
        }
        let tight = enclose_constant("e", 130).expect("e at 130");
        assert!(
            digit_band(E_30).contains_interval(&tight.interval),
            "e enclosure {} is outside the cited 30 digits",
            tight.interval.decimal(32)
        );
    }

    #[test]
    fn ln_two_meets_its_width_bound_and_the_cited_digits() {
        let expr = CasExpr::int(2).ln();
        for precision in [10u32, 50, 100, 200] {
            let e = enclose_constant("ln2", precision).expect("ln2 enclosure");
            assert!(e.interval.width() <= pow2(-i32::try_from(precision).unwrap()));
            e.verify(&expr, &[]).expect("ln2 verifies");
        }
        let tight = enclose_constant("ln 2", 130).expect("ln2 at 130");
        assert!(
            digit_band(LN2_30).contains_interval(&tight.interval),
            "ln 2 enclosure {} is outside the cited 30 digits",
            tight.interval.decimal(32)
        );
    }

    #[test]
    fn sqrt_two_meets_its_width_bound_and_the_cited_digits() {
        let p = [
            Rational::integer(-2),
            Rational::zero(),
            Rational::integer(1),
        ];
        let isolating = (Rational::integer(1), Rational::integer(2));
        for precision in [10u32, 50, 100, 200] {
            let e = enclose_constant("sqrt2", precision).expect("sqrt2 enclosure");
            assert!(e.interval.width() <= pow2(-i32::try_from(precision).unwrap()));
            e.verify_root(&p, isolating).expect("sqrt2 verifies");
        }
        let tight = enclose_constant("sqrt 2", 130).expect("sqrt2 at 130");
        assert!(
            digit_band(SQRT2_30).contains_interval(&tight.interval),
            "sqrt 2 enclosure {} is outside the cited 30 digits",
            tight.interval.decimal(32)
        );
    }

    #[test]
    fn unknown_constant_names_decline() {
        assert!(enclose_constant("euler-mascheroni", 10).is_none());
    }

    // -- Expression enclosures --------------------------------------------

    #[test]
    fn exp_one_contains_e() {
        let expr = CasExpr::int(1).exp();
        let e = enclose(&expr, &[], 120).expect("exp(1)");
        assert!(
            digit_band(E_30).contains_interval(&e.interval),
            "exp(1) enclosure {} misses e",
            e.interval.decimal(32)
        );
        e.verify(&expr, &[]).expect("verifies");
    }

    #[test]
    fn sin_over_a_binding_box_covers_the_whole_image() {
        // sin is increasing on [0, 1/2], so the image is [0, sin(1/2)] and the
        // enclosure must contain all of it. At precision 1 the width bound is
        // 1/2, and sin(1/2) = 0.4794... fits underneath it.
        let expr = CasExpr::var("x").sin();
        let unit = Interval::new(Rational::zero(), Rational::new(1, 2)).expect("box");
        let e = enclose(&expr, &[("x", unit)], 1).expect("sin enclosure");
        assert!(*e.interval.lo() <= BigRational::zero());
        // sin(1/2) = 0.479425538604203000...
        let sin_half = decimal_to_rational("0.479425538604203");
        assert!(*e.interval.hi() >= sin_half);
        e.verify(&expr, &[("x", unit)]).expect("verifies");
    }

    #[test]
    fn cos_zero_is_one_and_atan_one_is_a_quarter_of_pi() {
        let cos_expr = CasExpr::int(0).cos();
        let c = enclose(&cos_expr, &[], 60).expect("cos(0)");
        assert!(c.interval.contains(&BigRational::one()));
        c.verify(&cos_expr, &[]).expect("cos verifies");

        let atan_expr = CasExpr::int(1).atan();
        let a = enclose(&atan_expr, &[], 60).expect("atan(1)");
        // atan(1) = pi/4 = 0.78539816339744830961566084582...
        assert_near(&a.interval, "0.78539816339744830961566084582", 17);
        a.verify(&atan_expr, &[]).expect("atan verifies");
    }

    #[test]
    fn a_composite_expression_verifies_end_to_end() {
        // (sqrt(2) + ln(3)) / (1 + x^2) with x bound to the point 1.
        let expr = CasExpr::Div(
            Box::new(CasExpr::Add(vec![
                CasExpr::int(2).sqrt(),
                CasExpr::int(3).ln(),
            ])),
            Box::new(CasExpr::Add(vec![
                CasExpr::int(1),
                CasExpr::Pow(Box::new(CasExpr::var("x")), 2),
            ])),
        );
        let bindings = [("x", interval(1, 1))];
        let e = enclose(&expr, &bindings, 60).expect("composite enclosure");
        // (1.41421356237309505 + 1.09861228866810969) / 2 = 1.25641292552060237
        assert_near(&e.interval, "1.25641292552060237", 17);
        assert_eq!(e.evidence.len(), node_count(&expr));
        e.verify(&expr, &bindings).expect("verifies");
    }

    #[test]
    fn negative_arguments_and_reduction_still_enclose() {
        let expr = CasExpr::Neg(Box::new(CasExpr::int(7))).exp();
        let e = enclose(&expr, &[], 60).expect("exp(-7)");
        // e^-7 = 0.000911881965554516208...
        assert_near(&e.interval, "0.000911881965554516208", 17);
        e.verify(&expr, &[]).expect("verifies");

        let sin_expr = CasExpr::int(10).sin();
        let s = enclose(&sin_expr, &[], 60).expect("sin(10)");
        // sin(10) = -0.544021110889369813...
        assert_near(&s.interval, "-0.544021110889369813", 17);
        s.verify(&sin_expr, &[]).expect("verifies");
    }

    // -- Declines ----------------------------------------------------------

    #[test]
    fn division_by_an_interval_containing_zero_declines_with_that_reason() {
        let expr = CasExpr::Div(Box::new(CasExpr::int(1)), Box::new(CasExpr::var("x")));
        let bindings = [("x", interval(-1, 1))];
        let reason = enclose_with_reason(&expr, &bindings, 10).unwrap_err();
        assert_eq!(reason, DeclineReason::DivisorContainsZero);
        assert!(enclose(&expr, &bindings, 10).is_none());
    }

    #[test]
    fn an_unbound_variable_declines_by_name() {
        let expr = CasExpr::var("y").exp();
        let reason = enclose_with_reason(&expr, &[], 10).unwrap_err();
        assert_eq!(reason, DeclineReason::UnboundVariable("y".to_string()));
    }

    #[test]
    fn an_uncertified_head_declines_rather_than_approximating() {
        let expr = CasExpr::Unary(UnaryFunc::Erf, Box::new(CasExpr::int(1)));
        let reason = enclose_with_reason(&expr, &[], 10).unwrap_err();
        assert!(matches!(reason, DeclineReason::UnsupportedHead(_)));
    }

    #[test]
    fn ln_of_a_non_positive_interval_declines_as_a_domain_error() {
        let expr = CasExpr::var("x").ln();
        let bindings = [("x", interval(-1, 2))];
        let reason = enclose_with_reason(&expr, &bindings, 10).unwrap_err();
        assert!(matches!(reason, DeclineReason::DomainError(_)));
    }

    #[test]
    fn a_wide_binding_box_declines_rather_than_reporting_a_false_width() {
        // The image of exp over [0, 1] has width e − 1, so no certificate of
        // width 2^-10 exists; the module must say so, not shrink the answer.
        let expr = CasExpr::var("x").exp();
        let bindings = [("x", interval(0, 1))];
        assert_eq!(
            enclose_with_reason(&expr, &bindings, 10).unwrap_err(),
            DeclineReason::PrecisionUnreachable
        );
    }

    // -- Root enclosures ---------------------------------------------------

    #[test]
    fn enclose_root_refines_a_sturm_isolating_interval() {
        // x^3 - 2x - 5, LSB-first; the real root is near 2.0945514815.
        let p = [
            Rational::integer(-5),
            Rational::integer(-2),
            Rational::zero(),
            Rational::integer(1),
        ];
        let isolating = crate::sturm::isolate_real_roots(&p).expect("isolation");
        assert_eq!(isolating.len(), 1);
        let e = enclose_root(&p, isolating[0], 60).expect("root enclosure");
        // The real root of x^3 - 2x - 5 is 2.0945514815423265915...
        assert_near(&e.interval, "2.0945514815423265915", 17);
        assert!(e.interval.width() <= pow2(-60));
        e.verify_root(&p, isolating[0]).expect("verifies");
    }

    #[test]
    fn enclose_root_declines_a_non_isolating_interval() {
        // x^2 - 1 has two roots in [-2, 2].
        let p = [
            Rational::integer(-1),
            Rational::zero(),
            Rational::integer(1),
        ];
        let reason =
            enclose_root_with_reason(&p, (Rational::integer(-2), Rational::integer(2)), 10)
                .unwrap_err();
        assert_eq!(reason, DeclineReason::NotIsolating);
    }

    // -- Forged certificates: one guard, one death -------------------------

    fn pi_certificate() -> (CasExpr, Enclosure) {
        let expr = CasExpr::var("pi");
        let e = enclose(&expr, &[], 40).expect("pi");
        (expr, e)
    }

    #[test]
    fn forged_missing_step_is_refused() {
        let (expr, mut e) = pi_certificate();
        e.evidence.pop();
        let message = e.verify(&expr, &[]).unwrap_err();
        assert!(
            message.contains("nodes"),
            "expected the step-count guard, got: {message}"
        );
    }

    #[test]
    fn forged_understated_remainder_is_refused() {
        let (expr, mut e) = pi_certificate();
        e.evidence[0].remainder = BigRational::zero();
        let message = e.verify(&expr, &[]).unwrap_err();
        assert!(
            message.contains("recomputed bound"),
            "expected the remainder guard, got: {message}"
        );
    }

    #[test]
    fn forged_too_small_order_is_refused() {
        let (expr, mut e) = pi_certificate();
        // Claim the cheapest order on the ladder, and honestly report the large
        // remainder it produces, so only the order-adequacy guard can catch it.
        let (_, honest) = eval_head(&StepHead::Pi, &[], ORDERS[0]).expect("re-evaluate");
        e.evidence[0].order = ORDERS[0];
        e.evidence[0].remainder = honest;
        let message = e.verify(&expr, &[]).unwrap_err();
        assert!(
            message.contains("per-step budget"),
            "expected the order guard, got: {message}"
        );
    }

    #[test]
    fn forged_shifted_interval_is_refused() {
        let (expr, mut e) = pi_certificate();
        let shifted = e.interval.add(&BigInterval::point(BigRational::one()));
        e.evidence[0].output = shifted.clone();
        e.interval = shifted;
        let message = e.verify(&expr, &[]).unwrap_err();
        assert!(
            message.contains("does not contain the recomputed"),
            "expected the containment guard, got: {message}"
        );
    }

    #[test]
    fn forged_too_wide_interval_for_the_claimed_precision_is_refused() {
        let (expr, mut e) = pi_certificate();
        // Widen consistently: the step still contains the truth and the last
        // step still matches the enclosure, so only the width guard is left.
        let wide = BigInterval::new(
            e.interval.lo() - BigRational::one(),
            e.interval.hi() + BigRational::one(),
        )
        .expect("wide");
        e.evidence[0].output = wide.clone();
        e.interval = wide;
        let message = e.verify(&expr, &[]).unwrap_err();
        assert!(
            message.contains("exceeds 2^-"),
            "expected the width guard, got: {message}"
        );
    }

    #[test]
    fn forged_head_is_refused() {
        let (expr, mut e) = pi_certificate();
        e.evidence[0].head = StepHead::Exp;
        let message = e.verify(&expr, &[]).unwrap_err();
        assert!(
            message.contains("records head"),
            "expected the head guard, got: {message}"
        );
    }

    #[test]
    fn forged_step_input_is_refused() {
        // exp(1): two nodes, so a step can be fed an operand its child never
        // produced. Narrowing the operand is how a forger would fake a width.
        let expr = CasExpr::int(1).exp();
        let mut e = enclose(&expr, &[], 40).expect("exp(1)");
        e.evidence[1].inputs = vec![BigInterval::point(BigRational::zero())];
        let message = e.verify(&expr, &[]).unwrap_err();
        assert!(
            message.contains("not the outputs of its children"),
            "expected the input guard, got: {message}"
        );
    }

    #[test]
    fn forged_final_interval_detached_from_the_evidence_is_refused() {
        // Every step is honest; only the headline interval was swapped, and it
        // has the same width so the width guard cannot see it.
        let (expr, mut e) = pi_certificate();
        e.interval = e.interval.add(&BigInterval::point(bi(1)));
        let message = e.verify(&expr, &[]).unwrap_err();
        assert!(
            message.contains("does not produce the enclosure interval"),
            "expected the final-step guard, got: {message}"
        );
    }

    #[test]
    fn forged_root_certificate_with_extra_steps_is_refused() {
        let p = [
            Rational::integer(-2),
            Rational::zero(),
            Rational::integer(1),
        ];
        let isolating = (Rational::integer(1), Rational::integer(2));
        let mut e = enclose_root(&p, isolating, 30).expect("root");
        let duplicate = e.evidence[0].clone();
        e.evidence.push(duplicate);
        let message = e.verify_root(&p, isolating).unwrap_err();
        assert!(
            message.contains("exactly one step"),
            "expected the shape guard, got: {message}"
        );
    }

    #[test]
    fn a_root_certificate_against_a_non_isolating_interval_is_refused() {
        // The refined interval and its signs are honest; the interval it is
        // checked against holds two roots, so it does not identify which.
        let p = [
            Rational::integer(-2),
            Rational::zero(),
            Rational::integer(1),
        ];
        let e = enclose_root(&p, (Rational::integer(1), Rational::integer(2)), 30).expect("root");
        let message = e
            .verify_root(&p, (Rational::integer(-2), Rational::integer(2)))
            .unwrap_err();
        assert!(
            message.contains("roots in the isolating interval"),
            "expected the Sturm guard, got: {message}"
        );
    }

    #[test]
    fn forged_root_endpoint_sign_is_refused() {
        let p = [
            Rational::integer(-2),
            Rational::zero(),
            Rational::integer(1),
        ];
        let isolating = (Rational::integer(1), Rational::integer(2));
        let mut e = enclose_root(&p, isolating, 30).expect("root");
        let (lo, hi) = e.evidence[0].signs.expect("signs");
        e.evidence[0].signs = Some((-lo, hi));
        let message = e.verify_root(&p, isolating).unwrap_err();
        assert!(
            message.contains("do not match the recomputed"),
            "expected the sign guard, got: {message}"
        );
    }

    #[test]
    fn forged_root_without_a_sign_change_is_refused() {
        let p = [
            Rational::integer(-2),
            Rational::zero(),
            Rational::integer(1),
        ];
        let isolating = (Rational::integer(1), Rational::integer(2));
        let mut e = enclose_root(&p, isolating, 30).expect("root");
        // Move the interval wholly to the left of the root, where p is negative
        // at both ends, and record those (honest) equal signs.
        let shifted = BigInterval::new(bi(1), br(11, 10)).expect("shifted");
        e.interval = shifted.clone();
        e.evidence[0].output = shifted;
        e.evidence[0].signs = Some((-1, -1));
        let message = e.verify_root(&p, isolating).unwrap_err();
        assert!(
            message.contains("bracket a sign change"),
            "expected the sign-change guard, got: {message}"
        );
    }

    #[test]
    fn forged_root_outside_the_isolating_interval_is_refused() {
        let p = [
            Rational::integer(-2),
            Rational::zero(),
            Rational::integer(1),
        ];
        let isolating = (Rational::integer(1), Rational::integer(2));
        let mut e = enclose_root(&p, isolating, 30).expect("root");
        let outside = BigInterval::new(bi(5), bi(6)).expect("outside");
        e.interval = outside.clone();
        e.evidence[0].output = outside;
        let message = e.verify_root(&p, isolating).unwrap_err();
        assert!(
            message.contains("not inside the isolating interval"),
            "expected the containment guard, got: {message}"
        );
    }

    // -- Cost ---------------------------------------------------------------

    #[test]
    fn cost_table_pi() {
        // Advisory only: one unpinned run on a shared host. Printed so the
        // module doc's cost table can be re-measured with `--nocapture`.
        for precision in [10u32, 50, 100, 200, 500] {
            let start = std::time::Instant::now();
            let e = enclose_constant("pi", precision).expect("pi");
            let produced = start.elapsed();
            let start = std::time::Instant::now();
            e.verify(&CasExpr::var("pi"), &[]).expect("verifies");
            let verified = start.elapsed();
            println!(
                "pi precision {precision:>3}: order {:>4}  produce {produced:?}  verify {verified:?}",
                e.evidence[0].order
            );
        }
    }
}
