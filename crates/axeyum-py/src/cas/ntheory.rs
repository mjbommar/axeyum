//! `axeyum.cas` — elementary and advanced number theory (tier R).
//!
//! Every function here is a **pure function of plain integers** with no budget
//! and no hidden state, so the whole module is tier R: same inputs, same answer,
//! every time.
//!
//! Two conventions cross the boundary unchanged.
//!
//! * **The arithmetic is checked `i128`.** A Python `int` outside `i128` raises
//!   `OverflowError` at the boundary — `PyO3`'s own integer conversion — rather
//!   than silently truncating. Inside the range, an operation whose *result*
//!   would overflow returns `None`.
//! * **`None` is a value, not an error.** `lcm`, `factorial`, `binomial`,
//!   `sqrt_mod`, `primitive_root` and friends return `None` for *no such object*
//!   or *`i128` overflow*, which is a decided answer about this arithmetic and
//!   never an exception.

use axeyum_ir::Rational as IrRational;
use pyo3::exceptions::PyOverflowError;
use pyo3::prelude::*;
use pyo3::types::{PyAny, PyModule};

use crate::cas::rational;

/// Reads an exact rational, raising `OverflowError` — not `ValueError` — when
/// the value does not fit the CAS's checked `i128` pair.
///
/// The distinction matters for the statistical and number-theoretic surface,
/// where a caller routinely hands in Python's unbounded `int`: *this datum is
/// too large for the exact arithmetic* is an overflow, and reporting it as a
/// malformed value would invite the caller to "fix" a value that is not wrong.
///
/// # Errors
///
/// Raises `OverflowError` when the numerator or denominator does not fit in
/// `i128`, and propagates `ValueError`/`TypeError` from [`rational::from_py`]
/// otherwise.
pub(crate) fn rational_arg(value: &Bound<'_, PyAny>) -> PyResult<IrRational> {
    if let Ok(numerator) = value.getattr("numerator")
        && let Ok(denominator) = value.getattr("denominator")
        && (numerator.extract::<i128>().is_err() || denominator.extract::<i128>().is_err())
    {
        return Err(PyOverflowError::new_err(
            "value does not fit the CAS's exact i128 rational; the arithmetic is \
             checked i128 by design (inventory 0.4), so this is an overflow, not a \
             malformed input",
        ));
    }
    rational::from_py(value)
}

/// Reads a list of rationals with [`rational_arg`]'s overflow reporting.
///
/// # Errors
///
/// Propagates the per-element conversion error.
pub(crate) fn rational_vec_arg(values: &Bound<'_, PyAny>) -> PyResult<Vec<IrRational>> {
    values
        .try_iter()?
        .map(|item| rational_arg(&item?))
        .collect()
}

/// Binds `fn(i128) -> i128`-shaped total integer functions.
macro_rules! total {
    ($name:ident, $module:ident, $ret:ty, $doc:literal) => {
        #[doc = $doc]
        ///
        /// Tier R: a pure function of its arguments.
        #[cfg_attr(
            feature = "stub-gen",
            pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
        )]
        #[pyfunction]
        fn $name(n: i128) -> $ret {
            axeyum_cas::$module::$name(n)
        }
    };
}

/// Binds `fn(i128) -> Option<i128>`-shaped partial integer functions.
macro_rules! partial {
    ($name:ident, $module:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// Tier R: a pure function of its arguments. `None` is *no such value or
        /// `i128` overflow*, never an error.
        #[cfg_attr(
            feature = "stub-gen",
            pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
        )]
        #[pyfunction]
        fn $name(n: i128) -> Option<i128> {
            axeyum_cas::$module::$name(n)
        }
    };
}

// ---------------------------------------------------------------- ntheory.rs

/// The greatest common divisor of `a` and `b`, non-negative.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn gcd(a: i128, b: i128) -> i128 {
    axeyum_cas::ntheory::gcd(a, b)
}

/// The least common multiple, or `None` on `i128` overflow.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn lcm(a: i128, b: i128) -> Option<i128> {
    axeyum_cas::ntheory::lcm(a, b)
}

/// `(g, x, y)` with `g == gcd(a, b) == a * x + b * y` — the Bezout witness.
///
/// Tier R: a pure function of its arguments. The pair `(x, y)` is what makes
/// the gcd re-checkable without trusting this function.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn extended_gcd(a: i128, b: i128) -> (i128, i128, i128) {
    axeyum_cas::ntheory::extended_gcd(a, b)
}

/// `base ** exponent mod modulus`, or `None` for a non-positive modulus or
/// overflow.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn mod_pow(base: i128, exponent: u128, modulus: i128) -> Option<i128> {
    axeyum_cas::ntheory::mod_pow(base, exponent, modulus)
}

/// The inverse of `a` modulo `modulus`, or `None` when they are not coprime.
///
/// Tier R: a pure function of its arguments. `None` here is *decided*: no
/// inverse exists.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn mod_inverse(a: i128, modulus: i128) -> Option<i128> {
    axeyum_cas::ntheory::mod_inverse(a, modulus)
}

total!(is_prime, ntheory, bool, "Whether `n` is prime.");
total!(
    euler_phi,
    ntheory,
    i128,
    "Euler's totient: how many of `1..=n` are coprime to `n`."
);
total!(
    num_divisors,
    ntheory,
    u64,
    "The number of positive divisors of `n`."
);
partial!(
    sum_divisors,
    ntheory,
    "The sum of the positive divisors of `n`."
);
partial!(
    factorial,
    ntheory,
    "`n!`, or `None` past the `i128` ceiling (`n > 33`)."
);

/// The prime factorization as `[(prime, exponent), ...]`, ascending.
///
/// Tier R: a pure function of its arguments. `factorize(0)` and `factorize(1)`
/// are the empty list — the degenerate arguments this operator has.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn factorize(n: i128) -> Vec<(i128, u32)> {
    axeyum_cas::ntheory::factorize(n)
}

/// The prime factors with multiplicity, ascending.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn factor_list(n: i128) -> Vec<i128> {
    axeyum_cas::ntheory::factor_list(n)
}

/// Every positive divisor of `n`, ascending.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn divisors(n: i128) -> Vec<i128> {
    axeyum_cas::ntheory::divisors(n)
}

/// `C(n, k)`, or `None` on overflow. `k < 0` or `k > n` is `0`, not `None`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn binomial(n: i128, k: i128) -> Option<i128> {
    axeyum_cas::ntheory::binomial(n, k)
}

/// The Chinese remainder solution `(residue, modulus)` for
/// `[(residue, modulus), ...]`, or `None` when the congruences are inconsistent.
///
/// Tier R: a pure function of its arguments. An inconsistent system is a
/// *decided* `None`, exactly like an overflow — the pair is the witness the
/// caller re-checks.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn crt(residues: Vec<(i128, i128)>) -> Option<(i128, i128)> {
    axeyum_cas::ntheory::crt(&residues)
}

// ----------------------------------------------------------- ntheory_more.rs

total!(
    mobius,
    ntheory_more,
    i32,
    "The Moebius function: `0`, `1` or `-1`."
);
total!(
    mertens,
    ntheory_more,
    i64,
    "The Mertens function, the partial sum of `mobius`."
);
total!(is_perfect, ntheory_more, bool, "Whether `n` is perfect.");
total!(
    is_abundant,
    ntheory_more,
    bool,
    "Whether the aliquot sum exceeds `n`."
);
total!(
    is_deficient,
    ntheory_more,
    bool,
    "Whether the aliquot sum falls short of `n`."
);
total!(
    is_squarefree,
    ntheory_more,
    bool,
    "Whether no prime square divides `n`."
);
total!(
    prime_pi,
    ntheory_more,
    i64,
    "The prime-counting function: how many primes are at most `n`."
);
total!(
    is_carmichael_number,
    ntheory_more,
    bool,
    "Whether `n` is a Carmichael number (a Fermat pseudoprime to every base)."
);
partial!(
    aliquot_sum,
    ntheory_more,
    "The sum of the proper divisors of `n`."
);
partial!(
    radical,
    ntheory_more,
    "The product of the distinct primes dividing `n`."
);
partial!(
    carmichael_lambda,
    ntheory_more,
    "The reduced totient: the exponent of the unit group mod `n`."
);
partial!(
    primorial,
    ntheory_more,
    "The product of every prime at most `n`."
);
partial!(
    next_prime,
    ntheory_more,
    "The least prime strictly above `n`."
);
partial!(
    prev_prime,
    ntheory_more,
    "The greatest prime strictly below `n`."
);

/// `sigma_k(n)`, the sum of the `k`-th powers of the divisors of `n`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn sigma_k(k: u32, n: i128) -> Option<i128> {
    axeyum_cas::ntheory_more::sigma_k(k, n)
}

/// Jordan's totient `J_k(n)`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn jordan_totient(k: u32, n: i128) -> Option<i128> {
    axeyum_cas::ntheory_more::jordan_totient(k, n)
}

/// Whether `m` and `n` are an amicable pair.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn are_amicable(m: i128, n: i128) -> bool {
    axeyum_cas::ntheory_more::are_amicable(m, n)
}

/// Every primitive Pythagorean triple with hypotenuse at most `limit`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn primitive_pythagorean_triples(limit: i128) -> Option<Vec<(i128, i128, i128)>> {
    axeyum_cas::ntheory_more::primitive_pythagorean_triples(limit)
}

/// The integer `k`-th root of `n` (floor), or `None` outside the fragment.
///
/// Tier R: a pure function of its arguments. `k == 0` is the degenerate
/// argument and returns `None`.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn integer_nth_root(n: i128, k: u32) -> Option<i128> {
    axeyum_cas::ntheory_more::integer_nth_root(n, k)
}

/// `(base, exponent)` with `base ** exponent == n` and `exponent` maximal, or
/// `None` when `n` is not a perfect power.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn perfect_power(n: i128) -> Option<(i128, u32)> {
    axeyum_cas::ntheory_more::perfect_power(n)
}

/// The `k`-th prime, one-based: `nth_prime(1) == 2`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn nth_prime(k: u32) -> Option<i128> {
    axeyum_cas::ntheory_more::nth_prime(k)
}

// ------------------------------------------------------- ntheory_advanced.rs

/// `P(n, k)`, the number of ordered `k`-selections from `n`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn permutations(n: i128, k: i128) -> Option<i128> {
    axeyum_cas::ntheory_advanced::permutations(n, k)
}

/// The Legendre symbol `(a / p)` for an odd prime `p`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn legendre_symbol(a: i128, p: i128) -> i32 {
    axeyum_cas::ntheory_advanced::legendre_symbol(a, p)
}

/// The Jacobi symbol `(a / n)` for odd positive `n`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn jacobi_symbol(a: i128, n: i128) -> i32 {
    axeyum_cas::ntheory_advanced::jacobi_symbol(a, n)
}

/// The Kronecker symbol `(a / n)`, defined for every integer `n`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn kronecker_symbol(a: i128, n: i128) -> i32 {
    axeyum_cas::ntheory_advanced::kronecker_symbol(a, n)
}

/// Whether `a` is a nonzero quadratic residue mod the prime `p`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn is_quadratic_residue(a: i128, p: i128) -> bool {
    axeyum_cas::ntheory_advanced::is_quadratic_residue(a, p)
}

/// A square root of `a` mod the prime `p`, or `None` when none exists.
///
/// Tier R: a pure function of its arguments. `None` is decided: `a` is a
/// non-residue.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn sqrt_mod(a: i128, p: i128) -> Option<i128> {
    axeyum_cas::ntheory_advanced::sqrt_mod(a, p)
}

/// Every solution of `a x == b (mod n)` in `0..n`, or `None` when there is none.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn solve_linear_congruence(a: i128, b: i128, n: i128) -> Option<Vec<i128>> {
    axeyum_cas::ntheory_advanced::solve_linear_congruence(a, b, n)
}

/// The multiplicative order of `a` mod `n`, or `None` when they are not coprime.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn multiplicative_order(a: i128, n: i128) -> Option<i128> {
    axeyum_cas::ntheory_advanced::multiplicative_order(a, n)
}

/// The least primitive root mod `n`, or `None` when the unit group is not
/// cyclic.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn primitive_root(n: i128) -> Option<i128> {
    axeyum_cas::ntheory_advanced::primitive_root(n)
}

/// The least `x` with `base ** x == target (mod modulus)`, or `None`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn discrete_log(base: i128, target: i128, modulus: i128) -> Option<i128> {
    axeyum_cas::ntheory_advanced::discrete_log(base, target, modulus)
}

/// The continued-fraction expansion of `num / den`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn continued_fraction(num: i128, den: i128) -> Vec<i128> {
    axeyum_cas::ntheory_advanced::continued_fraction(num, den)
}

/// The convergents `[(numerator, denominator), ...]` of a continued fraction.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn convergents(cf: Vec<i128>) -> Vec<(i128, i128)> {
    axeyum_cas::ntheory_advanced::convergents(&cf)
}

/// `(a0, period)` for the continued fraction of `sqrt(d)`, or `None` when `d` is
/// a perfect square or non-positive.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn sqrt_continued_fraction(d: i128) -> Option<(i128, Vec<i128>)> {
    axeyum_cas::ntheory_advanced::sqrt_continued_fraction(d)
}

/// The fundamental solution `(x, y)` of `x^2 - d y^2 == 1`, or `None`.
///
/// Tier R: a pure function of its arguments.
#[cfg_attr(
    feature = "stub-gen",
    pyo3_stub_gen::derive::gen_stub_pyfunction(module = "axeyum._native.cas")
)]
#[pyfunction]
fn pell_fundamental_solution(d: i128) -> Option<(i128, i128)> {
    axeyum_cas::ntheory_advanced::pell_fundamental_solution(d)
}

/// Registers the number-theory surface on `module`.
///
/// # Errors
///
/// Propagates any Python error raised while setting the module attributes.
pub(crate) fn register(module: &Bound<'_, PyModule>) -> PyResult<()> {
    macro_rules! add {
        ($($name:ident),* $(,)?) => {
            $(module.add_function(wrap_pyfunction!($name, module)?)?;)*
        };
    }
    add!(
        gcd,
        lcm,
        extended_gcd,
        mod_pow,
        mod_inverse,
        is_prime,
        factorize,
        factor_list,
        divisors,
        euler_phi,
        num_divisors,
        sum_divisors,
        crt,
        factorial,
        binomial,
        mobius,
        mertens,
        sigma_k,
        jordan_totient,
        is_perfect,
        aliquot_sum,
        is_abundant,
        is_deficient,
        are_amicable,
        is_squarefree,
        radical,
        primitive_pythagorean_triples,
        integer_nth_root,
        perfect_power,
        carmichael_lambda,
        primorial,
        next_prime,
        prev_prime,
        prime_pi,
        nth_prime,
        is_carmichael_number,
        permutations,
        legendre_symbol,
        jacobi_symbol,
        kronecker_symbol,
        is_quadratic_residue,
        sqrt_mod,
        solve_linear_congruence,
        multiplicative_order,
        primitive_root,
        discrete_log,
        continued_fraction,
        convergents,
        sqrt_continued_fraction,
        pell_fundamental_solution,
    );
    Ok(())
}
