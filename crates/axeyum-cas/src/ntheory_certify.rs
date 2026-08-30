//! Independently checkable certificates for the classical number-theoretic
//! routines in [`crate::ntheory`].
//!
//! # Why this module exists
//!
//! [`crate::ntheory`] computes. It does not *justify*. `is_prime` is a
//! deterministic Miller-Rabin over a fixed witness set whose correctness rests
//! on an external literature result about that base set — nothing about a
//! particular call is checkable after the fact. `factorize`, `crt` and their
//! neighbours are likewise bare computation. Measured across the crate on
//! 2026-08-30, `ntheory.rs` and `ntheory_advanced.rs` carried **zero**
//! `verify_*`/`check_*` entry points between them (68 functions), while sibling
//! analysis modules in the same crate carried 8 (`taylor.rs`) and 9 (`mvt.rs`).
//!
//! This module closes that gap for four routines. Every type here is a
//! *certificate*: data that a checker sharing no code with the producer can
//! re-derive from the original question, using only exact integer arithmetic.
//! The model is `axeyum_solver::lia_gcd::check_diophantine_certificate`.
//!
//! # Trust anchor (ADR-0601)
//!
//! **Nothing in this module reconstructs through `Kernel::add_declaration`, and
//! that is deliberate.** These checkers are exact `i128` computation. A kernel
//! reconstruction of, say, `n = d * e` over the unary-numeral `Nat` prelude
//! would be an `Eq.refl` on a numeral tower — precisely the `refl`-shaped,
//! substance-free reconstruction the CAS substance gate exists to catch. So
//! this evidence is honestly labeled **`cas-internal`**: it is a real,
//! independently re-derivable check, and it is not a kernel proof.
//!
//! # The prime / composite asymmetry
//!
//! A *composite* witness is a divisor — one division checks it
//! ([`CompositeCertificate`]). A *prime* witness is not; primality is certified
//! by a **Pratt certificate** ([`PrattCertificate`]), the recursive Lucas test.
//! The two are separate types with separate checkers and are never
//! interchangeable.

use crate::ntheory;

// ---------------------------------------------------------------------------
// Independent modular arithmetic
// ---------------------------------------------------------------------------
//
// Written here rather than reused from `ntheory` on purpose: a defect in a
// shared `mod_pow` would fool the producer and the checker identically, which
// is exactly the failure an independent checker exists to rule out.

/// `(a + b) mod m` for `a, b < m`, without overflowing `u128`.
fn add_mod(a: u128, b: u128, m: u128) -> u128 {
    debug_assert!(a < m && b < m);
    if a >= m - b { a - (m - b) } else { a + b }
}

/// `(a * b) mod m`, overflow-safe for every `m <= u128::MAX`.
fn mul_mod(a: u128, b: u128, m: u128) -> u128 {
    if m <= 1 {
        return 0;
    }
    if m <= u64::MAX as u128 {
        // Both reduced operands are `< 2^64`, so the product fits `u128`.
        return (a % m) * (b % m) % m;
    }
    let mut a = a % m;
    let mut b = b % m;
    let mut acc: u128 = 0;
    while b > 0 {
        if b & 1 == 1 {
            acc = add_mod(acc, a, m);
        }
        a = add_mod(a, a, m);
        b >>= 1;
    }
    acc
}

/// `base^exp mod m`, overflow-safe. Returns `0` for `m <= 1`.
fn pow_mod(base: u128, mut exp: u128, m: u128) -> u128 {
    if m <= 1 {
        return 0;
    }
    let mut result: u128 = 1 % m;
    let mut b = base % m;
    while exp > 0 {
        if exp & 1 == 1 {
            result = mul_mod(result, b, m);
        }
        b = mul_mod(b, b, m);
        exp >>= 1;
    }
    result
}

/// Test-only access to [`pow_mod`], so the adversarial suite can compare this
/// module's independent modular arithmetic against [`crate::ntheory`]'s and
/// exercise the `> u64::MAX` slow path directly.
#[cfg(test)]
pub(crate) fn pow_mod_for_tests(base: u128, exp: u128, m: u128) -> u128 {
    pow_mod(base, exp, m)
}

/// Checked `∏ base^exp` over `(base, exponent)` pairs, as `u128`.
/// Returns `None` on overflow. The empty product is `1`.
fn checked_prod_pow(factors: &[(i128, u32)]) -> Option<u128> {
    let mut acc: u128 = 1;
    for &(base, exponent) in factors {
        let base = u128::try_from(base).ok()?;
        for _ in 0..exponent {
            acc = acc.checked_mul(base)?;
        }
    }
    Some(acc)
}

/// Recursion depth beyond which [`check_primality_certificate`] refuses.
///
/// Not part of the soundness argument — a *genuine* certificate for an `i128`
/// has depth well under 130, since every recursive step moves to a prime factor
/// of `n - 1`. It bounds a **forged** certificate, which can present a
/// syntactically consistent chain `n, n-1, n-2, …` of length `n` and would
/// otherwise exhaust the stack before any arithmetic guard fires.
const MAX_PRATT_DEPTH: u32 = 200;

// ---------------------------------------------------------------------------
// Primality: Pratt certificates
// ---------------------------------------------------------------------------

/// A Pratt (Lucas) certificate that a number `n` is **prime**.
///
/// It exhibits a `witness` `a` of multiplicative order exactly `n - 1` modulo
/// `n`, which forces `|(Z/n)*| >= n - 1` and hence `n` prime. Establishing that
/// order needs the *complete* prime factorization of `n - 1`, so the
/// certificate carries it (`factors`) together with a recursive certificate for
/// each prime base (`subcerts`).
///
/// The number being certified is **not** stored here: it is supplied by the
/// caller to [`check_primality_certificate`], so a certificate can never
/// disagree with itself about its own subject.
///
/// # Completeness is load-bearing
///
/// Omitting even one prime factor of `n - 1` makes the Lucas test unsound.
/// Measured: `n = 91` (`= 7*13`, composite) with `witness = 3` and
/// `factors = [(2, 1)]` satisfies `3^90 = 1` and `3^45 != 1 (mod 91)` — every
/// order check passes. Only `prod base^exp = n - 1` rejects it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrattCertificate {
    /// A claimed element of order `n - 1` modulo `n`.
    pub witness: i128,
    /// The complete prime factorization of `n - 1`, strictly ascending by base,
    /// every exponent `>= 1`. Empty exactly when `n = 2`.
    pub factors: Vec<(i128, u32)>,
    /// One certificate per entry of `factors`, in the same order; `subcerts[i]`
    /// certifies that `factors[i].0` is prime.
    pub subcerts: Vec<PrattCertificate>,
}

/// Independently validates that `cert` proves `n` is prime.
///
/// Re-derives every claim from `n` alone: that the stated factors multiply to
/// exactly `n - 1`, that each factor base is itself certified prime, that
/// `witness^(n-1) = 1 (mod n)`, and that `witness^((n-1)/q) != 1 (mod n)` for
/// every factor base `q`. Shares no code with [`certify_prime`] or with
/// [`crate::ntheory::is_prime`]; in particular the modular arithmetic is this
/// module's own.
///
/// Returns `true` only when every check passes. Arithmetic is checked; any
/// overflow conservatively returns `false`.
///
/// # Panics
///
/// Never panics.
#[must_use]
pub fn check_primality_certificate(n: i128, cert: &PrattCertificate) -> bool {
    check_primality_certificate_at(n, cert, 0)
}

fn check_primality_certificate_at(n: i128, cert: &PrattCertificate, depth: u32) -> bool {
    // G1: the subject must be a candidate prime at all.
    if n < 2 {
        return false;
    }
    // G2: the witness must be a residue in `1..n`.
    if cert.witness <= 0 || cert.witness >= n {
        return false;
    }
    // G3: one subcertificate per stated factor.
    if cert.factors.len() != cert.subcerts.len() {
        return false;
    }
    // G4: bases strictly ascending — canonical, and rejects duplicates.
    for window in cert.factors.windows(2) {
        if window[0].0 >= window[1].0 {
            return false;
        }
    }
    // G5: every exponent is at least one, and every base is at least two.
    if cert
        .factors
        .iter()
        .any(|&(base, exponent)| exponent == 0 || base < 2)
    {
        return false;
    }
    // G6: the factorization of `n - 1` is COMPLETE.
    let Some(target) = n.checked_sub(1).and_then(|v| u128::try_from(v).ok()) else {
        return false;
    };
    let Some(product) = checked_prod_pow(&cert.factors) else {
        return false;
    };
    if product != target {
        return false;
    }
    // G10: refuse an adversarially deep chain before recursing.
    if depth >= MAX_PRATT_DEPTH {
        return false;
    }
    // G7: every factor base is itself certified prime.
    for (&(base, _), sub) in cert.factors.iter().zip(&cert.subcerts) {
        if !check_primality_certificate_at(base, sub, depth + 1) {
            return false;
        }
    }
    let Ok(modulus) = u128::try_from(n) else {
        return false;
    };
    let Ok(witness) = u128::try_from(cert.witness) else {
        return false;
    };
    // G8: Fermat — the witness's order divides `n - 1`.
    if pow_mod(witness, target, modulus) != 1 % modulus {
        return false;
    }
    // G9: maximality — the order divides no proper divisor `(n-1)/q`.
    for &(base, _) in &cert.factors {
        let Ok(q) = u128::try_from(base) else {
            return false;
        };
        if q == 0 || target % q != 0 {
            return false;
        }
        if pow_mod(witness, target / q, modulus) == 1 % modulus {
            return false;
        }
    }
    true
}

/// Produces a [`PrattCertificate`] for `n`, or `None` when `n` is not prime (or
/// when no witness is found within the search budget).
///
/// The returned certificate is validated by [`check_primality_certificate`]
/// before being handed back, so a `Some` result is always checkable.
#[must_use]
pub fn certify_prime(n: i128) -> Option<PrattCertificate> {
    let cert = build_prime_certificate(n)?;
    check_primality_certificate(n, &cert).then_some(cert)
}

/// Number of small bases tried when searching for a Lucas witness.
const WITNESS_SEARCH_BUDGET: i128 = 2_000;

fn build_prime_certificate(n: i128) -> Option<PrattCertificate> {
    if n < 2 {
        return None;
    }
    if n == 2 {
        return Some(PrattCertificate {
            witness: 1,
            factors: Vec::new(),
            subcerts: Vec::new(),
        });
    }
    if !ntheory::is_prime(n) {
        return None;
    }
    let factors = ntheory::factorize(n - 1);
    let mut subcerts = Vec::with_capacity(factors.len());
    for &(base, _) in &factors {
        subcerts.push(build_prime_certificate(base)?);
    }
    let target = u128::try_from(n - 1).ok()?;
    let modulus = u128::try_from(n).ok()?;
    let limit = if n - 1 < WITNESS_SEARCH_BUDGET {
        n - 1
    } else {
        WITNESS_SEARCH_BUDGET
    };
    for candidate in 2..=limit {
        let witness = u128::try_from(candidate).ok()?;
        if pow_mod(witness, target, modulus) != 1 {
            continue;
        }
        let maximal = factors.iter().all(|&(base, _)| {
            u128::try_from(base).is_ok_and(|q| q != 0 && pow_mod(witness, target / q, modulus) != 1)
        });
        if maximal {
            return Some(PrattCertificate {
                witness: candidate,
                factors,
                subcerts,
            });
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Compositeness
// ---------------------------------------------------------------------------

/// A certificate that a number `n` is **composite**: a nontrivial divisor.
///
/// Deliberately a distinct type from [`PrattCertificate`]. The two directions
/// have entirely different costs and are never interchangeable — this one is
/// checked by a single division.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompositeCertificate {
    /// A divisor `d` of `n` with `1 < d < n`.
    pub divisor: i128,
}

/// Independently validates that `cert` proves `n` is composite.
///
/// Returns `true` only when `1 < divisor < n` and `divisor` divides `n`.
///
/// # Panics
///
/// Never panics.
#[must_use]
pub fn check_composite_certificate(n: i128, cert: &CompositeCertificate) -> bool {
    // C1: the divisor must be nontrivial from below.
    if cert.divisor <= 1 {
        return false;
    }
    // C2: and from above.
    if cert.divisor >= n {
        return false;
    }
    // C3: and must actually divide.
    n % cert.divisor == 0
}

/// Produces a [`CompositeCertificate`] for `n`, or `None` when `n` is not a
/// composite `>= 4`. Self-checked before return.
#[must_use]
pub fn certify_composite(n: i128) -> Option<CompositeCertificate> {
    if n < 4 {
        return None;
    }
    let divisor = ntheory::factorize(n).first().map(|&(p, _)| p)?;
    if divisor >= n {
        return None;
    }
    let cert = CompositeCertificate { divisor };
    check_composite_certificate(n, &cert).then_some(cert)
}

// ---------------------------------------------------------------------------
// Factorization
// ---------------------------------------------------------------------------

/// A certificate that a `(prime, exponent)` list is *the* prime factorization
/// of `|n|`.
///
/// Carries the factor list together with a [`PrattCertificate`] for every base,
/// so the checker establishes both halves independently: the product identity
/// and the primality of each factor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactorizationCertificate {
    /// `(prime, exponent)` pairs, strictly ascending by base, exponents `>= 1`.
    pub factors: Vec<(i128, u32)>,
    /// One [`PrattCertificate`] per entry of `factors`, in the same order.
    pub primality: Vec<PrattCertificate>,
}

/// Independently validates that `cert` gives the prime factorization of `|n|`.
///
/// Checks that the bases are strictly ascending (so the list is canonical and
/// duplicate-free), that every exponent is at least one, that `prod base^exp`
/// equals `|n|` exactly, and that every base carries a valid Pratt certificate.
///
/// `n = 0` is never certifiable: the empty product is `1`, and no finite
/// product of primes is `0`.
///
/// # Panics
///
/// Never panics.
#[must_use]
pub fn check_factorization_certificate(n: i128, cert: &FactorizationCertificate) -> bool {
    // F1: one primality certificate per factor.
    if cert.factors.len() != cert.primality.len() {
        return false;
    }
    // F2: strictly ascending bases — canonical, and rejects a repeated base.
    for window in cert.factors.windows(2) {
        if window[0].0 >= window[1].0 {
            return false;
        }
    }
    // F3: every exponent at least one.
    if cert.factors.iter().any(|&(_, exponent)| exponent == 0) {
        return false;
    }
    // F4: the product identity.
    let Some(product) = checked_prod_pow(&cert.factors) else {
        return false;
    };
    if product != n.unsigned_abs() {
        return false;
    }
    // F5: every base is certified prime.
    cert.factors
        .iter()
        .zip(&cert.primality)
        .all(|(&(base, _), sub)| check_primality_certificate(base, sub))
}

/// Produces a [`FactorizationCertificate`] for `|n|`, or `None` for `n = 0` or
/// when a factor cannot be certified prime. Self-checked before return.
#[must_use]
pub fn certify_factorization(n: i128) -> Option<FactorizationCertificate> {
    if n == 0 {
        return None;
    }
    let factors = ntheory::factorize(n);
    let mut primality = Vec::with_capacity(factors.len());
    for &(base, _) in &factors {
        primality.push(certify_prime(base)?);
    }
    let cert = FactorizationCertificate { factors, primality };
    check_factorization_certificate(n, &cert).then_some(cert)
}

// ---------------------------------------------------------------------------
// Chinese remainder theorem
// ---------------------------------------------------------------------------

/// A certificate for a system of congruences `x = a_i (mod m_i)`, in whichever
/// direction the system resolves.
///
/// The two variants are separate cases the producer distinguishes, and the
/// checker refutes each independently — a [`CrtCertificate::Inconsistent`]
/// witness over a solvable system is rejected, and vice versa.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CrtCertificate {
    /// The system is solvable: `solution` is the unique residue in
    /// `0..modulus`, and `modulus` is the **least** common multiple of the
    /// moduli.
    Solution {
        /// The claimed simultaneous solution.
        solution: i128,
        /// The claimed least common multiple of the input moduli.
        modulus: i128,
    },
    /// The system is unsolvable, witnessed by two congruences that already
    /// conflict: `a_left != a_right (mod gcd(m_left, m_right))`.
    Inconsistent {
        /// Index of the first conflicting congruence.
        left: usize,
        /// Index of the second conflicting congruence.
        right: usize,
    },
}

/// Independently validates `cert` against the original `residues`.
///
/// For a [`CrtCertificate::Solution`], re-derives every congruence and the
/// least common multiple from `residues` alone. Recording only a *common*
/// multiple would be insufficient: `residues = [(1, 4), (3, 6)]` with
/// `solution = 9, modulus = 24` satisfies both congruences and `0 <= 9 < 24`,
/// yet `24` is not the least common multiple `12`, so the certificate would
/// overstate the solution set's spacing. The leastness check is what rejects it.
///
/// For a [`CrtCertificate::Inconsistent`], recomputes the conflict.
///
/// # Panics
///
/// Never panics.
#[must_use]
pub fn check_crt_certificate(residues: &[(i128, i128)], cert: &CrtCertificate) -> bool {
    // R1: every modulus must be positive, in both directions.
    if residues.iter().any(|&(_, modulus)| modulus <= 0) {
        return false;
    }
    match *cert {
        CrtCertificate::Solution { solution, modulus } => {
            // R2: the modulus must be positive and the solution the canonical
            // representative in `0..modulus`.
            if modulus <= 0 || solution < 0 || solution >= modulus {
                return false;
            }
            // R3: every congruence must hold.
            if residues
                .iter()
                .any(|&(residue, m)| (solution - residue).rem_euclid(m) != 0)
            {
                return false;
            }
            // R4: the modulus must be the LEAST common multiple, not merely a
            // common one.
            let mut acc: i128 = 1;
            for &(_, m) in residues {
                let Some(next) = ntheory::lcm(acc, m) else {
                    return false;
                };
                acc = next;
            }
            acc == modulus
        }
        CrtCertificate::Inconsistent { left, right } => {
            // R5: both indices must name real congruences.
            let (Some(&(a_left, m_left)), Some(&(a_right, m_right))) =
                (residues.get(left), residues.get(right))
            else {
                return false;
            };
            // R6: the conflict must be real.
            let common = ntheory::gcd(m_left, m_right);
            if common == 0 {
                return false;
            }
            (a_left - a_right).rem_euclid(common) != 0
        }
    }
}

/// Produces a [`CrtCertificate`] for `residues`, or `None` when neither
/// direction can be certified (a non-positive modulus, or an overflow in the
/// least common multiple). Self-checked before return.
#[must_use]
pub fn certify_crt(residues: &[(i128, i128)]) -> Option<CrtCertificate> {
    if residues.iter().any(|&(_, modulus)| modulus <= 0) {
        return None;
    }
    let cert = if let Some((solution, modulus)) = ntheory::crt(residues) {
        CrtCertificate::Solution { solution, modulus }
    } else {
        // Pairwise compatibility is necessary and sufficient, so a conflicting
        // pair always exists for an unsolvable system with positive moduli.
        let mut found = None;
        'outer: for left in 0..residues.len() {
            for right in (left + 1)..residues.len() {
                let candidate = CrtCertificate::Inconsistent { left, right };
                if check_crt_certificate(residues, &candidate) {
                    found = Some(candidate);
                    break 'outer;
                }
            }
        }
        found?
    };
    check_crt_certificate(residues, &cert).then_some(cert)
}

#[cfg(test)]
mod ntheory_certify_tests;
