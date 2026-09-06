//! `p`-adic lifting of a **simple** root: [`HenselRoot`] and its certificate.
//!
//! Hensel's lemma in the form this module implements: if `f ∈ ℤ[x]`,
//! `f(a) ≡ 0 (mod p^k)` and `f'(a)` is a unit modulo `p`, then there is a
//! unique `a' ≡ a (mod p^k)` with `f(a') ≡ 0 (mod p^(2k))`, and it is one
//! Newton step — `a' = a − f(a)·f'(a)^(−1)` — reduced modulo `p^(2k)`.
//!
//! Two things this module is deliberate about.
//!
//! **The precision doubles, and the certificate records the doubling.** The
//! design note's §6 rule is that a certificate must carry every distinction
//! its producer makes, and the distinction a lift makes is *at which precision
//! each intermediate root was correct*. So [`HenselCertificate`] carries the
//! whole chain `a₁, a₂, a₄, …`, and its `verify` re-derives
//! `f(aᵢ) ≡ 0 (mod p^(2^i))` for every rung independently as well as the
//! congruence `aᵢ₊₁ ≡ aᵢ (mod p^(2^i))` that makes the chain a *lift* rather
//! than an unrelated sequence of roots.
//!
//! **Irreducibility gets no witness, and neither does uniqueness.** The
//! certificate says "this residue is a root at this precision, reached by this
//! chain from that seed". It does not say it is the only one — Hensel's
//! uniqueness is a theorem about the derivative condition, and the checker
//! discharges that condition (`f'(a₁)` invertible mod `p`) rather than
//! asserting the conclusion.
//!
//! # Relationship to `axeyum-cas`'s `factor_int.rs`
//!
//! `factor_int.rs:723`'s `hensel_lift_two` is a **different object**: linear
//! (not quadratic) lifting of a two-factor factorization in `𝔽ₚ[x]`, carried
//! on `i128` coefficients whose overflow is load-bearing as the termination
//! argument (ADR-1702's finding, and the design note's "a slice that removes a
//! bound must add one"). Migrating it is slice 7 of the design note's
//! migration plan, with `gfp.rs` named as its differential oracle. This module
//! is the **root** half of `HenselLift`, which had no in-tree implementation
//! at any width; it does not claim to replace the polynomial half.

use num_bigint::{BigInt, BigUint, Sign};

use crate::upoly::ZPoly;
use crate::{HenselLift, UnivariatePoly};

/// The largest number of doubling steps [`lift_root`] will take.
///
/// Each step squares the modulus, so 64 steps is a modulus of `p^(2^63)` — a
/// number no machine can hold. The cap is the crate's usual "decline rather
/// than run away" contract rather than a real limit on the mathematics.
pub const MAX_LIFT_STEPS: u32 = 64;

/// A root of an integer polynomial modulo a prime power, carried together with
/// the polynomial it is a root of.
///
/// The pair is the unit of a lift because [`HenselLift::lift`] needs both: a
/// residue alone cannot be Newton-stepped.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HenselRoot {
    polynomial: ZPoly,
    residue: BigUint,
}

impl HenselRoot {
    /// The claim that `residue` is a root of `polynomial` at some precision.
    ///
    /// Nothing is checked here — [`HenselRoot::is_root_mod`] is the check, and
    /// [`lift_root`] runs it on the seed before doing any work.
    #[must_use]
    pub fn new(polynomial: ZPoly, residue: BigUint) -> Self {
        Self {
            polynomial,
            residue,
        }
    }

    /// The polynomial.
    #[must_use]
    pub fn polynomial(&self) -> &ZPoly {
        &self.polynomial
    }

    /// The residue.
    #[must_use]
    pub fn residue(&self) -> &BigUint {
        &self.residue
    }

    /// Whether `f(residue) ≡ 0 (mod modulus)`.
    #[must_use]
    pub fn is_root_mod(&self, modulus: &BigUint) -> bool {
        if modulus.bits() == 0 {
            return false;
        }
        reduce(
            &self
                .polynomial
                .evaluate(&BigInt::from(self.residue.clone())),
            modulus,
        )
        .bits()
            == 0
    }
}

impl HenselLift for HenselRoot {
    /// One Newton step: `self`, a root modulo `prime^precision`, lifted to a
    /// root modulo `prime^(2·precision)`.
    ///
    /// Returns `None` when `prime < 2`, when `precision` is zero, when `self`
    /// is not actually a root at the stated precision, or when `f'(self)` is
    /// not invertible modulo `prime` — which is exactly the hypothesis
    /// Hensel's lemma needs and the one a "simple root" names.
    fn lift(&self, prime: &BigUint, precision: u32) -> Option<Self> {
        if prime < &BigUint::from(2u8) || precision == 0 {
            return None;
        }
        let modulus = prime.pow(precision);
        if !self.is_root_mod(&modulus) {
            return None;
        }
        let squared = &modulus * &modulus;
        let point = BigInt::from(self.residue.clone());
        let value = reduce(&self.polynomial.evaluate(&point), &squared);
        let slope = reduce(&self.polynomial.derivative().evaluate(&point), &squared);
        // The derivative must be a unit modulo `prime`; inverting it modulo
        // `prime^(2·precision)` fails exactly when it is not.
        let inverse = invert_mod(&slope, &squared)?;
        let correction = (&value * &inverse) % &squared;
        let residue = (&squared + &self.residue - correction) % &squared;
        Some(Self {
            polynomial: self.polynomial.clone(),
            residue,
        })
    }
}

/// The chain of a full lift from a root modulo `prime` to a root modulo
/// `prime^precision`.
///
/// The chain is the doubling sequence, so entry `i` is a root modulo
/// `prime^(2^i)` — except the last, which is reduced to the modulus the caller
/// asked for. Each entry is one congruence the checker discharges on its own.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HenselCertificate {
    /// The polynomial the residues are roots of.
    pub polynomial: ZPoly,
    /// The prime.
    pub prime: BigUint,
    /// The exponent the final residue is a root at.
    pub precision: u32,
    /// The final residue, reduced modulo `prime^precision`.
    pub root: BigUint,
    /// The doubling chain, starting from the seed root modulo `prime`. Entry
    /// `i` is claimed to be a root modulo `prime^min(2^i, precision)`.
    pub chain: Vec<BigUint>,
}

impl HenselCertificate {
    /// Re-derive every rung of the lift from the recorded polynomial and
    /// prime, using nothing the producer computed.
    ///
    /// Six independently-failable conditions:
    ///
    /// 1. the prime is at least two and the precision at least one (there is a
    ///    modulus to work in);
    /// 2. the chain is non-empty and has exactly the length the doubling
    ///    sequence from `1` to `precision` requires — a chain padded with an
    ///    extra, otherwise-consistent rung is caught here rather than by a
    ///    value that happens to still match;
    /// 3. **`f'(chain[0])` is invertible modulo `prime`** — the simple-root
    ///    hypothesis, without which the lift is not unique and the claim means
    ///    much less than it looks like it means;
    /// 4. **every rung is a root at its own precision**: `f(chain[i]) ≡ 0`
    ///    modulo `prime^min(2^i, precision)`, recomputed by Horner;
    /// 5. **every rung lifts the previous one**: `chain[i+1] ≡ chain[i]`
    ///    modulo the previous rung's modulus. Condition 4 alone is satisfied
    ///    by *any* sequence of roots at increasing precision, including one
    ///    that jumps between two different roots of the same polynomial, so
    ///    this is the guard that makes the chain a lift;
    /// 6. the final rung equals `root`, and `root` is reduced (`< prime^precision`).
    #[must_use]
    pub fn verify(&self) -> bool {
        if self.prime < BigUint::from(2u8) || self.precision == 0 {
            return false;
        }
        let steps = doubling_precisions(self.precision);
        if self.chain.len() != steps.len() {
            return false;
        }
        let Some(seed) = self.chain.first() else {
            return false;
        };
        let slope = reduce(
            &self
                .polynomial
                .derivative()
                .evaluate(&BigInt::from(seed.clone())),
            &self.prime,
        );
        if invert_mod(&slope, &self.prime).is_none() {
            return false;
        }
        let mut previous: Option<(BigUint, BigUint)> = None;
        for (rung, exponent) in self.chain.iter().zip(&steps) {
            let modulus = self.prime.pow(*exponent);
            if rung >= &modulus {
                return false;
            }
            let value = reduce(
                &self.polynomial.evaluate(&BigInt::from(rung.clone())),
                &modulus,
            );
            if value.bits() != 0 {
                return false;
            }
            if let Some((previous_rung, previous_modulus)) = &previous
                && rung % previous_modulus != previous_rung % previous_modulus
            {
                return false;
            }
            previous = Some((rung.clone(), modulus));
        }
        let final_modulus = self.prime.pow(self.precision);
        self.chain.last() == Some(&self.root) && self.root < final_modulus
    }
}

/// The exponents the doubling sequence visits on the way to `precision`:
/// `1, 2, 4, …`, with the last entry clamped to `precision`.
fn doubling_precisions(precision: u32) -> Vec<u32> {
    let mut out = vec![1u32];
    let mut current = 1u32;
    while current < precision && out.len() <= MAX_LIFT_STEPS as usize {
        current = current.saturating_mul(2).min(precision);
        out.push(current);
    }
    out
}

/// Lift a seed root of `polynomial` modulo `prime` all the way to modulo
/// `prime^precision`, recording the chain.
///
/// Returns `None` when `prime < 2`, when `precision` is zero or would need
/// more than [`MAX_LIFT_STEPS`] doublings, when `seed` is not a root modulo
/// `prime`, or when `f'(seed)` is not invertible modulo `prime`.
pub fn lift_root(
    polynomial: &ZPoly,
    prime: &BigUint,
    seed: &BigUint,
    precision: u32,
) -> Option<HenselCertificate> {
    if prime < &BigUint::from(2u8) || precision == 0 {
        return None;
    }
    let steps = doubling_precisions(precision);
    if steps.len() > MAX_LIFT_STEPS as usize {
        return None;
    }
    let mut current = HenselRoot::new(polynomial.clone(), seed % prime);
    if !current.is_root_mod(prime) {
        return None;
    }
    let slope = reduce(
        &polynomial
            .derivative()
            .evaluate(&BigInt::from(current.residue.clone())),
        prime,
    );
    invert_mod(&slope, prime)?;

    let mut chain = vec![current.residue.clone()];
    let mut reached = 1u32;
    for target in steps.iter().skip(1) {
        let lifted = current.lift(prime, reached)?;
        // A doubling can overshoot the requested precision; reduce onto the
        // modulus the chain entry claims.
        let modulus = prime.pow(*target);
        current = HenselRoot::new(polynomial.clone(), &lifted.residue % &modulus);
        chain.push(current.residue.clone());
        reached = *target;
    }
    Some(HenselCertificate {
        polynomial: polynomial.clone(),
        prime: prime.clone(),
        precision,
        root: current.residue.clone(),
        chain,
    })
}

/// `value mod modulus`, as a non-negative residue.
fn reduce(value: &BigInt, modulus: &BigUint) -> BigUint {
    let signed_modulus = BigInt::from(modulus.clone());
    let mut remainder = value % &signed_modulus;
    if remainder.sign() == Sign::Minus {
        remainder += &signed_modulus;
    }
    remainder
        .to_biguint()
        .expect("a value reduced modulo a positive modulus is non-negative")
}

/// The inverse of `value` modulo `modulus`, or `None` when it is not a unit.
///
/// The extended Euclidean algorithm written directly here rather than routed
/// through [`crate::extended_gcd`]: this is used inside
/// [`HenselCertificate::verify`], and a checker that calls the producer's
/// helper is not an independent check of it.
fn invert_mod(value: &BigUint, modulus: &BigUint) -> Option<BigUint> {
    if modulus.bits() == 0 {
        return None;
    }
    let modulus_signed = BigInt::from(modulus.clone());
    let mut old_remainder = BigInt::from(value.clone()) % &modulus_signed;
    let mut remainder = modulus_signed.clone();
    let mut old_coefficient = BigInt::from(1);
    let mut coefficient = BigInt::from(0);
    while remainder.sign() != Sign::NoSign {
        let quotient = &old_remainder / &remainder;
        let next_remainder = &old_remainder - &quotient * &remainder;
        old_remainder = core::mem::replace(&mut remainder, next_remainder);
        let next_coefficient = &old_coefficient - &quotient * &coefficient;
        old_coefficient = core::mem::replace(&mut coefficient, next_coefficient);
    }
    if old_remainder != BigInt::from(1) {
        return None;
    }
    Some(reduce(&old_coefficient, modulus))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn nat(value: u64) -> BigUint {
        BigUint::from(value)
    }

    /// A wholly independent oracle: **every** residue modulo `p^k`, tested by
    /// direct evaluation. Exponential, so only used at small moduli — which is
    /// exactly the point, since it shares no code path with the Newton step.
    fn brute_force_roots(polynomial: &ZPoly, prime: u64, precision: u32) -> Vec<u64> {
        let modulus = prime.pow(precision);
        (0..modulus)
            .filter(|candidate| {
                let value = polynomial.evaluate(&BigInt::from(*candidate));
                reduce(&value, &nat(modulus)).bits() == 0
            })
            .collect()
    }

    #[test]
    fn a_simple_root_lifts_and_its_certificate_verifies() {
        // x^2 - 2 over ℤ_7: 3^2 = 9 ≡ 2, so 3 is a seed root and 2·3 = 6 is a
        // unit mod 7.
        let poly = ZPoly::from_i64(&[-2, 0, 1]);
        let certificate = lift_root(&poly, &nat(7), &nat(3), 4).expect("the lift must succeed");
        assert!(certificate.verify());
        assert_eq!(certificate.chain.len(), 3); // 1 -> 2 -> 4
        let modulus = 7u64.pow(4);
        let root = u64::try_from(certificate.root.clone()).unwrap();
        assert_eq!((root * root) % modulus, 2 % modulus);
        assert!(brute_force_roots(&poly, 7, 4).contains(&root));
    }

    #[test]
    fn the_lift_agrees_with_brute_force_over_a_deterministic_corpus() {
        // Every (polynomial, prime, seed) triple whose seed is a simple root
        // mod p, lifted to p^3 and checked against the exhaustive search.
        let polynomials = [
            ZPoly::from_i64(&[-2, 0, 1]),      // x^2 - 2
            ZPoly::from_i64(&[-1, 0, 0, 1]),   // x^3 - 1
            ZPoly::from_i64(&[3, -5, 1]),      // x^2 - 5x + 3
            ZPoly::from_i64(&[-6, 11, -6, 1]), // (x-1)(x-2)(x-3)
            ZPoly::from_i64(&[7, 1]),          // x + 7, degree 1
        ];
        let mut lifted_count = 0usize;
        for poly in &polynomials {
            for prime in [3u64, 5, 7, 11] {
                for seed in 0..prime {
                    let Some(certificate) = lift_root(poly, &nat(prime), &nat(seed), 3) else {
                        continue;
                    };
                    lifted_count += 1;
                    assert!(
                        certificate.verify(),
                        "poly={poly:?} prime={prime} seed={seed}"
                    );
                    let root = u64::try_from(certificate.root.clone()).unwrap();
                    let all = brute_force_roots(poly, prime, 3);
                    assert!(
                        all.contains(&root),
                        "lifted root {root} is not a root mod {prime}^3 (brute force: {all:?})"
                    );
                    // The lift must stay in the residue class it started in.
                    assert_eq!(root % prime, seed % prime);
                }
            }
        }
        assert!(
            lifted_count >= 20,
            "the corpus must actually lift something: {lifted_count}"
        );
    }

    #[test]
    fn a_multiple_root_is_declined_rather_than_lifted() {
        // x^2 has a double root at 0 mod p: f'(0) = 0 is not a unit.
        let poly = ZPoly::from_i64(&[0, 0, 1]);
        assert!(lift_root(&poly, &nat(5), &nat(0), 3).is_none());
        // x^2 - 1 mod 2: both roots collapse and the derivative 2x ≡ 0.
        let poly = ZPoly::from_i64(&[-1, 0, 1]);
        assert!(lift_root(&poly, &nat(2), &nat(1), 3).is_none());
    }

    #[test]
    fn a_non_root_seed_is_declined() {
        let poly = ZPoly::from_i64(&[-2, 0, 1]);
        // 2^2 = 4 ≢ 2 (mod 7).
        assert!(lift_root(&poly, &nat(7), &nat(2), 3).is_none());
        // 2 is not a square mod 5, so no seed works at all.
        for seed in 0..5 {
            assert!(lift_root(&poly, &nat(5), &nat(seed), 2).is_none());
        }
    }

    #[test]
    fn degenerate_primes_and_precisions_are_declined() {
        let poly = ZPoly::from_i64(&[-2, 0, 1]);
        assert!(lift_root(&poly, &nat(1), &nat(0), 3).is_none());
        assert!(lift_root(&poly, &nat(0), &nat(0), 3).is_none());
        assert!(lift_root(&poly, &nat(7), &nat(3), 0).is_none());
    }

    #[test]
    fn the_lift_reaches_a_precision_no_machine_word_holds() {
        // 2^64 residues would be an exhaustive search of 1.8e19 candidates;
        // the lift takes six doublings.
        let poly = ZPoly::from_i64(&[-2, 0, 1]);
        let certificate = lift_root(&poly, &nat(7), &nat(3), 40).expect("lift");
        assert!(certificate.verify());
        assert!(certificate.root.bits() > 64, "the root must exceed a word");
        let modulus = nat(7).pow(40);
        let root = BigInt::from(certificate.root.clone());
        assert_eq!(
            reduce(&(&root * &root - BigInt::from(2)), &modulus).bits(),
            0
        );
    }

    #[test]
    fn forged_hensel_certificates_all_fail_verification() {
        let poly = ZPoly::from_i64(&[-2, 0, 1]);
        let honest = lift_root(&poly, &nat(7), &nat(3), 4).expect("lift");
        assert!(honest.verify());

        // 1. A prime below two.
        let forged = HenselCertificate {
            prime: nat(1),
            ..honest.clone()
        };
        assert!(!forged.verify(), "a prime below two must be caught");

        // 2. A chain padded with a duplicate of its own last rung -- every
        //    value in it is a true root, so only the length guard rejects it.
        let mut chain = honest.chain.clone();
        chain.push(honest.root.clone());
        let forged = HenselCertificate {
            chain,
            ..honest.clone()
        };
        assert!(!forged.verify(), "a padded chain must be caught");

        // 3. A tampered intermediate rung, with the final root left true.
        let mut chain = honest.chain.clone();
        chain[1] += nat(1);
        let forged = HenselCertificate {
            chain,
            ..honest.clone()
        };
        assert!(!forged.verify(), "a tampered rung must be caught");

        // 4. A chain that jumps to the OTHER root of x^2 - 2 at the last rung.
        //    Every rung is a genuine root at its own precision, so guard 4
        //    passes and only the congruence guard can reject it.
        let modulus = nat(7).pow(4);
        let other = &modulus - &honest.root;
        let mut chain = honest.chain.clone();
        let last = chain.len() - 1;
        chain[last] = other.clone();
        let forged = HenselCertificate {
            chain,
            root: other.clone(),
            ..honest.clone()
        };
        let value = reduce(&poly.evaluate(&BigInt::from(other.clone())), &modulus);
        assert_eq!(value.bits(), 0, "the decoy must really be a root");
        assert!(
            !forged.verify(),
            "a chain that switches roots must be caught even though every rung is a root"
        );

        // 5. A tampered final root, with the chain left correct.
        let forged = HenselCertificate {
            root: &honest.root + nat(1),
            ..honest.clone()
        };
        assert!(!forged.verify(), "a tampered root must be caught");

        // 6. A multiple-root seed: the certificate is otherwise consistent but
        //    the simple-root hypothesis fails, so the uniqueness the lift
        //    claims does not hold.
        let square = ZPoly::from_i64(&[0, 0, 1]);
        let forged = HenselCertificate {
            polynomial: square,
            prime: nat(5),
            precision: 2,
            root: nat(0),
            chain: vec![nat(0), nat(0)],
        };
        assert!(
            !forged.verify(),
            "a non-simple root must be caught even though every rung evaluates to zero"
        );
    }

    #[test]
    fn one_lift_step_doubles_the_precision() {
        let poly = ZPoly::from_i64(&[-2, 0, 1]);
        let seed = HenselRoot::new(poly.clone(), nat(3));
        assert!(seed.is_root_mod(&nat(7)));
        assert!(!seed.is_root_mod(&nat(49)));
        let once = seed.lift(&nat(7), 1).expect("one step");
        assert!(once.is_root_mod(&nat(49)));
        let twice = once.lift(&nat(7), 2).expect("two steps");
        assert!(twice.is_root_mod(&nat(49).pow(2)));
        // ...and the step declines when told the wrong current precision.
        assert!(once.lift(&nat(7), 3).is_none());
    }
}
