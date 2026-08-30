//! Adversarial fixtures for [`crate::ntheory_certify`].
//!
//! Every rejection test below is a **forgery**: a certificate for a claim that
//! is *false*, or a certificate that overstates what it establishes, built so
//! that **every guard except the one named passes**. That construction is what
//! mutation testing cannot give you — mutation deletes guards that exist and
//! cannot find a distinction the certificate format fails to record. Each
//! forgery's numbers were verified in Python before any Rust was written.
//!
//! The two headline fixtures:
//!
//! * `forged_primality_of_91_with_an_incomplete_factorization` — a certificate
//!   that **91 is prime** (it is `7 * 13`). Witness `3` has order `6` mod `91`,
//!   so `3^90 = 1` and `3^45 != 1`: the Fermat check and every order check
//!   pass, the single claimed factor `2` is genuinely prime. Only
//!   `prod base^exp = n - 1` (`2 != 90`) rejects it.
//! * `forged_crt_modulus_is_a_common_multiple_but_not_the_least` — over the
//!   **solvable** system `x = 1 (mod 4), x = 3 (mod 6)`, the certificate
//!   `(solution = 9, modulus = 24)` satisfies both congruences and
//!   `0 <= 9 < 24`, and `24` is a common multiple. Only leastness rejects it.

use crate::ntheory;
use crate::ntheory_certify::{
    CompositeCertificate, CrtCertificate, FactorizationCertificate, PrattCertificate,
    certify_composite, certify_crt, certify_factorization, certify_prime,
    check_composite_certificate, check_crt_certificate, check_factorization_certificate,
    check_primality_certificate,
};

/// A valid Pratt certificate for `n`, for use as a subcertificate inside a
/// forgery. Panics if `n` is not certifiably prime — the forgeries below rely
/// on their *other* components being genuine.
fn genuine(n: i128) -> PrattCertificate {
    certify_prime(n).expect("fixture prerequisite: n must be certifiably prime")
}

// ===========================================================================
// Positive controls: the producers work, and the checkers accept them.
// ===========================================================================

#[test]
fn certifies_primes_across_several_magnitudes() {
    for n in [2_i128, 3, 5, 7, 13, 97, 7919, 65537, 1_000_003, 2_147_483_647] {
        let cert = certify_prime(n).unwrap_or_else(|| panic!("no certificate for prime {n}"));
        assert!(
            check_primality_certificate(n, &cert),
            "self-checked certificate for {n} failed re-validation"
        );
    }
}

#[test]
fn declines_to_certify_composites_as_prime() {
    for n in [1_i128, 4, 15, 91, 561, 1105, 2_147_483_646] {
        assert!(
            certify_prime(n).is_none(),
            "produced a primality certificate for the non-prime {n}"
        );
    }
}

#[test]
fn certificate_route_agrees_with_is_prime_over_a_dense_range() {
    let mut certified = 0_u32;
    for n in 2_i128..500 {
        let has_cert = certify_prime(n).is_some();
        assert_eq!(
            has_cert,
            ntheory::is_prime(n),
            "certificate route disagrees with is_prime at {n}"
        );
        if has_cert {
            certified += 1;
        }
    }
    // 95 primes below 500. A vacuous run would certify zero.
    assert_eq!(certified, 95, "expected 95 certified primes below 500");
}

#[test]
fn certifies_composites_and_declines_primes() {
    for n in [4_i128, 15, 91, 561, 1_000_000] {
        let cert = certify_composite(n).unwrap_or_else(|| panic!("no certificate for {n}"));
        assert!(check_composite_certificate(n, &cert));
    }
    for n in [-7_i128, 0, 1, 2, 3, 97, 2_147_483_647] {
        assert!(
            certify_composite(n).is_none(),
            "produced a compositeness certificate for {n}"
        );
    }
}

#[test]
fn certifies_factorizations_including_negatives_and_units() {
    for n in [1_i128, -1, 12, -12, 360, 1024, 2_147_483_647, 999_983 * 2] {
        let cert = certify_factorization(n).unwrap_or_else(|| panic!("no certificate for {n}"));
        assert!(check_factorization_certificate(n, &cert));
        assert_eq!(cert.factors, ntheory::factorize(n));
    }
    assert!(
        certify_factorization(0).is_none(),
        "0 has no finite prime factorization and must not be certifiable"
    );
}

#[test]
fn certifies_crt_in_both_directions() {
    let solvable: &[&[(i128, i128)]] = &[
        &[(2, 3), (3, 5), (2, 7)],
        &[(1, 4), (3, 6)],
        &[],
        &[(5, 1)],
    ];
    for residues in solvable {
        let cert = certify_crt(residues).expect("solvable system must certify");
        assert!(matches!(cert, CrtCertificate::Solution { .. }));
        assert!(check_crt_certificate(residues, &cert));
    }
    let unsolvable: &[&[(i128, i128)]] = &[&[(0, 2), (1, 4)], &[(1, 6), (2, 9), (3, 4)]];
    for residues in unsolvable {
        let cert = certify_crt(residues).expect("unsolvable system must certify a conflict");
        assert!(matches!(cert, CrtCertificate::Inconsistent { .. }));
        assert!(check_crt_certificate(residues, &cert));
    }
}

// ===========================================================================
// Forged primality certificates.
//
// Each is a certificate that a COMPOSITE is prime, or that a genuine prime is
// prime on evidence that does not establish it, built so that only the named
// guard rejects.
// ===========================================================================

/// **G6, completeness.** `91 = 7 * 13`. `ord(3) = 6` mod `91`, so `3^90 = 1`
/// and `3^45 != 1`: the Fermat check passes and the single order check passes,
/// and `2` is genuinely prime, so the recursion passes. Only the requirement
/// that the stated factors multiply to `n - 1` (`2 != 90`) rejects it.
#[test]
fn forged_primality_of_91_with_an_incomplete_factorization() {
    let forged = PrattCertificate {
        witness: 3,
        factors: vec![(2, 1)],
        subcerts: vec![genuine(2)],
    };
    // Every other guard really does pass — assert it rather than assume it.
    assert_eq!(ntheory::mod_pow(3, 90, 91), Some(1), "Fermat check passes");
    assert_ne!(ntheory::mod_pow(3, 45, 91), Some(1), "order check passes");
    assert!(check_primality_certificate(2, &forged.subcerts[0]));
    assert!(!ntheory::is_prime(91), "the subject really is composite");

    assert!(
        !check_primality_certificate(91, &forged),
        "accepted a forged primality certificate for the composite 91"
    );
}

/// **G7, recursion.** `15 = 3 * 5`. `ord(4) = 2` mod `15`, so `4^14 = 1` and
/// `4^1 != 1`. The claimed factorization `[(14, 1)]` multiplies to exactly
/// `14 = n - 1`, so completeness passes, the bases are ascending, the exponent
/// is one, and the witness is in range. Only the requirement that `14` itself
/// be certified prime rejects it.
#[test]
fn forged_primality_of_15_with_a_composite_claimed_factor() {
    let bogus_subcert = PrattCertificate {
        witness: 1,
        factors: vec![(13, 1)],
        subcerts: vec![genuine(13)],
    };
    let forged = PrattCertificate {
        witness: 4,
        factors: vec![(14, 1)],
        subcerts: vec![bogus_subcert],
    };
    assert_eq!(ntheory::mod_pow(4, 14, 15), Some(1), "Fermat check passes");
    assert_ne!(ntheory::mod_pow(4, 1, 15), Some(1), "order check passes");
    assert_eq!(14_i128, 15 - 1, "completeness check passes");
    assert!(!ntheory::is_prime(14), "the claimed factor really is composite");

    assert!(
        !check_primality_certificate(15, &forged),
        "accepted a forged primality certificate for the composite 15"
    );
}

/// **G8, Fermat.** `15 = 3 * 5`, and `14 = 2 * 7` is a complete, correct,
/// ascending factorization of `n - 1` with both bases genuinely prime — so G1
/// through G7 all pass. `ord(2) = 4` mod `15`, which does not divide `14`, so
/// `2^14 = 4 != 1` and only the Fermat check rejects.
///
/// Note that the subject **has** to be composite for this fixture to exist: for
/// a prime `n`, `a^(n-1) = 1` for every witness in range, so the Fermat guard is
/// unreachable there. Verified: `[a^12 mod 13 for a in 1..13]` is all ones.
#[test]
fn forged_primality_rejects_a_witness_failing_fermat() {
    let forged = PrattCertificate {
        witness: 2,
        factors: vec![(2, 1), (7, 1)],
        subcerts: vec![genuine(2), genuine(7)],
    };
    assert_eq!(2 * 7, 15 - 1, "the factorization of n - 1 is complete");
    assert_eq!(ntheory::mod_pow(2, 14, 15), Some(4), "Fermat check fails");
    assert!(!ntheory::is_prime(15), "the subject really is composite");

    assert!(
        !check_primality_certificate(15, &forged),
        "accepted a certificate whose witness fails Fermat"
    );
    // Control: for the prime 13 no witness can fail Fermat, so this guard is
    // reachable only at a composite subject. Asserting it keeps the fixture
    // above from silently becoming vacuous.
    for a in 1..13_i128 {
        assert_eq!(ntheory::mod_pow(a, 12, 13), Some(1));
    }
}

/// **G9, order maximality.** `13` really is prime and the factorization of
/// `12` is complete and correct, but `ord(3) = 3` mod `13`, so `3^6 = 1` and
/// the witness does not have order `12`. The certificate does not establish
/// primality even though the subject is prime — validity of the certificate is
/// not the same question as primality of `n`, and the checker must say so.
#[test]
fn forged_primality_rejects_a_non_primitive_witness_for_a_genuine_prime() {
    let forged = PrattCertificate {
        witness: 3,
        factors: vec![(2, 2), (3, 1)],
        subcerts: vec![genuine(2), genuine(3)],
    };
    assert!(ntheory::is_prime(13), "the subject really is prime");
    assert_eq!(ntheory::mod_pow(3, 12, 13), Some(1), "Fermat check passes");
    assert_eq!(ntheory::mod_pow(3, 6, 13), Some(1), "but the order is not 12");

    assert!(
        !check_primality_certificate(13, &forged),
        "accepted a certificate that does not establish the order"
    );
    // Control: the same subject WITH a primitive root is accepted.
    let honest = PrattCertificate {
        witness: 2,
        factors: vec![(2, 2), (3, 1)],
        subcerts: vec![genuine(2), genuine(3)],
    };
    assert!(check_primality_certificate(13, &honest));
}

/// **G4, canonical ordering.** Same genuine content as the accepted control,
/// bases listed descending.
#[test]
fn forged_primality_rejects_descending_factor_bases() {
    let forged = PrattCertificate {
        witness: 2,
        factors: vec![(3, 1), (2, 2)],
        subcerts: vec![genuine(3), genuine(2)],
    };
    assert_eq!(3 * 2 * 2, 12, "the product identity still holds");
    assert!(!check_primality_certificate(13, &forged));
}

/// **G4, duplicate rejection.** `2 * 2 * 3 = 12`, so completeness passes, and
/// every base is prime — only strictness of the ordering rejects the repeat.
#[test]
fn forged_primality_rejects_a_repeated_factor_base() {
    let forged = PrattCertificate {
        witness: 2,
        factors: vec![(2, 1), (2, 1), (3, 1)],
        subcerts: vec![genuine(2), genuine(2), genuine(3)],
    };
    assert_eq!(2 * 2 * 3, 12, "the product identity still holds");
    assert!(!check_primality_certificate(13, &forged));
}

/// **G5, exponents.** A zero exponent contributes an empty product, so the
/// product identity still holds and every other guard passes; a zero-exponent
/// entry is a factor that is not there.
#[test]
fn forged_primality_rejects_a_zero_exponent_entry() {
    let forged = PrattCertificate {
        witness: 2,
        factors: vec![(2, 2), (3, 1), (5, 0)],
        subcerts: vec![genuine(2), genuine(3), genuine(5)],
    };
    assert!(!check_primality_certificate(13, &forged));
}

/// **G3, arity.** Fewer subcertificates than factors would leave a factor's
/// primality unexamined by `zip`, which stops at the shorter side.
#[test]
fn forged_primality_rejects_a_missing_subcertificate() {
    let forged = PrattCertificate {
        witness: 2,
        factors: vec![(2, 2), (3, 1)],
        subcerts: vec![genuine(2)],
    };
    assert!(!check_primality_certificate(13, &forged));
}

/// **G1, subject range.** Nothing below `2` is prime, whatever is claimed.
#[test]
fn forged_primality_rejects_subjects_below_two() {
    let empty = PrattCertificate {
        witness: 1,
        factors: vec![],
        subcerts: vec![],
    };
    for n in [-7_i128, 0, 1] {
        assert!(
            !check_primality_certificate(n, &empty),
            "accepted a primality certificate for {n}"
        );
    }
    // Control: the same empty-factor shape IS the genuine certificate for 2.
    assert!(check_primality_certificate(2, &empty));
}

/// **G2, witness range.** A witness of `0`, or one at or above `n`, is not a
/// residue that can have order `n - 1`.
#[test]
fn forged_primality_rejects_out_of_range_witnesses() {
    for witness in [0_i128, 13, 15, -2] {
        let forged = PrattCertificate {
            witness,
            factors: vec![(2, 2), (3, 1)],
            subcerts: vec![genuine(2), genuine(3)],
        };
        assert!(
            !check_primality_certificate(13, &forged),
            "accepted witness {witness} for n = 13"
        );
    }
}

/// **G10, depth.** A forged chain `n, n-1, n-2, …` is syntactically consistent
/// at every level — each level's single factor multiplies to exactly that
/// level's `n - 1` — so completeness, ordering and exponents all pass all the
/// way down. Without the depth bound the checker recurses `n` deep before any
/// arithmetic guard fires. This must terminate and reject, not overflow.
#[test]
fn forged_primality_rejects_an_adversarially_deep_chain() {
    // Build bottom-up: level k certifies `k` with the single factor `k - 1`.
    let mut chain = PrattCertificate {
        witness: 1,
        factors: vec![],
        subcerts: vec![],
    };
    let top = 400_i128;
    for n in 3..=top {
        chain = PrattCertificate {
            witness: 1,
            factors: vec![(n - 1, 1)],
            subcerts: vec![chain],
        };
    }
    assert!(
        !check_primality_certificate(top, &chain),
        "accepted a 400-deep forged certificate chain"
    );
}

// ===========================================================================
// Forged compositeness certificates.
// ===========================================================================

#[test]
fn forged_compositeness_rejects_the_trivial_divisors() {
    // 1 divides everything; n divides itself. Neither shows compositeness.
    assert!(!check_composite_certificate(91, &CompositeCertificate { divisor: 1 }));
    assert!(!check_composite_certificate(91, &CompositeCertificate { divisor: 91 }));
    // Control: the honest divisor is accepted.
    assert!(check_composite_certificate(91, &CompositeCertificate { divisor: 7 }));
}

#[test]
fn forged_compositeness_rejects_a_non_divisor_and_a_prime_subject() {
    // In range but does not divide.
    assert!(!check_composite_certificate(91, &CompositeCertificate { divisor: 5 }));
    // A prime subject admits no in-range divisor at all.
    for divisor in 2..97_i128 {
        assert!(
            !check_composite_certificate(97, &CompositeCertificate { divisor }),
            "accepted divisor {divisor} for the prime 97"
        );
    }
}

// ===========================================================================
// Forged factorization certificates.
// ===========================================================================

/// **F2.** `4 * 2 * 9 * 5 = 360` and every base is prime — only the strictness
/// of the ordering rejects `2` appearing twice, which is what makes the
/// certificate about *the* factorization rather than *a* product of primes.
#[test]
fn forged_factorization_rejects_a_repeated_base() {
    let forged = FactorizationCertificate {
        factors: vec![(2, 2), (2, 1), (3, 2), (5, 1)],
        primality: vec![genuine(2), genuine(2), genuine(3), genuine(5)],
    };
    assert_eq!(4 * 2 * 9 * 5, 360, "the product identity still holds");
    assert!(!check_factorization_certificate(360, &forged));
}

/// **F5.** `9 * 5 = 45` and the ordering and exponents are fine — only the
/// per-factor primality rejects `9`. Verified: no witness certifies `9`, since
/// `ord(a) | gcd(8, lambda(9)) = 2` divides `4` for every unit `a`.
#[test]
fn forged_factorization_rejects_a_composite_factor() {
    let bogus = PrattCertificate {
        witness: 2,
        factors: vec![(2, 3)],
        subcerts: vec![genuine(2)],
    };
    let forged = FactorizationCertificate {
        factors: vec![(5, 1), (9, 1)],
        primality: vec![genuine(5), bogus],
    };
    assert_eq!(5 * 9, 45, "the product identity still holds");
    assert!(!ntheory::is_prime(9));
    assert!(!check_factorization_certificate(45, &forged));
    // Control: the honest factorization of 45 is accepted.
    assert!(check_factorization_certificate(
        45,
        &certify_factorization(45).unwrap()
    ));
}

/// **F3.** A zero exponent contributes nothing to the product, so the identity
/// still holds while the certificate names a prime that does not divide `n`.
#[test]
fn forged_factorization_rejects_a_zero_exponent() {
    let forged = FactorizationCertificate {
        factors: vec![(2, 3), (3, 2), (5, 1), (7, 0)],
        primality: vec![genuine(2), genuine(3), genuine(5), genuine(7)],
    };
    assert!(!check_factorization_certificate(360, &forged));
}

/// **F4.** Dropping a factor entirely.
#[test]
fn forged_factorization_rejects_a_product_mismatch() {
    let forged = FactorizationCertificate {
        factors: vec![(2, 3), (3, 2)],
        primality: vec![genuine(2), genuine(3)],
    };
    assert!(!check_factorization_certificate(360, &forged));
    // ...and the empty certificate does not certify anything but a unit.
    let empty = FactorizationCertificate {
        factors: vec![],
        primality: vec![],
    };
    assert!(!check_factorization_certificate(0, &empty));
    assert!(!check_factorization_certificate(360, &empty));
    assert!(check_factorization_certificate(1, &empty));
    assert!(check_factorization_certificate(-1, &empty));
}

/// **F1.** A short `primality` list leaves later factors unexamined.
#[test]
fn forged_factorization_rejects_a_missing_primality_certificate() {
    let forged = FactorizationCertificate {
        factors: vec![(2, 3), (3, 2), (5, 1)],
        primality: vec![genuine(2), genuine(3)],
    };
    assert!(!check_factorization_certificate(360, &forged));
}

// ===========================================================================
// Forged CRT certificates.
// ===========================================================================

/// **R4, leastness.** The headline fixture, over a **solvable** system.
/// `x = 1 (mod 4), x = 3 (mod 6)` really has solution `9 mod 12`. The forged
/// certificate `(9, 24)` satisfies both congruences, is in canonical range for
/// its stated modulus, and `24` is a genuine common multiple of `4` and `6` —
/// every guard passes except the one requiring the *least* common multiple. A
/// certificate that recorded only "a common multiple" could not express the
/// distinction at all, and would accept it.
#[test]
fn forged_crt_modulus_is_a_common_multiple_but_not_the_least() {
    let residues = [(1_i128, 4_i128), (3, 6)];
    let forged = CrtCertificate::Solution {
        solution: 9,
        modulus: 24,
    };
    // Every other guard passes — asserted, not assumed.
    assert_eq!((9 - 1) % 4, 0, "first congruence holds");
    assert_eq!((9 - 3) % 6, 0, "second congruence holds");
    assert!((0..24).contains(&9), "canonical range holds");
    assert_eq!(24 % 4, 0, "24 is a common multiple");
    assert_eq!(24 % 6, 0, "24 is a common multiple");
    assert_eq!(ntheory::lcm(4, 6), Some(12), "but the least one is 12");

    assert!(
        !check_crt_certificate(&residues, &forged),
        "accepted a modulus that is a common multiple but not the least"
    );
    // Control: the honest certificate is accepted.
    assert!(check_crt_certificate(
        &residues,
        &CrtCertificate::Solution {
            solution: 9,
            modulus: 12
        }
    ));
}

/// **R2, canonical representative.** `21 = 9 (mod 12)` satisfies both
/// congruences and the modulus is the true least common multiple — only the
/// requirement that the solution be the representative in `0..modulus` rejects
/// it. Without it the "unique residue" the routine promises is not pinned down.
#[test]
fn forged_crt_rejects_a_non_canonical_solution() {
    let residues = [(1_i128, 4_i128), (3, 6)];
    for solution in [21_i128, -3, 12] {
        assert!(
            !check_crt_certificate(
                &residues,
                &CrtCertificate::Solution {
                    solution,
                    modulus: 12
                }
            ),
            "accepted non-canonical solution {solution}"
        );
    }
}

/// **R3, the congruences.** A value in canonical range under the correct least
/// common multiple that simply is not a solution.
#[test]
fn forged_crt_rejects_a_value_that_is_not_a_solution() {
    let residues = [(1_i128, 4_i128), (3, 6)];
    assert!(!check_crt_certificate(
        &residues,
        &CrtCertificate::Solution {
            solution: 3,
            modulus: 12
        }
    ));
}

/// **R1, moduli.** A non-positive modulus makes the congruence meaningless in
/// either direction, so both variants must refuse.
#[test]
fn forged_crt_rejects_non_positive_moduli() {
    let residues = [(1_i128, 4_i128), (3, 0)];
    assert!(!check_crt_certificate(
        &residues,
        &CrtCertificate::Solution {
            solution: 1,
            modulus: 4
        }
    ));
    assert!(!check_crt_certificate(
        &residues,
        &CrtCertificate::Inconsistent { left: 0, right: 1 }
    ));
    assert!(certify_crt(&residues).is_none());
}

/// **R6, the conflict is real.** Claiming inconsistency over a **solvable**
/// system: `1 = 3 (mod gcd(4, 6) = 2)`, so the named pair does not conflict.
/// This is the cross-direction forgery — the checker must not let an
/// unsolvability claim ride on a system that is solvable.
#[test]
fn forged_crt_rejects_a_fabricated_conflict_over_a_solvable_system() {
    let residues = [(1_i128, 4_i128), (3, 6)];
    assert_eq!(ntheory::gcd(4, 6), 2);
    assert_eq!((1 - 3_i128).rem_euclid(2), 0, "the pair does NOT conflict");
    assert!(certify_crt(&residues).is_some(), "the system is solvable");

    assert!(
        !check_crt_certificate(&residues, &CrtCertificate::Inconsistent { left: 0, right: 1 }),
        "accepted a fabricated inconsistency over a solvable system"
    );
}

/// **R5, indices.** Out-of-range indices must refuse rather than panic.
#[test]
fn forged_crt_rejects_out_of_range_conflict_indices() {
    let residues = [(0_i128, 2_i128), (1, 4)];
    // Control: the genuine conflict is accepted.
    assert!(check_crt_certificate(
        &residues,
        &CrtCertificate::Inconsistent { left: 0, right: 1 }
    ));
    for (left, right) in [(0_usize, 9_usize), (9, 0), (7, 8)] {
        assert!(
            !check_crt_certificate(&residues, &CrtCertificate::Inconsistent { left, right }),
            "accepted indices ({left}, {right})"
        );
    }
    // A degenerate self-pair can never conflict: `a - a = 0`.
    assert!(!check_crt_certificate(
        &residues,
        &CrtCertificate::Inconsistent { left: 0, right: 0 }
    ));
}

// ===========================================================================
// The checker's independent modular arithmetic.
//
// Not a soundness guard: a divergence from `ntheory::mod_pow` means one of the
// two is wrong, and this locates it rather than letting a shared defect hide
// behind agreement. The independence is the point — a bug in a *shared*
// `mod_pow` would fool producer and checker identically.
// ===========================================================================

#[test]
fn independent_modular_exponentiation_agrees_with_ntheory() {
    let mut compared = 0_u32;
    for modulus in [7_i128, 91, 1_000_003, 4_294_967_291, 170_141_183_460_469_231_731_687_303_715_884_105_727]
    {
        for base in [2_i128, 3, 10, 12_345, 999_999_937] {
            for exponent in [0_u128, 1, 5, 90, 1_000_000, u64::MAX as u128] {
                let theirs = ntheory::mod_pow(base, exponent, modulus).expect("mod_pow defined");
                let ours = crate::ntheory_certify::pow_mod_for_tests(
                    u128::try_from(base).unwrap(),
                    exponent,
                    u128::try_from(modulus).unwrap(),
                );
                assert_eq!(
                    u128::try_from(theirs).unwrap(),
                    ours,
                    "mod_pow({base}, {exponent}, {modulus}) disagrees"
                );
                compared += 1;
            }
        }
    }
    assert_eq!(compared, 150, "expected 150 comparisons, not a vacuous sweep");
}

/// The `mul_mod` slow path only runs for a modulus above `u64::MAX`; the fast
/// path would silently overflow there. This pins that the slow path is
/// exercised at all — a positive control for the sweep above.
#[test]
fn modular_arithmetic_slow_path_is_exercised_above_u64_max() {
    let modulus = (1_u128 << 100) + 277; // exceeds u64::MAX, so the slow path runs
    assert!(modulus > u64::MAX as u128);
    // (2^100 + 277) is odd, so 2 is a unit; check a square-and-multiply identity
    // that the fast path could not compute without overflow.
    let a = 3_u128;
    let squared = crate::ntheory_certify::pow_mod_for_tests(a, 2, modulus);
    assert_eq!(squared, 9);
    let big = crate::ntheory_certify::pow_mod_for_tests(a, 200, modulus);
    let half = crate::ntheory_certify::pow_mod_for_tests(a, 100, modulus);
    let recombined = crate::ntheory_certify::pow_mod_for_tests(half, 2, modulus);
    assert_eq!(big, recombined, "a^200 must equal (a^100)^2 mod m");
    assert_ne!(big, 0);
}

/// The certificate route works on a prime beyond `u64::MAX`, which is where the
/// slow modular path actually carries a real certificate rather than a synthetic
/// identity. `2^89 - 1` is a Mersenne prime; `2^89 - 2 = 2 * (2^88 - 1)`
/// factors into small enough pieces for the producer to recurse.
#[test]
fn certifies_a_prime_beyond_u64_max() {
    let mersenne_89: i128 = (1_i128 << 89) - 1;
    assert!(mersenne_89 > u64::MAX as i128);
    let cert = certify_prime(mersenne_89).expect("2^89 - 1 must certify");
    assert!(check_primality_certificate(mersenne_89, &cert));
    // Non-vacuity: the certificate really does carry a factorization tree.
    assert!(!cert.factors.is_empty());
    // And the checker rejects the neighbouring composite with the same shape.
    assert!(!check_primality_certificate(mersenne_89 - 2, &cert));
}
