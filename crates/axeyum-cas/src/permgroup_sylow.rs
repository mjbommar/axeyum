//! Sylow subgroups, their conjugate count, subgroup normality, normal
//! closure, and quotient order -- split out of `permgroup.rs` to keep that
//! file under its line-count budget. A child module of [`crate::permgroup`]
//! (declared there via `#[path = "permgroup_sylow.rs"] mod permgroup_sylow;`,
//! never in `lib.rs`), so every private item it needs from the parent
//! (`image_key`, `enumerate_group`, `sift_with_trace`, `SiftOutcome`,
//! `p_adic_valuation`, `is_power_of`, and `PermutationGroup`'s private
//! fields) is visible here by ordinary Rust privacy (private = visible in
//! the defining module and its descendants) without being made `pub`.
//!
//! See the parent module's doc for the shared certificate philosophy: every
//! public entry point returns a certificate whose `verify` re-derives the
//! claim independently, sharing no bookkeeping with the producer.

use super::{
    ENUMERATION_BOUND, MembershipCertificate, OrderCertificate, PermgroupError, Permutation,
    PermutationGroup, SiftOutcome, enumerate_group, image_key, is_power_of, p_adic_valuation,
    sift_with_trace,
};
use std::collections::BTreeSet;

// ---------------------------------------------------------------------------
// SylowCertificate: existence and order of a Sylow p-subgroup
// ---------------------------------------------------------------------------

/// A checkable certificate that `sylow_order` is a Sylow `p`-subgroup of `G`:
/// its own [`OrderCertificate`] verifies (so it is a genuine, closed
/// subgroup), every one of its generators is a member of `G` (re-derived by
/// sifting through `group_order`'s own stabilizer chain), and its order is
/// exactly the full `p`-part of `|G|` (recomputed from `|G|`'s factorization,
/// never trusted from the producer).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SylowCertificate {
    /// The order certificate for `G`.
    pub group_order: OrderCertificate,
    /// The prime `p`.
    pub prime: u128,
    /// The claimed exponent: `|sylow_order| == prime^exponent`.
    pub exponent: u32,
    /// The order certificate for the claimed Sylow `p`-subgroup.
    pub sylow_order: OrderCertificate,
}

/// Why a [`SylowCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SylowFailure {
    /// `group_order` itself does not verify.
    GroupCertificateInvalid,
    /// `sylow_order` itself does not verify.
    SylowCertificateInvalid,
    /// The two certificates act on different numbers of points.
    DegreeMismatch,
    /// `prime` does not divide `group_order.claimed_order` at all.
    PrimeDoesNotDivideOrder,
    /// The independently recomputed exponent of `prime` in `|G|` does not
    /// match `exponent`.
    ExponentMismatch {
        /// The recomputed exponent.
        expected: u32,
        /// The claimed exponent.
        claimed: u32,
    },
    /// `prime.checked_pow(exponent)` overflows `u128`.
    Overflow,
    /// `sylow_order.claimed_order != prime^exponent`.
    OrderIsNotFullPPart {
        /// The recomputed `prime^exponent`.
        computed: u128,
        /// `sylow_order`'s claimed order.
        claimed: u128,
    },
    /// Some generator of the claimed Sylow subgroup does not sift to the
    /// identity through `group_order`'s stabilizer chain -- it is not a
    /// member of `G`.
    GeneratorNotInGroup,
}

impl SylowCertificate {
    /// Independently re-derives every claim this certificate makes,
    /// returning the first guard that fails.
    ///
    /// # Errors
    ///
    /// Returns the first [`SylowFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), SylowFailure> {
        use SylowFailure as F;
        self.group_order
            .verify()
            .map_err(|_| F::GroupCertificateInvalid)?;
        self.sylow_order
            .verify()
            .map_err(|_| F::SylowCertificateInvalid)?;
        if self.group_order.degree != self.sylow_order.degree {
            return Err(F::DegreeMismatch);
        }
        let expected_exponent = p_adic_valuation(self.group_order.claimed_order, self.prime);
        if expected_exponent != self.exponent {
            return Err(F::ExponentMismatch {
                expected: expected_exponent,
                claimed: self.exponent,
            });
        }
        if self.exponent == 0 {
            return Err(F::PrimeDoesNotDivideOrder);
        }
        let expected_order = self.prime.checked_pow(self.exponent).ok_or(F::Overflow)?;
        if self.sylow_order.claimed_order != expected_order {
            return Err(F::OrderIsNotFullPPart {
                computed: expected_order,
                claimed: self.sylow_order.claimed_order,
            });
        }
        let degree = self.group_order.degree;
        for g in &self.sylow_order.original_generators {
            if g.len() != degree {
                return Err(F::GeneratorNotInGroup);
            }
            match sift_with_trace(
                g,
                &self.group_order.base,
                &self.group_order.transversals,
                &self.group_order.strong_generators,
                degree,
            ) {
                SiftOutcome::Success { .. } => {}
                SiftOutcome::Failure { .. } => return Err(F::GeneratorNotInGroup),
            }
        }
        Ok(())
    }
}

impl PermutationGroup {
    /// A Sylow `p`-subgroup of `G`, for `|G| <=` [`ENUMERATION_BOUND`].
    /// Declined with [`PermgroupError::PrimeDoesNotDivideOrder`] if `p` does
    /// not divide `|G|`.
    ///
    /// Built by the "closure of `p`-elements" method: enumerate `G`, collect
    /// every non-identity element whose order is a power of `p` (a
    /// `p`-element), and greedily grow a subgroup generated from these,
    /// keeping only additions that keep the running subgroup a `p`-group
    /// (order a power of `p`). This always reaches the full `p`-part: if the
    /// running subgroup `H` is a proper subgroup of some Sylow `p`-subgroup
    /// `P` (which it always is, until `|H| == p^k`, since every `p`-subgroup
    /// lies inside a Sylow `p`-subgroup), then because `H` is a proper
    /// subgroup of the `p`-group `P`, `H` is properly contained in its own
    /// normalizer inside `P` -- so some element `y ∈ P \ H` normalizes `H`,
    /// and `⟨H, y⟩` is again a `p`-group (a subgroup of `P`) strictly larger
    /// than `H`. That `y` is itself a `p`-element of `G`, so it appears in
    /// the search list; trying every `p`-element at each step is guaranteed
    /// to find *some* generator that makes progress.
    ///
    /// # Errors
    ///
    /// [`PermgroupError::TooLarge`] if `|G|` exceeds [`ENUMERATION_BOUND`];
    /// [`PermgroupError::PrimeDoesNotDivideOrder`] if `p` does not divide
    /// `|G|`.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn sylow_subgroup(
        &self,
        p: u128,
    ) -> Result<(PermutationGroup, SylowCertificate), PermgroupError> {
        if self.order_certificate.claimed_order > ENUMERATION_BOUND {
            return Err(PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: self.order_certificate.claimed_order,
            });
        }
        let exponent = p_adic_valuation(self.order_certificate.claimed_order, p);
        if exponent == 0 {
            return Err(PermgroupError::PrimeDoesNotDivideOrder);
        }
        let target = p
            .checked_pow(exponent)
            .expect("p^exponent divides an order already bounded by ENUMERATION_BOUND");
        let elems = enumerate_group(&self.generators, self.degree, ENUMERATION_BOUND).ok_or(
            PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: self.order_certificate.claimed_order,
            },
        )?;
        let mut p_elements: Vec<Permutation> = elems
            .iter()
            .filter(|e| {
                let ord = e.order().expect("finite permutation has a finite order");
                ord > 1 && is_power_of(ord, p)
            })
            .cloned()
            .collect();
        p_elements.sort_by_key(|e| image_key(e, self.degree));

        let mut current_gens: Vec<Permutation> = Vec::new();
        let mut current_group =
            PermutationGroup::from_generators(current_gens.clone(), self.degree)
                .expect("the empty generator list always builds the trivial group");
        let mut current_order = current_group.order();
        while current_order < target {
            let mut progressed = false;
            for x in &p_elements {
                if let MembershipCertificate::Member { .. } = current_group.contains(x) {
                    continue;
                }
                let mut candidate_gens = current_gens.clone();
                candidate_gens.push(x.clone());
                let candidate_group =
                    PermutationGroup::from_generators(candidate_gens.clone(), self.degree)
                        .expect("degree matches by construction");
                let candidate_order = candidate_group.order();
                if candidate_order > current_order && is_power_of(candidate_order, p) {
                    current_gens = candidate_gens;
                    current_group = candidate_group;
                    current_order = candidate_order;
                    progressed = true;
                    break;
                }
            }
            if !progressed {
                // Never observed: the normalizer-growth argument above
                // guarantees a next p-element always exists while
                // current_order < target. Kept as a distinct, checkable
                // refusal rather than an infinite loop or a silent wrong
                // answer, in case that argument's precondition (p_elements
                // drawn from the WHOLE group) is ever violated by a future
                // edit.
                return Err(PermgroupError::SylowConstructionFailed);
            }
        }
        let sylow_order = current_group.order_certificate().clone();
        let cert = SylowCertificate {
            group_order: self.order_certificate.clone(),
            prime: p,
            exponent,
            sylow_order,
        };
        Ok((current_group, cert))
    }
}

// ---------------------------------------------------------------------------
// SylowCountCertificate: n_p, the number of Sylow p-subgroups
// ---------------------------------------------------------------------------

/// A checkable certificate for `n_p`, the number of Sylow `p`-subgroups of
/// `G`, for `|G| <=` [`ENUMERATION_BOUND`]: counts the distinct conjugates
/// `gPg⁻¹` of one Sylow `p`-subgroup `P` under every `g ∈ G`, then checks the
/// two Sylow-theorem congruences (`n_p ≡ 1 (mod p)` and `n_p | |G| / p^k`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SylowCountCertificate {
    /// The order certificate for `G`.
    pub group_order: OrderCertificate,
    /// The order certificate for one Sylow `p`-subgroup `P`.
    pub sylow_order: OrderCertificate,
    /// The prime `p`.
    pub prime: u128,
    /// The claimed number of Sylow `p`-subgroups.
    pub n_p: u128,
}

/// Why a [`SylowCountCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SylowCountFailure {
    /// `group_order` itself does not verify.
    GroupCertificateInvalid,
    /// `sylow_order` itself does not verify.
    SylowCertificateInvalid,
    /// The two certificates act on different numbers of points.
    DegreeMismatch,
    /// `group_order.claimed_order` exceeds [`ENUMERATION_BOUND`].
    TooLargeToVerify,
    /// `prime.checked_pow(exponent)` overflows `u128`.
    Overflow,
    /// `n_p % prime != 1`.
    NotCongruentToOneModPrime,
    /// `n_p` does not divide `|G| / p^k`.
    DoesNotDivideCofactor,
    /// The independently recomputed conjugate count does not equal `n_p`.
    CountMismatch {
        /// The recomputed count.
        computed: u128,
        /// The claimed count.
        claimed: u128,
    },
}

impl SylowCountCertificate {
    /// Independently re-derives every claim this certificate makes,
    /// returning the first guard that fails. The two Sylow-theorem
    /// congruences are checked *before* the expensive full recomputation, so
    /// a forged count violating either is refused without ever enumerating
    /// `G`.
    ///
    /// # Errors
    ///
    /// Returns the first [`SylowCountFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), SylowCountFailure> {
        use SylowCountFailure as F;
        self.group_order
            .verify()
            .map_err(|_| F::GroupCertificateInvalid)?;
        self.sylow_order
            .verify()
            .map_err(|_| F::SylowCertificateInvalid)?;
        if self.group_order.degree != self.sylow_order.degree {
            return Err(F::DegreeMismatch);
        }
        if self.n_p % self.prime != 1 {
            return Err(F::NotCongruentToOneModPrime);
        }
        let exponent = p_adic_valuation(self.group_order.claimed_order, self.prime);
        let p_power = self.prime.checked_pow(exponent).ok_or(F::Overflow)?;
        let cofactor = self.group_order.claimed_order / p_power;
        if !cofactor.is_multiple_of(self.n_p) {
            return Err(F::DoesNotDivideCofactor);
        }
        if self.group_order.claimed_order > ENUMERATION_BOUND {
            return Err(F::TooLargeToVerify);
        }
        let degree = self.group_order.degree;
        let g_elems = enumerate_group(
            &self.group_order.original_generators,
            degree,
            ENUMERATION_BOUND,
        )
        .ok_or(F::TooLargeToVerify)?;
        let p_elems = enumerate_group(
            &self.sylow_order.original_generators,
            degree,
            ENUMERATION_BOUND,
        )
        .ok_or(F::TooLargeToVerify)?;
        let mut distinct: BTreeSet<Vec<Vec<usize>>> = BTreeSet::new();
        for g in &g_elems {
            let g_inv = g.inverse();
            let mut conj_keys: Vec<Vec<usize>> = p_elems
                .iter()
                .map(|x| {
                    let conj = g
                        .compose(x)
                        .expect("same degree")
                        .compose(&g_inv)
                        .expect("same degree");
                    image_key(&conj, degree)
                })
                .collect();
            conj_keys.sort();
            distinct.insert(conj_keys);
        }
        let computed = u128::try_from(distinct.len()).unwrap_or(u128::MAX);
        if computed != self.n_p {
            return Err(F::CountMismatch {
                computed,
                claimed: self.n_p,
            });
        }
        Ok(())
    }
}

impl PermutationGroup {
    /// `n_p`, the number of Sylow `p`-subgroups of `G` conjugate to `sylow`,
    /// for `|G| <=` [`ENUMERATION_BOUND`]: computed as the number of distinct
    /// conjugates of `sylow` under every element of `G`. Declines above the
    /// bound.
    ///
    /// # Errors
    ///
    /// [`PermgroupError::DegreeMismatch`] if `sylow` acts on a different
    /// number of points; [`PermgroupError::TooLarge`] if `|G|` exceeds
    /// [`ENUMERATION_BOUND`].
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn sylow_count(
        &self,
        sylow: &PermutationGroup,
        prime: u128,
    ) -> Result<SylowCountCertificate, PermgroupError> {
        if sylow.degree != self.degree {
            return Err(PermgroupError::DegreeMismatch);
        }
        if self.order_certificate.claimed_order > ENUMERATION_BOUND {
            return Err(PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: self.order_certificate.claimed_order,
            });
        }
        let g_elems = enumerate_group(&self.generators, self.degree, ENUMERATION_BOUND).ok_or(
            PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: self.order_certificate.claimed_order,
            },
        )?;
        let p_elems = enumerate_group(&sylow.generators, self.degree, ENUMERATION_BOUND).ok_or(
            PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: sylow.order_certificate.claimed_order,
            },
        )?;
        let mut distinct: BTreeSet<Vec<Vec<usize>>> = BTreeSet::new();
        for g in &g_elems {
            let g_inv = g.inverse();
            let mut conj_keys: Vec<Vec<usize>> = p_elems
                .iter()
                .map(|x| {
                    let conj = g
                        .compose(x)
                        .expect("same degree")
                        .compose(&g_inv)
                        .expect("same degree");
                    image_key(&conj, self.degree)
                })
                .collect();
            conj_keys.sort();
            distinct.insert(conj_keys);
        }
        let n_p = u128::try_from(distinct.len()).unwrap_or(u128::MAX);
        Ok(SylowCountCertificate {
            group_order: self.order_certificate.clone(),
            sylow_order: sylow.order_certificate.clone(),
            prime,
            n_p,
        })
    }
}
// ---------------------------------------------------------------------------
// NormalityCertificate, NormalClosureCertificate, QuotientOrderCertificate
// ---------------------------------------------------------------------------

/// A checkable certificate for whether `H <= G` is normal: either a claim
/// that every conjugate of every element of `H` by every element of `G`
/// stays in `H`, or a witnessing pair `(g, h)` with `g h g⁻¹ ∉ H`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NormalityCertificate {
    /// `H` is normal in `G`.
    Normal {
        /// The order certificate for `G`.
        group_order: OrderCertificate,
        /// The order certificate for `H`.
        subgroup_order: OrderCertificate,
    },
    /// `H` is not normal in `G`; conjugating `subgroup_element ∈ H` by
    /// `conjugating_element ∈ G` leaves `H`.
    NotNormal {
        /// The order certificate for `G`.
        group_order: OrderCertificate,
        /// The order certificate for `H`.
        subgroup_order: OrderCertificate,
        /// The witnessing element of `G`.
        conjugating_element: Permutation,
        /// The witnessing element of `H`.
        subgroup_element: Permutation,
    },
}

/// Why a [`NormalityCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NormalityFailure {
    /// `group_order` itself does not verify.
    GroupCertificateInvalid,
    /// `subgroup_order` itself does not verify.
    SubgroupCertificateInvalid,
    /// The two certificates act on different numbers of points.
    DegreeMismatch,
    /// `group_order.claimed_order` exceeds [`ENUMERATION_BOUND`].
    TooLargeToVerify,
    /// Some generator of `H` is not a member of `G`.
    SubgroupNotContainedInGroup,
    /// `Normal` was claimed, but some conjugate leaves `H`.
    NotActuallyNormal,
    /// The `NotNormal` `conjugating_element` is not a member of `G`.
    ConjugatingElementNotInGroup,
    /// The `NotNormal` `subgroup_element` is not a member of `H`.
    SubgroupElementNotInSubgroup,
    /// The `NotNormal` witness's conjugate is (independently recomputed)
    /// actually in `H` -- the claimed non-normality is not established.
    WitnessActuallyNormal,
}

/// Shared preconditions for both [`NormalityCertificate`] variants: both
/// order certificates verify, they act on the same degree, and every
/// generator of `subgroup_order` is genuinely a member of `group_order`
/// (re-derived by sifting -- never trusted from the producer). Returns the
/// shared degree on success.
fn verify_normality_preconditions(
    group_order: &OrderCertificate,
    subgroup_order: &OrderCertificate,
) -> Result<usize, NormalityFailure> {
    use NormalityFailure as F;
    group_order
        .verify()
        .map_err(|_| F::GroupCertificateInvalid)?;
    subgroup_order
        .verify()
        .map_err(|_| F::SubgroupCertificateInvalid)?;
    if group_order.degree != subgroup_order.degree {
        return Err(F::DegreeMismatch);
    }
    let degree = group_order.degree;
    for h in &subgroup_order.original_generators {
        if let SiftOutcome::Failure { .. } = sift_with_trace(
            h,
            &group_order.base,
            &group_order.transversals,
            &group_order.strong_generators,
            degree,
        ) {
            return Err(F::SubgroupNotContainedInGroup);
        }
    }
    Ok(degree)
}

impl NormalityCertificate {
    /// Independently re-derives this certificate's claim, returning the
    /// first guard that fails.
    ///
    /// # Errors
    ///
    /// Returns the first [`NormalityFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), NormalityFailure> {
        use NormalityFailure as F;
        match self {
            NormalityCertificate::Normal {
                group_order,
                subgroup_order,
            } => {
                let degree = verify_normality_preconditions(group_order, subgroup_order)?;
                if group_order.claimed_order > ENUMERATION_BOUND {
                    return Err(F::TooLargeToVerify);
                }
                let g_elems =
                    enumerate_group(&group_order.original_generators, degree, ENUMERATION_BOUND)
                        .ok_or(F::TooLargeToVerify)?;
                let h_elems = enumerate_group(
                    &subgroup_order.original_generators,
                    degree,
                    ENUMERATION_BOUND,
                )
                .ok_or(F::TooLargeToVerify)?;
                let h_keys: BTreeSet<Vec<usize>> =
                    h_elems.iter().map(|p| image_key(p, degree)).collect();
                for g in &g_elems {
                    let g_inv = g.inverse();
                    for h in &h_elems {
                        let conj = g
                            .compose(h)
                            .expect("same degree")
                            .compose(&g_inv)
                            .expect("same degree");
                        if !h_keys.contains(&image_key(&conj, degree)) {
                            return Err(F::NotActuallyNormal);
                        }
                    }
                }
                Ok(())
            }
            NormalityCertificate::NotNormal {
                group_order,
                subgroup_order,
                conjugating_element,
                subgroup_element,
            } => {
                let degree = verify_normality_preconditions(group_order, subgroup_order)?;
                if conjugating_element.len() != degree || subgroup_element.len() != degree {
                    return Err(F::ConjugatingElementNotInGroup);
                }
                if let SiftOutcome::Failure { .. } = sift_with_trace(
                    conjugating_element,
                    &group_order.base,
                    &group_order.transversals,
                    &group_order.strong_generators,
                    degree,
                ) {
                    return Err(F::ConjugatingElementNotInGroup);
                }
                if let SiftOutcome::Failure { .. } = sift_with_trace(
                    subgroup_element,
                    &subgroup_order.base,
                    &subgroup_order.transversals,
                    &subgroup_order.strong_generators,
                    degree,
                ) {
                    return Err(F::SubgroupElementNotInSubgroup);
                }
                let conj = conjugating_element
                    .compose(subgroup_element)
                    .expect("same degree")
                    .compose(&conjugating_element.inverse())
                    .expect("same degree");
                if subgroup_order.claimed_order > ENUMERATION_BOUND {
                    return Err(F::TooLargeToVerify);
                }
                let h_elems = enumerate_group(
                    &subgroup_order.original_generators,
                    degree,
                    ENUMERATION_BOUND,
                )
                .ok_or(F::TooLargeToVerify)?;
                let conj_key = image_key(&conj, degree);
                let in_h = h_elems.iter().any(|h| image_key(h, degree) == conj_key);
                if in_h {
                    return Err(F::WitnessActuallyNormal);
                }
                Ok(())
            }
        }
    }
}

impl PermutationGroup {
    /// Whether `subgroup` is normal in `G`, for `|G| <=`
    /// [`ENUMERATION_BOUND`]: every conjugate of every element of `subgroup`
    /// by every element of `G`, checked exhaustively.
    ///
    /// # Errors
    ///
    /// [`PermgroupError::DegreeMismatch`] if `subgroup` acts on a different
    /// number of points; [`PermgroupError::SubgroupNotContainedInGroup`] if
    /// some generator of `subgroup` is not a member of `G`;
    /// [`PermgroupError::TooLarge`] if `|G|` exceeds [`ENUMERATION_BOUND`].
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn is_normal(
        &self,
        subgroup: &PermutationGroup,
    ) -> Result<NormalityCertificate, PermgroupError> {
        if subgroup.degree != self.degree {
            return Err(PermgroupError::DegreeMismatch);
        }
        for h in &subgroup.generators {
            if let MembershipCertificate::NonMember { .. } = self.contains(h) {
                return Err(PermgroupError::SubgroupNotContainedInGroup);
            }
        }
        if self.order_certificate.claimed_order > ENUMERATION_BOUND {
            return Err(PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: self.order_certificate.claimed_order,
            });
        }
        let g_elems = enumerate_group(&self.generators, self.degree, ENUMERATION_BOUND).ok_or(
            PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: self.order_certificate.claimed_order,
            },
        )?;
        let h_elems = enumerate_group(&subgroup.generators, self.degree, ENUMERATION_BOUND).ok_or(
            PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: subgroup.order_certificate.claimed_order,
            },
        )?;
        let h_keys: BTreeSet<Vec<usize>> =
            h_elems.iter().map(|p| image_key(p, self.degree)).collect();
        for g in &g_elems {
            let g_inv = g.inverse();
            for h in &h_elems {
                let conj = g
                    .compose(h)
                    .expect("same degree")
                    .compose(&g_inv)
                    .expect("same degree");
                if !h_keys.contains(&image_key(&conj, self.degree)) {
                    return Ok(NormalityCertificate::NotNormal {
                        group_order: self.order_certificate.clone(),
                        subgroup_order: subgroup.order_certificate.clone(),
                        conjugating_element: g.clone(),
                        subgroup_element: h.clone(),
                    });
                }
            }
        }
        Ok(NormalityCertificate::Normal {
            group_order: self.order_certificate.clone(),
            subgroup_order: subgroup.order_certificate.clone(),
        })
    }
}

/// A checkable certificate for the normal closure of `H` in `G`: the
/// smallest normal subgroup of `G` containing `H`, i.e. the subgroup
/// generated by `{ g h g⁻¹ : g ∈ G, h ∈ H }`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NormalClosureCertificate {
    /// The order certificate for `G`.
    pub group_order: OrderCertificate,
    /// The order certificate for `H`.
    pub subgroup_order: OrderCertificate,
    /// The order certificate for the normal closure.
    pub closure_order: OrderCertificate,
}

/// Why a [`NormalClosureCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NormalClosureFailure {
    /// `group_order` itself does not verify.
    GroupCertificateInvalid,
    /// `subgroup_order` itself does not verify.
    SubgroupCertificateInvalid,
    /// `closure_order` itself does not verify.
    ClosureCertificateInvalid,
    /// The three certificates do not all act on the same number of points.
    DegreeMismatch,
    /// `group_order.claimed_order` exceeds [`ENUMERATION_BOUND`].
    TooLargeToVerify,
    /// Some generator of `H` does not sift into the claimed closure.
    SubgroupNotContainedInClosure,
    /// Some generator of the claimed closure is not a member of `G`.
    ClosureNotContainedInGroup,
    /// The independently recomputed normal closure (the subgroup generated
    /// by every conjugate of `H`'s generators by every element of `G`) does
    /// not equal the claimed closure.
    SetMismatch,
}

impl NormalClosureCertificate {
    /// Independently re-derives every claim this certificate makes,
    /// returning the first guard that fails.
    ///
    /// # Errors
    ///
    /// Returns the first [`NormalClosureFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), NormalClosureFailure> {
        use NormalClosureFailure as F;
        self.group_order
            .verify()
            .map_err(|_| F::GroupCertificateInvalid)?;
        self.subgroup_order
            .verify()
            .map_err(|_| F::SubgroupCertificateInvalid)?;
        self.closure_order
            .verify()
            .map_err(|_| F::ClosureCertificateInvalid)?;
        if self.group_order.degree != self.subgroup_order.degree
            || self.group_order.degree != self.closure_order.degree
        {
            return Err(F::DegreeMismatch);
        }
        let degree = self.group_order.degree;
        for h in &self.subgroup_order.original_generators {
            if let SiftOutcome::Failure { .. } = sift_with_trace(
                h,
                &self.closure_order.base,
                &self.closure_order.transversals,
                &self.closure_order.strong_generators,
                degree,
            ) {
                return Err(F::SubgroupNotContainedInClosure);
            }
        }
        for c in &self.closure_order.original_generators {
            if let SiftOutcome::Failure { .. } = sift_with_trace(
                c,
                &self.group_order.base,
                &self.group_order.transversals,
                &self.group_order.strong_generators,
                degree,
            ) {
                return Err(F::ClosureNotContainedInGroup);
            }
        }
        if self.group_order.claimed_order > ENUMERATION_BOUND {
            return Err(F::TooLargeToVerify);
        }
        let g_elems = enumerate_group(
            &self.group_order.original_generators,
            degree,
            ENUMERATION_BOUND,
        )
        .ok_or(F::TooLargeToVerify)?;
        let mut gens: Vec<Permutation> = self.subgroup_order.original_generators.clone();
        for g in &g_elems {
            let g_inv = g.inverse();
            for h in &self.subgroup_order.original_generators {
                gens.push(
                    g.compose(h)
                        .expect("same degree")
                        .compose(&g_inv)
                        .expect("same degree"),
                );
            }
        }
        let recomputed_elems =
            enumerate_group(&gens, degree, ENUMERATION_BOUND).ok_or(F::TooLargeToVerify)?;
        let recomputed: BTreeSet<Vec<usize>> = recomputed_elems
            .iter()
            .map(|p| image_key(p, degree))
            .collect();
        let claimed_elems = enumerate_group(
            &self.closure_order.original_generators,
            degree,
            ENUMERATION_BOUND,
        )
        .ok_or(F::TooLargeToVerify)?;
        let claimed: BTreeSet<Vec<usize>> =
            claimed_elems.iter().map(|p| image_key(p, degree)).collect();
        if recomputed != claimed {
            return Err(F::SetMismatch);
        }
        Ok(())
    }
}

impl PermutationGroup {
    /// The normal closure of `subgroup` in `G` -- the smallest normal
    /// subgroup of `G` containing it -- for `|G| <=` [`ENUMERATION_BOUND`]:
    /// built directly as the subgroup generated by every conjugate of
    /// `subgroup`'s generators by every element of `G` (a standard identity,
    /// so no iteration to a fixed point is needed).
    ///
    /// # Errors
    ///
    /// [`PermgroupError::DegreeMismatch`] if `subgroup` acts on a different
    /// number of points; [`PermgroupError::TooLarge`] if `|G|` exceeds
    /// [`ENUMERATION_BOUND`].
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn normal_closure(
        &self,
        subgroup: &PermutationGroup,
    ) -> Result<(PermutationGroup, NormalClosureCertificate), PermgroupError> {
        if subgroup.degree != self.degree {
            return Err(PermgroupError::DegreeMismatch);
        }
        if self.order_certificate.claimed_order > ENUMERATION_BOUND {
            return Err(PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: self.order_certificate.claimed_order,
            });
        }
        let g_elems = enumerate_group(&self.generators, self.degree, ENUMERATION_BOUND).ok_or(
            PermgroupError::TooLarge {
                bound: ENUMERATION_BOUND,
                actual: self.order_certificate.claimed_order,
            },
        )?;
        let mut gens: Vec<Permutation> = subgroup.generators.clone();
        for g in &g_elems {
            let g_inv = g.inverse();
            for h in &subgroup.generators {
                gens.push(
                    g.compose(h)
                        .expect("same degree")
                        .compose(&g_inv)
                        .expect("same degree"),
                );
            }
        }
        let closure = PermutationGroup::from_generators(gens, self.degree)
            .expect("degree matches by construction");
        let cert = NormalClosureCertificate {
            group_order: self.order_certificate.clone(),
            subgroup_order: subgroup.order_certificate.clone(),
            closure_order: closure.order_certificate.clone(),
        };
        Ok((closure, cert))
    }
}

/// A checkable certificate for `|G / H|` when `H` is normal in `G`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct QuotientOrderCertificate {
    /// The normality certificate establishing `H ⊴ G`.
    pub normality: NormalityCertificate,
    /// The claimed quotient order `|G| / |H|`.
    pub quotient_order: u128,
}

/// Why a [`QuotientOrderCertificate`] failed to verify.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QuotientOrderFailure {
    /// `normality` itself does not verify.
    NormalityCertificateInvalid,
    /// `normality` is a `NotNormal` claim, so no quotient group order exists
    /// to certify.
    NotNormal,
    /// `subgroup_order.claimed_order` does not divide `group_order.claimed_order`
    /// (impossible for a genuine subgroup by Lagrange's theorem, but checked
    /// rather than assumed).
    SubgroupOrderDoesNotDivideGroupOrder,
    /// The recomputed exact quotient does not equal `quotient_order`.
    QuotientOrderMismatch {
        /// The recomputed quotient.
        computed: u128,
        /// The claimed quotient.
        claimed: u128,
    },
}

impl QuotientOrderCertificate {
    /// Independently re-derives every claim this certificate makes,
    /// returning the first guard that fails.
    ///
    /// # Errors
    ///
    /// Returns the first [`QuotientOrderFailure`] guard that does not hold.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn verify(&self) -> Result<(), QuotientOrderFailure> {
        use QuotientOrderFailure as F;
        self.normality
            .verify()
            .map_err(|_| F::NormalityCertificateInvalid)?;
        let (group_order, subgroup_order) = match &self.normality {
            NormalityCertificate::Normal {
                group_order,
                subgroup_order,
            } => (group_order, subgroup_order),
            NormalityCertificate::NotNormal { .. } => return Err(F::NotNormal),
        };
        if subgroup_order.claimed_order == 0
            || group_order.claimed_order % subgroup_order.claimed_order != 0
        {
            return Err(F::SubgroupOrderDoesNotDivideGroupOrder);
        }
        let computed = group_order.claimed_order / subgroup_order.claimed_order;
        if computed != self.quotient_order {
            return Err(F::QuotientOrderMismatch {
                computed,
                claimed: self.quotient_order,
            });
        }
        Ok(())
    }
}

impl PermutationGroup {
    /// `|G / H|` for `subgroup` normal in `G`, for `|G| <=`
    /// [`ENUMERATION_BOUND`] (the bound [`Self::is_normal`] carries).
    ///
    /// # Errors
    ///
    /// Propagates every error [`Self::is_normal`] can return, plus
    /// [`PermgroupError::NotNormal`] if `subgroup` is not normal in `G`.
    ///
    /// # Panics
    ///
    /// Never panics.
    pub fn quotient_order(
        &self,
        subgroup: &PermutationGroup,
    ) -> Result<QuotientOrderCertificate, PermgroupError> {
        let normality = self.is_normal(subgroup)?;
        match &normality {
            NormalityCertificate::Normal {
                group_order,
                subgroup_order,
            } => {
                let quotient_order = group_order.claimed_order / subgroup_order.claimed_order;
                Ok(QuotientOrderCertificate {
                    normality,
                    quotient_order,
                })
            }
            NormalityCertificate::NotNormal { .. } => Err(PermgroupError::NotNormal),
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn transposition(n: usize, a: usize, b: usize) -> Permutation {
        Permutation::from_cycles(&[vec![a, b]], n).unwrap()
    }

    fn cycle(n: usize, pts: &[usize]) -> Permutation {
        Permutation::from_cycles(&[pts.to_vec()], n).unwrap()
    }

    fn symmetric_group(n: usize) -> PermutationGroup {
        let gens: Vec<Permutation> = (0..n - 1).map(|i| transposition(n, i, i + 1)).collect();
        PermutationGroup::from_generators(gens, n).unwrap()
    }

    fn alternating_group(n: usize) -> PermutationGroup {
        let gens: Vec<Permutation> = (2..n).map(|k| cycle(n, &[0, 1, k])).collect();
        PermutationGroup::from_generators(gens, n).unwrap()
    }

    // -- sylow_subgroup / sylow_count --

    #[test]
    fn s4_has_three_sylow_2_subgroups_of_order_8() {
        let g = symmetric_group(4);
        let (sylow2, cert) = g.sylow_subgroup(2).unwrap();
        assert_eq!(sylow2.order(), 8);
        assert_eq!(cert.exponent, 3);
        assert!(cert.verify().is_ok());
        let count_cert = g.sylow_count(&sylow2, 2).unwrap();
        assert_eq!(count_cert.n_p, 3);
        assert!(count_cert.verify().is_ok());
    }

    #[test]
    fn s4_has_four_sylow_3_subgroups_of_order_3() {
        let g = symmetric_group(4);
        let (sylow3, cert) = g.sylow_subgroup(3).unwrap();
        assert_eq!(sylow3.order(), 3);
        assert_eq!(cert.exponent, 1);
        assert!(cert.verify().is_ok());
        let count_cert = g.sylow_count(&sylow3, 3).unwrap();
        assert_eq!(count_cert.n_p, 4);
        assert!(count_cert.verify().is_ok());
    }

    #[test]
    fn a5_sylow_counts_are_5_10_6_for_p_2_3_5() {
        let g = alternating_group(5);
        assert_eq!(g.order(), 60);
        for (p, expected_order, expected_count) in [(2u128, 4u128, 5u128), (3, 3, 10), (5, 5, 6)] {
            let (sylow, cert) = g.sylow_subgroup(p).unwrap();
            assert_eq!(sylow.order(), expected_order, "prime {p}");
            assert!(cert.verify().is_ok());
            let count_cert = g.sylow_count(&sylow, p).unwrap();
            assert_eq!(count_cert.n_p, expected_count, "prime {p}");
            assert!(count_cert.verify().is_ok());
        }
    }

    #[test]
    fn sylow_subgroup_declines_for_a_prime_not_dividing_the_order() {
        let g = symmetric_group(4); // order 24 = 2^3 * 3
        assert!(matches!(
            g.sylow_subgroup(5),
            Err(PermgroupError::PrimeDoesNotDivideOrder)
        ));
    }

    #[test]
    fn forged_sylow_certificate_wrong_order_is_refused() {
        let g = symmetric_group(4);
        let (_, cert) = g.sylow_subgroup(2).unwrap();
        let trivial = PermutationGroup::from_generators(vec![], 4).unwrap();
        let mut forged = cert.clone();
        forged.sylow_order = trivial.order_certificate().clone();
        assert_eq!(
            forged.verify(),
            Err(SylowFailure::OrderIsNotFullPPart {
                computed: 8,
                claimed: 1,
            })
        );
    }

    #[test]
    fn forged_sylow_count_violating_congruence_is_refused() {
        let g = symmetric_group(4);
        let (sylow2, _) = g.sylow_subgroup(2).unwrap();
        let mut cert = g.sylow_count(&sylow2, 2).unwrap();
        assert_eq!(cert.n_p, 3);
        // 2 % 2 == 0, violating n_p == 1 (mod p); checked before the
        // expensive recount, so this never enumerates G.
        cert.n_p = 2;
        assert_eq!(
            cert.verify(),
            Err(SylowCountFailure::NotCongruentToOneModPrime)
        );
    }

    #[test]
    fn forged_sylow_count_recompute_mismatch_is_refused() {
        let g = symmetric_group(4);
        let (sylow2, _) = g.sylow_subgroup(2).unwrap();
        let mut cert = g.sylow_count(&sylow2, 2).unwrap();
        assert_eq!(cert.n_p, 3);
        // 1 % 2 == 1 (congruent) and 3 % 1 == 0 (divides the cofactor), so
        // both cheap arithmetic guards pass; only the full recount catches
        // this forgery.
        cert.n_p = 1;
        assert_eq!(
            cert.verify(),
            Err(SylowCountFailure::CountMismatch {
                computed: 3,
                claimed: 1,
            })
        );
    }

    // -- is_normal / normal_closure / quotient_order --

    #[test]
    fn a4_is_normal_in_s4_with_quotient_order_2() {
        let s4 = symmetric_group(4);
        let a4 = alternating_group(4);
        let cert = s4.is_normal(&a4).unwrap();
        assert!(matches!(cert, NormalityCertificate::Normal { .. }));
        assert!(cert.verify().is_ok());

        let quotient_cert = s4.quotient_order(&a4).unwrap();
        assert_eq!(quotient_cert.quotient_order, 2);
        assert!(quotient_cert.verify().is_ok());
    }

    #[test]
    fn a_sylow_3_subgroup_of_s4_is_not_normal() {
        let s4 = symmetric_group(4);
        let (sylow3, _) = s4.sylow_subgroup(3).unwrap();
        let cert = s4.is_normal(&sylow3).unwrap();
        assert!(matches!(cert, NormalityCertificate::NotNormal { .. }));
        assert!(cert.verify().is_ok());

        assert_eq!(s4.quotient_order(&sylow3), Err(PermgroupError::NotNormal));
    }

    #[test]
    fn normal_closure_of_a_3_cycle_in_s4_is_a4() {
        let s4 = symmetric_group(4);
        let three_cycle = PermutationGroup::from_generators(vec![cycle(4, &[0, 1, 2])], 4).unwrap();
        let (closure, cert) = s4.normal_closure(&three_cycle).unwrap();
        assert_eq!(closure.order(), 12);
        assert!(cert.verify().is_ok());

        let normal_cert = s4.is_normal(&closure).unwrap();
        assert!(matches!(normal_cert, NormalityCertificate::Normal { .. }));
        assert!(normal_cert.verify().is_ok());
    }

    #[test]
    fn forged_normality_witness_actually_normal_is_refused() {
        let s4 = symmetric_group(4);
        let a4 = alternating_group(4);
        // a4 IS normal in s4, so any (g, h) pair conjugates back into a4 --
        // a manufactured "NotNormal" claim over this genuinely-normal pair
        // is refused because the witness's conjugate is actually in H.
        let g = transposition(4, 0, 1);
        let h = cycle(4, &[0, 1, 2]);
        let forged = NormalityCertificate::NotNormal {
            group_order: s4.order_certificate().clone(),
            subgroup_order: a4.order_certificate().clone(),
            conjugating_element: g,
            subgroup_element: h,
        };
        assert_eq!(
            forged.verify(),
            Err(NormalityFailure::WitnessActuallyNormal)
        );
    }

    #[test]
    fn forged_normal_closure_too_small_is_refused() {
        let s4 = symmetric_group(4);
        let three_cycle = PermutationGroup::from_generators(vec![cycle(4, &[0, 1, 2])], 4).unwrap();
        let (_, mut cert) = s4.normal_closure(&three_cycle).unwrap();
        // Claim the closure is just the subgroup itself (order 3, not 12).
        cert.closure_order = three_cycle.order_certificate().clone();
        assert!(matches!(
            cert.verify(),
            Err(NormalClosureFailure::SubgroupNotContainedInClosure
                | NormalClosureFailure::SetMismatch)
        ));
    }

    #[test]
    fn forged_quotient_order_mismatch_is_refused() {
        let s4 = symmetric_group(4);
        let a4 = alternating_group(4);
        let mut cert = s4.quotient_order(&a4).unwrap();
        assert_eq!(cert.quotient_order, 2);
        cert.quotient_order = 3;
        assert_eq!(
            cert.verify(),
            Err(QuotientOrderFailure::QuotientOrderMismatch {
                computed: 2,
                claimed: 3,
            })
        );
    }

    #[test]
    fn is_normal_declines_when_degrees_mismatch() {
        let s4 = symmetric_group(4);
        let other_degree =
            PermutationGroup::from_generators(vec![cycle(5, &[0, 1, 2, 3, 4])], 5).unwrap();
        assert_eq!(
            s4.is_normal(&other_degree),
            Err(PermgroupError::DegreeMismatch)
        );
    }
}
