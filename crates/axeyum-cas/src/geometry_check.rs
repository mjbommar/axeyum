//! The **independent** re-derivation of a geometry cofactor certificate.
//!
//! [`crate::geometry_certify`] finds the certificate by running `Buchberger`'s
//! algorithm with cofactor tracking. Nothing in this module knows that. It reads
//! a [`GeometryCertificate`] as data and re-establishes it with polynomial
//! addition and multiplication alone:
//!
//! 1. **Shape.** The saturation generators are rebuilt here from the stated
//!    condition polynomial and inverse variable as `d·z − 1`, and compared with
//!    the generator list in the artifact. A certificate that saturates by
//!    something other than what it says it saturates by is rejected, which is the
//!    only way the non-degeneracy conditions in the file can be trusted to be the
//!    ones the proof used.
//! 2. **The identity.** For each conclusion, `Σᵢ uᵢ·gᵢ` is expanded and compared
//!    to the conclusion polynomial. Exact rational arithmetic, canonical normal
//!    form, so the comparison is decisive.
//! 3. **A second, numeric re-derivation.** The same identity is evaluated at a
//!    deterministic grid of integer points. Symbolic expansion and pointwise
//!    evaluation are different code paths through [`MvPoly`], so agreement is a
//!    real cross-check on the expansion rather than a restatement of it.
//! 4. **The negative controls.** Every degenerate witness must satisfy every
//!    hypothesis, annihilate the non-degeneracy condition it names, and
//!    **falsify** at least one conclusion. A certificate whose side conditions
//!    cannot be shown to bite is rejected here — that is what stops this route
//!    from manufacturing theorems that are true only off the degeneracy locus.
//! 5. **The positive controls.** Every generic witness must satisfy the
//!    hypotheses, keep every saturating condition nonzero, and satisfy every
//!    conclusion.
//!
//! Steps 4 and 5 are the ones that check the *coordinatisation* rather than the
//! algebra: they are configurations of actual rational points, and they are the
//! only place where a mis-encoded predicate could show up.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_ir::Rational;

use crate::geometry_certify::GeometryCertificate;
use crate::mvpoly::MvPoly;

/// What a verified certificate exercised.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GeometryReport {
    /// Conclusions whose cofactor identity was expanded and matched.
    pub conclusions_checked: usize,
    /// Non-degeneracy conditions whose saturation generator carries a **nonzero**
    /// cofactor in at least one conclusion — i.e. the ones the proof genuinely
    /// consumed. A condition listed but unused would be a claim of a weaker
    /// theorem than was proved.
    pub conditions_used: Vec<String>,
    /// Degenerate configurations confirmed to satisfy the hypotheses, break the
    /// named condition, and falsify a conclusion.
    pub degenerate_witnesses_checked: usize,
    /// Non-degenerate configurations confirmed to satisfy everything.
    pub generic_witnesses_checked: usize,
    /// Integer points at which the identity was re-evaluated numerically.
    pub numeric_points_checked: usize,
}

/// The outcome of checking a certificate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GeometryVerdict {
    /// The certificate re-derives.
    Verified(GeometryReport),
    /// It does not, with the reason.
    Rejected(String),
}

impl GeometryVerdict {
    /// Whether the certificate re-derived.
    #[must_use]
    pub fn is_verified(&self) -> bool {
        matches!(self, GeometryVerdict::Verified(_))
    }
}

/// How hard to work at the numeric cross-check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CheckOptions {
    /// Integer points per conclusion at which to re-evaluate the identity.
    pub numeric_points: usize,
    /// Points are drawn from `−half_range ..= half_range`, avoiding zeros where
    /// an inverse variable would be meaningless.
    pub half_range: i128,
}

impl Default for CheckOptions {
    fn default() -> CheckOptions {
        CheckOptions {
            numeric_points: 24,
            half_range: 6,
        }
    }
}

fn reject(reason: impl Into<String>) -> GeometryVerdict {
    GeometryVerdict::Rejected(reason.into())
}

/// Re-derive a certificate from the outside.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn check_certificate(
    certificate: &GeometryCertificate,
    options: &CheckOptions,
) -> GeometryVerdict {
    // --- 1. shape --------------------------------------------------------
    let expected = certificate.hypotheses.len() + certificate.saturations.len();
    if certificate.generators.len() != expected {
        return reject(format!(
            "generator count {} does not match {} hypotheses + {} saturations",
            certificate.generators.len(),
            certificate.hypotheses.len(),
            certificate.saturations.len()
        ));
    }
    for (index, hypothesis) in certificate.hypotheses.iter().enumerate() {
        if certificate.generators[index] != hypothesis.poly {
            return reject(format!(
                "generator {index} is not the stated hypothesis `{}`",
                hypothesis.id
            ));
        }
    }
    let mut inverse_vars: BTreeSet<&str> = BTreeSet::new();
    for (slot, saturation) in certificate.saturations.iter().enumerate() {
        if !inverse_vars.insert(saturation.var.as_str()) {
            return reject(format!("inverse variable `{}` is reused", saturation.var));
        }
        if certificate.coordinates.contains(&saturation.var) {
            return reject(format!(
                "inverse variable `{}` collides with a coordinate",
                saturation.var
            ));
        }
        if saturation.condition.is_zero() {
            return reject(format!(
                "condition `{}` is the zero polynomial, which is never nonzero",
                saturation.condition_id
            ));
        }
        let Some(rebuilt) = saturation
            .condition
            .mul(&MvPoly::var(&saturation.var))
            .and_then(|product| product.sub(&MvPoly::constant(Rational::integer(1))))
        else {
            return reject(format!(
                "rebuilding the saturation generator for `{}` overflowed",
                saturation.condition_id
            ));
        };
        let index = certificate.hypotheses.len() + slot;
        if certificate.generators[index] != rebuilt {
            return reject(format!(
                "generator {index} is not `{} · {} − 1`",
                saturation.condition_id, saturation.var
            ));
        }
    }

    // --- 2. the identity, symbolically ----------------------------------
    if certificate.conclusions.is_empty() {
        return reject("a certificate with no conclusion establishes nothing");
    }
    let mut used: BTreeSet<String> = BTreeSet::new();
    for conclusion in &certificate.conclusions {
        if conclusion.cofactors.len() != certificate.generators.len() {
            return reject(format!(
                "conclusion `{}` has {} cofactors for {} generators",
                conclusion.id,
                conclusion.cofactors.len(),
                certificate.generators.len()
            ));
        }
        let mut combined = MvPoly::zero();
        for (cofactor, generator) in conclusion.cofactors.iter().zip(&certificate.generators) {
            if cofactor.is_zero() {
                continue;
            }
            let Some(product) = cofactor.mul(generator) else {
                return reject(format!(
                    "expanding a cofactor product for `{}` overflowed",
                    conclusion.id
                ));
            };
            let Some(sum) = combined.add(&product) else {
                return reject(format!(
                    "accumulating the identity for `{}` overflowed",
                    conclusion.id
                ));
            };
            combined = sum;
        }
        if combined != conclusion.poly {
            return reject(format!(
                "the cofactor identity does not reproduce conclusion `{}`",
                conclusion.id
            ));
        }
        for (slot, saturation) in certificate.saturations.iter().enumerate() {
            let index = certificate.hypotheses.len() + slot;
            if !conclusion.cofactors[index].is_zero() {
                used.insert(saturation.condition_id.clone());
            }
        }
    }
    for saturation in &certificate.saturations {
        if !used.contains(&saturation.condition_id) {
            return reject(format!(
                "condition `{}` is saturated by but never used; the theorem proved is stronger \
                 than the one stated",
                saturation.condition_id
            ));
        }
    }

    // --- 3. the identity, numerically -----------------------------------
    let mut variables: Vec<String> = certificate.coordinates.clone();
    variables.extend(certificate.saturations.iter().map(|s| s.var.clone()));
    variables.sort();
    variables.dedup();
    let mut numeric_points = 0usize;
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    for _ in 0..options.numeric_points {
        let mut assignment: BTreeMap<String, Rational> = BTreeMap::new();
        for name in &variables {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let span = 2 * options.half_range + 1;
            #[allow(clippy::cast_possible_wrap)]
            let value = i128::from((state >> 33) as u32) % span - options.half_range;
            assignment.insert(name.clone(), Rational::integer(value));
        }
        let mut usable = true;
        for conclusion in &certificate.conclusions {
            let Some(target) = conclusion.poly.evaluate(&assignment) else {
                usable = false;
                break;
            };
            let mut total = Rational::zero();
            for (cofactor, generator) in conclusion.cofactors.iter().zip(&certificate.generators) {
                let (Some(left), Some(right)) = (
                    cofactor.evaluate(&assignment),
                    generator.evaluate(&assignment),
                ) else {
                    usable = false;
                    break;
                };
                let (Some(product), ..) = (left.checked_mul(right), ()) else {
                    usable = false;
                    break;
                };
                let Some(sum) = total.checked_add(product) else {
                    usable = false;
                    break;
                };
                total = sum;
            }
            if !usable {
                break;
            }
            if total != target {
                return reject(format!(
                    "the identity for `{}` fails numerically at {assignment:?}",
                    conclusion.id
                ));
            }
        }
        if usable {
            numeric_points += 1;
        }
    }

    // --- 4. the negative controls ---------------------------------------
    for saturation in &certificate.saturations {
        if !certificate
            .degenerate_witnesses
            .iter()
            .any(|witness| witness.condition_id == saturation.condition_id)
        {
            return reject(format!(
                "condition `{}` is used but no degenerate counterexample is exhibited for it",
                saturation.condition_id
            ));
        }
    }
    for witness in &certificate.degenerate_witnesses {
        let Some(saturation) = certificate
            .saturations
            .iter()
            .find(|saturation| saturation.condition_id == witness.condition_id)
        else {
            return reject(format!(
                "degenerate witness names condition `{}`, which the proof does not use",
                witness.condition_id
            ));
        };
        for hypothesis in &certificate.hypotheses {
            match hypothesis.poly.evaluate(&witness.assignment) {
                Some(value) if value.is_zero() => {}
                Some(_) => {
                    return reject(format!(
                        "degenerate witness for `{}` violates hypothesis `{}`",
                        witness.condition_id, hypothesis.id
                    ));
                }
                None => {
                    return reject(format!(
                        "degenerate witness for `{}` is not fully assigned",
                        witness.condition_id
                    ));
                }
            }
        }
        match saturation.condition.evaluate(&witness.assignment) {
            Some(value) if value.is_zero() => {}
            _ => {
                return reject(format!(
                    "degenerate witness for `{}` does not actually violate it",
                    witness.condition_id
                ));
            }
        }
        let broken = certificate.conclusions.iter().any(|conclusion| {
            matches!(conclusion.poly.evaluate(&witness.assignment), Some(value) if !value.is_zero())
        });
        if !broken {
            return reject(format!(
                "degenerate witness for `{}` satisfies every conclusion, so it is not a \
                 counterexample and the condition is not shown to be needed",
                witness.condition_id
            ));
        }
    }

    // --- 5. the positive controls ---------------------------------------
    for (index, witness) in certificate.generic_witnesses.iter().enumerate() {
        for hypothesis in &certificate.hypotheses {
            match hypothesis.poly.evaluate(&witness.assignment) {
                Some(value) if value.is_zero() => {}
                _ => {
                    return reject(format!(
                        "generic witness {index} violates hypothesis `{}`",
                        hypothesis.id
                    ));
                }
            }
        }
        for saturation in &certificate.saturations {
            match saturation.condition.evaluate(&witness.assignment) {
                Some(value) if !value.is_zero() => {}
                _ => {
                    return reject(format!(
                        "generic witness {index} is degenerate for `{}`",
                        saturation.condition_id
                    ));
                }
            }
        }
        for conclusion in &certificate.conclusions {
            match conclusion.poly.evaluate(&witness.assignment) {
                Some(value) if value.is_zero() => {}
                _ => {
                    return reject(format!(
                        "generic witness {index} falsifies conclusion `{}`",
                        conclusion.id
                    ));
                }
            }
        }
    }

    GeometryVerdict::Verified(GeometryReport {
        conclusions_checked: certificate.conclusions.len(),
        conditions_used: used.into_iter().collect(),
        degenerate_witnesses_checked: certificate.degenerate_witnesses.len(),
        generic_witnesses_checked: certificate.generic_witnesses.len(),
        numeric_points_checked: numeric_points,
    })
}
