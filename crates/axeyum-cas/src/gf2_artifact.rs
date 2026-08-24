//! Canonical evidence artifacts for Lemire half-degree witnesses.

use core::fmt;

use serde::{Deserialize, Serialize};

use crate::gf2::{
    FrobeniusReduction, Gf2Error, Gf2Limits, Gf2Poly, IrreducibilityCertificate, RabinBezout,
    check_irreducible_certificate,
};
use crate::gf2_independent::{IndependentCheckLimits, check_irreducible_certificate_independent};

/// Artifact format tag.
pub const FORMAT: &str = "axeyum-gf2-half-degree-irreducible";
/// Artifact format version.
pub const VERSION: u32 = 1;
/// Exact bounded statement carried by one artifact.
pub const STATEMENT: &str = "monic irreducible f over GF(2), deg(f)=n, deg(f-x^n)<=floor(n/2)";

/// Parser and checker limits for an artifact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ArtifactLimits {
    /// Maximum serialized input size.
    pub max_bytes: usize,
    /// Maximum identifier length in bytes.
    pub max_id_bytes: usize,
    /// Maximum producer-identity length in bytes.
    pub max_producer_bytes: usize,
    /// Packed primary-checker limits.
    pub primary: Gf2Limits,
    /// Dense independent-checker limits.
    pub independent: IndependentCheckLimits,
}

impl Default for ArtifactLimits {
    fn default() -> Self {
        Self {
            max_bytes: 32 * 1024 * 1024,
            max_id_bytes: 256,
            max_producer_bytes: 256,
            primary: Gf2Limits::default(),
            independent: IndependentCheckLimits::default(),
        }
    }
}

/// A checked bounded witness and its provenance label.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HalfDegreeArtifact {
    /// Stable caller-chosen artifact identifier.
    pub id: String,
    /// Content or executable identity of the untrusted producer.
    pub producer: String,
    /// Portable Rabin certificate.
    pub certificate: IrreducibilityCertificate,
}

/// Fail-closed artifact parsing or validation error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ArtifactError {
    /// Serialized bytes exceed the front-door ceiling.
    InputTooLarge {
        /// Serialized byte count encountered.
        observed: usize,
        /// Configured byte ceiling.
        limit: usize,
    },
    /// JSON syntax or type validation failed.
    Json(String),
    /// A format, canonicalization, or theorem-shape invariant failed.
    Format(&'static str),
    /// One of the two algebraic checkers declined or rejected the certificate.
    Certificate(Gf2Error),
}

impl fmt::Display for ArtifactError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InputTooLarge { observed, limit } => {
                write!(formatter, "artifact has {observed} bytes; limit is {limit}")
            }
            Self::Json(message) => write!(formatter, "invalid artifact JSON: {message}"),
            Self::Format(message) => write!(formatter, "invalid artifact format: {message}"),
            Self::Certificate(error) => write!(formatter, "certificate check failed: {error}"),
        }
    }
}

impl std::error::Error for ArtifactError {}

impl From<Gf2Error> for ArtifactError {
    fn from(error: Gf2Error) -> Self {
        Self::Certificate(error)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawArtifact {
    format: String,
    version: u32,
    statement: String,
    id: String,
    producer: String,
    degree: usize,
    tail_degree_bound: usize,
    polynomial_words_le: Vec<String>,
    frobenius: Vec<RawReduction>,
    bezout: Vec<RawBezout>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawReduction {
    quotient_words_le: Vec<String>,
    remainder_words_le: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawBezout {
    prime_divisor: usize,
    polynomial_coefficient_words_le: Vec<String>,
    frobenius_coefficient_words_le: Vec<String>,
}

/// Validate both checkers and render canonical pretty JSON with one final newline.
///
/// # Errors
///
/// Returns a format error for an invalid half-degree shape or provenance field,
/// a certificate error from either checker, or an input-size error if the
/// canonical output would exceed the configured byte ceiling.
pub fn to_canonical_json(
    artifact: &HalfDegreeArtifact,
    limits: ArtifactLimits,
) -> Result<String, ArtifactError> {
    validate(artifact, limits)?;
    let raw = RawArtifact::from_artifact(artifact)?;
    let mut output = serde_json::to_string_pretty(&raw)
        .map_err(|error| ArtifactError::Json(error.to_string()))?;
    output.push('\n');
    if output.len() > limits.max_bytes {
        return Err(ArtifactError::InputTooLarge {
            observed: output.len(),
            limit: limits.max_bytes,
        });
    }
    Ok(output)
}

/// Parse canonical JSON and rerun both algebraically distinct checkers.
///
/// Noncanonical whitespace, field order, uppercase/padded variants, and unknown
/// fields are rejected by re-rendering the parsed artifact byte for byte.
///
/// # Errors
///
/// Returns a typed size, JSON, format, or certificate error.
pub fn from_canonical_json(
    input: &str,
    limits: ArtifactLimits,
) -> Result<HalfDegreeArtifact, ArtifactError> {
    if input.len() > limits.max_bytes {
        return Err(ArtifactError::InputTooLarge {
            observed: input.len(),
            limit: limits.max_bytes,
        });
    }
    let raw: RawArtifact =
        serde_json::from_str(input).map_err(|error| ArtifactError::Json(error.to_string()))?;
    let artifact = raw.into_artifact(limits)?;
    let canonical = to_canonical_json(&artifact, limits)?;
    if canonical != input {
        return Err(ArtifactError::Format("JSON is not in canonical form"));
    }
    Ok(artifact)
}

/// Validate theorem shape and run both certificate checkers.
///
/// # Errors
///
/// Returns a typed format or certificate error.
pub fn validate(
    artifact: &HalfDegreeArtifact,
    limits: ArtifactLimits,
) -> Result<(), ArtifactError> {
    validate_label(&artifact.id, limits.max_id_bytes, "invalid artifact id")?;
    validate_label(
        &artifact.producer,
        limits.max_producer_bytes,
        "invalid producer identity",
    )?;
    let polynomial = &artifact.certificate.polynomial;
    let degree = polynomial
        .degree()
        .ok_or(ArtifactError::Format("candidate is zero"))?;
    if degree == 0 {
        return Err(ArtifactError::Format("candidate is constant"));
    }
    let tail_bound = degree / 2;
    for exponent in polynomial.exponents() {
        if exponent != degree && exponent > tail_bound {
            return Err(ArtifactError::Format(
                "candidate has a nonleading term above floor(n/2)",
            ));
        }
    }
    check_irreducible_certificate(&artifact.certificate, limits.primary)?;
    check_irreducible_certificate_independent(&artifact.certificate, limits.independent)?;
    Ok(())
}

fn validate_label(
    label: &str,
    max_bytes: usize,
    message: &'static str,
) -> Result<(), ArtifactError> {
    if label.is_empty() || label.len() > max_bytes || label.chars().any(char::is_control) {
        return Err(ArtifactError::Format(message));
    }
    Ok(())
}

impl RawArtifact {
    fn from_artifact(artifact: &HalfDegreeArtifact) -> Result<Self, ArtifactError> {
        let degree = artifact
            .certificate
            .polynomial
            .degree()
            .ok_or(ArtifactError::Format("candidate is zero"))?;
        Ok(Self {
            format: FORMAT.to_owned(),
            version: VERSION,
            statement: STATEMENT.to_owned(),
            id: artifact.id.clone(),
            producer: artifact.producer.clone(),
            degree,
            tail_degree_bound: degree / 2,
            polynomial_words_le: encode_poly(&artifact.certificate.polynomial),
            frobenius: artifact
                .certificate
                .frobenius
                .iter()
                .map(|reduction| RawReduction {
                    quotient_words_le: encode_poly(&reduction.quotient),
                    remainder_words_le: encode_poly(&reduction.remainder),
                })
                .collect(),
            bezout: artifact
                .certificate
                .bezout
                .iter()
                .map(|witness| RawBezout {
                    prime_divisor: witness.prime_divisor,
                    polynomial_coefficient_words_le: encode_poly(&witness.polynomial_coefficient),
                    frobenius_coefficient_words_le: encode_poly(&witness.frobenius_coefficient),
                })
                .collect(),
        })
    }

    fn into_artifact(self, limits: ArtifactLimits) -> Result<HalfDegreeArtifact, ArtifactError> {
        if self.format != FORMAT {
            return Err(ArtifactError::Format("unknown format tag"));
        }
        if self.version != VERSION {
            return Err(ArtifactError::Format("unsupported format version"));
        }
        if self.statement != STATEMENT {
            return Err(ArtifactError::Format("statement identity differs"));
        }
        if self.tail_degree_bound != self.degree / 2 {
            return Err(ArtifactError::Format("tail-degree bound is not floor(n/2)"));
        }
        let max_words = limits.primary.max_intermediate_degree / 64 + 1;
        let polynomial = decode_poly(&self.polynomial_words_le, max_words)?;
        if polynomial.degree() != Some(self.degree) {
            return Err(ArtifactError::Format(
                "declared degree differs from polynomial",
            ));
        }
        let frobenius = self
            .frobenius
            .into_iter()
            .map(|reduction| {
                Ok(FrobeniusReduction {
                    quotient: decode_poly(&reduction.quotient_words_le, max_words)?,
                    remainder: decode_poly(&reduction.remainder_words_le, max_words)?,
                })
            })
            .collect::<Result<Vec<_>, ArtifactError>>()?;
        let bezout = self
            .bezout
            .into_iter()
            .map(|witness| {
                Ok(RabinBezout {
                    prime_divisor: witness.prime_divisor,
                    polynomial_coefficient: decode_poly(
                        &witness.polynomial_coefficient_words_le,
                        max_words,
                    )?,
                    frobenius_coefficient: decode_poly(
                        &witness.frobenius_coefficient_words_le,
                        max_words,
                    )?,
                })
            })
            .collect::<Result<Vec<_>, ArtifactError>>()?;
        let artifact = HalfDegreeArtifact {
            id: self.id,
            producer: self.producer,
            certificate: IrreducibilityCertificate {
                polynomial,
                frobenius,
                bezout,
            },
        };
        validate(&artifact, limits)?;
        Ok(artifact)
    }
}

fn encode_poly(polynomial: &Gf2Poly) -> Vec<String> {
    polynomial
        .words()
        .iter()
        .map(|word| format!("{word:016x}"))
        .collect()
}

fn decode_poly(words: &[String], max_words: usize) -> Result<Gf2Poly, ArtifactError> {
    if words.len() > max_words {
        return Err(ArtifactError::Format("polynomial word count exceeds limit"));
    }
    let mut decoded = Vec::with_capacity(words.len());
    for word in words {
        if word.len() != 16
            || !word
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(ArtifactError::Format(
                "coefficient words must be 16 lowercase hexadecimal digits",
            ));
        }
        decoded.push(
            u64::from_str_radix(word, 16)
                .map_err(|_| ArtifactError::Format("invalid coefficient word"))?,
        );
    }
    if decoded.last() == Some(&0) {
        return Err(ArtifactError::Format("polynomial words are not normalized"));
    }
    Ok(Gf2Poly::from_words(decoded))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::gf2::certify_irreducible;

    fn artifact() -> HalfDegreeArtifact {
        let limits = Gf2Limits::default();
        let polynomial = Gf2Poly::from_exponents(&[0, 1, 4], limits).unwrap();
        HalfDegreeArtifact {
            id: "degree-4-control".to_owned(),
            producer: "unit-test".to_owned(),
            certificate: certify_irreducible(&polynomial, limits)
                .unwrap()
                .expect("control is irreducible"),
        }
    }

    #[test]
    fn canonical_round_trip_is_byte_stable() {
        let limits = ArtifactLimits::default();
        let expected = artifact();
        let first = to_canonical_json(&expected, limits).unwrap();
        let parsed = from_canonical_json(&first, limits).unwrap();
        assert_eq!(parsed, expected);
        assert_eq!(to_canonical_json(&parsed, limits).unwrap(), first);
    }

    #[test]
    fn noncanonical_and_unknown_fields_are_rejected() {
        let limits = ArtifactLimits::default();
        let canonical = to_canonical_json(&artifact(), limits).unwrap();
        let noncanonical = canonical.replace("  \"format\"", " \"format\"");
        assert_eq!(
            from_canonical_json(&noncanonical, limits),
            Err(ArtifactError::Format("JSON is not in canonical form"))
        );
        let unknown = canonical.replacen(
            "  \"version\": 1,",
            "  \"version\": 1,\n  \"trusted\": true,",
            1,
        );
        assert!(matches!(
            from_canonical_json(&unknown, limits),
            Err(ArtifactError::Json(_))
        ));
    }

    #[test]
    fn theorem_shape_and_declared_degree_are_checked() {
        let limits = ArtifactLimits::default();
        let polynomial = Gf2Poly::from_exponents(&[0, 1, 3, 4], limits.primary).unwrap();
        let malformed = HalfDegreeArtifact {
            id: "bad-tail".to_owned(),
            producer: "unit-test".to_owned(),
            certificate: IrreducibilityCertificate {
                polynomial,
                frobenius: Vec::new(),
                bezout: Vec::new(),
            },
        };
        assert_eq!(
            validate(&malformed, limits),
            Err(ArtifactError::Format(
                "candidate has a nonleading term above floor(n/2)"
            ))
        );

        let canonical = to_canonical_json(&artifact(), limits).unwrap();
        let wrong_degree = canonical.replacen("\"degree\": 4", "\"degree\": 5", 1);
        assert_eq!(
            from_canonical_json(&wrong_degree, limits),
            Err(ArtifactError::Format(
                "declared degree differs from polynomial"
            ))
        );
    }

    #[test]
    fn serialized_certificate_mutation_is_rejected() {
        let limits = ArtifactLimits::default();
        let canonical = to_canonical_json(&artifact(), limits).unwrap();
        let mutated = canonical.replacen("0000000000000004", "0000000000000005", 1);
        assert!(from_canonical_json(&mutated, limits).is_err());
    }
}
