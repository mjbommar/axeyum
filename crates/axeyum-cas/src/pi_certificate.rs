//! Portable source-bound Machin enclosure for distinguished Pi (ADR-6200).
use crate::{
    CasExpr,
    enclosure::{BigInterval, Enclosure, Step, StepHead},
    expression_wire::{self, WireError},
};
use num_bigint::BigInt;
use num_rational::BigRational;
use serde::{Deserialize, Serialize};

const MAX_BYTES: usize = 65_536;
const MAX_PRECISION: u32 = 256;
const MAX_ORDER: u32 = 128;
const MAX_BITS: u64 = 16_384;
fn invalid(reason: &str) -> WireError {
    WireError::Invalid(reason.into())
}
fn resource(reason: &str) -> WireError {
    WireError::ResourceLimit(reason.into())
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Exact {
    numerator: String,
    denominator: String,
}
impl Exact {
    fn encode(value: &BigRational) -> Self {
        Self {
            numerator: value.numer().to_string(),
            denominator: value.denom().to_string(),
        }
    }
    fn decode(&self) -> Result<BigRational, WireError> {
        if self.numerator.len() > 5000 || self.denominator.len() > 5000 {
            return Err(resource("rational digits"));
        }
        let n: BigInt = self.numerator.parse().map_err(|_| invalid("numerator"))?;
        let d: BigInt = self
            .denominator
            .parse()
            .map_err(|_| invalid("denominator"))?;
        if n.bits() > MAX_BITS || d.bits() > MAX_BITS {
            return Err(resource("rational bits"));
        }
        if d <= BigInt::from(0) {
            return Err(invalid("denominator must be positive"));
        }
        let value = BigRational::new(n, d);
        if value.numer().to_string() != self.numerator
            || value.denom().to_string() != self.denominator
        {
            return Err(invalid("rational components must be canonical and reduced"));
        }
        Ok(value)
    }
}

/// Serialized single-node Pi evidence. Parsing is distinct from replay acceptance.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PiEnclosureCertificate {
    version: u32,
    source_expression: String,
    precision: u32,
    order: u32,
    remainder: Exact,
    lower: Exact,
    upper: Exact,
}

/// Actual replay counts and acceptance; a zero discharge is never a success.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PiEnclosureReport {
    /// Whether the claimed source-bound interval was verified.
    pub accepted: bool,
    /// Number of certificate steps examined.
    pub examined: usize,
    /// Number of certificate steps discharged.
    pub discharged: usize,
    /// The failed obligation, or None for acceptance.
    pub reason: Option<String>,
}
impl PiEnclosureCertificate {
    fn enclosure(&self) -> Result<Enclosure, WireError> {
        if self.version != 1 {
            return Err(invalid("unsupported pi certificate version"));
        }
        if self.precision > MAX_PRECISION || self.order > MAX_ORDER {
            return Err(resource("precision or order"));
        }
        if self.source_expression.len() > 1024 {
            return Err(resource("source identity bytes"));
        }
        let interval = BigInterval::new(self.lower.decode()?, self.upper.decode()?)
            .ok_or_else(|| invalid("reversed interval"))?;
        Ok(Enclosure {
            interval: interval.clone(),
            precision: self.precision,
            evidence: vec![Step {
                head: StepHead::Pi,
                inputs: vec![],
                order: self.order,
                remainder: self.remainder.decode()?,
                output: interval,
                signs: None,
            }],
        })
    }
    /// Requested precision, in bits.
    #[must_use]
    pub fn precision(&self) -> u32 {
        self.precision
    }
    /// Claimed lower endpoint, not a verification result.
    ///
    /// # Errors
    /// Rejects malformed or oversized components.
    pub fn lower(&self) -> Result<BigRational, WireError> {
        self.lower.decode()
    }
    /// Claimed upper endpoint, not a verification result.
    ///
    /// # Errors
    /// Rejects malformed or oversized components.
    pub fn upper(&self) -> Result<BigRational, WireError> {
        self.upper.decode()
    }
    /// Deterministic version1 certificate JSON; this does not itself verify it.
    ///
    /// # Errors
    /// Rejects malformed metadata and hard cap violations.
    pub fn to_json(&self) -> Result<String, WireError> {
        self.enclosure()?;
        let s = serde_json::to_string(self).map_err(|e| invalid(&e.to_string()))?;
        if s.len() > MAX_BYTES {
            return Err(resource("certificate bytes"));
        }
        Ok(s)
    }
    /// Parse bounded certificate data; use check to establish acceptance.
    ///
    /// # Errors
    /// Rejects malformed data, versions, components and hard cap violations.
    pub fn from_json(s: &str) -> Result<Self, WireError> {
        if s.len() > MAX_BYTES {
            return Err(resource("certificate bytes"));
        }
        let certificate: Self = serde_json::from_str(s).map_err(|e| invalid(&e.to_string()))?;
        certificate.enclosure()?;
        Ok(certificate)
    }
    /// Replay against the caller's original source without invoking production.
    #[must_use]
    pub fn check(&self, subject: &CasExpr) -> PiEnclosureReport {
        let result = (|| {
            // Source binding is independently required, even for a valid Pi interval.
            if !matches!(subject, CasExpr::Pi)
                || self.source_expression != expression_wire::to_json(&CasExpr::Pi)?
            {
                return Err(invalid(
                    "certificate source is not the original distinguished Pi",
                ));
            }
            self.enclosure()?
                .verify(subject, &[])
                .map_err(|s| invalid(&s))
        })();
        match result {
            Ok(()) => PiEnclosureReport {
                accepted: true,
                examined: 1,
                discharged: 1,
                reason: None,
            },
            Err(error) => PiEnclosureReport {
                accepted: false,
                examined: 1,
                discharged: 0,
                reason: Some(error.to_string()),
            },
        }
    }
}
/// Produce a bounded, self-checked exact Machin enclosure for distinguished Pi.
///
/// # Errors
/// Reports hard cap exhaustion or a failed producer/checker obligation.
pub fn enclose_pi(precision: u32) -> Result<PiEnclosureCertificate, WireError> {
    if precision > MAX_PRECISION {
        return Err(resource("pi precision exceeds 256 bits"));
    }
    let result = crate::enclosure::enclose(&CasExpr::Pi, &[], precision)
        .ok_or_else(|| resource("pi enclosure declined"))?;
    let [step] = result.evidence.as_slice() else {
        return Err(invalid("pi producer step count"));
    };
    if step.head != StepHead::Pi
        || !step.inputs.is_empty()
        || step.signs.is_some()
        || step.output != result.interval
    {
        return Err(invalid("pi producer evidence shape"));
    }
    let certificate = PiEnclosureCertificate {
        version: 1,
        source_expression: expression_wire::to_json(&CasExpr::Pi)?,
        precision: result.precision,
        order: step.order,
        remainder: Exact::encode(&step.remainder),
        lower: Exact::encode(result.interval.lo()),
        upper: Exact::encode(result.interval.hi()),
    };
    certificate.to_json()?;
    let report = certificate.check(&CasExpr::Pi);
    if !report.accepted {
        return Err(invalid(
            report.reason.as_deref().unwrap_or("pi replay failed"),
        ));
    }
    Ok(certificate)
}
