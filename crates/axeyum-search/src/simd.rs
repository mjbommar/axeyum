//! Exact byte-tag semantics and proof-carrying lower bounds for a small SIMD
//! shuffle language.
//!
//! This module intentionally models a named subset, rather than pretending to
//! cover an entire ISA.  The current language contains unary AVX2 `vpshufb`
//! and same-source `vperm2i128`.  Tags record provenance (`Some(input_byte)`)
//! or an instruction-produced zero (`None`), so exhaustive replay does not
//! depend on concrete test bytes accidentally being equal.

use axeyum_cnf::{
    CnfClause, CnfError, CnfFormula, CnfLit, CnfVar, DratError, DratStep, ProofSolveOutcome,
    check_drat_backward, solve_with_drat_proof,
};

/// Number of bytes in an AVX2 YMM register.
pub const AVX2_BYTES: usize = 32;

const IDENTITY_TAGS: [u8; AVX2_BYTES] = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31,
];
const LANE_REVERSE_CONTROL: [u8; AVX2_BYTES] = [
    15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4,
    3, 2, 1, 0,
];

/// Provenance tags for all bytes of one YMM value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ByteTags([Option<u8>; AVX2_BYTES]);

impl ByteTags {
    /// The identity input: output byte `i` carries input tag `i`.
    pub fn identity() -> Self {
        Self(IDENTITY_TAGS.map(Some))
    }

    /// A global byte reversal, used as the first calibration target.
    pub fn reversed() -> Self {
        let mut tags = IDENTITY_TAGS;
        tags.reverse();
        Self(tags.map(Some))
    }

    /// Creates tags after checking that every source tag belongs to this YMM.
    ///
    /// # Errors
    ///
    /// Returns [`SimdError::TagOutOfRange`] for a tag greater than 31.
    pub fn new(tags: [Option<u8>; AVX2_BYTES]) -> Result<Self, SimdError> {
        for (byte, tag) in tags.iter().enumerate() {
            if let Some(tag) = tag
                && usize::from(*tag) >= AVX2_BYTES
            {
                return Err(SimdError::TagOutOfRange { byte, tag: *tag });
            }
        }
        Ok(Self(tags))
    }

    /// Returns the byte tags in increasing output-byte order.
    pub fn as_array(&self) -> &[Option<u8>; AVX2_BYTES] {
        &self.0
    }
}

/// A half selected by unary, same-source `vperm2i128`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HalfSelect {
    /// Bytes 0 through 15 of the source.
    Low,
    /// Bytes 16 through 31 of the source.
    High,
    /// The instruction's zeroing choice.
    Zero,
}

/// One instruction in the explicitly supported AVX2 shuffle subset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Avx2Shuffle {
    /// `_mm256_shuffle_epi8`: each control byte selects inside its own
    /// 128-bit lane; bit 7 produces zero.
    Pshufb([u8; AVX2_BYTES]),
    /// `_mm256_permute2x128_si256(x, x, imm8)` represented semantically as
    /// independently selected output halves.
    Permute2x128 {
        /// Selection for output bytes 0 through 15.
        low: HalfSelect,
        /// Selection for output bytes 16 through 31.
        high: HalfSelect,
    },
}

impl Avx2Shuffle {
    /// Replays this instruction on provenance tags.
    pub fn replay(&self, input: &ByteTags) -> ByteTags {
        match self {
            Self::Pshufb(control) => ByteTags(std::array::from_fn(|out| {
                let ctl = control[out];
                if ctl & 0x80 != 0 {
                    None
                } else {
                    let lane = (out / 16) * 16;
                    input.0[lane + usize::from(ctl & 0x0f)]
                }
            })),
            Self::Permute2x128 { low, high } => ByteTags(std::array::from_fn(|out| {
                let (selection, offset) = if out < 16 {
                    (*low, out)
                } else {
                    (*high, out - 16)
                };
                match selection {
                    HalfSelect::Low => input.0[offset],
                    HalfSelect::High => input.0[16 + offset],
                    HalfSelect::Zero => None,
                }
            })),
        }
    }
}

/// Replays a straight-line sequence from the identity input.
pub fn replay_sequence(steps: &[Avx2Shuffle]) -> ByteTags {
    steps
        .iter()
        .fold(ByteTags::identity(), |value, step| step.replay(&value))
}

/// The constructed two-instruction global byte reversal.
pub fn byte_reverse_sequence() -> [Avx2Shuffle; 2] {
    [
        Avx2Shuffle::Pshufb(LANE_REVERSE_CONTROL),
        Avx2Shuffle::Permute2x128 {
            low: HalfSelect::High,
            high: HalfSelect::Low,
        },
    ]
}

/// Feasibility of each instruction family for a one-step target.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OneStepEligibility {
    /// Whether some 32-byte `vpshufb` control realizes the target.
    pub pshufb: bool,
    /// Whether some same-source `vperm2i128` immediate realizes the target.
    pub permute2x128: bool,
}

/// Computes one-step feasibility independently of the SAT encoding.
pub fn one_step_eligibility(target: &ByteTags) -> OneStepEligibility {
    let pshufb = target.0.iter().enumerate().all(|(out, tag)| match tag {
        None => true,
        Some(source) => usize::from(*source) / 16 == out / 16,
    });
    let half_matches = |output_base: usize, source_base: Option<usize>| {
        (0..16).all(|offset| {
            target.0[output_base + offset] == source_base.map(|base| IDENTITY_TAGS[base + offset])
        })
    };
    let low_ok = [Some(0), Some(16), None]
        .into_iter()
        .any(|source| half_matches(0, source));
    let high_ok = [Some(0), Some(16), None]
        .into_iter()
        .any(|source| half_matches(16, source));
    OneStepEligibility {
        pshufb,
        permute2x128: low_ok && high_ok,
    }
}

/// Builds the existential one-instruction CNF for the supported language.
///
/// Variable 1 selects `vpshufb`, variable 2 selects `vperm2i128`.  The first
/// clause requires exactly one family; the second enforces at most one; and a
/// unit clause excludes each family whose controls cannot realize `target`.
/// Control feasibility is complete for these two instructions because every
/// `vpshufb` output control is independent and each `vperm2i128` half selector
/// is independent.
///
/// # Errors
///
/// Returns a [`CnfError`] only if the fixed two-variable formula cannot be
/// constructed.
pub fn one_step_formula(target: &ByteTags) -> Result<CnfFormula, CnfError> {
    let pshufb = CnfLit::positive(CnfVar::new(0)?);
    let permute = CnfLit::positive(CnfVar::new(1)?);
    let mut formula = CnfFormula::new(2);
    formula.add_clause(CnfClause::new(vec![pshufb, permute]))?;
    formula.add_clause(CnfClause::new(vec![pshufb.negated(), permute.negated()]))?;
    let eligibility = one_step_eligibility(target);
    if !eligibility.pshufb {
        formula.add_clause(CnfClause::new(vec![pshufb.negated()]))?;
    }
    if !eligibility.permute2x128 {
        formula.add_clause(CnfClause::new(vec![permute.negated()]))?;
    }
    Ok(formula)
}

/// Checked result of a one-step impossibility proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OneStepRefutation {
    /// Formula that was solved and checked.
    pub formula: CnfFormula,
    /// DRAT proof accepted by the independent backward checker.
    pub proof: Vec<DratStep>,
}

/// Produces and independently checks a DRAT refutation for the one-step query.
///
/// # Errors
///
/// Returns [`SimdError`] if construction or checking fails, or if the query is
/// not refuted.
pub fn refute_one_step(target: &ByteTags) -> Result<OneStepRefutation, SimdError> {
    let formula = one_step_formula(target)?;
    let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(&formula) else {
        return Err(SimdError::OneStepNotRefuted);
    };
    if !check_drat_backward(&formula, &proof)? {
        return Err(SimdError::ProofRejected);
    }
    Ok(OneStepRefutation { formula, proof })
}

/// Fail-closed errors from SIMD semantic and proof checks.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SimdError {
    /// An input-provenance tag does not belong to a 32-byte YMM value.
    TagOutOfRange {
        /// Zero-based output-byte position containing the tag.
        byte: usize,
        /// Rejected provenance tag.
        tag: u8,
    },
    /// CNF construction failed.
    Cnf(CnfError),
    /// DRAT checking failed structurally.
    Drat(DratError),
    /// The one-step query was satisfiable or resource-declined.
    OneStepNotRefuted,
    /// The producer returned UNSAT but the independent checker rejected it.
    ProofRejected,
}

impl From<CnfError> for SimdError {
    fn from(value: CnfError) -> Self {
        Self::Cnf(value)
    }
}

impl From<DratError> for SimdError {
    fn from(value: DratError) -> Self {
        Self::Drat(value)
    }
}

#[cfg(test)]
mod tests {
    use axeyum_cnf::{check_drat_backward, parse_drat, write_drat};

    use super::{
        AVX2_BYTES, Avx2Shuffle, ByteTags, byte_reverse_sequence, one_step_eligibility,
        refute_one_step, replay_sequence,
    };

    #[test]
    fn constructed_sequence_reverses_all_distinct_tags() {
        assert_eq!(
            replay_sequence(&byte_reverse_sequence()),
            ByteTags::reversed()
        );
    }

    #[test]
    fn pshufb_is_lane_local_and_high_bit_zeros() {
        let mut controls = [0_u8; AVX2_BYTES];
        controls[0] = 0x1f;
        controls[16] = 0x80;
        let output = Avx2Shuffle::Pshufb(controls).replay(&ByteTags::identity());
        assert_eq!(output.as_array()[0], Some(15));
        assert_eq!(output.as_array()[16], None);
    }

    #[test]
    fn global_reverse_is_ineligible_for_either_one_step_family() {
        let eligibility = one_step_eligibility(&ByteTags::reversed());
        assert!(!eligibility.pshufb);
        assert!(!eligibility.permute2x128);
    }

    #[test]
    fn global_reverse_has_round_tripped_checked_drat_refutation() {
        let certificate = refute_one_step(&ByteTags::reversed()).unwrap();
        let text = write_drat(&certificate.proof);
        let reparsed = parse_drat(&text).unwrap();
        assert_eq!(reparsed, certificate.proof);
        assert!(check_drat_backward(&certificate.formula, &reparsed).unwrap());

        let mut truncated = reparsed;
        truncated.pop();
        assert_ne!(
            check_drat_backward(&certificate.formula, &truncated),
            Ok(true)
        );
    }

    #[test]
    fn target_mutation_breaks_the_constructed_sequence() {
        let mut tags = *ByteTags::reversed().as_array();
        tags[0] = Some(30);
        let changed = ByteTags::new(tags).unwrap();
        assert_ne!(replay_sequence(&byte_reverse_sequence()), changed);
    }

    #[test]
    fn out_of_range_provenance_is_rejected() {
        let mut tags = [None; AVX2_BYTES];
        tags[7] = Some(32);
        assert!(ByteTags::new(tags).is_err());
    }
}
