//! Exact byte-tag semantics and proof-carrying lower bounds for a small SIMD
//! shuffle languages.
//!
//! This module intentionally models a named subset, rather than pretending to
//! cover an entire ISA. Tags record provenance (`Some(input_byte)`) or an
//! instruction-produced zero (`None`), so exhaustive replay does not depend
//! on concrete test bytes accidentally being equal. The original two-family
//! calibration remains below; generic multi-step synthesis over five
//! permutation-preserving unary families lives in [`crate::simd_synthesis`].

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
    /// `vpermd`: each output dword selects one source dword; bytes retain
    /// their offset inside the selected dword.
    PermuteDwords([u8; 8]),
    /// `vpermq`: each output qword selects one source qword; bytes retain
    /// their offset inside the selected qword.
    PermuteQwords([u8; 4]),
    /// Same-source `vpalignr`: extract from two concatenated copies of each
    /// 128-bit lane and zero-fill after the concatenation is exhausted.
    AlignRight(u8),
}

/// One of the four nonzero half selections of two-source `vperm2i128`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryHalfSelect {
    /// Low 128-bit lane of the first source.
    FirstLow,
    /// High 128-bit lane of the first source.
    FirstHigh,
    /// Low 128-bit lane of the second source.
    SecondLow,
    /// High 128-bit lane of the second source.
    SecondHigh,
}

/// Element width for lane-local AVX2 unpack operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnpackWidth {
    /// `vpunpcklbw` / `vpunpckhbw`.
    Bytes,
    /// `vpunpcklwd` / `vpunpckhwd`.
    Words,
    /// `vpunpckldq` / `vpunpckhdq`.
    Dwords,
    /// `vpunpcklqdq` / `vpunpckhqdq`.
    Qwords,
}

impl UnpackWidth {
    fn bytes(self) -> usize {
        match self {
            Self::Bytes => 1,
            Self::Words => 2,
            Self::Dwords => 4,
            Self::Qwords => 8,
        }
    }
}

/// One SSA instruction in the modeled multi-source AVX2 shuffle language.
///
/// Value zero is the original input register. Instruction `i` produces value
/// `i + 1`, and every source index must refer to an earlier value. The unary
/// variant retains the complete semantics already exposed by [`Avx2Shuffle`];
/// synthesis layers may justify and document narrower control sets separately.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Avx2ProgramInstruction {
    /// Apply an existing unary instruction to one earlier value.
    Unary {
        /// Earlier SSA value.
        source: usize,
        /// Unary operation and control.
        operation: Avx2Shuffle,
    },
    /// Two-source lane-local `vpalignr`; each lane is extracted from
    /// `second || first`, with `second` supplying the low half of the
    /// conceptual concatenation.
    AlignRight {
        /// First source operand, supplying the high half of each concatenation.
        first: usize,
        /// Second source operand, supplying the low half of each concatenation.
        second: usize,
        /// Byte shift, restricted to 0 through 16 by program validation.
        immediate: u8,
    },
    /// Two-source `vperm2i128` without its zeroing controls.
    Permute2x128 {
        /// First source operand.
        first: usize,
        /// Second source operand.
        second: usize,
        /// Source half for destination bytes 0 through 15.
        low: BinaryHalfSelect,
        /// Source half for destination bytes 16 through 31.
        high: BinaryHalfSelect,
    },
    /// Lane-local low or high unpack at byte/word/dword/qword granularity.
    Unpack {
        /// First source operand, emitted first in each pair.
        first: usize,
        /// Second source operand, emitted second in each pair.
        second: usize,
        /// Element width.
        width: UnpackWidth,
        /// Select the high half of each 128-bit lane instead of the low half.
        high: bool,
    },
    /// `vpblendd`: each immediate bit selects a dword from the second source
    /// when set and the first source when clear.
    BlendDwords {
        /// First source operand.
        first: usize,
        /// Second source operand.
        second: usize,
        /// One selection bit per destination dword.
        mask: u8,
    },
}

impl Avx2ProgramInstruction {
    fn sources(&self) -> (usize, Option<usize>) {
        match self {
            Self::Unary { source, .. } => (*source, None),
            Self::AlignRight { first, second, .. }
            | Self::Permute2x128 { first, second, .. }
            | Self::Unpack { first, second, .. }
            | Self::BlendDwords { first, second, .. } => (*first, Some(*second)),
        }
    }

    fn replay(&self, values: &[ByteTags]) -> ByteTags {
        match self {
            Self::Unary { source, operation } => operation.replay(&values[*source]),
            Self::AlignRight {
                first,
                second,
                immediate,
            } => ByteTags(std::array::from_fn(|out| {
                let lane = (out / 16) * 16;
                let index = out % 16 + usize::from(*immediate);
                if index < 16 {
                    values[*second].0[lane + index]
                } else {
                    values[*first].0[lane + index - 16]
                }
            })),
            Self::Permute2x128 {
                first,
                second,
                low,
                high,
            } => ByteTags(std::array::from_fn(|out| {
                let selection = if out < 16 { *low } else { *high };
                let offset = out % 16;
                let (source, base) = match selection {
                    BinaryHalfSelect::FirstLow => (*first, 0),
                    BinaryHalfSelect::FirstHigh => (*first, 16),
                    BinaryHalfSelect::SecondLow => (*second, 0),
                    BinaryHalfSelect::SecondHigh => (*second, 16),
                };
                values[source].0[base + offset]
            })),
            Self::Unpack {
                first,
                second,
                width,
                high,
            } => {
                let element_bytes = width.bytes();
                ByteTags(std::array::from_fn(|out| {
                    let lane = (out / 16) * 16;
                    let output_in_lane = out % 16;
                    let output_element = output_in_lane / element_bytes;
                    let byte = output_in_lane % element_bytes;
                    let source = if output_element % 2 == 0 {
                        *first
                    } else {
                        *second
                    };
                    let input_element =
                        output_element / 2 + if *high { 8 / element_bytes } else { 0 };
                    values[source].0[lane + input_element * element_bytes + byte]
                }))
            }
            Self::BlendDwords {
                first,
                second,
                mask,
            } => ByteTags(std::array::from_fn(|out| {
                let dword = out / 4;
                let source = if mask & (1 << dword) == 0 {
                    *first
                } else {
                    *second
                };
                values[source].0[out]
            })),
        }
    }
}

/// Replay an SSA multi-source program from one identity input register.
///
/// # Errors
///
/// Rejects an empty program, a forward/out-of-range source, or a two-source
/// align immediate outside the retained nonzero range 0 through 16.
pub fn replay_program(program: &[Avx2ProgramInstruction]) -> Result<ByteTags, SimdError> {
    if program.is_empty() {
        return Err(SimdError::EmptyProgram);
    }
    let mut values = vec![ByteTags::identity()];
    for (instruction, step) in program.iter().enumerate() {
        let available = instruction + 1;
        let (first, second) = step.sources();
        for source in [Some(first), second].into_iter().flatten() {
            if source >= available {
                return Err(SimdError::ProgramSourceOutOfRange {
                    instruction,
                    source,
                    available,
                });
            }
        }
        if let Avx2ProgramInstruction::AlignRight { immediate, .. } = step
            && *immediate > 16
        {
            return Err(SimdError::AlignImmediateOutOfRange {
                instruction,
                immediate: *immediate,
            });
        }
        values.push(step.replay(&values));
    }
    values.last().copied().ok_or(SimdError::EmptyProgram)
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
            Self::PermuteDwords(control) => ByteTags(std::array::from_fn(|out| {
                let output_dword = out / 4;
                let byte = out % 4;
                let source_dword = usize::from(control[output_dword] & 7);
                input.0[source_dword * 4 + byte]
            })),
            Self::PermuteQwords(control) => ByteTags(std::array::from_fn(|out| {
                let output_qword = out / 8;
                let byte = out % 8;
                let source_qword = usize::from(control[output_qword] & 3);
                input.0[source_qword * 8 + byte]
            })),
            Self::AlignRight(immediate) => ByteTags(std::array::from_fn(|out| {
                let shift = usize::from(*immediate);
                let byte = out % 16;
                let concatenated = byte + shift;
                if concatenated < 32 {
                    let lane = (out / 16) * 16;
                    input.0[lane + concatenated % 16]
                } else {
                    None
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
    /// A multi-source program has no instruction and therefore no result.
    EmptyProgram,
    /// An SSA instruction refers to its own or a future value.
    ProgramSourceOutOfRange {
        /// Zero-based instruction position.
        instruction: usize,
        /// Rejected value index.
        source: usize,
        /// Number of values available before this instruction.
        available: usize,
    },
    /// The nonzero permutation language retains only align immediates 0..=16.
    AlignImmediateOutOfRange {
        /// Zero-based instruction position.
        instruction: usize,
        /// Rejected immediate.
        immediate: u8,
    },
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
        AVX2_BYTES, Avx2ProgramInstruction, Avx2Shuffle, BinaryHalfSelect, ByteTags, SimdError,
        UnpackWidth, byte_reverse_sequence, one_step_eligibility, refute_one_step, replay_program,
        replay_sequence,
    };

    #[test]
    fn constructed_sequence_reverses_all_distinct_tags() {
        assert_eq!(
            replay_sequence(&byte_reverse_sequence()),
            ByteTags::reversed()
        );
    }

    fn lane_reverse() -> Avx2Shuffle {
        Avx2Shuffle::Pshufb([
            15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8, 7,
            6, 5, 4, 3, 2, 1, 0,
        ])
    }

    #[test]
    fn multi_source_program_replays_operand_order_and_ssa_values() {
        let prefix = Avx2ProgramInstruction::Unary {
            source: 0,
            operation: lane_reverse(),
        };
        let aligned = replay_program(&[
            prefix.clone(),
            Avx2ProgramInstruction::AlignRight {
                first: 1,
                second: 0,
                immediate: 12,
            },
        ])
        .unwrap();
        assert_eq!(
            &aligned.as_array()[..16],
            &[
                Some(12),
                Some(13),
                Some(14),
                Some(15),
                Some(15),
                Some(14),
                Some(13),
                Some(12),
                Some(11),
                Some(10),
                Some(9),
                Some(8),
                Some(7),
                Some(6),
                Some(5),
                Some(4),
            ]
        );

        let permuted = replay_program(&[
            prefix.clone(),
            Avx2ProgramInstruction::Permute2x128 {
                first: 0,
                second: 1,
                low: BinaryHalfSelect::SecondHigh,
                high: BinaryHalfSelect::FirstLow,
            },
        ])
        .unwrap();
        assert_eq!(permuted.as_array()[0], Some(31));
        assert_eq!(permuted.as_array()[15], Some(16));
        assert_eq!(permuted.as_array()[16], Some(0));
        assert_eq!(permuted.as_array()[31], Some(15));

        let unpacked = replay_program(&[
            prefix.clone(),
            Avx2ProgramInstruction::Unpack {
                first: 0,
                second: 1,
                width: UnpackWidth::Bytes,
                high: false,
            },
        ])
        .unwrap();
        assert_eq!(
            &unpacked.as_array()[..8],
            &[
                Some(0),
                Some(15),
                Some(1),
                Some(14),
                Some(2),
                Some(13),
                Some(3),
                Some(12),
            ]
        );

        let blended = replay_program(&[
            prefix,
            Avx2ProgramInstruction::BlendDwords {
                first: 0,
                second: 1,
                mask: 0b0000_0010,
            },
        ])
        .unwrap();
        assert_eq!(
            &blended.as_array()[..4],
            &[Some(0), Some(1), Some(2), Some(3)]
        );
        assert_eq!(
            &blended.as_array()[4..8],
            &[Some(11), Some(10), Some(9), Some(8)]
        );
    }

    #[test]
    fn multi_source_program_validation_fails_closed() {
        assert_eq!(replay_program(&[]), Err(SimdError::EmptyProgram));
        assert!(matches!(
            replay_program(&[Avx2ProgramInstruction::Unary {
                source: 1,
                operation: lane_reverse(),
            }]),
            Err(SimdError::ProgramSourceOutOfRange {
                instruction: 0,
                source: 1,
                available: 1,
            })
        ));
        assert!(matches!(
            replay_program(&[Avx2ProgramInstruction::AlignRight {
                first: 0,
                second: 0,
                immediate: 17,
            }]),
            Err(SimdError::AlignImmediateOutOfRange {
                instruction: 0,
                immediate: 17,
            })
        ));
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

    #[test]
    fn word_permutations_preserve_offsets_inside_selected_words() {
        let dwords =
            Avx2Shuffle::PermuteDwords([7, 6, 5, 4, 3, 2, 1, 0]).replay(&ByteTags::identity());
        assert_eq!(dwords.as_array()[0], Some(28));
        assert_eq!(dwords.as_array()[3], Some(31));
        assert_eq!(dwords.as_array()[28], Some(0));

        let qwords = Avx2Shuffle::PermuteQwords([3, 2, 1, 0]).replay(&ByteTags::identity());
        assert_eq!(qwords.as_array()[0], Some(24));
        assert_eq!(qwords.as_array()[7], Some(31));
        assert_eq!(qwords.as_array()[24], Some(0));
    }

    #[test]
    fn same_source_align_rotates_each_128_bit_lane() {
        let aligned = Avx2Shuffle::AlignRight(5).replay(&ByteTags::identity());
        assert_eq!(aligned.as_array()[0], Some(5));
        assert_eq!(aligned.as_array()[11], Some(0));
        assert_eq!(aligned.as_array()[16], Some(21));
        assert_eq!(aligned.as_array()[27], Some(16));

        let partial = Avx2Shuffle::AlignRight(17).replay(&ByteTags::identity());
        assert_eq!(partial.as_array()[0], Some(1));
        assert_eq!(partial.as_array()[14], Some(15));
        assert_eq!(partial.as_array()[15], None);
        assert_eq!(
            Avx2Shuffle::AlignRight(32)
                .replay(&ByteTags::identity())
                .as_array(),
            &[None; 32]
        );
    }
}
