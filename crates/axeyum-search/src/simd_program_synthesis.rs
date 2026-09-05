//! Complete bounded synthesis for a multi-source AVX2 shuffle language.
//!
//! Value zero is the original YMM input and every instruction appends one SSA
//! value. Source selectors can choose the input or any earlier result. Unlike
//! the unary encoder, intermediate values may duplicate or discard tags:
//! separate live branches can later be recombined by an unpack, blend, align,
//! or two-source half permutation. SAT models are lifted to typed programs and
//! replayed through [`crate::simd::replay_program`].

use axeyum_cnf::{CnfAssignment, CnfFormula};

use crate::simd::{
    AVX2_BYTES, Avx2ProgramInstruction, Avx2Shuffle, BinaryHalfSelect, ByteTags, UnpackWidth,
    replay_program,
};
use crate::simd_synthesis::{
    Builder, UnaryAvx2SynthesisError, UnaryAvx2SynthesisLimits, selected, selected_u8,
    valid_permutation_target,
};

const FAMILIES: usize = 14;

#[derive(Debug, Clone, PartialEq, Eq)]
struct StepLayout {
    families: Vec<usize>,
    first_sources: Vec<usize>,
    second_sources: Vec<usize>,
    pshufb: Vec<Vec<usize>>,
    dwords: Vec<Vec<usize>>,
    qwords: Vec<Vec<usize>>,
    align: Vec<usize>,
    low_half: Vec<usize>,
    high_half: Vec<usize>,
    blend_dwords: Vec<Vec<usize>>,
}

impl StepLayout {
    fn lift(&self, values: &[bool]) -> Result<Avx2ProgramInstruction, UnaryAvx2SynthesisError> {
        let family = selected(&self.families, values)?;
        let first = selected(&self.first_sources, values)?;
        let second = selected(&self.second_sources, values)?;
        Ok(match family {
            0 => {
                let mut control = [0_u8; AVX2_BYTES];
                for (output, choices) in self.pshufb.iter().enumerate() {
                    control[output] = selected_u8(choices, values)?;
                }
                Avx2ProgramInstruction::Unary {
                    source: first,
                    operation: Avx2Shuffle::Pshufb(control),
                }
            }
            1 => {
                let mut control = [0_u8; 8];
                for (output, choices) in self.dwords.iter().enumerate() {
                    control[output] = selected_u8(choices, values)?;
                }
                Avx2ProgramInstruction::Unary {
                    source: first,
                    operation: Avx2Shuffle::PermuteDwords(control),
                }
            }
            2 => {
                let mut control = [0_u8; 4];
                for (output, choices) in self.qwords.iter().enumerate() {
                    control[output] = selected_u8(choices, values)?;
                }
                Avx2ProgramInstruction::Unary {
                    source: first,
                    operation: Avx2Shuffle::PermuteQwords(control),
                }
            }
            3 => Avx2ProgramInstruction::AlignRight {
                first,
                second,
                immediate: selected_u8(&self.align, values)?,
            },
            4 => Avx2ProgramInstruction::Permute2x128 {
                first,
                second,
                low: half_selection(selected(&self.low_half, values)?),
                high: half_selection(selected(&self.high_half, values)?),
            },
            5..=12 => {
                let unpack = family - 5;
                Avx2ProgramInstruction::Unpack {
                    first,
                    second,
                    width: match unpack / 2 {
                        0 => UnpackWidth::Bytes,
                        1 => UnpackWidth::Words,
                        2 => UnpackWidth::Dwords,
                        3 => UnpackWidth::Qwords,
                        _ => unreachable!("eight unpack families"),
                    },
                    high: unpack % 2 == 1,
                }
            }
            13 => {
                let mut mask = 0_u8;
                for (dword, choices) in self.blend_dwords.iter().enumerate() {
                    if selected(choices, values)? == 1 {
                        mask |= 1 << dword;
                    }
                }
                Avx2ProgramInstruction::BlendDwords {
                    first,
                    second,
                    mask,
                }
            }
            _ => unreachable!("fourteen families"),
        })
    }
}

/// Exact multi-source synthesis formula and the controls required for lifting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MultiSourceAvx2Encoding {
    formula: CnfFormula,
    target: ByteTags,
    steps: Vec<StepLayout>,
}

impl MultiSourceAvx2Encoding {
    /// Deterministic complete bounded formula.
    pub fn formula(&self) -> &CnfFormula {
        &self.formula
    }

    /// Lift a satisfying assignment and independently replay the typed program.
    ///
    /// # Errors
    ///
    /// Refuses a non-satisfying/wrong-width assignment, malformed selectors,
    /// invalid SSA sources, or a lifted program that misses the original target.
    pub fn lift_model(
        &self,
        model: &CnfAssignment,
    ) -> Result<Vec<Avx2ProgramInstruction>, UnaryAvx2SynthesisError> {
        if !self
            .formula
            .evaluate(model.values())
            .map_err(|error| UnaryAvx2SynthesisError::Cnf(format!("evaluation: {error:?}")))?
        {
            return Err(UnaryAvx2SynthesisError::InvalidModel(
                "model does not satisfy formula".to_owned(),
            ));
        }
        let mut program = Vec::with_capacity(self.steps.len());
        for step in &self.steps {
            program.push(step.lift(model.values())?);
        }
        let replayed = if program.is_empty() {
            ByteTags::identity()
        } else {
            replay_program(&program).map_err(|error| {
                UnaryAvx2SynthesisError::InvalidModel(format!("program replay: {error:?}"))
            })?
        };
        if replayed != self.target {
            return Err(UnaryAvx2SynthesisError::InvalidModel(
                "lifted program does not replay to target".to_owned(),
            ));
        }
        Ok(program)
    }
}

fn half_selection(index: usize) -> BinaryHalfSelect {
    match index {
        0 => BinaryHalfSelect::FirstLow,
        1 => BinaryHalfSelect::FirstHigh,
        2 => BinaryHalfSelect::SecondLow,
        3 => BinaryHalfSelect::SecondHigh,
        _ => unreachable!("four half choices"),
    }
}

fn controls(
    builder: &mut Builder,
    family: usize,
    outputs: usize,
    choices: usize,
) -> Result<Vec<Vec<usize>>, UnaryAvx2SynthesisError> {
    (0..outputs)
        .map(|_| {
            let selectors = builder.variables(choices)?;
            builder.gated_exactly_one(family, &selectors)?;
            Ok(selectors)
        })
        .collect()
}

fn guarded_transition(
    builder: &mut Builder,
    guards: &[usize],
    input: &[Vec<usize>],
    output: &[Vec<usize>],
    mappings: &[(usize, usize)],
) -> Result<(), UnaryAvx2SynthesisError> {
    for &(destination, source) in mappings {
        for tag in 0..AVX2_BYTES {
            let mut clause = guards
                .iter()
                .copied()
                .map(|guard| (guard, true))
                .collect::<Vec<_>>();
            clause.push((input[source][tag], true));
            clause.push((output[destination][tag], false));
            builder.clause(&clause)?;
        }
    }
    Ok(())
}

fn source_transition(
    builder: &mut Builder,
    guards: &[usize],
    source_selectors: &[usize],
    states: &[Vec<Vec<usize>>],
    output: &[Vec<usize>],
    mappings: &[(usize, usize)],
) -> Result<(), UnaryAvx2SynthesisError> {
    for (source, &selector) in source_selectors.iter().enumerate() {
        let mut source_guards = guards.to_vec();
        source_guards.push(selector);
        guarded_transition(builder, &source_guards, &states[source], output, mappings)?;
    }
    Ok(())
}

fn unpack_mappings(width: usize, high: bool, operand: usize) -> Vec<(usize, usize)> {
    (0..AVX2_BYTES)
        .filter_map(|destination| {
            let output_in_lane = destination % 16;
            let output_element = output_in_lane / width;
            (output_element % 2 == operand).then(|| {
                let lane = (destination / 16) * 16;
                let byte = output_in_lane % width;
                let source_element = output_element / 2 + if high { 8 / width } else { 0 };
                (destination, lane + source_element * width + byte)
            })
        })
        .collect()
}

#[allow(clippy::too_many_lines)] // one allocation/transition order is part of deterministic CNF
fn encode_step(
    builder: &mut Builder,
    states: &[Vec<Vec<usize>>],
    output: &[Vec<usize>],
) -> Result<StepLayout, UnaryAvx2SynthesisError> {
    let available = states.len();
    let families = builder.variables(FAMILIES)?;
    builder.exactly_one(&families)?;
    let first_sources = builder.variables(available)?;
    let second_sources = builder.variables(available)?;
    builder.exactly_one(&first_sources)?;
    builder.exactly_one(&second_sources)?;
    let pshufb = controls(builder, families[0], AVX2_BYTES, 16)?;
    let dwords = controls(builder, families[1], 8, 8)?;
    let qwords = controls(builder, families[2], 4, 4)?;
    let align = controls(builder, families[3], 1, 17)?.remove(0);
    let low_half = controls(builder, families[4], 1, 4)?.remove(0);
    let high_half = controls(builder, families[4], 1, 4)?.remove(0);
    let blend_dwords = controls(builder, families[13], 8, 2)?;

    for (destination, choices) in pshufb.iter().enumerate() {
        let lane = (destination / 16) * 16;
        for (source_byte, &control) in choices.iter().enumerate() {
            source_transition(
                builder,
                &[families[0], control],
                &first_sources,
                states,
                output,
                &[(destination, lane + source_byte)],
            )?;
        }
    }
    for (destination, choices) in dwords.iter().enumerate() {
        for (source_dword, &control) in choices.iter().enumerate() {
            source_transition(
                builder,
                &[families[1], control],
                &first_sources,
                states,
                output,
                &(0..4)
                    .map(|byte| (destination * 4 + byte, source_dword * 4 + byte))
                    .collect::<Vec<_>>(),
            )?;
        }
    }
    for (destination, choices) in qwords.iter().enumerate() {
        for (source_qword, &control) in choices.iter().enumerate() {
            source_transition(
                builder,
                &[families[2], control],
                &first_sources,
                states,
                output,
                &(0..8)
                    .map(|byte| (destination * 8 + byte, source_qword * 8 + byte))
                    .collect::<Vec<_>>(),
            )?;
        }
    }
    for (shift, &control) in align.iter().enumerate() {
        let first = (0..AVX2_BYTES)
            .filter_map(|destination| {
                let index = destination % 16 + shift;
                (index >= 16).then(|| {
                    let lane = (destination / 16) * 16;
                    (destination, lane + index - 16)
                })
            })
            .collect::<Vec<_>>();
        let second = (0..AVX2_BYTES)
            .filter_map(|destination| {
                let index = destination % 16 + shift;
                (index < 16).then_some((destination, (destination / 16) * 16 + index))
            })
            .collect::<Vec<_>>();
        source_transition(
            builder,
            &[families[3], control],
            &first_sources,
            states,
            output,
            &first,
        )?;
        source_transition(
            builder,
            &[families[3], control],
            &second_sources,
            states,
            output,
            &second,
        )?;
    }
    for (destination_half, choices) in [&low_half, &high_half].into_iter().enumerate() {
        for (choice, &control) in choices.iter().enumerate() {
            let source_selectors = if choice < 2 {
                &first_sources
            } else {
                &second_sources
            };
            let source_half = choice % 2;
            source_transition(
                builder,
                &[families[4], control],
                source_selectors,
                states,
                output,
                &(0..16)
                    .map(|byte| (destination_half * 16 + byte, source_half * 16 + byte))
                    .collect::<Vec<_>>(),
            )?;
        }
    }
    for (unpack, &family) in families[5..13].iter().enumerate() {
        let width = 1 << (unpack / 2);
        let high = unpack % 2 == 1;
        source_transition(
            builder,
            &[family],
            &first_sources,
            states,
            output,
            &unpack_mappings(width, high, 0),
        )?;
        source_transition(
            builder,
            &[family],
            &second_sources,
            states,
            output,
            &unpack_mappings(width, high, 1),
        )?;
    }
    for (dword, choices) in blend_dwords.iter().enumerate() {
        for (operand, &control) in choices.iter().enumerate() {
            source_transition(
                builder,
                &[families[13], control],
                if operand == 0 {
                    &first_sources
                } else {
                    &second_sources
                },
                states,
                output,
                &(0..4)
                    .map(|byte| (dword * 4 + byte, dword * 4 + byte))
                    .collect::<Vec<_>>(),
            )?;
        }
    }
    Ok(StepLayout {
        families,
        first_sources,
        second_sources,
        pshufb,
        dwords,
        qwords,
        align,
        low_half,
        high_half,
        blend_dwords,
    })
}

/// Encode exact-length multi-source AVX2 synthesis.
///
/// The language contains arbitrary lane-local `vpshufb`, dword and qword
/// permutes, two-source `vpalignr` shifts 0..=16, two-source nonzero
/// `vperm2i128`, all low/high byte/word/dword/qword unpacks, and `vpblendd`.
/// The language contains a `vpshufb` identity instance, so any shorter program
/// can be padded and exact length is equisatisfiable with length at most
/// `steps`.
///
/// # Errors
///
/// Refuses non-permutation targets and constructions above explicit limits.
pub fn encode_multisource_avx2_sequence(
    target: &ByteTags,
    steps: usize,
    limits: UnaryAvx2SynthesisLimits,
) -> Result<MultiSourceAvx2Encoding, UnaryAvx2SynthesisError> {
    if !valid_permutation_target(target) {
        return Err(UnaryAvx2SynthesisError::NonPermutationTarget);
    }
    if steps > limits.max_steps {
        return Err(UnaryAvx2SynthesisError::LimitExceeded {
            resource: "steps",
            observed: steps,
            limit: limits.max_steps,
        });
    }
    let mut builder = Builder::new(limits);
    let mut states = Vec::with_capacity(steps + 1);
    for _ in 0..=steps {
        let mut state = Vec::with_capacity(AVX2_BYTES);
        for _ in 0..AVX2_BYTES {
            let tags = builder.variables(AVX2_BYTES)?;
            builder.exactly_one(&tags)?;
            state.push(tags);
        }
        states.push(state);
    }
    for (byte, &target_tag) in target.as_array().iter().enumerate() {
        builder.clause(&[(states[0][byte][byte], false)])?;
        let tag = usize::from(target_tag.ok_or(UnaryAvx2SynthesisError::NonPermutationTarget)?);
        builder.clause(&[(states[steps][byte][tag], false)])?;
    }
    let mut layouts = Vec::with_capacity(steps);
    for step in 0..steps {
        let layout = encode_step(&mut builder, &states[..=step], &states[step + 1])?;
        layouts.push(layout);
    }
    Ok(MultiSourceAvx2Encoding {
        formula: builder.finish()?,
        target: *target,
        steps: layouts,
    })
}

#[cfg(test)]
mod tests {
    use axeyum_cnf::{
        CnfClause, CnfLit, CnfVar, ProofSolveOutcome, SatResult, check_drat_backward,
        solve_with_drat_proof,
    };

    use super::*;

    #[test]
    fn global_reverse_keeps_checked_one_step_lower_and_lifted_two_step_upper() {
        let lower = encode_multisource_avx2_sequence(
            &ByteTags::reversed(),
            1,
            UnaryAvx2SynthesisLimits::default(),
        )
        .unwrap();
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(lower.formula()) else {
            panic!("no one AVX2 family in the modeled language globally reverses bytes");
        };
        assert_eq!(check_drat_backward(lower.formula(), &proof), Ok(true));

        let upper = encode_multisource_avx2_sequence(
            &ByteTags::reversed(),
            2,
            UnaryAvx2SynthesisLimits::default(),
        )
        .unwrap();
        let SatResult::Sat(model) = axeyum_cnf::solve_with_native_core(upper.formula()).unwrap()
        else {
            panic!("two unary instructions remain available in the multi-source language");
        };
        let program = upper.lift_model(&model).unwrap();
        assert_eq!(replay_program(&program), Ok(ByteTags::reversed()));
    }

    #[test]
    fn constructed_unpack_program_can_be_pinned_and_lifted() {
        let target = replay_program(&[
            Avx2ProgramInstruction::Unary {
                source: 0,
                operation: Avx2Shuffle::Pshufb([
                    15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10,
                    9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
                ]),
            },
            Avx2ProgramInstruction::Unpack {
                first: 0,
                second: 1,
                width: UnpackWidth::Bytes,
                high: false,
            },
        ])
        .unwrap();
        let encoding =
            encode_multisource_avx2_sequence(&target, 2, UnaryAvx2SynthesisLimits::default())
                .unwrap();
        let mut pinned = encoding.formula().clone();
        let unit = |variable: usize, value: bool| {
            let literal = CnfLit::positive(CnfVar::new(variable).unwrap());
            CnfClause::new(vec![if value { literal } else { literal.negated() }])
        };
        for (family, &variable) in encoding.steps[0].families.iter().enumerate() {
            pinned.add_clause(unit(variable, family == 0)).unwrap();
        }
        pinned
            .add_clause(unit(encoding.steps[0].first_sources[0], true))
            .unwrap();
        for (output, choices) in encoding.steps[0].pshufb.iter().enumerate() {
            for (source, &variable) in choices.iter().enumerate() {
                pinned
                    .add_clause(unit(variable, source == 15 - output % 16))
                    .unwrap();
            }
        }
        for (family, &variable) in encoding.steps[1].families.iter().enumerate() {
            pinned.add_clause(unit(variable, family == 5)).unwrap();
        }
        for (source, &variable) in encoding.steps[1].first_sources.iter().enumerate() {
            pinned.add_clause(unit(variable, source == 0)).unwrap();
        }
        for (source, &variable) in encoding.steps[1].second_sources.iter().enumerate() {
            pinned.add_clause(unit(variable, source == 1)).unwrap();
        }
        let SatResult::Sat(model) = axeyum_cnf::solve_with_native_core(&pinned).unwrap() else {
            panic!("pinned two-source unpack construction must be satisfiable");
        };
        let program = encoding.lift_model(&model).unwrap();
        assert_eq!(replay_program(&program), Ok(target));
        assert!(matches!(
            program[1],
            Avx2ProgramInstruction::Unpack {
                first: 0,
                second: 1,
                width: UnpackWidth::Bytes,
                high: false,
            }
        ));
    }
}
