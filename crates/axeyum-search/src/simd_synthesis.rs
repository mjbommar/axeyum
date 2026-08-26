//! Complete bounded synthesis for a permutation-preserving unary AVX2 subset.
//!
//! Search is over distinct provenance tags, not byte values. Every SAT model
//! is lifted to concrete instruction controls and replayed from the identity.
//! Lossy controls are omitted without losing completeness for permutation
//! targets: a deterministic single-register unary sequence cannot recreate a
//! distinct input tag after duplication or zeroing has discarded it.

use axeyum_cnf::{CnfAssignment, CnfClause, CnfFormula, CnfLit, CnfVar};

use crate::simd::{AVX2_BYTES, Avx2Shuffle, ByteTags, HalfSelect, replay_sequence};

const FAMILIES: usize = 5;

/// Stable ceilings for unary AVX2 synthesis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnaryAvx2SynthesisLimits {
    /// Maximum instruction count.
    pub max_steps: usize,
    /// Maximum generated variables.
    pub max_variables: usize,
    /// Maximum generated clauses.
    pub max_clauses: usize,
}

impl Default for UnaryAvx2SynthesisLimits {
    fn default() -> Self {
        Self {
            max_steps: 32,
            max_variables: 16_000_000,
            max_clauses: 64_000_000,
        }
    }
}

/// Malformed target, resource decline, or rejected SAT model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnaryAvx2SynthesisError {
    /// Target is not a permutation of all 32 input tags.
    NonPermutationTarget,
    /// A stable ceiling was exceeded.
    LimitExceeded {
        /// Resource name.
        resource: &'static str,
        /// First value beyond the ceiling.
        observed: usize,
        /// Configured ceiling.
        limit: usize,
    },
    /// CNF construction/evaluation failed.
    Cnf(String),
    /// A satisfying assignment did not lift and replay.
    InvalidModel(String),
}

#[derive(Debug)]
struct Builder {
    variables: usize,
    clauses: Vec<Vec<(usize, bool)>>,
    limits: UnaryAvx2SynthesisLimits,
}

impl Builder {
    fn variable(&mut self) -> Result<usize, UnaryAvx2SynthesisError> {
        self.variables = self.variables.saturating_add(1);
        if self.variables > self.limits.max_variables {
            return Err(UnaryAvx2SynthesisError::LimitExceeded {
                resource: "variables",
                observed: self.variables,
                limit: self.limits.max_variables,
            });
        }
        Ok(self.variables - 1)
    }

    fn variables(&mut self, count: usize) -> Result<Vec<usize>, UnaryAvx2SynthesisError> {
        (0..count).map(|_| self.variable()).collect()
    }

    fn clause(&mut self, literals: &[(usize, bool)]) -> Result<(), UnaryAvx2SynthesisError> {
        self.clauses.push(literals.to_vec());
        if self.clauses.len() > self.limits.max_clauses {
            return Err(UnaryAvx2SynthesisError::LimitExceeded {
                resource: "clauses",
                observed: self.clauses.len(),
                limit: self.limits.max_clauses,
            });
        }
        Ok(())
    }

    fn at_most_one(&mut self, choices: &[usize]) -> Result<(), UnaryAvx2SynthesisError> {
        for left in 0..choices.len() {
            for right in left + 1..choices.len() {
                self.clause(&[(choices[left], true), (choices[right], true)])?;
            }
        }
        Ok(())
    }

    fn exactly_one(&mut self, choices: &[usize]) -> Result<(), UnaryAvx2SynthesisError> {
        self.clause(
            &choices
                .iter()
                .copied()
                .map(|variable| (variable, false))
                .collect::<Vec<_>>(),
        )?;
        self.at_most_one(choices)
    }

    fn gated_exactly_one(
        &mut self,
        family: usize,
        choices: &[usize],
    ) -> Result<(), UnaryAvx2SynthesisError> {
        let mut at_least = vec![(family, true)];
        at_least.extend(choices.iter().copied().map(|choice| (choice, false)));
        self.clause(&at_least)?;
        for &choice in choices {
            self.clause(&[(choice, true), (family, false)])?;
        }
        self.at_most_one(choices)
    }

    fn finish(self) -> Result<CnfFormula, UnaryAvx2SynthesisError> {
        let mut formula = CnfFormula::new(self.variables);
        for clause in self.clauses {
            let literals = clause
                .into_iter()
                .map(|(variable, negated)| {
                    let literal = CnfLit::positive(CnfVar::new(variable).map_err(|error| {
                        UnaryAvx2SynthesisError::Cnf(format!("variable: {error:?}"))
                    })?);
                    Ok(if negated { literal.negated() } else { literal })
                })
                .collect::<Result<Vec<_>, UnaryAvx2SynthesisError>>()?;
            formula
                .add_clause(CnfClause::new(literals))
                .map_err(|error| UnaryAvx2SynthesisError::Cnf(format!("clause: {error:?}")))?;
        }
        Ok(formula)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct StepLayout {
    families: Vec<usize>,
    pshufb: Vec<Vec<usize>>,
    dwords: Vec<Vec<usize>>,
    qwords: Vec<Vec<usize>>,
    align: Vec<usize>,
    halves: Vec<usize>,
}

/// Exact question “does the target have a sequence of exactly `steps`?”.
///
/// Identity instructions exist in every family, so exact length is equivalent
/// to length at most `steps` for satisfiability and lower-bound purposes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnaryAvx2Encoding {
    formula: CnfFormula,
    target: ByteTags,
    steps: Vec<StepLayout>,
}

impl UnaryAvx2Encoding {
    /// Exact deterministic formula.
    pub fn formula(&self) -> &CnfFormula {
        &self.formula
    }

    /// Lift concrete instruction controls and replay the whole sequence.
    ///
    /// # Errors
    ///
    /// Refuses a wrong-width/non-satisfying model, malformed selector model,
    /// or any sequence whose independent replay differs from the target.
    pub fn lift_model(
        &self,
        model: &CnfAssignment,
    ) -> Result<Vec<Avx2Shuffle>, UnaryAvx2SynthesisError> {
        if !self
            .formula
            .evaluate(model.values())
            .map_err(|error| UnaryAvx2SynthesisError::Cnf(format!("evaluation: {error:?}")))?
        {
            return Err(UnaryAvx2SynthesisError::InvalidModel(
                "model does not satisfy formula".to_owned(),
            ));
        }
        let mut sequence = Vec::with_capacity(self.steps.len());
        for step in &self.steps {
            let family = selected(&step.families, model.values())?;
            let instruction = match family {
                0 => {
                    let mut control = [0_u8; AVX2_BYTES];
                    for (output, choices) in step.pshufb.iter().enumerate() {
                        control[output] = selected_u8(choices, model.values())?;
                    }
                    Avx2Shuffle::Pshufb(control)
                }
                1 => {
                    let mut control = [0_u8; 8];
                    for (output, choices) in step.dwords.iter().enumerate() {
                        control[output] = selected_u8(choices, model.values())?;
                    }
                    Avx2Shuffle::PermuteDwords(control)
                }
                2 => {
                    let mut control = [0_u8; 4];
                    for (output, choices) in step.qwords.iter().enumerate() {
                        control[output] = selected_u8(choices, model.values())?;
                    }
                    Avx2Shuffle::PermuteQwords(control)
                }
                3 => Avx2Shuffle::AlignRight(selected_u8(&step.align, model.values())?),
                4 => match selected(&step.halves, model.values())? {
                    0 => Avx2Shuffle::Permute2x128 {
                        low: HalfSelect::Low,
                        high: HalfSelect::High,
                    },
                    1 => Avx2Shuffle::Permute2x128 {
                        low: HalfSelect::High,
                        high: HalfSelect::Low,
                    },
                    _ => unreachable!("two selectors"),
                },
                _ => unreachable!("five families"),
            };
            sequence.push(instruction);
        }
        if replay_sequence(&sequence) != self.target {
            return Err(UnaryAvx2SynthesisError::InvalidModel(
                "lifted controls do not replay to target".to_owned(),
            ));
        }
        Ok(sequence)
    }
}

fn selected(choices: &[usize], values: &[bool]) -> Result<usize, UnaryAvx2SynthesisError> {
    let selected: Vec<usize> = choices
        .iter()
        .enumerate()
        .filter_map(|(index, &variable)| values[variable].then_some(index))
        .collect();
    if selected.len() != 1 {
        return Err(UnaryAvx2SynthesisError::InvalidModel(format!(
            "expected one selector, found {}",
            selected.len()
        )));
    }
    Ok(selected[0])
}

fn selected_u8(choices: &[usize], values: &[bool]) -> Result<u8, UnaryAvx2SynthesisError> {
    u8::try_from(selected(choices, values)?)
        .map_err(|_| UnaryAvx2SynthesisError::InvalidModel("selector does not fit u8".to_owned()))
}

fn transition(
    builder: &mut Builder,
    selector: usize,
    input: &[Vec<usize>],
    output: &[Vec<usize>],
    mappings: &[(usize, usize)],
) -> Result<(), UnaryAvx2SynthesisError> {
    for &(destination, source) in mappings {
        for tag in 0..AVX2_BYTES {
            builder.clause(&[
                (selector, true),
                (input[source][tag], true),
                (output[destination][tag], false),
            ])?;
        }
    }
    Ok(())
}

fn permutation_controls(
    builder: &mut Builder,
    family: usize,
    outputs: usize,
    sources: usize,
) -> Result<Vec<Vec<usize>>, UnaryAvx2SynthesisError> {
    let mut controls = Vec::with_capacity(outputs);
    for _ in 0..outputs {
        let choices = builder.variables(sources)?;
        builder.gated_exactly_one(family, &choices)?;
        controls.push(choices);
    }
    for (source, _) in controls[0].iter().enumerate() {
        builder.at_most_one(
            &(0..outputs)
                .map(|output| controls[output][source])
                .collect::<Vec<_>>(),
        )?;
    }
    Ok(controls)
}

fn lane_permutation_controls(
    builder: &mut Builder,
    family: usize,
) -> Result<Vec<Vec<usize>>, UnaryAvx2SynthesisError> {
    let mut controls = Vec::with_capacity(AVX2_BYTES);
    for _ in 0..AVX2_BYTES {
        let choices = builder.variables(16)?;
        builder.gated_exactly_one(family, &choices)?;
        controls.push(choices);
    }
    for lane in 0..2 {
        for (source, _) in controls[lane * 16].iter().enumerate() {
            builder.at_most_one(
                &(0..16)
                    .map(|output| controls[lane * 16 + output][source])
                    .collect::<Vec<_>>(),
            )?;
        }
    }
    Ok(controls)
}

fn valid_permutation_target(target: &ByteTags) -> bool {
    let mut seen = [false; AVX2_BYTES];
    for &tag in target.as_array() {
        let Some(tag) = tag.map(usize::from) else {
            return false;
        };
        if tag >= AVX2_BYTES || seen[tag] {
            return false;
        }
        seen[tag] = true;
    }
    true
}

fn encode_step(
    builder: &mut Builder,
    input: &[Vec<usize>],
    output: &[Vec<usize>],
) -> Result<StepLayout, UnaryAvx2SynthesisError> {
    let families = builder.variables(FAMILIES)?;
    builder.exactly_one(&families)?;
    let pshufb = lane_permutation_controls(builder, families[0])?;
    let dwords = permutation_controls(builder, families[1], 8, 8)?;
    let qwords = permutation_controls(builder, families[2], 4, 4)?;
    let align = builder.variables(16)?;
    builder.gated_exactly_one(families[3], &align)?;
    let halves = builder.variables(2)?;
    builder.gated_exactly_one(families[4], &halves)?;

    for (destination, choices) in pshufb.iter().enumerate() {
        let lane = (destination / 16) * 16;
        for (source, &selector) in choices.iter().enumerate() {
            transition(
                builder,
                selector,
                input,
                output,
                &[(destination, lane + source)],
            )?;
        }
    }
    for (destination, choices) in dwords.iter().enumerate() {
        for (source, &selector) in choices.iter().enumerate() {
            let mappings = (0..4)
                .map(|byte| (destination * 4 + byte, source * 4 + byte))
                .collect::<Vec<_>>();
            transition(builder, selector, input, output, &mappings)?;
        }
    }
    for (destination, choices) in qwords.iter().enumerate() {
        for (source, &selector) in choices.iter().enumerate() {
            let mappings = (0..8)
                .map(|byte| (destination * 8 + byte, source * 8 + byte))
                .collect::<Vec<_>>();
            transition(builder, selector, input, output, &mappings)?;
        }
    }
    for (shift, &selector) in align.iter().enumerate() {
        let mappings = (0..AVX2_BYTES)
            .map(|destination| {
                let lane = (destination / 16) * 16;
                (destination, lane + (destination % 16 + shift) % 16)
            })
            .collect::<Vec<_>>();
        transition(builder, selector, input, output, &mappings)?;
    }
    for (swap, &selector) in halves.iter().enumerate() {
        let mappings = (0..AVX2_BYTES)
            .map(|destination| {
                let source = if swap == 0 {
                    destination
                } else {
                    (destination + 16) % 32
                };
                (destination, source)
            })
            .collect::<Vec<_>>();
        transition(builder, selector, input, output, &mappings)?;
    }
    Ok(StepLayout {
        families,
        pshufb,
        dwords,
        qwords,
        align,
        halves,
    })
}

/// Encode complete bounded synthesis for permutation-preserving unary
/// `vpshufb`, `vpermd`, `vpermq`, same-source `vpalignr`, and same-source
/// `vperm2i128`.
///
/// # Errors
///
/// Refuses non-permutation targets and constructions above explicit limits.
pub fn encode_unary_avx2_sequence(
    target: &ByteTags,
    steps: usize,
    limits: UnaryAvx2SynthesisLimits,
) -> Result<UnaryAvx2Encoding, UnaryAvx2SynthesisError> {
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
    let mut builder = Builder {
        variables: 0,
        clauses: Vec::new(),
        limits,
    };
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

    let mut step_layouts = Vec::with_capacity(steps);
    for adjacent in states.windows(2) {
        step_layouts.push(encode_step(&mut builder, &adjacent[0], &adjacent[1])?);
    }
    Ok(UnaryAvx2Encoding {
        formula: builder.finish()?,
        target: *target,
        steps: step_layouts,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_cnf::{
        ProofSolveOutcome, SatResult, solve_with_drat_proof, solve_with_rustsat_batsat,
    };

    #[test]
    fn global_reverse_has_checked_one_step_refutation_and_lifted_two_step_model() {
        let target = ByteTags::reversed();
        let one =
            encode_unary_avx2_sequence(&target, 1, UnaryAvx2SynthesisLimits::default()).unwrap();
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(one.formula()) else {
            panic!("global reversal is impossible in one supported instruction");
        };
        assert_eq!(
            axeyum_cnf::check_drat_backward(one.formula(), &proof),
            Ok(true)
        );

        let two =
            encode_unary_avx2_sequence(&target, 2, UnaryAvx2SynthesisLimits::default()).unwrap();
        let SatResult::Sat(model) = solve_with_rustsat_batsat(two.formula()).unwrap() else {
            panic!("global reversal has a two-instruction sequence");
        };
        let sequence = two.lift_model(&model).unwrap();
        assert_eq!(sequence.len(), 2);
        assert_eq!(replay_sequence(&sequence), target);
    }

    #[test]
    fn dword_reverse_lifts_as_one_instruction() {
        let target =
            Avx2Shuffle::PermuteDwords([7, 6, 5, 4, 3, 2, 1, 0]).replay(&ByteTags::identity());
        let encoding =
            encode_unary_avx2_sequence(&target, 1, UnaryAvx2SynthesisLimits::default()).unwrap();
        let SatResult::Sat(model) = solve_with_rustsat_batsat(encoding.formula()).unwrap() else {
            panic!("dword reversal is one vpermd");
        };
        assert_eq!(
            replay_sequence(&encoding.lift_model(&model).unwrap()),
            target
        );
    }

    #[test]
    fn zeroing_or_duplicate_target_is_not_admitted() {
        let mut tags = *ByteTags::identity().as_array();
        tags[0] = None;
        let zero = ByteTags::new(tags).unwrap();
        assert_eq!(
            encode_unary_avx2_sequence(&zero, 1, UnaryAvx2SynthesisLimits::default()),
            Err(UnaryAvx2SynthesisError::NonPermutationTarget)
        );
    }
}
