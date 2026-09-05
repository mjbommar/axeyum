//! Complete bounded synthesis for a permutation-preserving unary AVX2 subset.
//!
//! Search is over distinct provenance tags, not byte values. Every SAT model
//! is lifted to concrete instruction controls and replayed from the identity.
//! Lossy controls are omitted without losing completeness for permutation
//! targets: a deterministic single-register unary sequence cannot recreate a
//! distinct input tag after duplication or zeroing has discarded it.

use axeyum_cnf::{
    CnfAssignment, CnfClause, CnfFormula, CnfLit, CnfVar, WeightedAtMostLimits,
    encode_weighted_at_most,
};

use crate::simd::{AVX2_BYTES, Avx2Shuffle, ByteTags, HalfSelect, replay_sequence};

const FAMILIES: usize = 5;
const WEIGHTED_FAMILIES: usize = 6;

/// Positive integer costs for the five real instruction families.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnaryAvx2InstructionCosts {
    /// Cost of `vpshufb`.
    pub pshufb: u64,
    /// Cost of `vpermd`.
    pub permute_dwords: u64,
    /// Cost of `vpermq`.
    pub permute_qwords: u64,
    /// Cost of same-source `vpalignr`.
    pub align_right: u64,
    /// Cost of same-source `vperm2i128`.
    pub permute_2x128: u64,
}

impl UnaryAvx2InstructionCosts {
    fn as_array(self) -> [u64; FAMILIES] {
        [
            self.pshufb,
            self.permute_dwords,
            self.permute_qwords,
            self.align_right,
            self.permute_2x128,
        ]
    }

    /// Sum the configured costs of a lifted concrete sequence.
    pub fn sequence_cost(self, sequence: &[Avx2Shuffle]) -> u64 {
        sequence.iter().fold(0_u64, |total, instruction| {
            total.saturating_add(match instruction {
                Avx2Shuffle::Pshufb(_) => self.pshufb,
                Avx2Shuffle::PermuteDwords(_) => self.permute_dwords,
                Avx2Shuffle::PermuteQwords(_) => self.permute_qwords,
                Avx2Shuffle::AlignRight(_) => self.align_right,
                Avx2Shuffle::Permute2x128 { .. } => self.permute_2x128,
            })
        })
    }
}

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
    /// Weighted search requires every real instruction to have positive cost.
    ZeroInstructionCost,
    /// Weighted-CNF composition failed.
    Weighted(String),
}

#[derive(Debug)]
pub(crate) struct Builder {
    variables: usize,
    clauses: Vec<Vec<(usize, bool)>>,
    limits: UnaryAvx2SynthesisLimits,
}

impl Builder {
    pub(crate) fn new(limits: UnaryAvx2SynthesisLimits) -> Self {
        Self {
            variables: 0,
            clauses: Vec::new(),
            limits,
        }
    }

    pub(crate) fn variable(&mut self) -> Result<usize, UnaryAvx2SynthesisError> {
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

    pub(crate) fn variables(
        &mut self,
        count: usize,
    ) -> Result<Vec<usize>, UnaryAvx2SynthesisError> {
        (0..count).map(|_| self.variable()).collect()
    }

    pub(crate) fn clause(
        &mut self,
        literals: &[(usize, bool)],
    ) -> Result<(), UnaryAvx2SynthesisError> {
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

    pub(crate) fn at_most_one(&mut self, choices: &[usize]) -> Result<(), UnaryAvx2SynthesisError> {
        for left in 0..choices.len() {
            for right in left + 1..choices.len() {
                self.clause(&[(choices[left], true), (choices[right], true)])?;
            }
        }
        Ok(())
    }

    pub(crate) fn exactly_one(&mut self, choices: &[usize]) -> Result<(), UnaryAvx2SynthesisError> {
        self.clause(
            &choices
                .iter()
                .copied()
                .map(|variable| (variable, false))
                .collect::<Vec<_>>(),
        )?;
        self.at_most_one(choices)
    }

    pub(crate) fn gated_exactly_one(
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

    pub(crate) fn finish(self) -> Result<CnfFormula, UnaryAvx2SynthesisError> {
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
    allow_noop: bool,
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
                5 if self.allow_noop => continue,
                _ => unreachable!("validated family selector"),
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

pub(crate) fn selected(
    choices: &[usize],
    values: &[bool],
) -> Result<usize, UnaryAvx2SynthesisError> {
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

pub(crate) fn selected_u8(
    choices: &[usize],
    values: &[bool],
) -> Result<u8, UnaryAvx2SynthesisError> {
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

pub(crate) fn valid_permutation_target(target: &ByteTags) -> bool {
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
    include_noop: bool,
) -> Result<StepLayout, UnaryAvx2SynthesisError> {
    let families = builder.variables(if include_noop {
        WEIGHTED_FAMILIES
    } else {
        FAMILIES
    })?;
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
    if include_noop {
        transition(
            builder,
            families[FAMILIES],
            input,
            output,
            &(0..AVX2_BYTES).map(|byte| (byte, byte)).collect::<Vec<_>>(),
        )?;
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
    encode_unary_avx2_sequence_internal(target, steps, limits, false)
}

fn encode_unary_avx2_sequence_internal(
    target: &ByteTags,
    steps: usize,
    limits: UnaryAvx2SynthesisLimits,
    include_noop: bool,
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

    let mut step_layouts = Vec::with_capacity(steps);
    for adjacent in states.windows(2) {
        step_layouts.push(encode_step(
            &mut builder,
            &adjacent[0],
            &adjacent[1],
            include_noop,
        )?);
    }
    Ok(UnaryAvx2Encoding {
        formula: builder.finish()?,
        target: *target,
        steps: step_layouts,
        allow_noop: include_noop,
    })
}

/// Encode the complete weighted-cost query for this unary AVX2 language.
///
/// The number of slots is derived as `bound / minimum_positive_cost`. A
/// zero-cost pseudo-instruction pads every shorter real sequence to that width,
/// so the formula covers every sequence whose total cost is at most `bound`
/// without charging padding. Real instruction costs must be positive.
///
/// # Errors
///
/// Refuses zero real costs, non-permutation targets, or either base/weighted
/// construction exceeding its explicit resource policy.
pub fn encode_weighted_unary_avx2_sequence(
    target: &ByteTags,
    costs: UnaryAvx2InstructionCosts,
    bound: u64,
    limits: UnaryAvx2SynthesisLimits,
) -> Result<UnaryAvx2Encoding, UnaryAvx2SynthesisError> {
    let weights = costs.as_array();
    let minimum = weights
        .iter()
        .copied()
        .min()
        .filter(|minimum| *minimum != 0)
        .ok_or(UnaryAvx2SynthesisError::ZeroInstructionCost)?;
    if weights.contains(&0) {
        return Err(UnaryAvx2SynthesisError::ZeroInstructionCost);
    }
    let slots_u64 = bound / minimum;
    let slots = usize::try_from(slots_u64).map_err(|_| UnaryAvx2SynthesisError::LimitExceeded {
        resource: "weighted_steps",
        observed: usize::MAX,
        limit: limits.max_steps,
    })?;
    let mut encoding = encode_unary_avx2_sequence_internal(target, slots, limits, true)?;
    let mut terms = Vec::with_capacity(encoding.steps.len().saturating_mul(FAMILIES));
    for step in &encoding.steps {
        for (variable, weight) in step.families[..FAMILIES].iter().copied().zip(weights) {
            let variable = CnfVar::new(variable)
                .map_err(|error| UnaryAvx2SynthesisError::Cnf(format!("{error:?}")))?;
            terms.push((CnfLit::positive(variable), weight));
        }
    }
    let weighted = encode_weighted_at_most(
        &encoding.formula,
        &terms,
        bound,
        WeightedAtMostLimits {
            max_auxiliary_variables: limits.max_variables,
            max_added_clauses: limits.max_clauses,
            max_bound: u64::try_from(limits.max_clauses).unwrap_or(u64::MAX),
        },
    )
    .map_err(|error| UnaryAvx2SynthesisError::Weighted(format!("{error:?}")))?;
    if weighted.formula().variable_count() > limits.max_variables {
        return Err(UnaryAvx2SynthesisError::LimitExceeded {
            resource: "variables",
            observed: weighted.formula().variable_count(),
            limit: limits.max_variables,
        });
    }
    if weighted.formula().clauses().len() > limits.max_clauses {
        return Err(UnaryAvx2SynthesisError::LimitExceeded {
            resource: "clauses",
            observed: weighted.formula().clauses().len(),
            limit: limits.max_clauses,
        });
    }
    encoding.formula = weighted.formula().clone();
    Ok(encoding)
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_cnf::{ProofSolveOutcome, SatResult, solve_with_drat_proof, solve_with_native_core};

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
        let SatResult::Sat(model) = solve_with_native_core(two.formula()).unwrap() else {
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
        let SatResult::Sat(model) = solve_with_native_core(encoding.formula()).unwrap() else {
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

    #[test]
    fn weighted_reverse_has_checked_cost_three_refutation_and_cost_four_witness() {
        let costs = UnaryAvx2InstructionCosts {
            pshufb: 1,
            permute_dwords: 3,
            permute_qwords: 3,
            align_right: 1,
            permute_2x128: 3,
        };
        let target = ByteTags::reversed();
        let lower = encode_weighted_unary_avx2_sequence(
            &target,
            costs,
            3,
            UnaryAvx2SynthesisLimits::default(),
        )
        .unwrap();
        let ProofSolveOutcome::Unsat(proof) = solve_with_drat_proof(lower.formula()) else {
            panic!("lane-local unit-cost shuffles cannot reverse globally at cost three");
        };
        assert_eq!(
            axeyum_cnf::check_drat_backward(lower.formula(), &proof),
            Ok(true)
        );

        let upper = encode_weighted_unary_avx2_sequence(
            &target,
            costs,
            4,
            UnaryAvx2SynthesisLimits::default(),
        )
        .unwrap();
        let SatResult::Sat(model) = solve_with_native_core(upper.formula()).unwrap() else {
            panic!("global reversal has weighted cost four");
        };
        let sequence = upper.lift_model(&model).unwrap();
        assert_eq!(replay_sequence(&sequence), target);
        assert!(costs.sequence_cost(&sequence) <= 4);
    }

    #[test]
    fn zero_cost_padding_preserves_a_short_expensive_sequence() {
        let costs = UnaryAvx2InstructionCosts {
            pshufb: 1,
            permute_dwords: 3,
            permute_qwords: 3,
            align_right: 1,
            permute_2x128: 3,
        };
        let target =
            Avx2Shuffle::PermuteDwords([7, 6, 5, 4, 3, 2, 1, 0]).replay(&ByteTags::identity());
        let encoding = encode_weighted_unary_avx2_sequence(
            &target,
            costs,
            3,
            UnaryAvx2SynthesisLimits::default(),
        )
        .unwrap();
        let mut pinned = encoding.formula().clone();
        let unit = |variable: usize, value: bool| {
            let literal = CnfLit::positive(CnfVar::new(variable).unwrap());
            CnfClause::new(vec![if value { literal } else { literal.negated() }])
        };
        // Slot 0 is the cost-three dword reversal; slots 1 and 2 are the
        // zero-cost padding pseudo-instruction. Pinning avoids turning this
        // structural completeness control into an unrelated synthesis run.
        for (family, &variable) in encoding.steps[0].families.iter().enumerate() {
            pinned.add_clause(unit(variable, family == 1)).unwrap();
        }
        for (output, choices) in encoding.steps[0].dwords.iter().enumerate() {
            for (source, &variable) in choices.iter().enumerate() {
                pinned
                    .add_clause(unit(variable, source == 7 - output))
                    .unwrap();
            }
        }
        for step in &encoding.steps[1..] {
            for (family, &variable) in step.families.iter().enumerate() {
                pinned.add_clause(unit(variable, family == 5)).unwrap();
            }
        }
        let SatResult::Sat(model) = solve_with_native_core(&pinned).unwrap() else {
            panic!("one cost-three instruction must survive in three padded slots");
        };
        let sequence = encoding.lift_model(&model).unwrap();
        assert_eq!(sequence.len(), 1);
        assert_eq!(costs.sequence_cost(&sequence), 3);
        assert_eq!(replay_sequence(&sequence), target);
    }
}
