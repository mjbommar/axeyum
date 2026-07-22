//! The exercise view: a scenario presented as a graded learning task.
//!
//! Per [ADR-0033](../../../docs/research/09-decisions/adr-0033-double-duty-educational-artifacts.md),
//! an [`Exercise`] is a thin projection over a [`Scenario`] that adds the three
//! things a test artifact lacks to become a homework problem: its place in the
//! curriculum ([`Exercise::concepts`]), a *measured* difficulty
//! ([`Exercise::difficulty`]), and a **sound auto-grader**
//! ([`Exercise::grade`]).
//!
//! The grader is the project's identity applied to teaching: a candidate answer
//! is judged by the trusted evaluator ([`Scenario::is_satisfied_by`]), never by
//! a solver's search. A grader defect therefore yields a *rejected* answer, not
//! a wrongly-accepted one.

use axeyum_ir::{Assignment, Sort};

use crate::{Concept, Renderable, Scenario, concept::concepts_for_family};

/// A learner's submitted answer to an exercise.
#[derive(Debug, Clone)]
pub enum Answer {
    /// "Satisfiable, and here is a witness." The witness is always checked.
    Sat {
        /// The proposed satisfying assignment.
        witness: Assignment,
    },
    /// "Unsatisfiable — no assignment works."
    Unsat,
}

/// The result of grading an [`Answer`] against an [`Exercise`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Grade {
    /// The answer is correct, confirmed by the trusted checker.
    Correct,
    /// The verdict (sat vs. unsat) disagrees with the scenario's ground truth.
    WrongVerdict,
    /// A `Sat` answer was submitted but its witness does not satisfy the
    /// constraints (the evaluator rejected it).
    WitnessRejected,
}

/// Coarse, human-facing difficulty buckets derived from the measured signals.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DifficultyTier {
    /// Tiny, fully exhaustible by hand.
    Intro,
    /// Small finite domain.
    Easy,
    /// Larger finite domain or several constraints.
    Medium,
    /// Beyond hand-enumeration, or a non-finite domain.
    Hard,
}

/// A *measured* difficulty profile for an exercise.
///
/// Every field is computed from the artifact (symbol count, constraint count,
/// enumeration-domain size), never asserted by hand — satisfying ADR-0033's
/// "difficulty is measured, not guessed" rule. Deeper, solver-derived signals
/// (CNF size, proof length) are layered on in later work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Difficulty {
    /// Number of input symbols.
    pub symbols: usize,
    /// Number of asserted constraints.
    pub constraints: usize,
    /// Total bits of the finite enumeration domain, or `None` when the domain is
    /// not finitely enumerable (integers/reals/arrays).
    pub enumeration_bits: Option<u32>,
    /// The coarse tier derived from the above.
    pub tier: DifficultyTier,
}

/// A scenario presented as a graded, curriculum-placed learning task.
#[derive(Debug)]
pub struct Exercise<'a> {
    /// The underlying self-checking scenario.
    pub scenario: &'a Scenario,
}

impl<'a> Exercise<'a> {
    /// Wraps a scenario as an exercise.
    pub fn new(scenario: &'a Scenario) -> Self {
        Exercise { scenario }
    }

    /// The curriculum concepts this exercise exercises.
    pub fn concepts(&self) -> Vec<Concept> {
        concepts_for_family(self.scenario.family)
    }

    /// The rendered problem statement.
    pub fn prompt(&self) -> String {
        self.scenario.problem_statement()
    }

    /// The rendered worked solution.
    pub fn solution(&self) -> String {
        self.scenario.worked_solution()
    }

    /// The measured difficulty profile.
    pub fn difficulty(&self) -> Difficulty {
        let mut symbols = 0usize;
        let mut total_bits = 0u32;
        let mut finite = true;
        for (_symbol, _name, sort) in self.scenario.arena.symbols() {
            symbols += 1;
            match enumeration_bits(sort) {
                Some(bits) => total_bits = total_bits.saturating_add(bits),
                None => finite = false,
            }
        }
        let constraints = self.scenario.query.solver_term_count();
        let enumeration_bits = if finite { Some(total_bits) } else { None };
        let tier = tier_for(enumeration_bits, constraints);
        Difficulty {
            symbols,
            constraints,
            enumeration_bits,
            tier,
        }
    }

    /// Grades a candidate [`Answer`] against the scenario's self-checked ground
    /// truth, using only the trusted evaluator.
    ///
    /// A `Sat` answer's witness is always evaluated: it is accepted only if it
    /// genuinely satisfies every constraint *and* the scenario is satisfiable.
    /// An answer can never be accepted because a search said so.
    pub fn grade(&self, answer: &Answer) -> Grade {
        match answer {
            Answer::Sat { witness } => match self.scenario.is_satisfied_by(witness) {
                // The witness genuinely satisfies the constraints. This is only
                // correct for a satisfiable scenario; for a self-checked UNSAT
                // scenario this branch is unreachable (a satisfying witness
                // cannot exist), so treating it as WrongVerdict is safe.
                Ok(true) if self.scenario.expectation.is_sat() => Grade::Correct,
                Ok(true) => Grade::WrongVerdict,
                // The witness does not satisfy the constraints (or referenced an
                // unbound symbol): rejected by the evaluator.
                Ok(false) | Err(_) => Grade::WitnessRejected,
            },
            Answer::Unsat => {
                if self.scenario.expectation.is_unsat() {
                    Grade::Correct
                } else {
                    Grade::WrongVerdict
                }
            }
        }
    }
}

/// Bits an enumerable sort contributes, or `None` for non-finite domains.
fn enumeration_bits(sort: Sort) -> Option<u32> {
    match sort {
        Sort::Bool => Some(1),
        Sort::BitVec(width) => Some(width),
        Sort::RoundingMode => Some(3),
        Sort::Float { exp, sig } => Some(exp + sig),
        Sort::Int
        | Sort::Real
        | Sort::Array { .. }
        | Sort::Datatype(_)
        | Sort::Uninterpreted(_)
        | Sort::Seq(_) => None,
    }
}

fn tier_for(enumeration_bits: Option<u32>, constraints: usize) -> DifficultyTier {
    match enumeration_bits {
        Some(bits) if bits <= 8 => DifficultyTier::Intro,
        Some(bits) if bits <= 16 => DifficultyTier::Easy,
        Some(bits) if bits <= 24 && constraints <= 4 => DifficultyTier::Medium,
        // Larger finite domains and all non-finite domains are Hard.
        _ => DifficultyTier::Hard,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Expectation, full_adder_identity, mixing_inversion};

    #[test]
    fn correct_sat_witness_grades_correct() {
        let scenario = mixing_inversion(8, 3, 0xBEEF);
        scenario.self_check().unwrap();
        let Expectation::Sat { witness } = &scenario.expectation else {
            panic!("mixing should be sat");
        };
        let ex = Exercise::new(&scenario);
        let grade = ex.grade(&Answer::Sat {
            witness: witness.clone(),
        });
        assert_eq!(grade, Grade::Correct);
    }

    #[test]
    fn empty_witness_is_rejected_by_the_evaluator() {
        let scenario = mixing_inversion(8, 3, 0xBEEF);
        let ex = Exercise::new(&scenario);
        // An empty assignment leaves inputs unbound: the evaluator rejects it,
        // so the grade is WitnessRejected — never silently Correct.
        let grade = ex.grade(&Answer::Sat {
            witness: Assignment::new(),
        });
        assert_eq!(grade, Grade::WitnessRejected);
    }

    #[test]
    fn claiming_unsat_on_a_sat_scenario_is_wrong_verdict() {
        let scenario = mixing_inversion(8, 3, 0xBEEF);
        let ex = Exercise::new(&scenario);
        assert_eq!(ex.grade(&Answer::Unsat), Grade::WrongVerdict);
    }

    #[test]
    fn correct_unsat_verdict_grades_correct() {
        let scenario = full_adder_identity(4);
        scenario.self_check().unwrap();
        let ex = Exercise::new(&scenario);
        assert_eq!(ex.grade(&Answer::Unsat), Grade::Correct);
    }

    #[test]
    fn difficulty_is_measured_from_the_arena() {
        let small = full_adder_identity(4);
        let d = Exercise::new(&small).difficulty();
        assert_eq!(d.symbols, 2);
        assert_eq!(d.enumeration_bits, Some(8));
        assert_eq!(d.tier, DifficultyTier::Intro);

        let wide = full_adder_identity(8);
        let d = Exercise::new(&wide).difficulty();
        assert_eq!(d.enumeration_bits, Some(16));
        assert_eq!(d.tier, DifficultyTier::Easy);
    }
}
