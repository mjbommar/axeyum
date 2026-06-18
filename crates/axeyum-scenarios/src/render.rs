//! Human-readable rendering of scenarios into problem statements and worked
//! solutions.
//!
//! This is the layer that turns a self-checking test/benchmark artifact into a
//! piece of educational content ([ADR-0033](../../../docs/research/09-decisions/adr-0033-double-duty-educational-artifacts.md)):
//! the *same* [`Scenario`] is rendered as a problem to solve and as a worked
//! solution backed by its [`Expectation`]. Rendering never decides anything — it
//! only describes the arena, the query, and the already-known, self-checked
//! ground truth.

use std::fmt::Write as _;

use axeyum_ir::render;

use crate::{Expectation, Scenario, UnsatEvidence, concept::concepts_for_family};

/// Something that can be presented as an educational problem with a worked
/// solution.
pub trait Renderable {
    /// A human-readable statement of the problem the artifact poses.
    fn problem_statement(&self) -> String;

    /// A human-readable worked solution, derived from the known ground truth.
    fn worked_solution(&self) -> String;
}

impl Renderable for Scenario {
    fn problem_statement(&self) -> String {
        let mut out = String::new();
        writeln!(out, "# {}\n", self.name).unwrap();

        let concepts = concepts_for_family(self.family);
        if !concepts.is_empty() {
            let titles: Vec<&str> = concepts.iter().map(|c| c.title()).collect();
            writeln!(out, "Concept(s): {}", titles.join(", ")).unwrap();
        }
        writeln!(
            out,
            "Family: {:?} · width: {} bits\n",
            self.family, self.width
        )
        .unwrap();

        out.push_str("Given:\n");
        for (_symbol, name, sort) in self.arena.symbols() {
            writeln!(out, "  - {name} : {sort:?}").unwrap();
        }

        out.push_str("\nDecide whether there is an assignment satisfying all of:\n");
        for term in self.query.solver_terms() {
            writeln!(out, "  - {}", render(&self.arena, term)).unwrap();
        }
        out
    }

    fn worked_solution(&self) -> String {
        let mut out = String::new();
        match &self.expectation {
            Expectation::Sat { witness } => {
                out.push_str("Answer: SATISFIABLE.\n\nA satisfying assignment is:\n");
                for (symbol, name, _sort) in self.arena.symbols() {
                    if let Some(value) = witness.get(symbol) {
                        writeln!(out, "  - {name} = {value}").unwrap();
                    }
                }
                out.push_str(
                    "\nThis witness is verified by evaluating every constraint against it \
                     (the evaluator, not a solver, is the judge).\n",
                );
            }
            Expectation::Unsat { evidence } => {
                out.push_str(
                    "Answer: UNSATISFIABLE — no assignment satisfies all constraints.\n\n",
                );
                match evidence {
                    UnsatEvidence::Exhaustive { cases } => {
                        writeln!(
                            out,
                            "Established by checking all {cases} assignments over the scenario \
                             width: a genuine finite-domain proof.",
                        )
                        .unwrap();
                    }
                    UnsatEvidence::Sampled { cases, seed } => {
                        writeln!(
                            out,
                            "Established over {cases} deterministic samples (seed {seed:#x}): \
                             lower assurance, since a model could exist outside the sample.",
                        )
                        .unwrap();
                    }
                }
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{catalog, full_adder_identity, mixing_inversion};

    #[test]
    fn every_catalog_scenario_renders_nonempty() {
        for scenario in catalog() {
            let statement = scenario.problem_statement();
            let solution = scenario.worked_solution();
            assert!(
                statement.contains(&scenario.name),
                "statement omits the scenario name for {}",
                scenario.name
            );
            assert!(
                statement.contains("Decide whether"),
                "statement omits the question for {}",
                scenario.name
            );
            assert!(
                !solution.trim().is_empty(),
                "empty solution for {}",
                scenario.name
            );
        }
    }

    #[test]
    fn sat_solution_exhibits_a_witness_and_unsat_states_evidence() {
        let sat = mixing_inversion(8, 3, 0x1234);
        sat.self_check().unwrap();
        let solution = sat.worked_solution();
        assert!(solution.contains("SATISFIABLE"));
        // The witness lines name the input symbols.
        assert!(solution.contains(" = "));

        let unsat = full_adder_identity(4);
        unsat.self_check().unwrap();
        let solution = unsat.worked_solution();
        assert!(solution.contains("UNSATISFIABLE"));
        assert!(solution.contains("finite-domain proof"));
    }
}
