//! The coverage audit: concept DAG ↔ self-checking exercises.
//!
//! This is the "test-coverage" half of the double-duty thesis
//! ([ADR-0033](../../../docs/research/09-decisions/adr-0033-double-duty-educational-artifacts.md)):
//! the curriculum [`Concept`] graph is also a coverage map over the
//! self-checking [`Family`] suites. The audit answers two questions:
//!
//! - **Which concepts have an exercise yet?** A concept whose
//!   [`Concept::families`] is empty is a curriculum node with no self-checking
//!   exercise — an honest, visible gap (e.g. `Proofs`, `SoftwareVerification`).
//! - **Are the declared exercises actually realized?** For a concept that *does*
//!   declare families, the audit checks those families are genuinely produced by
//!   self-checking scenarios — catching a stale mapping that claims coverage it
//!   does not have.

use std::collections::BTreeSet;
use std::fmt::Write as _;

use crate::{
    Concept, Family, Scenario, algebra_catalog, catalog, concept::ALL, counting_catalog,
    function_catalog, integer_catalog, linear_algebra_catalog, logic_catalog, memory_catalog,
    number_system_catalog, number_theory_catalog, polynomial_catalog, predicate_catalog,
    real_catalog, sets_catalog, verification_catalog,
};

/// Every self-checking scenario across all family catalogs.
///
/// Aggregates the main [`catalog`] with the per-family catalogs that are not
/// folded into it (`memory`, `function`, `integer`, `real`), giving the audit a
/// complete view of what exercises actually exist.
pub fn all_catalog_scenarios() -> Vec<Scenario> {
    let mut scenarios = catalog();
    scenarios.extend(logic_catalog());
    scenarios.extend(number_theory_catalog());
    scenarios.extend(linear_algebra_catalog());
    scenarios.extend(counting_catalog());
    scenarios.extend(algebra_catalog());
    scenarios.extend(polynomial_catalog());
    scenarios.extend(verification_catalog());
    scenarios.extend(sets_catalog());
    scenarios.extend(predicate_catalog());
    scenarios.extend(number_system_catalog());
    scenarios.extend(memory_catalog());
    scenarios.extend(function_catalog());
    scenarios.extend(integer_catalog());
    scenarios.extend(real_catalog());
    scenarios
}

/// Per-concept coverage relative to a set of scenarios.
#[derive(Debug, Clone)]
pub struct ConceptCoverage {
    /// The concept being audited.
    pub concept: Concept,
    /// The families the concept *declares* it is exercised by.
    pub declared_families: &'static [Family],
    /// The declared families actually realized by a self-checking scenario in
    /// the audited set.
    pub realized_families: Vec<Family>,
}

impl ConceptCoverage {
    /// Whether the concept declares at least one exercise family.
    pub fn has_exercise(&self) -> bool {
        !self.declared_families.is_empty()
    }

    /// Whether every declared family is realized by a self-checking scenario.
    /// Vacuously true for concepts that declare no families.
    pub fn is_fully_realized(&self) -> bool {
        self.declared_families
            .iter()
            .all(|f| self.realized_families.contains(f))
    }
}

/// Audits every concept against `scenarios`, recording which declared exercise
/// families are realized by a *self-checking* scenario.
///
/// A family counts as realized only if some scenario of that family passes
/// [`Scenario::self_check`] — so the audit measures genuine, verified coverage.
pub fn audit(scenarios: &[Scenario]) -> Vec<ConceptCoverage> {
    let realized: BTreeSet<Family> = scenarios
        .iter()
        .filter(|s| s.self_check().is_ok())
        .map(|s| s.family)
        .collect();

    ALL.iter()
        .map(|&concept| {
            let declared = concept.families();
            let realized_families = declared
                .iter()
                .copied()
                .filter(|f| realized.contains(f))
                .collect();
            ConceptCoverage {
                concept,
                declared_families: declared,
                realized_families,
            }
        })
        .collect()
}

/// Concepts that have no self-checking exercise yet (curriculum gaps).
pub fn uncovered_concepts() -> Vec<Concept> {
    ALL.iter().copied().filter(|c| !c.has_exercise()).collect()
}

/// A human-readable coverage report over `scenarios`.
pub fn report(scenarios: &[Scenario]) -> String {
    let rows = audit(scenarios);
    let mut out = String::from("# Curriculum coverage audit\n\n");
    for row in &rows {
        let mark = if !row.has_exercise() {
            "gap "
        } else if row.is_fully_realized() {
            "ok  "
        } else {
            "STALE"
        };
        writeln!(
            out,
            "[{mark}] {} — declared {:?}, realized {:?}",
            row.concept.title(),
            row.declared_families,
            row.realized_families,
        )
        .unwrap();
    }
    let gaps = uncovered_concepts();
    writeln!(
        out,
        "\n{} of {} concepts have a self-checking exercise; {} gaps remain.",
        ALL.len() - gaps.len(),
        ALL.len(),
        gaps.len(),
    )
    .unwrap();
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::concepts_for_family;

    #[test]
    fn every_declared_family_is_realized_by_a_self_checking_scenario() {
        // The core guarantee: no concept claims an exercise family that no
        // self-checking scenario actually provides. This is the test-coverage
        // double duty — a stale concept→family mapping fails here.
        let scenarios = all_catalog_scenarios();
        let rows = audit(&scenarios);
        for row in &rows {
            assert!(
                row.is_fully_realized(),
                "concept {:?} declares {:?} but only {:?} are realized by self-checking scenarios",
                row.concept,
                row.declared_families,
                row.realized_families,
            );
        }
    }

    #[test]
    fn coverage_matches_declared_exercise_status() {
        let scenarios = all_catalog_scenarios();
        for row in audit(&scenarios) {
            assert_eq!(row.has_exercise(), row.concept.has_exercise());
        }
    }

    #[test]
    fn known_roadmap_concepts_are_tracked_as_gaps() {
        // These are the deliberate, documented gaps: foundations exercised
        // indirectly and rungs not yet given a self-checking family. Tracking
        // them keeps the curriculum honest about what is not yet covered.
        let gaps: BTreeSet<Concept> = uncovered_concepts().into_iter().collect();
        for expected in [
            Concept::Proofs,
            Concept::DecidableGeometry,
            Concept::SatAndCnf,
            Concept::BitBlasting,
        ] {
            assert!(
                gaps.contains(&expected),
                "{expected:?} should be a tracked gap"
            );
        }
    }

    #[test]
    fn covered_concepts_have_a_realized_exercise() {
        // Every concept that maps to a family must be reachable from that family.
        for &family in &[
            Family::Identity,
            Family::Arithmetic,
            Family::Mixing,
            Family::Machine,
            Family::Function,
            Family::Memory,
            Family::Integer,
            Family::Real,
        ] {
            assert!(
                !concepts_for_family(family).is_empty(),
                "family {family:?} maps to no concept"
            );
        }
    }

    #[test]
    fn report_renders() {
        let scenarios = all_catalog_scenarios();
        let text = report(&scenarios);
        assert!(text.contains("coverage audit"));
        assert!(text.contains("gaps remain"));
    }
}
