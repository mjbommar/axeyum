//! The formal mathematics tour as a queryable curriculum graph.
//!
//! A compact Rust mirror of the knowledge graph in
//! [`docs/curriculum/curriculum.toml`](../../../docs/curriculum/curriculum.toml):
//! a backward-derived prerequisite DAG from calculus / number theory / linear
//! algebra to the foundations, annotated with each node's *decidable/computable*
//! fragment and the self-checking [`Family`] that exercises it (if any).
//!
//! This is the *mathematical-content* companion to the *solver-capability*
//! [`crate::concept`] DAG. Both feed the same `Exercise`/grading/render layer
//! (ADR-0033). The TOML file and this table mirror each other; the tests below
//! enforce the graph invariants (acyclic, prerequisites exist, every `Covered`
//! node's family is realized by a self-checking scenario).

use crate::Family;

/// How much of a node's content axeyum can decide/check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Decidability {
    /// A complete decision procedure exists (e.g. propositional logic).
    Decidable,
    /// The answer is computed, then independently checked (e.g. gcd/Bézout).
    Computable,
    /// Only finite/fixed instances are decided.
    Bounded,
    /// The general case is proof-assistant territory (Lean-horizon).
    Undecidable,
}

/// A node's exercise status in axeyum.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    /// Has a self-checking exercise family today.
    Covered,
    /// Testable fragment identified; family not yet built.
    Planned,
    /// Primarily a proof-reconstruction target (P3.6/P3.7), not a benchmark.
    LeanHorizon,
}

/// A curriculum node: a teachable mathematical concept and its axeyum mapping.
#[derive(Debug, Clone, Copy)]
pub struct MathNode {
    /// Stable kebab-case id (matches the TOML and the markdown filename).
    pub id: &'static str,
    /// Human-readable title.
    pub title: &'static str,
    /// Curriculum layer: 0 foundations · 1 number systems · 2 structures · 3 destinations.
    pub layer: u8,
    /// Prerequisite node ids (the DAG edges).
    pub prerequisites: &'static [&'static str],
    /// How much axeyum can decide/check.
    pub decidability: Decidability,
    /// The self-checking family that exercises it, if any.
    pub family: Option<Family>,
    /// Exercise status.
    pub status: Status,
}

// `Undecidable` is part of the public enum but no node's *testable fragment* is
// fully undecidable (general-theorem undecidability is captured by
// `Status::LeanHorizon`), so it is not imported here.
use Decidability::{Bounded, Computable, Decidable};
use Status::{Covered, LeanHorizon, Planned};

/// Every curriculum node, mirroring `docs/curriculum/curriculum.toml`.
pub const NODES: &[MathNode] = &[
    // Layer 0 — foundations
    MathNode {
        id: "propositional-logic",
        title: "Propositional Logic",
        layer: 0,
        prerequisites: &[],
        decidability: Decidable,
        family: Some(Family::Logic),
        status: Covered,
    },
    MathNode {
        id: "predicate-logic",
        title: "Predicate Logic",
        layer: 0,
        prerequisites: &["propositional-logic", "sets"],
        decidability: Bounded,
        family: Some(Family::Predicate),
        status: Covered,
    },
    MathNode {
        id: "proof-methods",
        title: "Proof Methods",
        layer: 0,
        prerequisites: &["propositional-logic", "predicate-logic"],
        decidability: Bounded,
        family: None,
        status: Planned,
    },
    MathNode {
        id: "induction",
        title: "Mathematical Induction",
        layer: 0,
        prerequisites: &["proof-methods", "naturals"],
        decidability: Bounded,
        family: None,
        status: Planned,
    },
    MathNode {
        id: "sets",
        title: "Sets",
        layer: 0,
        prerequisites: &["propositional-logic"],
        decidability: Bounded,
        family: Some(Family::Sets),
        status: Covered,
    },
    MathNode {
        id: "relations-and-functions",
        title: "Relations & Functions",
        layer: 0,
        prerequisites: &["sets"],
        decidability: Bounded,
        family: None,
        status: Planned,
    },
    MathNode {
        id: "cardinality",
        title: "Cardinality",
        layer: 0,
        prerequisites: &["relations-and-functions"],
        decidability: Bounded,
        family: None,
        status: LeanHorizon,
    },
    // Layer 1 — number systems
    MathNode {
        id: "naturals",
        title: "Natural Numbers (Peano)",
        layer: 1,
        prerequisites: &["sets"],
        decidability: Bounded,
        family: Some(Family::NumberSystem),
        status: Covered,
    },
    MathNode {
        id: "integers",
        title: "Integers",
        layer: 1,
        prerequisites: &["naturals"],
        decidability: Computable,
        family: Some(Family::NumberSystem),
        status: Covered,
    },
    MathNode {
        id: "rationals",
        title: "Rational Numbers",
        layer: 1,
        prerequisites: &["integers"],
        decidability: Computable,
        family: None,
        status: Planned,
    },
    MathNode {
        id: "reals",
        title: "Real Numbers",
        layer: 1,
        prerequisites: &["rationals"],
        decidability: Bounded,
        family: None,
        status: Planned,
    },
    MathNode {
        id: "complex",
        title: "Complex Numbers",
        layer: 1,
        prerequisites: &["reals"],
        decidability: Bounded,
        family: None,
        status: LeanHorizon,
    },
    // Layer 2 — structures
    MathNode {
        id: "divisibility-and-euclid",
        title: "Divisibility & the Euclidean Algorithm",
        layer: 2,
        prerequisites: &["integers"],
        decidability: Computable,
        family: Some(Family::NumberTheory),
        status: Covered,
    },
    MathNode {
        id: "modular-arithmetic",
        title: "Modular Arithmetic & Congruences",
        layer: 2,
        prerequisites: &["divisibility-and-euclid"],
        decidability: Bounded,
        family: Some(Family::NumberTheory),
        status: Covered,
    },
    MathNode {
        id: "groups",
        title: "Groups",
        layer: 2,
        prerequisites: &["relations-and-functions"],
        decidability: Bounded,
        family: Some(Family::Algebra),
        status: Covered,
    },
    MathNode {
        id: "rings",
        title: "Rings",
        layer: 2,
        prerequisites: &["groups", "integers"],
        decidability: Bounded,
        family: Some(Family::Algebra),
        status: Covered,
    },
    MathNode {
        id: "fields",
        title: "Fields",
        layer: 2,
        prerequisites: &["rings", "rationals", "modular-arithmetic"],
        decidability: Bounded,
        family: Some(Family::Algebra),
        status: Covered,
    },
    MathNode {
        id: "polynomials",
        title: "Polynomials",
        layer: 2,
        prerequisites: &["rings", "fields"],
        decidability: Computable,
        family: Some(Family::Polynomial),
        status: Covered,
    },
    MathNode {
        id: "sequences-and-limits",
        title: "Sequences & Limits",
        layer: 2,
        prerequisites: &["reals"],
        decidability: Bounded,
        family: None,
        status: LeanHorizon,
    },
    MathNode {
        id: "counting",
        title: "Counting & Combinatorics",
        layer: 2,
        prerequisites: &["sets", "naturals"],
        decidability: Computable,
        family: Some(Family::Counting),
        status: Covered,
    },
    // Layer 3 — destinations
    MathNode {
        id: "number-theory",
        title: "Number Theory",
        layer: 3,
        prerequisites: &[
            "divisibility-and-euclid",
            "modular-arithmetic",
            "induction",
            "counting",
        ],
        decidability: Bounded,
        family: Some(Family::NumberTheory),
        status: Covered,
    },
    MathNode {
        id: "linear-algebra",
        title: "Linear Algebra",
        layer: 3,
        prerequisites: &["fields", "relations-and-functions", "polynomials"],
        decidability: Computable,
        family: Some(Family::LinearAlgebra),
        status: Covered,
    },
    MathNode {
        id: "calculus",
        title: "Calculus",
        layer: 3,
        prerequisites: &["reals", "sequences-and-limits", "polynomials"],
        decidability: Bounded,
        family: None,
        status: LeanHorizon,
    },
];

/// Looks up a node by id.
pub fn node(id: &str) -> Option<&'static MathNode> {
    NODES.iter().find(|n| n.id == id)
}

/// A deterministic topological ordering of the curriculum DAG: every node
/// appears after all of its prerequisites. Ties break by `NODES` order, so the
/// teaching sequence is stable. A returned length below `NODES.len()` would
/// indicate a cycle (asserted in tests).
pub fn topological_order() -> Vec<&'static MathNode> {
    let mut placed: Vec<&str> = Vec::new();
    let mut emitted: Vec<&'static MathNode> = Vec::new();
    loop {
        let mut progressed = false;
        for n in NODES {
            if placed.contains(&n.id) {
                continue;
            }
            if n.prerequisites.iter().all(|p| placed.contains(p)) {
                emitted.push(n);
                placed.push(n.id);
                progressed = true;
            }
        }
        if !progressed {
            break;
        }
    }
    emitted
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::all_catalog_scenarios;

    #[test]
    fn graph_is_acyclic_and_total() {
        assert_eq!(
            topological_order().len(),
            NODES.len(),
            "topological_order dropped nodes — the curriculum DAG has a cycle"
        );
    }

    #[test]
    fn prerequisites_reference_real_nodes() {
        for n in NODES {
            for p in n.prerequisites {
                assert!(node(p).is_some(), "{} lists unknown prerequisite {p}", n.id);
                assert_ne!(&n.id, p, "{} is its own prerequisite", n.id);
            }
        }
    }

    #[test]
    fn ids_are_unique() {
        for (i, n) in NODES.iter().enumerate() {
            assert!(
                NODES[..i].iter().all(|m| m.id != n.id),
                "duplicate node id {}",
                n.id
            );
        }
    }

    #[test]
    fn covered_nodes_have_a_family_realized_by_a_self_checking_scenario() {
        // The double-duty guarantee for the math tour: a node marked Covered must
        // name a Family that some self-checking scenario actually provides.
        let realized: Vec<Family> = all_catalog_scenarios()
            .iter()
            .filter(|s| s.self_check().is_ok())
            .map(|s| s.family)
            .collect();
        for n in NODES.iter().filter(|n| n.status == Status::Covered) {
            let family = n
                .family
                .unwrap_or_else(|| panic!("{} is Covered but names no family", n.id));
            assert!(
                realized.contains(&family),
                "{} is Covered by {family:?}, but no self-checking scenario realizes it",
                n.id
            );
        }
    }

    #[test]
    fn destinations_are_present() {
        for dest in ["calculus", "number-theory", "linear-algebra"] {
            let n = node(dest).expect("destination present");
            assert_eq!(n.layer, 3);
        }
    }

    #[test]
    fn topological_order_respects_prerequisites() {
        let order = topological_order();
        let pos = |id: &str| order.iter().position(|n| n.id == id).unwrap();
        for n in NODES {
            for p in n.prerequisites {
                assert!(
                    pos(p) < pos(n.id),
                    "{} taught before prerequisite {p}",
                    n.id
                );
            }
        }
    }
}
