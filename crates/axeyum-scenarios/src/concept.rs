//! The curriculum concept DAG.
//!
//! Per [ADR-0033](../../../docs/research/09-decisions/adr-0033-double-duty-educational-artifacts.md),
//! the self-checking scenarios double as educational content. This module is the
//! *substrate* for that second role: a small, acyclic dependency graph of the
//! concepts axeyum can teach, derived from the engineering
//! [foundational DAG](../../../docs/research/08-planning/foundational-dag.md).
//!
//! It serves triple duty:
//!
//! - **Curriculum order.** [`topological_order`] is a teaching sequence that
//!   never presents a concept before its prerequisites; [`frontier`] selects the
//!   next learnable concepts given what a learner has mastered.
//! - **Coverage map.** [`Concept::families`] links each concept to the
//!   self-checking [`Family`] values that exercise it. A concept with no family
//!   is a curriculum node with no exercise *yet* — a visible, honest gap (see
//!   the `coverage` module).
//! - **Engineering gate.** The same prerequisite structure the project already
//!   enforces when adding layers.
//!
//! The graph is deliberately coarse and hand-maintained; it is a teaching map,
//! not a proof object.

use std::collections::BTreeSet;

use crate::Family;

/// A teachable concept in the axeyum curriculum.
///
/// Variants are declared bottom-up (foundations first). That declaration order
/// is also the deterministic tie-break used by [`topological_order`], so the
/// curriculum sequence is stable across runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Concept {
    /// Propositional logic: Boolean connectives, truth tables, validity.
    PropositionalLogic,
    /// Conjunctive normal form, Tseitin encoding, and Boolean satisfiability.
    SatAndCnf,
    /// Fixed-width bit-vectors and two's-complement representation.
    BitVectors,
    /// Bitwise identities (De Morgan, xor-swap) as exhaustively checkable laws.
    BitwiseIdentities,
    /// Modular arithmetic over bit-vectors (add/neg/mul, the full-adder law).
    ModularArithmetic,
    /// Bit-blasting: reducing bit-vector reasoning to SAT.
    BitBlasting,
    /// Symbolic execution: path conditions over a small machine.
    SymbolicExecution,
    /// Uninterpreted functions and congruence (`a = b ⇒ f(a) = f(b)`).
    UninterpretedFunctions,
    /// Arrays: `select`/`store` and the read-over-write axiom.
    Arrays,
    /// Linear integer arithmetic.
    LinearIntegerArithmetic,
    /// Linear real arithmetic.
    LinearRealArithmetic,
    /// Proofs and independent checking (DRAT/LRAT/Alethe; trusted small checking).
    Proofs,
    /// Software verification: bounded model checking and k-induction.
    SoftwareVerification,
    /// Decidable geometry over real-closed fields.
    DecidableGeometry,
    /// The limits of automation: decidable vs. provable, and first-class `unknown`.
    LimitsOfAutomation,
}

/// Every concept, in bottom-up declaration order.
pub const ALL: &[Concept] = &[
    Concept::PropositionalLogic,
    Concept::SatAndCnf,
    Concept::BitVectors,
    Concept::BitwiseIdentities,
    Concept::ModularArithmetic,
    Concept::BitBlasting,
    Concept::SymbolicExecution,
    Concept::UninterpretedFunctions,
    Concept::Arrays,
    Concept::LinearIntegerArithmetic,
    Concept::LinearRealArithmetic,
    Concept::Proofs,
    Concept::SoftwareVerification,
    Concept::DecidableGeometry,
    Concept::LimitsOfAutomation,
];

impl Concept {
    /// A short human-readable title.
    pub fn title(self) -> &'static str {
        match self {
            Concept::PropositionalLogic => "Propositional logic",
            Concept::SatAndCnf => "SAT and CNF",
            Concept::BitVectors => "Bit-vectors",
            Concept::BitwiseIdentities => "Bitwise identities",
            Concept::ModularArithmetic => "Modular arithmetic",
            Concept::BitBlasting => "Bit-blasting",
            Concept::SymbolicExecution => "Symbolic execution",
            Concept::UninterpretedFunctions => "Uninterpreted functions",
            Concept::Arrays => "Arrays",
            Concept::LinearIntegerArithmetic => "Linear integer arithmetic",
            Concept::LinearRealArithmetic => "Linear real arithmetic",
            Concept::Proofs => "Proofs and checking",
            Concept::SoftwareVerification => "Software verification",
            Concept::DecidableGeometry => "Decidable geometry",
            Concept::LimitsOfAutomation => "The limits of automation",
        }
    }

    /// A stable kebab-case slug for names and artifacts.
    pub fn slug(self) -> &'static str {
        match self {
            Concept::PropositionalLogic => "propositional-logic",
            Concept::SatAndCnf => "sat-and-cnf",
            Concept::BitVectors => "bit-vectors",
            Concept::BitwiseIdentities => "bitwise-identities",
            Concept::ModularArithmetic => "modular-arithmetic",
            Concept::BitBlasting => "bit-blasting",
            Concept::SymbolicExecution => "symbolic-execution",
            Concept::UninterpretedFunctions => "uninterpreted-functions",
            Concept::Arrays => "arrays",
            Concept::LinearIntegerArithmetic => "linear-integer-arithmetic",
            Concept::LinearRealArithmetic => "linear-real-arithmetic",
            Concept::Proofs => "proofs",
            Concept::SoftwareVerification => "software-verification",
            Concept::DecidableGeometry => "decidable-geometry",
            Concept::LimitsOfAutomation => "limits-of-automation",
        }
    }

    /// A one-line teaching summary of the concept.
    pub fn summary(self) -> &'static str {
        match self {
            Concept::PropositionalLogic => {
                "Boolean variables, connectives, and what it means for a formula to be valid or satisfiable."
            }
            Concept::SatAndCnf => {
                "Putting formulas in conjunctive normal form (Tseitin) and deciding satisfiability with DPLL/CDCL."
            }
            Concept::BitVectors => {
                "Fixed-width machine integers: two's complement, wrap-around, and bit-level operations."
            }
            Concept::BitwiseIdentities => {
                "Laws like De Morgan and xor-swap, provable by checking every input at small widths."
            }
            Concept::ModularArithmetic => {
                "Addition, negation, and multiplication mod 2^n, including the full-adder decomposition of +."
            }
            Concept::BitBlasting => {
                "Compiling a bit-vector formula down to an equivalent Boolean (SAT) problem, bit by bit."
            }
            Concept::SymbolicExecution => {
                "Running a program over symbolic inputs and accumulating a path condition the solver decides."
            }
            Concept::UninterpretedFunctions => {
                "Reasoning about unknown functions using only congruence: equal inputs give equal outputs."
            }
            Concept::Arrays => "Modelling memory with select/store and the read-over-write axiom.",
            Concept::LinearIntegerArithmetic => {
                "Systems of linear constraints over the integers, and why integrality changes the answer."
            }
            Concept::LinearRealArithmetic => {
                "Systems of linear constraints over the rationals/reals, decided exactly."
            }
            Concept::Proofs => {
                "Why a solver should emit a checkable certificate, and how a tiny independent checker validates it."
            }
            Concept::SoftwareVerification => {
                "Proving programs safe (or finding a counterexample) with bounded model checking and k-induction."
            }
            Concept::DecidableGeometry => {
                "Euclidean geometry as polynomial constraints over real-closed fields — decidable by Tarski's theorem."
            }
            Concept::LimitsOfAutomation => {
                "Decidable is not the same as provable: where automation must answer `unknown`, and why that is honest."
            }
        }
    }

    /// The concepts that should be taught before this one.
    pub fn prerequisites(self) -> &'static [Concept] {
        match self {
            Concept::PropositionalLogic => &[],
            // Several concepts share the same single prerequisite; arms are
            // grouped by body to keep clippy's `match_same_arms` happy.
            Concept::SatAndCnf
            | Concept::BitVectors
            | Concept::UninterpretedFunctions
            | Concept::LinearIntegerArithmetic => &[Concept::PropositionalLogic],
            Concept::BitwiseIdentities | Concept::ModularArithmetic => &[Concept::BitVectors],
            Concept::BitBlasting => &[Concept::BitVectors, Concept::SatAndCnf],
            Concept::SymbolicExecution => &[Concept::ModularArithmetic],
            Concept::Arrays => &[Concept::UninterpretedFunctions],
            Concept::LinearRealArithmetic => &[Concept::LinearIntegerArithmetic],
            Concept::Proofs => &[Concept::SatAndCnf],
            Concept::SoftwareVerification => &[Concept::SymbolicExecution, Concept::BitBlasting],
            Concept::DecidableGeometry => &[Concept::LinearRealArithmetic],
            Concept::LimitsOfAutomation => &[Concept::Proofs],
        }
    }

    /// The self-checking scenario [`Family`] values that currently exercise this
    /// concept. An empty slice means the concept has no self-checking exercise
    /// yet — a curriculum/coverage gap, not an error.
    pub fn families(self) -> &'static [Family] {
        match self {
            Concept::PropositionalLogic => &[Family::Logic],
            Concept::BitwiseIdentities => &[Family::Identity],
            Concept::ModularArithmetic => &[Family::Arithmetic],
            Concept::SymbolicExecution => &[Family::Mixing, Family::Machine],
            Concept::UninterpretedFunctions => &[Family::Function],
            Concept::Arrays => &[Family::Memory],
            Concept::LinearIntegerArithmetic => &[Family::Integer],
            Concept::LinearRealArithmetic => &[Family::Real],
            Concept::SoftwareVerification => &[Family::Verification],
            // Foundations exercised indirectly, or rungs not yet given a
            // self-checking family (the honest gaps the coverage audit reports).
            Concept::SatAndCnf
            | Concept::BitVectors
            | Concept::BitBlasting
            | Concept::Proofs
            | Concept::DecidableGeometry
            | Concept::LimitsOfAutomation => &[],
        }
    }

    /// Whether this concept has at least one self-checking exercise family.
    pub fn has_exercise(self) -> bool {
        !self.families().is_empty()
    }
}

/// Every concept, in bottom-up declaration order.
pub fn all() -> &'static [Concept] {
    ALL
}

/// The concepts a given scenario [`Family`] exercises (the reverse of
/// [`Concept::families`]).
///
/// Returned in `ALL` declaration order for stability.
pub fn concepts_for_family(family: Family) -> Vec<Concept> {
    ALL.iter()
        .copied()
        .filter(|concept| concept.families().contains(&family))
        .collect()
}

/// A deterministic topological ordering of the concept DAG: every concept
/// appears after all of its [`Concept::prerequisites`].
///
/// Ties are broken by `ALL` declaration order, so the sequence is stable. The
/// returned vector contains every concept exactly once; if it were ever shorter
/// than `ALL` the graph would contain a cycle (asserted in tests).
pub fn topological_order() -> Vec<Concept> {
    let mut emitted: Vec<Concept> = Vec::with_capacity(ALL.len());
    let mut placed: BTreeSet<Concept> = BTreeSet::new();

    // Repeatedly scan in declaration order, emitting any concept whose
    // prerequisites are all already placed. O(n^2) over a tiny n, fully
    // deterministic.
    loop {
        let mut progressed = false;
        for &concept in ALL {
            if placed.contains(&concept) {
                continue;
            }
            if concept
                .prerequisites()
                .iter()
                .all(|prereq| placed.contains(prereq))
            {
                emitted.push(concept);
                placed.insert(concept);
                progressed = true;
            }
        }
        if !progressed {
            break;
        }
    }
    emitted
}

/// The set of concepts a learner can study next: not yet mastered, but with
/// every prerequisite already in `mastered`.
///
/// Returned in `ALL` declaration order for stability.
pub fn frontier(mastered: &BTreeSet<Concept>) -> Vec<Concept> {
    ALL.iter()
        .copied()
        .filter(|concept| !mastered.contains(concept))
        .filter(|concept| {
            concept
                .prerequisites()
                .iter()
                .all(|prereq| mastered.contains(prereq))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn graph_is_acyclic_and_total() {
        // A complete topological order exists iff the graph is acyclic.
        let order = topological_order();
        assert_eq!(
            order.len(),
            ALL.len(),
            "topological_order dropped concepts — the DAG has a cycle"
        );
        let unique: BTreeSet<Concept> = order.iter().copied().collect();
        assert_eq!(unique.len(), ALL.len(), "a concept appeared twice");
    }

    #[test]
    fn topological_order_respects_prerequisites() {
        let order = topological_order();
        let position = |c: Concept| order.iter().position(|&x| x == c).unwrap();
        for &concept in ALL {
            for &prereq in concept.prerequisites() {
                assert!(
                    position(prereq) < position(concept),
                    "{concept:?} taught before its prerequisite {prereq:?}"
                );
            }
        }
    }

    #[test]
    fn prerequisites_reference_earlier_foundations_only() {
        // No concept lists itself; every prerequisite is a real concept.
        for &concept in ALL {
            for &prereq in concept.prerequisites() {
                assert_ne!(concept, prereq, "{concept:?} is its own prerequisite");
                assert!(ALL.contains(&prereq));
            }
        }
    }

    #[test]
    fn frontier_starts_at_the_roots() {
        let mastered = BTreeSet::new();
        let start = frontier(&mastered);
        // With nothing mastered, the frontier is exactly the prerequisite-free
        // roots.
        for concept in &start {
            assert!(concept.prerequisites().is_empty());
        }
        assert!(start.contains(&Concept::PropositionalLogic));
        assert!(!start.contains(&Concept::Proofs));
    }

    #[test]
    fn frontier_opens_after_mastering_prerequisites() {
        let mut mastered = BTreeSet::new();
        mastered.insert(Concept::PropositionalLogic);
        let next = frontier(&mastered);
        assert!(next.contains(&Concept::SatAndCnf));
        assert!(next.contains(&Concept::BitVectors));
        // BitBlasting still needs both BitVectors and SatAndCnf.
        assert!(!next.contains(&Concept::BitBlasting));
    }

    #[test]
    fn slugs_and_titles_are_unique() {
        let slugs: BTreeSet<&str> = ALL.iter().map(|c| c.slug()).collect();
        assert_eq!(slugs.len(), ALL.len(), "duplicate slug");
    }
}
