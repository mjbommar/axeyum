//! Self-checking consumer scenario models for Axeyum.
//!
//! This crate generates realistic solver-consumer workloads — symbolic
//! execution path conditions, crypto-style mixing-function inversions, and
//! bit-twiddling identities — whose ground truth is established by the
//! `axeyum-ir` evaluator rather than by a native oracle (ADR-0008). It exists
//! to give the pure-Rust backend a corpus that is realistic in shape, scalable
//! in difficulty, oracle-free, and strictly inside the supported lowering
//! subset.
//!
//! Ground truth comes from two oracle-free constructions:
//!
//! - **SAT by concrete execution.** A scenario picks concrete inputs from an
//!   explicit seed, runs a concrete computation over supported BV operators,
//!   and asserts constraints the run satisfies by construction. The concrete
//!   input is carried as a [`Expectation::Sat`] witness and self-verified by
//!   evaluating every query term against it.
//! - **UNSAT by bounded-verified identity.** A scenario asserts the negation of
//!   a bit-vector theorem. [`Scenario::self_check`] confirms no assignment over
//!   the scenario width satisfies the conjunction — exhaustively at small
//!   widths, or over a deterministic sample above the exhaustive threshold.
//!
//! Because the witness/refutation is independent *in kind* from the
//! bit-blast-to-SAT search path, a solver's answer can be cross-checked without
//! trusting another solver.
//!
//! # Example
//!
//! ```
//! use axeyum_scenarios::{full_adder_identity, mixing_inversion, Expectation};
//!
//! // A satisfiable mixing inversion carries a known model.
//! let sat = mixing_inversion(8, 3, 0x1234);
//! sat.self_check().unwrap();
//! assert!(matches!(sat.expectation, Expectation::Sat { .. }));
//!
//! // The negation of the full-adder identity is unsatisfiable.
//! let unsat = full_adder_identity(8);
//! unsat.self_check().unwrap();
//! assert!(matches!(unsat.expectation, Expectation::Unsat { .. }));
//! ```

mod algebra;
mod arithmetic;
mod concept;
mod counting;
mod coverage;
mod exercise;
mod functions;
mod identities;
mod induction;
mod integers;
mod linear_algebra;
mod logic;
mod machine;
mod mathtour;
mod memory;
mod mixing;
mod number_system;
mod number_theory;
mod polynomial;
mod predicate;
mod proof_methods;
mod rationals;
mod real_algebra;
mod reals;
mod relations;
mod render;
mod rng;
mod sets;
mod verification;

use axeyum_ir::{Assignment, IrError, Sort, SymbolId, TermArena, Value, eval};
use axeyum_query::Query;

pub use algebra::{
    addition_associative, additive_inverse, algebra_catalog, composite_modulus_non_invertible,
    field_failure_even, prime_field_all_invertible, subtraction_not_associative, zero_divisor,
};
pub use arithmetic::{
    distributivity_identity, division_roundtrip_identity, division_target, factor_target,
};
pub use concept::{Concept, all as all_concepts, concepts_for_family, frontier, topological_order};
pub use counting::{counting_catalog, permutation_exists, pigeonhole};
pub use coverage::{
    ConceptCoverage, all_catalog_scenarios, audit as coverage_audit, report as coverage_report,
    uncovered_concepts,
};
pub use exercise::{Answer, Difficulty, DifficultyTier, Exercise, Grade};
pub use functions::{function_binary_merge, function_catalog, function_chain, function_lookup};
pub use identities::{
    de_morgan_identity, full_adder_identity, twos_complement_identity, xor_swap_identity,
};
pub use induction::{
    bad_invariant_step, gauss_sum_step, induction_catalog, sum_of_odds_obligations,
};
pub use integers::{integer_catalog, integer_equation, integer_system};
pub use linear_algebra::{
    det_product_2x2, det_product_3x3_f2, linear_algebra_catalog, linear_solve_2x2,
    mult_associative_2x2, transpose_product_2x2,
};
pub use logic::{
    contradiction, de_morgan_law, excluded_middle, logic_catalog, modus_ponens, satisfiable_clause,
};
pub use machine::{conflicting_path, register_machine_path};
pub use mathtour::{
    Decidability, MathNode, NODES as MATH_NODES, Status, node as math_node,
    topological_order as math_topological_order,
};
pub use memory::{memory_catalog, memory_trace};
pub use mixing::mixing_inversion;
pub use number_system::{
    number_system_catalog, order_transitivity, signed_trichotomy, successor_injective,
    unsigned_non_negative,
};
pub use number_theory::{
    bezout_identity, consecutive_product_even, crt_witness, modular_inverse, number_theory_catalog,
    pythagorean_triple, quadratic_nonresidue_unsat, quadratic_residue_sat, rsa_roundtrip,
    square_parity, sum_of_two_squares_none, sum_of_two_squares_sat,
};
pub use polynomial::{
    binomial_square, difference_of_squares, division_with_remainder_identity,
    factorization_identity, polynomial_catalog, quadratic_root,
};
pub use predicate::{
    exists_square_root, fermat_little_theorem, forall_additive_identity, forall_exists_inverse,
    predicate_catalog,
};
pub use proof_methods::{
    case_analysis_elimination, contradiction_odd_square, contrapositive_equivalence,
    counterexample_square_growth, proof_methods_catalog,
};
pub use rationals::{
    density_midpoint, exact_linear_solution, mediant_between, rational_catalog, trichotomy_case,
};
pub use real_algebra::{
    am_gm_instance, nested_intervals_point, quadratic_rational_root, real_algebra_catalog,
};
pub use reals::{real_catalog, real_ratio_equation, real_system};
pub use relations::{
    bijection_witness, injective_composition, no_injection_into_smaller, relation_catalog,
    symmetric_transitive_not_reflexive,
};
pub use render::Renderable;
pub use sets::{absorption, complement_union_is_universe, distributivity, sets_catalog};
pub use verification::{
    abs_non_negative_bug, max_is_an_upper_bound, midpoint_overflow_bug, saturating_add_safe,
    unsigned_overflow_idiom, verification_catalog,
};

pub(crate) use rng::SplitMix64;

/// The largest total input width (summed over all scenario symbols) for which
/// [`Scenario::self_check`] proves UNSAT by exhaustive enumeration. Above this,
/// UNSAT is checked over a deterministic sample and reported as lower
/// assurance.
pub const EXHAUSTIVE_BIT_LIMIT: u32 = 20;

/// Number of deterministic samples drawn when an UNSAT scenario exceeds
/// [`EXHAUSTIVE_BIT_LIMIT`].
pub const SAMPLE_COUNT: u64 = 4096;

/// The family a scenario belongs to, for grouping and reporting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Family {
    /// Propositional-logic tautologies/contradictions over Boolean variables,
    /// proven by exhaustive truth tables (the curriculum's bottom rung).
    Logic,
    /// Crypto-style mixing-function inversion (satisfiable by construction).
    Mixing,
    /// Straight-line register-machine path condition.
    Machine,
    /// Negation of a bit-vector identity (unsatisfiable).
    Identity,
    /// Multiplication queries: factoring (satisfiable) and the negation of a
    /// distributivity identity (unsatisfiable).
    Arithmetic,
    /// Memory (`QF_ABV`) store/load traces (satisfiable by construction).
    Memory,
    /// Uninterpreted-function (`QF_UFBV`) application traces (satisfiable by
    /// construction).
    Function,
    /// Linear integer arithmetic (`QF_LIA`) constraint systems (satisfiable by
    /// construction).
    Integer,
    /// Linear real arithmetic (`QF_LRA`) constraint systems (satisfiable by
    /// construction).
    Real,
    /// Number theory: gcd/Bézout, modular inverses, and parity identities (the
    /// first destination of the formal mathematics tour).
    NumberTheory,
    /// Linear algebra: fixed-size matrix identities and linear-system solving
    /// over bit-vector arithmetic.
    LinearAlgebra,
    /// Counting & combinatorics: the pigeonhole principle and counting
    /// identities.
    Counting,
    /// Abstract algebra: finite-group/ring/field axiom checks over Cayley tables.
    Algebra,
    /// Polynomials: fixed-degree polynomial identities and roots over bit-vector
    /// arithmetic.
    Polynomial,
    /// Software verification: bounded safety theorems and bug counterexamples
    /// (abs/max/swap/overflow), the "Hello, World" of verification.
    Verification,
    /// Finite sets: set-algebra laws (distributivity, absorption, complement)
    /// over subset bitmasks.
    Sets,
    /// Predicate logic: closed quantified (`∀`/`∃`) theorems over a finite
    /// bit-vector domain, including quantifier alternation.
    Predicate,
    /// Number systems: signed-order (trichotomy, transitivity) and naturals
    /// (non-negativity, successor injectivity) theorems.
    NumberSystem,
    /// Proof methods: contrapositive, contradiction, case analysis, and
    /// disproof-by-counterexample as refutation shapes.
    ProofMethods,
    /// Induction: base and step obligations of concrete invariants as
    /// quantifier-free bit-vector facts, plus a failing step for a false
    /// invariant.
    Induction,
    /// Relations & functions: packed finite function tables and relations —
    /// injectivity, bijections, composition, and equivalence-axiom facts.
    Relation,
    /// Rational numbers: exact ordered-field facts over `QF_LRA` — density,
    /// the mediant inequality, exact linear solving, and trichotomy.
    Rational,
    /// Real numbers: algebraic (real-closed-field) facts with exact rational
    /// witnesses — quadratic roots, an AM–GM instance, and nested intervals.
    RealAlgebra,
}

impl Family {
    /// A short, stable slug for names and artifacts.
    pub fn slug(self) -> &'static str {
        match self {
            Family::Logic => "logic",
            Family::Mixing => "mixing",
            Family::Machine => "machine",
            Family::Identity => "identity",
            Family::Arithmetic => "arithmetic",
            Family::Memory => "memory",
            Family::Function => "function",
            Family::Integer => "integer",
            Family::Real => "real",
            Family::NumberTheory => "number_theory",
            Family::LinearAlgebra => "linear_algebra",
            Family::Counting => "counting",
            Family::Algebra => "algebra",
            Family::Polynomial => "polynomial",
            Family::Verification => "verification",
            Family::Sets => "sets",
            Family::Predicate => "predicate",
            Family::NumberSystem => "number_system",
            Family::ProofMethods => "proof_methods",
            Family::Induction => "induction",
            Family::Relation => "relation",
            Family::Rational => "rational",
            Family::RealAlgebra => "real_algebra",
        }
    }
}

/// The known ground-truth status of a [`Scenario`].
#[derive(Debug, Clone)]
pub enum Expectation {
    /// Satisfiable, with a known-good model derived from concrete execution.
    Sat {
        /// An assignment that satisfies every query term, verified by the
        /// evaluator in [`Scenario::self_check`].
        witness: Assignment,
    },
    /// Unsatisfiable, with the evidence backing the claim.
    Unsat {
        /// How the absence of a model was established.
        evidence: UnsatEvidence,
    },
}

impl Expectation {
    /// Returns `true` for [`Expectation::Sat`].
    pub fn is_sat(&self) -> bool {
        matches!(self, Expectation::Sat { .. })
    }

    /// Returns `true` for [`Expectation::Unsat`].
    pub fn is_unsat(&self) -> bool {
        matches!(self, Expectation::Unsat { .. })
    }
}

/// How an UNSAT expectation was established by [`Scenario::self_check`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnsatEvidence {
    /// Every assignment over the scenario width was checked; none is a model.
    /// This is a genuine proof of UNSAT over the finite domain.
    Exhaustive {
        /// Number of assignments enumerated.
        cases: u64,
    },
    /// A deterministic sample of assignments was checked; none is a model.
    /// Lower assurance: a model could exist outside the sample.
    Sampled {
        /// Number of assignments sampled.
        cases: u64,
        /// Seed used to draw the sample.
        seed: u64,
    },
}

/// A self-checking consumer scenario: an arena, a query, and a known status.
///
/// The arena and query are self-contained, so a scenario can be handed
/// directly to any [`axeyum_query::Query`]-aware backend.
#[derive(Debug)]
pub struct Scenario {
    /// Stable, descriptive name (includes family and parameters).
    pub name: String,
    /// The family this scenario belongs to.
    pub family: Family,
    /// The bit width used for the scenario's symbols.
    pub width: u32,
    /// The seed used to generate the scenario (`0` for deterministic
    /// parameter-only families such as identities).
    pub seed: u64,
    /// The arena owning every term referenced by [`Scenario::query`].
    pub arena: TermArena,
    /// The query a backend should decide.
    pub query: Query,
    /// The known ground-truth status.
    pub expectation: Expectation,
}

impl Scenario {
    /// Verifies the scenario's stated [`Expectation`] using only the evaluator.
    ///
    /// For [`Expectation::Sat`], every query term must evaluate to `true` under
    /// the witness. For [`Expectation::Unsat`], no assignment over the scenario
    /// width may satisfy the conjunction of query terms (checked exhaustively
    /// below [`EXHAUSTIVE_BIT_LIMIT`], sampled above it). On success an UNSAT
    /// scenario's evidence is recomputed and returned so callers can see how it
    /// was established.
    ///
    /// # Errors
    ///
    /// Returns [`SelfCheckError`] if the witness fails to satisfy a SAT
    /// scenario, if a model is found for an UNSAT scenario, or if evaluation
    /// fails (for example, an unbound symbol).
    pub fn self_check(&self) -> Result<UnsatEvidence, SelfCheckError> {
        match &self.expectation {
            Expectation::Sat { witness } => {
                self.check_witness(witness)?;
                // A satisfied SAT scenario has no UNSAT evidence; report the
                // trivial exhaustive form so the signature stays uniform.
                Ok(UnsatEvidence::Exhaustive { cases: 0 })
            }
            Expectation::Unsat { evidence } => self.check_unsat(*evidence),
        }
    }

    fn check_witness(&self, witness: &Assignment) -> Result<(), SelfCheckError> {
        for term in self.query.solver_terms() {
            match eval(&self.arena, term, witness) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => {
                    return Err(SelfCheckError::WitnessUnsatisfied { term });
                }
                Ok(value) => return Err(SelfCheckError::NonBoolean { term, value }),
                Err(error) => return Err(SelfCheckError::Eval { term, error }),
            }
        }
        Ok(())
    }

    fn check_unsat(&self, claimed: UnsatEvidence) -> Result<UnsatEvidence, SelfCheckError> {
        let symbols: Vec<(SymbolId, Sort)> = self
            .arena
            .symbols()
            .map(|(symbol, _name, sort)| (symbol, sort))
            .collect();
        let total_bits = symbols
            .iter()
            .map(|(_, sort)| sort_bits(*sort))
            .sum::<u32>();

        if total_bits <= EXHAUSTIVE_BIT_LIMIT {
            let cases = 1u64 << total_bits;
            for code in 0..cases {
                let assignment = decode_assignment(&symbols, u128::from(code));
                if self.is_model(&assignment)? {
                    return Err(SelfCheckError::UnexpectedModel { assignment });
                }
            }
            Ok(UnsatEvidence::Exhaustive { cases })
        } else {
            let seed = match claimed {
                UnsatEvidence::Sampled { seed, .. } => seed,
                UnsatEvidence::Exhaustive { .. } => self.seed ^ 0x5343_454e_4f5f_5341,
            };
            let mut rng = SplitMix64::new(seed);
            for _ in 0..SAMPLE_COUNT {
                let assignment = sample_assignment(&symbols, &mut rng);
                if self.is_model(&assignment)? {
                    return Err(SelfCheckError::UnexpectedModel { assignment });
                }
            }
            Ok(UnsatEvidence::Sampled {
                cases: SAMPLE_COUNT,
                seed,
            })
        }
    }

    /// Returns whether `assignment` satisfies every query term, judged purely by
    /// the evaluator.
    ///
    /// This is the **sound grading primitive**: a candidate answer is accepted
    /// only because the evaluator (a small, trusted checker) confirms it
    /// satisfies the original constraints — never because a search returned
    /// `sat`. See [`Exercise`].
    ///
    /// # Errors
    ///
    /// Returns [`SelfCheckError::Eval`] if a term fails to evaluate (for example,
    /// the assignment leaves an input symbol unbound) and
    /// [`SelfCheckError::NonBoolean`] if a query term is not Boolean.
    pub fn is_satisfied_by(&self, assignment: &Assignment) -> Result<bool, SelfCheckError> {
        self.is_model(assignment)
    }

    /// Returns `true` if `assignment` satisfies every query term.
    fn is_model(&self, assignment: &Assignment) -> Result<bool, SelfCheckError> {
        for term in self.query.solver_terms() {
            match eval(&self.arena, term, assignment) {
                Ok(Value::Bool(true)) => {}
                Ok(Value::Bool(false)) => return Ok(false),
                Ok(value) => return Err(SelfCheckError::NonBoolean { term, value }),
                Err(error) => return Err(SelfCheckError::Eval { term, error }),
            }
        }
        Ok(true)
    }
}

/// Why a [`Scenario::self_check`] failed.
#[derive(Debug, Clone)]
pub enum SelfCheckError {
    /// A SAT scenario's witness did not satisfy a query term.
    WitnessUnsatisfied {
        /// The unsatisfied term.
        term: axeyum_ir::TermId,
    },
    /// An UNSAT scenario had a satisfying assignment, so it is not UNSAT.
    UnexpectedModel {
        /// The assignment that satisfied the conjunction.
        assignment: Assignment,
    },
    /// A query term evaluated to a non-Boolean value (internal invariant).
    NonBoolean {
        /// The offending term.
        term: axeyum_ir::TermId,
        /// The non-Boolean value.
        value: Value,
    },
    /// Evaluation failed, usually due to a missing symbol binding.
    Eval {
        /// The term that failed to evaluate.
        term: axeyum_ir::TermId,
        /// The underlying evaluator error.
        error: IrError,
    },
}

impl core::fmt::Display for SelfCheckError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SelfCheckError::WitnessUnsatisfied { term } => {
                write!(f, "witness did not satisfy term #{}", term.index())
            }
            SelfCheckError::UnexpectedModel { .. } => {
                write!(f, "scenario claimed UNSAT but a satisfying model exists")
            }
            SelfCheckError::NonBoolean { term, value } => {
                write!(f, "term #{} evaluated to non-Boolean {value}", term.index())
            }
            SelfCheckError::Eval { term, error } => {
                write!(f, "term #{} failed evaluation: {error}", term.index())
            }
        }
    }
}

impl core::error::Error for SelfCheckError {}

/// A deterministic catalog of scenarios spanning all families and a range of
/// sizes, for benchmarking and regression coverage.
///
/// Every scenario in the catalog passes [`Scenario::self_check`]; sizes are
/// chosen to stay inside the exhaustive UNSAT-verification budget.
pub fn catalog() -> Vec<Scenario> {
    let mut scenarios = Vec::new();
    for width in [4u32, 8, 16] {
        for (round_index, rounds) in [2usize, 4, 8].into_iter().enumerate() {
            let seed = 0xA5A5_0000_u64 ^ ((u64::from(width) << 8) | round_index as u64);
            scenarios.push(mixing_inversion(width, rounds, seed));
        }
        for (step_index, steps) in [3usize, 6].into_iter().enumerate() {
            let seed = 0x1357_0000_u64 ^ ((u64::from(width) << 8) | step_index as u64);
            scenarios.push(register_machine_path(width, steps, seed));
        }
    }
    for width in [4u32, 8] {
        scenarios.push(full_adder_identity(width));
        scenarios.push(xor_swap_identity(width));
        scenarios.push(de_morgan_identity(width));
        scenarios.push(twos_complement_identity(width));
        scenarios.push(conflicting_path(width, 0x2468 ^ u64::from(width)));
        scenarios.push(factor_target(width, 0x9753 ^ u64::from(width)));
        scenarios.push(division_target(width, 0x1d2c ^ u64::from(width)));
        scenarios.push(division_roundtrip_identity(width));
    }
    // Distributivity self-checks exhaustively (3 symbols), so keep its widths
    // inside the enumeration budget (3 * width <= EXHAUSTIVE_BIT_LIMIT).
    for width in [3u32, 4] {
        scenarios.push(distributivity_identity(width));
    }
    scenarios
}

/// The number of bits a sort contributes to the enumeration domain.
fn sort_bits(sort: Sort) -> u32 {
    match sort {
        Sort::Bool => 1,
        Sort::BitVec(width) => width,
        // Floating point enumerates over its `exp + sig`-bit pattern.
        Sort::Float { exp, sig } => exp + sig,
        // No scenario family declares array or integer symbols for finite
        // enumeration (arrays via elimination, ADR-0010; integers are not in the
        // enumerable domain, ADR-0014).
        Sort::Array { .. } => {
            unreachable!("scenarios do not declare array symbols for enumeration")
        }
        Sort::Int => {
            unreachable!("scenarios do not declare integer symbols for enumeration")
        }
        Sort::Real => {
            unreachable!("scenarios do not declare real symbols for enumeration")
        }
        Sort::Datatype(_) => {
            unreachable!("scenarios do not declare datatype symbols for enumeration")
        }
        Sort::Uninterpreted(_) => {
            unreachable!("scenarios do not declare uninterpreted-sort symbols for enumeration")
        }
        Sort::Seq(_) => {
            unreachable!("scenarios do not declare sequence symbols for enumeration")
        }
    }
}

/// Decodes a flat bit code into an assignment over `symbols`.
///
/// Symbols are filled from the low bits of `code` in declaration order.
fn decode_assignment(symbols: &[(SymbolId, Sort)], code: u128) -> Assignment {
    let mut assignment = Assignment::new();
    let mut offset = 0u32;
    for &(symbol, sort) in symbols {
        let bits = sort_bits(sort);
        let field = (code >> offset) & mask(bits);
        assignment.set(symbol, decode_value(sort, field));
        offset += bits;
    }
    assignment
}

/// Draws a deterministic random assignment over `symbols`.
fn sample_assignment(symbols: &[(SymbolId, Sort)], rng: &mut SplitMix64) -> Assignment {
    let mut assignment = Assignment::new();
    for &(symbol, sort) in symbols {
        let field = rng.next_u128() & mask(sort_bits(sort));
        assignment.set(symbol, decode_value(sort, field));
    }
    assignment
}

fn decode_value(sort: Sort, field: u128) -> Value {
    match sort {
        Sort::Bool => Value::Bool(field & 1 == 1),
        Sort::BitVec(width) => Value::Bv {
            width,
            value: field,
        },
        Sort::Float { exp, sig } => Value::Bv {
            width: exp + sig,
            value: field,
        },
        Sort::Array { .. } => {
            unreachable!("scenarios do not declare array symbols for enumeration")
        }
        Sort::Int => {
            unreachable!("scenarios do not declare integer symbols for enumeration")
        }
        Sort::Real => {
            unreachable!("scenarios do not declare real symbols for enumeration")
        }
        Sort::Datatype(_) => {
            unreachable!("scenarios do not declare datatype symbols for enumeration")
        }
        Sort::Uninterpreted(_) => {
            unreachable!("scenarios do not declare uninterpreted-sort symbols for enumeration")
        }
        Sort::Seq(_) => {
            unreachable!("scenarios do not declare sequence symbols for enumeration")
        }
    }
}

/// Low-`width` bit mask as a `u128`.
pub(crate) fn mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn catalog_scenarios_all_self_check() {
        for scenario in catalog() {
            scenario.self_check().unwrap_or_else(|error| {
                panic!("scenario {} failed self-check: {error}", scenario.name)
            });
        }
    }

    #[test]
    fn memory_catalog_scenarios_all_self_check() {
        let scenarios = memory_catalog();
        assert!(!scenarios.is_empty());
        for scenario in scenarios {
            assert_eq!(scenario.family, Family::Memory);
            scenario.self_check().unwrap_or_else(|error| {
                panic!(
                    "memory scenario {} failed self-check: {error}",
                    scenario.name
                )
            });
        }
    }

    #[test]
    fn catalog_covers_every_family() {
        let scenarios = catalog();
        for family in [
            Family::Mixing,
            Family::Machine,
            Family::Identity,
            Family::Arithmetic,
        ] {
            assert!(
                scenarios.iter().any(|s| s.family == family),
                "catalog is missing family {family:?}"
            );
        }
    }

    #[test]
    fn exhaustive_unsat_evidence_is_a_real_proof() {
        let scenario = full_adder_identity(4);
        match scenario.self_check().unwrap() {
            UnsatEvidence::Exhaustive { cases } => assert_eq!(cases, 1 << 8),
            sampled @ UnsatEvidence::Sampled { .. } => {
                panic!("expected exhaustive evidence, got {sampled:?}")
            }
        }
    }

    #[test]
    fn corrupting_a_witness_is_detected() {
        let mut scenario = mixing_inversion(8, 3, 0x99);
        // Replace the witness with an empty assignment: evaluation must fail on
        // the unbound input symbol rather than silently passing.
        scenario.expectation = Expectation::Sat {
            witness: Assignment::new(),
        };
        assert!(matches!(
            scenario.self_check(),
            Err(SelfCheckError::Eval { .. })
        ));
    }
}
