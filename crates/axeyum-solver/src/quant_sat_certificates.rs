//! Certificate *data* for satisfiable quantifiers, separated from its checkers.
//!
//! [`Model`](crate::Model) carries these certificates so a `sat` verdict on a
//! quantified query can be replayed. Because each type was defined next to its
//! *checker*, that made the crate's base value type depend on five quantifier
//! checker modules, and through two of them on the dispatcher, the `QF_BV` route,
//! the e-graph, the theory solvers, and back to `Model`: one dependency cycle of
//! **65 modules and 115,840 lines**, half the crate. Holding the data here
//! leaves a largest cycle of 24 modules -- measured, not estimated, by
//! `scripts/analyze_solver_module_graph.py`, which now gates it.
//!
//! The rule this module exists to enforce: a value type may depend on the
//! *shape* of a certificate, never on the search or the checker that produces
//! it. So the plain data lives here, depending only on `axeyum-ir` and
//! [`UnsatProof`](crate::proof::UnsatProof), and each checker module re-exports
//! its own types from here. Every historical path -- `crate::quant_sat_cert::X`,
//! `crate::quant_bool_model_sat::X`, and the crate-root facade -- resolves
//! unchanged, which is what makes the move invisible to consumers.
//!
//! Nothing here is trusted. The checkers
//! ([`check_quantified_skolem_sat`](crate::quant_sat_cert::check_quantified_skolem_sat),
//! [`check_quantified_bool_model_sat`](crate::quant_bool_model_sat::check_quantified_bool_model_sat),
//! and the three beside them) re-derive every structural fact from the original
//! assertion; these structs are the proposal, not the proof.

use axeyum_ir::{Rational, SymbolId, TermId, Value};

use crate::proof::UnsatProof;

/// A checked Skolem witness for one supported universally closed assertion.
///
/// The IDs refer only to atoms in the caller's original arena. The synthesized
/// affine/source expression is owned by the certificate, so it remains
/// replayable when solving occurred on an arena clone.
/// [`check_quantified_skolem_sat`](crate::quant_sat_cert::check_quantified_skolem_sat)
/// re-derives every structural fact from `assertion`; no field is trusted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedSkolemSatCertificate {
    /// The exact original quantified assertion covered by this certificate.
    pub assertion: TermId,
    /// The leading universal binders, outermost first.
    pub universals: Vec<SymbolId>,
    /// The single existential binder witnessed by `witness`.
    pub existential: SymbolId,
    /// An owned expression recipe over original-arena terms that witnesses the
    /// existential. Arithmetic recipes are affine. For bit-vectors, the exact
    /// source-term encoding documented by [`AffineSkolemWitness`] is supported.
    pub witness: AffineSkolemWitness,
}

/// Arena-stable arithmetic-affine or exact bit-vector source-term witness.
///
/// For `Int`/`Real`, this represents `sum(coeff_i * atom_i) + constant`.
/// `terms` must be strictly ordered by `TermId`, contain no zero coefficient,
/// and refer only to quantifier-free, same-sort atoms over the universal binders.
///
/// For a bit-vector existential, ADR-0141 defines one deliberately different,
/// exact-source recipe: `terms` contains exactly one original-arena,
/// quantifier-free, same-width term over only the universal binders, its
/// coefficient is one, and `constant` is zero. The checker does not interpret
/// rational arithmetic modulo the BV width. It substitutes that exact term into
/// the untouched source and grants SAT only when the small checker proves the
/// resulting equality or non-strict order by reflexivity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AffineSkolemWitness {
    /// Deterministically ordered `(atom, coefficient)` pairs.
    pub terms: Vec<(TermId, Rational)>,
    /// The affine constant.
    pub constant: Rational,
}

/// Independently checked reason that a complete free-Boolean model satisfies
/// one quantified assertion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantifiedBoolModelSatProof {
    /// Boolean structure, bounded Boolean enumeration, and affine integer
    /// normalization prove the untouched assertion directly (ADR-0107/0123).
    Structural,
    /// Opening admitted positive universals under the complete free-Boolean
    /// model leaves a `QF_BV` validity whose negation has this checked proof.
    PositiveUniversalQfBv {
        /// Source-bound refutation of the deterministically rebuilt residual.
        residual_proof: UnsatProof,
    },
}

/// A checked free-Boolean interpretation for one original quantified assertion.
///
/// Values are strictly ordered by symbol ID and cover exactly the assertion's
/// free Boolean symbols. Canonical model replay checks both this structure and
/// agreement with the enclosing [`Model`](crate::Model).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedBoolModelSatCertificate {
    /// The untouched original assertion proved by this certificate.
    pub assertion: TermId,
    /// Complete free-Boolean interpretation for that assertion.
    pub values: Vec<(SymbolId, bool)>,
    /// Independently checked source-level proof mode.
    pub proof: QuantifiedBoolModelSatProof,
}

/// The independently checked proof attached to one quantified BV assertion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QuantifiedBvModelSatProof {
    /// A direct universal body is true because a BV equality below its Boolean
    /// structure has affine LSB forms that differ for every binder assignment.
    AffineLsbUniversal,
    /// A direct negated universal is true at this complete binder assignment.
    NegatedUniversalWitness {
        /// Universal binders, outermost first.
        binders: Vec<SymbolId>,
        /// One exact Bool/BV value for every binder.
        values: Vec<Value>,
    },
    /// A directly negated existential implication is false at every binder
    /// value because its ground facts hold, its ground conclusion is false,
    /// and its sole binder-dependent interval implication is contained.
    NegatedExistentialIntervalImplication {
        /// The single existential binder named by the untouched source.
        binder: SymbolId,
    },
    /// A directly negated existential implication is false at every binder
    /// value because an exact ground-zero signed-division factor annihilates
    /// the sole binder-dependent product obligation.
    NegatedExistentialZeroProductImplication {
        /// The single existential binder named by the untouched source.
        binder: SymbolId,
    },
}

/// A complete free-BV interpretation and source-level proof for one assertion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedBvModelSatCertificate {
    /// The untouched original assertion covered by this certificate.
    pub assertion: TermId,
    /// Exact, strictly ordered values for every free symbol in the assertion.
    pub free_values: Vec<(SymbolId, Value)>,
    /// The source-level proof checked independently from candidate search.
    pub proof: QuantifiedBvModelSatProof,
}

/// A concrete outer witness that makes an exact guarded quantified assertion true.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedGuardSatCertificate {
    /// The untouched original assertion covered by this certificate.
    pub assertion: TermId,
    /// The assertion's outer existential binder.
    pub existential: SymbolId,
    /// A concrete bit-vector value for `existential`.
    pub witness: Value,
}

/// A checked finite-profile model witness for one almost-uninterpreted assertion.
///
/// Deliberately minimal: the checker
/// ([`check_quantified_uf_model_sat`](crate::quant_uf_model_sat_cert::check_quantified_uf_model_sat))
/// trusts neither a search-generated candidate list nor any derived profile
/// metadata. It reconstructs the complete finite representative set from
/// `assertion` and the model's finite function tables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuantifiedUfModelSatCertificate {
    /// Exact original quantified assertion covered by this certificate.
    pub assertion: TermId,
    /// Exact outer source binder, redundantly recorded so stale/tampered
    /// certificates fail closed before finite-profile evaluation. The assertion
    /// itself binds the complete leading prefix.
    pub binder: SymbolId,
}
