//! Solver backend interface for the Axeyum automated reasoning stack.
//!
//! This crate owns the Axeyum-side solver contract: the [`SolverBackend`]
//! trait, [`CheckResult`] with `Unknown` as a first-class outcome, and
//! [`Model`]s keyed by Axeyum symbols rather than backend AST pointers.
//! Native backends are feature-gated adapters implementing this contract;
//! the default build has no C or C++ dependency (ADR-0002).
//!
//! Enable the `z3` feature for the [`Z3Backend`] oracle (system libz3 via
//! pkg-config) or `z3-static` for a hermetic prebuilt libz3. The milestone
//! M0 doctest lives on the `Z3Backend` module.
//!
//! Design notes: `docs/research/03-architecture/backend-model.md`,
//! `incrementality-and-solver-lifecycle.md`, and
//! `07-verification/evidence-and-checking.md` in the repository.

mod abv;
mod aufbv;
mod auto;
mod backend;
mod certify;
mod combined;
mod dpll_t;
mod euf;
mod evidence;
mod incremental;
mod layers;
mod lia;
mod lra;
mod model;
mod proof;
mod sat_bv_backend;
mod smtlib;
mod solver;
#[cfg(feature = "z3")]
mod z3_backend;

pub use abv::check_with_array_elimination;
pub use aufbv::check_with_arrays_and_functions;
pub use auto::{
    check_auto, check_with_quantifiers, prove_unsat_by_ematching, prove_unsat_by_instantiation,
    solve, unsat_core,
};
pub use backend::{
    Capabilities, CheckResult, SolveStats, SolverBackend, SolverConfig, SolverError, UnknownKind,
    UnknownReason,
};
pub use certify::{CertifyOutcome, certify_qf_bv_by_enumeration};
pub use combined::check_with_all_theories;
pub use dpll_t::{
    LemmaLiteral, LraDpllOutcome, LraDpllRefutation, certify_lra_dpll_unsat, check_with_lra_dpll,
};
pub use euf::check_with_function_elimination;
pub use evidence::{
    Evidence, EvidenceReport, ProofOutcome, Provenance, SEMANTICS_VERSION, produce_evidence,
    produce_lra_dpll_evidence, produce_lra_evidence, produce_qf_bv_evidence, prove,
};
pub use incremental::IncrementalBvSolver;
pub use layers::BvLayerStats;
pub use lia::{DEFAULT_INT_WIDTH, check_with_int_blasting};
pub use lra::{
    FarkasAtom, FarkasCertificate, check_with_lra, lra_farkas_certificate, lra_unsat_core,
};
pub use model::Model;
pub use proof::{UnsatProof, UnsatProofOutcome, export_qf_bv_unsat_proof};
pub use sat_bv_backend::SatBvBackend;
pub use smtlib::{SmtLibOutcome, solve_smtlib};
pub use solver::Solver;
#[cfg(feature = "z3")]
pub use z3_backend::Z3Backend;
