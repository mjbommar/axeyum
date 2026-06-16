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
mod bitblast_miter;
mod bmc;
pub mod capabilities;
mod cardinality;
mod certify;
mod combined;
mod datatype_elim;
mod datatype_native;
mod distinct;
mod dpll_lia;
mod dpll_t;
mod enums;
mod euf;
mod euf_egraph;
/// Floating-point (IEEE 754) formula builders — predicates, classification, sign
/// ops, equality, ordering — re-exported from the `axeyum-fp` crate (extracted so
/// the SMT-LIB front-end can share them without depending on the solver). FP
/// values are `BitVec(eb + sb)`; see the module docs.
pub use axeyum_fp as fp;
mod evidence;
mod faithfulness;
mod incremental;
mod layers;
mod lazy_bv;
mod lia;
mod lra;
mod maxsat;
mod model;
mod nra;
mod optimize;
mod pb;
mod preprocess;
mod proof;
mod qinst_egraph;
mod records;
mod sat_bv_backend;
mod smtlib;
mod solver;
mod strategy;
/// Bounded-length string theory by bit-vector lowering (no IR sort): `str.len`,
/// `str.=`, `str.at`, literals over byte strings of length `0..=max_len`.
pub mod strings;
mod symexec;
pub mod trust;
#[cfg(feature = "z3")]
mod z3_backend;

pub use abv::check_with_array_elimination;
pub use aufbv::check_with_arrays_and_functions;
pub use auto::{
    check_auto, check_with_quantifiers, prove_unsat_by_ematching, prove_unsat_by_instantiation,
    prove_unsat_by_mbqi, solve, unsat_core,
};
pub use backend::{
    Capabilities, CheckResult, SolveStats, SolverBackend, SolverConfig, SolverError, UnknownKind,
    UnknownReason,
};
pub use bitblast_miter::{
    BitblastMiterOutcome, EndToEndUnsatOutcome, certify_bitblast_by_miter,
    certify_qf_bv_unsat_end_to_end,
};
pub use bmc::{
    BmcOutcome, CertifiedSafetyOutcome, SafetyCertificate, SafetyOutcome, TransitionSystem,
    bounded_model_check, bounded_model_check_with_memory, certify_safety_k_induction,
    prove_safety_k_induction,
};
pub use cardinality::{at_least, at_most, exactly};
pub use certify::{CertifyOutcome, certify_qf_bv_by_enumeration};
pub use combined::check_with_all_theories;
pub use datatype_elim::check_with_datatype_elimination;
pub use datatype_native::check_with_datatype_native;
pub use distinct::distinct;
pub use dpll_lia::{
    ArithDpllOutcome, ArithDpllRefutation, ArithLemmaLiteral, certify_arith_dpll_unsat,
    check_with_arith_dpll, check_with_lia_dpll,
};
pub use dpll_t::{
    LemmaLiteral, LraDpllOutcome, LraDpllRefutation, certify_lra_dpll_unsat, check_with_lra_dpll,
};
pub use enums::{EnumError, EnumSort, EnumVar};
pub use euf::check_with_function_elimination;
pub use euf_egraph::{EufConflict, check_qf_uf, prove_unsat_by_congruence, prove_unsat_lazy};
pub use evidence::{
    Evidence, EvidenceReport, LayerVersions, ProofOutcome, Provenance, SEMANTICS_VERSION,
    produce_evidence, produce_lra_dpll_evidence, produce_lra_evidence, produce_qf_bv_evidence,
    prove,
};
pub use faithfulness::{FaithfulnessOutcome, check_qf_bv_faithfulness};
pub use fp::FloatFormat;
pub use incremental::{AssumptionOutcome, IncrementalBvSolver};
pub use layers::BvLayerStats;
pub use lazy_bv::{LazyBvOutcome, check_lazy_bv_abstraction, solve_lazy_bv_abstraction};
pub use lia::{DEFAULT_INT_WIDTH, check_with_int_blasting};
pub use lra::{
    FarkasAtom, FarkasCertificate, check_with_lia_simplex, check_with_lra, check_with_lra_simplex,
    lra_farkas_certificate, lra_unsat_core,
};
pub use maxsat::{max_satisfiable, max_satisfiable_weighted};
pub use model::Model;
pub use nra::check_with_nra;
pub use optimize::{
    OptOutcome, maximize_bv, maximize_bv_signed, maximize_lia, minimize_bv, minimize_bv_signed,
    minimize_lia,
};
pub use pb::{pb_eq, pb_ge, pb_le};
pub use preprocess::check_with_preprocessing;
pub use proof::{
    UnsatProof, UnsatProofOutcome, export_datatype_unsat_proof, export_qf_abv_unsat_proof,
    export_qf_aufbv_unsat_proof, export_qf_bv_unsat_proof, export_qf_lia_unsat_proof,
    export_qf_uf_unsat_proof,
};
pub use qinst_egraph::instantiate_forall_via_egraph;
pub use records::{RecordError, RecordSort};
pub use sat_bv_backend::SatBvBackend;
pub use smtlib::{
    SmtLibOutcome, optimize_smtlib, optimize_smtlib_lexicographic, solve_smtlib,
    solve_smtlib_get_value, solve_smtlib_incremental, solve_smtlib_unsat_core,
};
pub use solver::Solver;
pub use strategy::{Strategy, solve_with_strategy};
pub use symexec::{Branch, PathStatus, SymbolicExecutor};
pub use trust::{ALL_TRUST_IDS, TrustId, TrustStep, trust_ledger_markdown};
#[cfg(feature = "z3")]
pub use z3_backend::Z3Backend;
