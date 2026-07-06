//! Solver backend interface for the Axeyum automated reasoning stack.
//!
//! This crate owns the Axeyum-side solver contract: the [`SolverBackend`]
//! trait, [`CheckResult`] with `Unknown` as a first-class outcome, and
//! [`Model`]s keyed by Axeyum symbols rather than backend AST pointers.
//! Native backends are feature-gated adapters implementing this contract;
//! the default build has no C or C++ dependency (ADR-0002).
//!
//! Enable the `z3` feature for the `Z3Backend` oracle (system libz3 via
//! pkg-config) or `z3-static` for a hermetic prebuilt libz3. The milestone
//! M0 doctest lives on the `Z3Backend` module. (Rendered as plain code, not an
//! intra-doc link, so the crate docs build with or without the `z3` feature —
//! the type only exists when that feature is enabled.)
//!
//! Design notes: `docs/research/03-architecture/backend-model.md`,
//! `incrementality-and-solver-lifecycle.md`, and
//! `07-verification/evidence-and-checking.md` in the repository.

mod abduct;
mod abv;
mod alethe_lra;
mod array_axiom;
mod array_binary_search;
mod array_bv_abs;
mod array_fifo;
mod array_finite;
mod array_memcpy;
mod array_sort2;
mod array_write_chain;
mod array_xor_swap;
mod aufbv;
mod auto;
mod backend;
mod bitblast_alethe;
mod bitblast_miter;
mod bmc;
mod bool_euf;
mod bool_simplify;
mod bv2nat_blast;
mod bv2nat_bound;
mod bv_defined_enum;
mod bv_forall_nonconstant;
mod bv_interpolant;
mod bv_uf_local;
pub mod capabilities;
mod cardinality;
mod cdclt;
mod certify;
mod combined;
mod combined_theory;
mod combined_theory_lia;
mod counterexample;
mod datatype_acyclicity;
mod datatype_elim;
mod datatype_native;
mod distinct;
mod dpll_lia;
mod dpll_t;
mod enums;
mod euf;
mod euf_alethe;
mod euf_egraph;
mod euf_interpolant;
/// Floating-point (IEEE 754) formula builders — predicates, classification, sign
/// ops, equality, ordering — re-exported from the `axeyum-fp` crate (extracted so
/// the SMT-LIB front-end can share them without depending on the solver). FP
/// values are `BitVec(eb + sb)`; see the module docs.
pub use axeyum_fp as fp;
mod evidence;
mod faithfulness;
mod horn;
mod imc;
mod imc_lia;
mod imc_lra;
mod incremental;
mod int_real_relax;
mod int_reconstruct;
mod interpolant;
mod layers;
mod lazy_bv;
mod lia;
mod lia_gcd;
mod lia_interpolant;
mod lia_interpolant_cnf;
mod lia_online;
mod lra;
mod lra_interpolant_cnf;
mod lra_online;
mod maxsat;
mod mbp;
mod model;
mod nia_linearize;
mod nia_square;
mod nra;
mod nra_even_power;
mod nra_real_root;
mod optimize;
mod pb;
mod pbls;
mod pdr;
mod pdr_lia;
mod pdr_lra;
mod preprocess;
mod proof;
mod qfabv_alethe;
mod qfabv_elim_alethe;
mod qfbv_alethe;
mod qfdt_simp_alethe;
mod qfufbv_alethe;
mod qfuflia_alethe;
mod qinst_egraph;
mod quant_alethe;
mod quant_exists_witness;
mod quant_finite_cert;
mod quant_fourier_motzkin;
mod quant_guarded_int;
mod quant_unsat_universal;
mod quant_vacuous_universal;
mod quant_valid_universal;
mod reconstruct;
mod records;
pub mod route_trace;
mod sat_bv_backend;
mod set_cardinality;
// P1.9 — exact-rational simplex feasibility core; the LRA layer (`lra.rs`) routes
// FM-timeout cases through it (T1.9.2).
mod simplex;
mod skolem_alethe;
mod smtlib;
mod solver;
mod strategy;
mod string_theory;
/// Bounded-length string theory by bit-vector lowering (no IR sort): `str.len`,
/// `str.=`, `str.at`, literals over byte strings of length `0..=max_len`.
pub mod strings;
pub mod support_matrix;
mod symexec;
mod term_identity;
mod theory_combination;
mod toy_bv_vm;
pub mod trust;
mod uf_arith;
mod ufbv_finite;
mod uflia_interpolant;
mod uflia_online;
mod uflra_interpolant;
mod uflra_online;
mod word_alethe;
#[cfg(feature = "z3")]
mod z3_backend;

pub use abduct::{MAX_CANDIDATES, abduct};
pub use abv::{
    ArrayElimUnsatCertificate, CrossStoreArrayDisequalityCertificate, certify_array_elim_unsat,
    check_qf_abv_lazy, check_qf_abv_lazy_row, check_qf_ax_declared_sort_lazy_row,
    check_with_array_elimination, cross_store_array_disequality_refutation,
};
pub use alethe_lra::{
    check_alethe_lra, prove_lia_unsat_alethe, prove_lra_unsat_alethe,
    prove_uflia_opaque_unsat_alethe, prove_uflra_unsat_alethe,
};
pub use array_axiom::{ArrayAxiomKind, ArrayAxiomRefutationCertificate, array_axiom_refutation};
pub use array_binary_search::{BinarySearch16Certificate, binary_search16_refutation};
pub use array_bv_abs::{BvAbstractionRefutationCertificate, bv_abstraction_refutation};
pub use array_fifo::{FifoBc04Certificate, fifo_bc04_refutation, fifo_ia04_sat_model};
pub use array_finite::{
    BoolArrayReadCollapseCertificate, FiniteArrayExtensionalityCertificate,
    FiniteArrayReadEquality, bool_array_read_collapse_refutation,
    finite_array_extensionality_refutation,
};
pub use array_memcpy::{TwoByteMemcpyRefutationCertificate, two_byte_memcpy_refutation};
pub use array_sort2::{
    TwoElementBubbleSortCertificate, TwoElementSelectionSortCertificate,
    two_element_bubble_sort_refutation, two_element_selection_sort_refutation,
};
pub use array_write_chain::{
    AlignedWriteChainCommutationCertificate, aligned_write_chain_commutation_refutation,
};
pub use array_xor_swap::{
    TwoByteXorSwapRoundtripCertificate, TwoCellXorSwapCertificate,
    two_byte_xor_swap_roundtrip_refutation, two_cell_xor_swap_refutation,
};
pub use aufbv::check_with_arrays_and_functions;
pub use auto::{
    BoundedIntBlastCertificate, certify_bounded_int_blast, check_auto, check_auto_explained,
    check_with_quantifiers, prove_unsat_by_ematching, prove_unsat_by_instantiation,
    prove_unsat_by_mbqi, solve, unsat_core,
};
pub use backend::{
    Capabilities, CheckResult, SolveStats, SolverBackend, SolverConfig, SolverError, UnknownKind,
    UnknownReason,
};
pub use bitblast_alethe::bitblast_step;
pub use bitblast_miter::{
    BitblastMiterOutcome, EndToEndUnsatOutcome, certify_bitblast_by_miter,
    certify_qf_bv_unsat_end_to_end,
};
pub use bmc::{
    BmcOutcome, CertifiedSafetyOutcome, SafetyCertificate, SafetyOutcome, TransitionSystem,
    bounded_model_check, bounded_model_check_with_memory, certify_safety_k_induction,
    prove_safety_k_induction,
};
pub use bool_euf::{
    BoolEufExhaustiveCertificate, BoolEufOnlineCertificate, bool_euf_exhaustive_refutation,
    bool_euf_online_refutation,
};
pub use bool_simplify::{BoolSimplificationRefutationCertificate, bool_simplification_refutation};
pub use bv_forall_nonconstant::{
    BvForallNonconstantKind, BvForallNonconstantRefutationCertificate,
    bv_forall_nonconstant_refutation,
};
pub use bv_interpolant::{
    QfBvInterpolantCertificate, qf_bv_interpolant, qf_bv_interpolant_certified,
};
pub use bv_uf_local::{
    BvUfLocalDerivedEquality, BvUfLocalRefutationCertificate, BvUfLocalRefutationKind,
    bv_uf_local_refutation,
};
pub use cardinality::{at_least, at_most, at_most_one, between, exactly, exactly_one};
pub use certify::{CertifyOutcome, certify_finite_bv_by_enumeration, certify_qf_bv_by_enumeration};
pub use combined::check_with_all_theories;
#[doc(hidden)]
pub use combined_theory::{
    IncrementalDecision, PropagationReport, combined_incremental_structure,
    combined_incremental_vs_check, combined_theory_propagations, combined_vs_cold_conjunction,
};
#[doc(hidden)]
pub use combined_theory_lia::{
    IncrementalDecision as IncrementalDecisionLia, combined_incremental_lia_structure,
    combined_incremental_lia_vs_check, combined_lia_vs_cold_conjunction,
    combined_theory_lia_propagations,
};
pub use counterexample::{
    ModelMinimizeObjective, ModelMinimizeOutcome, minimize_model, minimize_model_objectives,
    minimize_model_objectives_with_config, minimize_model_with_config,
};
pub use datatype_acyclicity::prove_datatype_unsat_structurally;
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
pub use euf::{
    AckermannUnsatCertificate, certify_ackermann_unsat, check_qf_ufbv_lazy,
    check_with_function_elimination, check_with_uf_arithmetic, check_with_uf_arithmetic_lazy,
};
pub use euf_alethe::prove_qf_uf_unsat_alethe;
pub use euf_egraph::{
    EufConflict, EufTheory, TheoryLit, TheoryProp, TheorySolver, check_qf_uf,
    check_qf_uf_online_cdclt, check_qf_uf_with_config, prove_unsat_by_congruence, prove_unsat_lazy,
    prove_unsat_qf_uf_online, solve_qf_uf_online,
};
pub use euf_interpolant::{
    QfUfInterpolantCertificate, qf_uf_interpolant, qf_uf_interpolant_certified,
};
pub use evidence::{
    Evidence, EvidenceReport, LayerVersions, ProofOutcome, Provenance, SEMANTICS_VERSION,
    produce_diophantine_evidence, produce_evidence, produce_evidence_minimized,
    produce_evidence_minimized_with_objectives, produce_lra_dpll_evidence, produce_lra_evidence,
    produce_nra_even_power_evidence, produce_nra_evidence, produce_nra_sos_evidence,
    produce_qf_bv_evidence, prove, prove_minimized, prove_minimized_with_objectives,
};
pub use faithfulness::{FaithfulnessOutcome, check_qf_bv_faithfulness};
pub use fp::FloatFormat;
pub use horn::{HornClause, HornModel, HornOutcome, HornSystem, solve_horn};
pub use imc::{ImcOutcome, prove_safety_imc};
pub use imc_lia::{ImcLiaOutcome, prove_safety_imc_lia};
pub use imc_lra::{ImcLraOutcome, prove_safety_imc_lra};
pub use incremental::{AssumptionOutcome, IncrementalBvSolver};
pub use int_reconstruct::{
    IntReconstructCtx, is_int_inequality_refutation, reconstruct_diophantine_proof,
    reconstruct_diophantine_to_lean_module, reconstruct_int_inequality_proof,
    reconstruct_int_inequality_to_lean_module,
};
pub use interpolant::{LraInterpolantCertificate, lra_interpolant, lra_interpolant_certified};
pub use layers::BvLayerStats;
pub use lazy_bv::{
    LazyBvBackend, LazyBvOutcome, check_lazy_bv_abstraction, check_lazy_bv_abstraction_ro,
    solve_lazy_bv_abstraction,
};
pub use lia::{DEFAULT_INT_WIDTH, check_with_int_blasting};
pub use lia_gcd::{
    DiophantineCertificate, Equality, check_diophantine_certificate,
    prove_lia_unsat_by_diophantine, prove_lia_unsat_by_diophantine_certified,
    prove_lia_unsat_by_gcd,
};
pub use lia_interpolant::{LiaInterpolantCertificate, lia_interpolant, lia_interpolant_certified};
pub use lia_interpolant_cnf::lia_interpolant_cnf;
pub use lia_online::{LiaTheory, check_qf_lia_online};
pub use lra::{
    FarkasAtom, FarkasCertificate, check_with_lia_simplex, check_with_lra, check_with_lra_simplex,
    lra_farkas_certificate, lra_unsat_core,
};
pub use lra_interpolant_cnf::lra_interpolant_cnf;
pub use lra_online::{LraTheory, check_qf_lra_online};
pub use maxsat::{
    MaxSatOutcome, max_satisfiable, max_satisfiable_model, max_satisfiable_weighted,
    max_satisfiable_weighted_model,
};
pub use mbp::{mbp_lia, mbp_lra};
pub use model::Model;
pub use nra::check_with_nra;
pub use nra_even_power::{NraEvenPowerRefutationCertificate, nra_even_power_refutation};
pub use nra_real_root::SosCertificate;
pub use optimize::{
    BvLexObjective, LexObjective, LexOutcome, OptOutcome, ParetoOutcome, maximize_bv,
    maximize_bv_signed, maximize_bv_signed_with_config, maximize_bv_with_config, maximize_lia,
    maximize_lia_with_config, minimize_bv, minimize_bv_signed, minimize_bv_signed_with_config,
    minimize_bv_with_config, minimize_lia, minimize_lia_with_config, optimize_bv_box,
    optimize_bv_box_with_config, optimize_bv_lexicographic, optimize_bv_lexicographic_with_config,
    optimize_bv_pareto, optimize_bv_pareto_with_config, optimize_lia_box,
    optimize_lia_box_with_config, optimize_lia_lexicographic,
    optimize_lia_lexicographic_with_config, optimize_lia_pareto, optimize_lia_pareto_with_config,
};
pub use pb::{pb_eq, pb_ge, pb_gt, pb_le, pb_lt};
pub use pbls::{LocalSearchOutcome, PblsBackend, solve_local_search};
pub use pdr::{
    CertifiedPdrOutcome, ChcSafetyCertificate, PdrOutcome, prove_safety_pdr,
    prove_safety_pdr_certified,
};
pub use pdr_lia::{PdrLiaOutcome, prove_safety_pdr_lia};
pub use pdr_lra::{PdrLraOutcome, prove_safety_pdr_lra};
pub use preprocess::check_with_preprocessing;
pub use proof::{
    UnsatProof, UnsatProofOutcome, export_datatype_unsat_proof, export_qf_abv_unsat_proof,
    export_qf_abv_unsat_proof_within, export_qf_aufbv_unsat_proof,
    export_qf_aufbv_unsat_proof_within, export_qf_bv_unsat_proof, export_qf_bv_unsat_proof_within,
    export_qf_lia_unsat_proof, export_qf_uf_unsat_proof,
};
pub use qfabv_alethe::{
    prove_qf_abv_row_diff_alethe_carcara, prove_qf_abv_row_same_alethe_carcara,
    prove_qf_abv_unsat_alethe,
};
pub use qfabv_elim_alethe::prove_qf_abv_unsat_alethe_via_elimination;
pub use qfbv_alethe::{
    prove_qf_bv_unsat_alethe, prove_qf_bv_unsat_alethe_ext_compare,
    prove_qf_bv_unsat_alethe_lowered, prove_qf_bv_unsat_alethe_route2,
};
pub use qfdt_simp_alethe::{
    prove_qf_dt_distinct_alethe_carcara, prove_qf_dt_injective_alethe_carcara,
    prove_qf_dt_unsat_alethe_via_simplification,
};
pub use qfufbv_alethe::prove_qf_ufbv_unsat_alethe;
pub use qfuflia_alethe::prove_qf_uflia_unsat_alethe;
pub use qinst_egraph::{
    instantiate_forall_via_egraph, prove_quantified_unsat_via_egraph, witness_tuples_via_egraph,
};
pub use quant_alethe::prove_quant_unsat_alethe;
pub use quant_finite_cert::{
    GuardedUniversalForm, check_alethe_lra_guarded_inst, check_alethe_lra_guarded_inst_against,
    guarded_universal_form_for_test, prove_finite_int_quant_unsat_alethe,
    prove_finite_int_quant_unsat_uf_alethe,
};
pub use reconstruct::{
    LraReconstructCtx, ProofFragment, ReconstructCtx, ReconstructError,
    prove_const_shift_lowering_to_lean_module, prove_unsat_to_lean, prove_unsat_to_lean_module,
    reconstruct_bitblast_step, reconstruct_cnf_intro_rule, reconstruct_const_shift_lowering,
    reconstruct_eq_step, reconstruct_lra_proof, reconstruct_qf_bv_proof, reconstruct_qf_uf_proof,
    reconstruct_qf_ufbv_proof, reconstruct_quant_unsat_proof, reconstruct_resolution_proof,
    reconstruct_skolem_unsat_proof, reconstruct_sos_proof, scan_proof_fragment,
};
pub use records::{RecordError, RecordSort};
pub use route_trace::{DeclineReason, RouteAttempt, RouteOutcome, RouteTrace, Verdict};
pub use sat_bv_backend::SatBvBackend;
pub use set_cardinality::{SetCardinalityRefutationCertificate, set_cardinality_refutation};
pub use skolem_alethe::{SkolemCert, SkolemRecord, prove_skolem_unsat_alethe};
pub use smtlib::{
    SmtLibModel, SmtLibOutcome, confirm_bounded_string_verdict, decide_word_only_script,
    membership_verdict, online_string_verdict, optimize_smtlib, optimize_smtlib_lexicographic,
    solve_smtlib, solve_smtlib_get_assertions, solve_smtlib_get_assignment, solve_smtlib_get_info,
    solve_smtlib_get_model, solve_smtlib_get_option, solve_smtlib_get_proof,
    solve_smtlib_get_value, solve_smtlib_incremental, solve_smtlib_unsat_core,
    upgrade_bounded_string_unknown, word_route_verdict,
};
pub use solver::{InterpolantOutcome, Solver};
pub use strategy::{Strategy, recommended_portfolio, solve_with_portfolio, solve_with_strategy};
pub use string_theory::{check_qf_s_online_cdclt, check_qf_s_online_cdclt_with_memberships};
pub use symexec::{
    Branch, CfgCheckedOutcome, CfgCheckedReached, CfgConcreteMismatch, CfgExploreConfig,
    CfgExploreOutcome, CfgReached, CfgStep, PathStatus, SymbolicExecutor, SymbolicMemory,
    SymbolicMemoryWrite,
};
pub use term_identity::{
    TermIdentityKind, TermIdentityRefutationCertificate, term_identity_refutation,
};
pub use theory_combination::{
    InterfaceStatus, classify_interface_equalities, combination_conflict, interface_th_eqs,
    propose_interface_equalities, shared_terms,
};
pub use toy_bv_vm::{
    TinyBvBasicBlock, TinyBvCfgEdge, TinyBvCfgEdgeKind, TinyBvConcreteOutcome, TinyBvConcreteStep,
    TinyBvConcreteTrace, TinyBvCoverageReport, TinyBvEdgeCoverageReport,
    TinyBvEdgeTestGenerationReport, TinyBvExploreOutcome, TinyBvInsn, TinyBvProgram,
    TinyBvReachabilityReport, TinyBvReachabilityStatus, TinyBvSafetyReport, TinyBvSafetyStatus,
    TinyBvState, TinyBvTestCase, TinyBvTestGenerationReport, TinyBvTraceBlockStep,
    TinyBvTraceEdgeStep, TinyBvTraceReport, TinyBvTraceSourceStep, TinyBvWitness,
};
pub use trust::{ALL_TRUST_IDS, TrustId, TrustStep, trust_ledger_markdown};
pub use uf_arith::{UfArithCongruenceCertificate, uf_arith_congruence_refutation};
pub use ufbv_finite::{
    BoolUfExhaustiveCertificate, FiniteDomainPigeonholeCertificate, bool_uf_exhaustive_refutation,
    finite_domain_pigeonhole_refutation,
};
pub use uflia_interpolant::{
    UfliaInterpolantCertificate, uflia_interpolant, uflia_interpolant_certified,
};
#[doc(hidden)]
pub use uflia_online::check_qf_uflia_boolean_prop_metrics;
pub use uflia_online::check_qf_uflia_boolean_with_metrics;
pub use uflia_online::check_qf_uflia_online;
pub use uflra_interpolant::{
    UflraInterpolantCertificate, uflra_interpolant, uflra_interpolant_certified,
};
#[doc(hidden)]
pub use uflra_online::check_qf_uflra_boolean_prop_metrics;
pub use uflra_online::check_qf_uflra_boolean_with_metrics;
pub use uflra_online::check_qf_uflra_online;
pub use word_alethe::{
    WORD_CLASH_RULE, WordAletheError, WordClashCertificate, word_conflict_alethe,
};
#[cfg(feature = "z3")]
pub use z3_backend::Z3Backend;
