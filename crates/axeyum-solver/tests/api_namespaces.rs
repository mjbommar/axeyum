//! Public namespace compatibility gates.
//!
//! The grouped paths are the canonical documentation surface. Historical root
//! paths remain source-compatible aliases while downstream consumers migrate.

use std::any::TypeId;

fn assert_same_type<T: 'static, U: 'static>() {
    assert_eq!(TypeId::of::<T>(), TypeId::of::<U>());
}

macro_rules! assert_same_function {
    ($canonical:expr, $historical:expr) => {
        assert_eq!($canonical as *const (), $historical as *const ());
    };
}

#[test]
fn qfbv_proof_namespace_preserves_root_aliases() {
    assert_same_type::<axeyum_solver::proofs::UnsatProof, axeyum_solver::UnsatProof>();
    assert_same_type::<axeyum_solver::proofs::UnsatProofOutcome, axeyum_solver::UnsatProofOutcome>(
    );

    assert_same_function!(
        axeyum_solver::proofs::export_qf_bv_unsat_proof,
        axeyum_solver::export_qf_bv_unsat_proof
    );
}

#[cfg(feature = "full")]
#[test]
fn full_proof_namespaces_preserve_root_aliases() {
    assert_same_type::<axeyum_solver::proofs::alethe::SkolemCert, axeyum_solver::SkolemCert>();
    assert_same_type::<
        axeyum_solver::proofs::end_to_end::EndToEndUnsatOutcome,
        axeyum_solver::EndToEndUnsatOutcome,
    >();
    assert_same_type::<axeyum_solver::proofs::evidence::Evidence, axeyum_solver::Evidence>();
    assert_same_type::<
        axeyum_solver::proofs::faithfulness::FaithfulnessOutcome,
        axeyum_solver::FaithfulnessOutcome,
    >();
    assert_same_type::<axeyum_solver::proofs::lean::ProofFragment, axeyum_solver::ProofFragment>();

    assert_same_function!(
        axeyum_solver::proofs::alethe::prove_qf_bv_unsat_alethe,
        axeyum_solver::prove_qf_bv_unsat_alethe
    );
    assert_same_function!(
        axeyum_solver::proofs::alethe::prove_finite_int_quant_unsat_alethe,
        axeyum_solver::prove_finite_int_quant_unsat_alethe
    );
    assert_same_function!(
        axeyum_solver::proofs::evidence::produce_evidence,
        axeyum_solver::produce_evidence
    );
    assert_same_function!(
        axeyum_solver::proofs::faithfulness::check_qf_bv_faithfulness,
        axeyum_solver::check_qf_bv_faithfulness
    );
    assert_same_function!(
        axeyum_solver::proofs::lean::prove_unsat_to_lean_module,
        axeyum_solver::prove_unsat_to_lean_module
    );
}

#[cfg(feature = "full")]
#[test]
fn certificate_namespaces_preserve_root_aliases() {
    use axeyum_solver::certificates::{arrays, quantifiers};

    assert_same_type::<arrays::ArrayElimUnsatCertificate, axeyum_solver::ArrayElimUnsatCertificate>(
    );
    assert_same_type::<
        arrays::ArrayAxiomRefutationCertificate,
        axeyum_solver::ArrayAxiomRefutationCertificate,
    >();
    assert_same_type::<arrays::BinarySearch16Certificate, axeyum_solver::BinarySearch16Certificate>(
    );
    assert_same_type::<
        arrays::FiniteArrayExtensionalityCertificate,
        axeyum_solver::FiniteArrayExtensionalityCertificate,
    >();
    assert_same_type::<
        arrays::TwoByteMemcpyRefutationCertificate,
        axeyum_solver::TwoByteMemcpyRefutationCertificate,
    >();
    assert_same_type::<arrays::TwoCellXorSwapCertificate, axeyum_solver::TwoCellXorSwapCertificate>(
    );

    assert_same_type::<
        quantifiers::QuantifierInstanceCertificate,
        axeyum_solver::QuantifierInstanceCertificate,
    >();
    assert_same_type::<
        quantifiers::QuantifiedBoolModelSatCertificate,
        axeyum_solver::QuantifiedBoolModelSatCertificate,
    >();
    assert_same_type::<
        quantifiers::BvAlternationCounterexampleCertificate,
        axeyum_solver::BvAlternationCounterexampleCertificate,
    >();
    assert_same_type::<
        quantifiers::BvPairedExistentialTransferCertificate,
        axeyum_solver::BvPairedExistentialTransferCertificate,
    >();
    assert_same_type::<
        quantifiers::QuantifiedCounterexampleCoverCertificate,
        axeyum_solver::QuantifiedCounterexampleCoverCertificate,
    >();
    assert_same_type::<quantifiers::GuardedUniversalForm, axeyum_solver::GuardedUniversalForm>();
    assert_same_type::<
        quantifiers::QuantifiedSkolemSatCertificate,
        axeyum_solver::QuantifiedSkolemSatCertificate,
    >();
    assert_same_type::<
        quantifiers::VacuousExistsUniversalCounterexampleCertificate,
        axeyum_solver::VacuousExistsUniversalCounterexampleCertificate,
    >();

    assert_same_function!(
        arrays::certify_array_elim_unsat,
        axeyum_solver::certify_array_elim_unsat
    );
    assert_same_function!(
        arrays::binary_search16_refutation,
        axeyum_solver::binary_search16_refutation
    );
    assert_same_function!(
        arrays::finite_array_extensionality_refutation,
        axeyum_solver::finite_array_extensionality_refutation
    );
    assert_same_function!(
        quantifiers::check_quantifier_clause_propagation,
        axeyum_solver::check_quantifier_clause_propagation
    );
    assert_same_function!(
        quantifiers::check_bv_alternation_counterexample,
        axeyum_solver::check_bv_alternation_counterexample
    );
    assert_same_function!(
        quantifiers::check_quantified_counterexample_cover,
        axeyum_solver::check_quantified_counterexample_cover
    );
    assert_same_function!(
        quantifiers::check_quantified_skolem_sat,
        axeyum_solver::check_quantified_skolem_sat
    );
}

#[cfg(feature = "full")]
#[test]
fn theory_namespaces_preserve_root_aliases() {
    use axeyum_solver::theories::{
        arithmetic, arrays, combination, datatypes, quantifiers, strings, uninterpreted_functions,
    };

    assert_same_type::<arithmetic::LiaTheory, axeyum_solver::LiaTheory>();
    assert_same_type::<arithmetic::LraTheory, axeyum_solver::LraTheory>();
    assert_same_type::<datatypes::EnumSort, axeyum_solver::EnumSort>();
    assert_same_type::<datatypes::RecordSort, axeyum_solver::RecordSort>();
    assert_same_type::<uninterpreted_functions::EufTheory, axeyum_solver::EufTheory>();
    assert_same_type::<combination::TheoryLit, axeyum_solver::TheoryLit>();

    assert_same_function!(
        arrays::check_with_array_elimination::<axeyum_solver::SatBvBackend>,
        axeyum_solver::check_with_array_elimination::<axeyum_solver::SatBvBackend>
    );
    assert_same_function!(
        arithmetic::check_qf_lia_online_cdclt,
        axeyum_solver::check_qf_lia_online_cdclt
    );
    assert_same_function!(arithmetic::check_with_lra, axeyum_solver::check_with_lra);
    assert_same_function!(arithmetic::check_with_nra, axeyum_solver::check_with_nra);
    assert_same_function!(
        datatypes::check_with_datatype_native,
        axeyum_solver::check_with_datatype_native
    );
    assert_same_function!(
        quantifiers::check_with_quantifiers,
        axeyum_solver::check_with_quantifiers
    );
    assert_same_function!(
        strings::check_qf_s_online_cdclt,
        axeyum_solver::check_qf_s_online_cdclt
    );
    assert_same_function!(
        uninterpreted_functions::check_qf_uf,
        axeyum_solver::check_qf_uf
    );
    assert_same_function!(
        combination::check_with_arrays_and_functions::<axeyum_solver::SatBvBackend>,
        axeyum_solver::check_with_arrays_and_functions::<axeyum_solver::SatBvBackend>
    );
    assert_same_function!(
        combination::check_qf_ufbv_online_cdclt,
        axeyum_solver::check_qf_ufbv_online_cdclt
    );
}

#[cfg(feature = "full")]
#[test]
fn verification_namespaces_preserve_root_aliases() {
    use axeyum_solver::verification::{
        horn, imc, pdr, symbolic_execution, toy_bv_vm, transition_systems,
    };

    assert_same_type::<transition_systems::BmcOutcome, axeyum_solver::BmcOutcome>();
    assert_same_type::<
        transition_systems::CertifiedSafetyOutcome,
        axeyum_solver::CertifiedSafetyOutcome,
    >();
    assert_same_type::<horn::HornSystem, axeyum_solver::HornSystem>();
    assert_same_type::<imc::ImcOutcome, axeyum_solver::ImcOutcome>();
    assert_same_type::<imc::ImcLiaOutcome, axeyum_solver::ImcLiaOutcome>();
    assert_same_type::<pdr::PdrOutcome, axeyum_solver::PdrOutcome>();
    assert_same_type::<pdr::CertifiedPdrOutcome, axeyum_solver::CertifiedPdrOutcome>();
    assert_same_type::<symbolic_execution::SymbolicExecutor, axeyum_solver::SymbolicExecutor>();
    assert_same_type::<symbolic_execution::SymbolicMemory, axeyum_solver::SymbolicMemory>();
    assert_same_type::<toy_bv_vm::TinyBvProgram, axeyum_solver::TinyBvProgram>();
    assert_same_type::<toy_bv_vm::TinyBvExploreOutcome, axeyum_solver::TinyBvExploreOutcome>();

    assert_same_function!(horn::solve_horn, axeyum_solver::solve_horn);
}

#[cfg(feature = "full")]
#[test]
fn optimization_namespaces_preserve_root_aliases() {
    use axeyum_solver::optimization::{maxsat, models, objectives};

    assert_same_type::<models::ModelMinimizeObjective, axeyum_solver::ModelMinimizeObjective>();
    assert_same_type::<models::ModelMinimizeOutcome, axeyum_solver::ModelMinimizeOutcome>();
    assert_same_type::<maxsat::MaxSatOutcome, axeyum_solver::MaxSatOutcome>();
    assert_same_type::<objectives::OptOutcome, axeyum_solver::OptOutcome>();
    assert_same_type::<objectives::LexOutcome, axeyum_solver::LexOutcome>();
    assert_same_type::<objectives::ParetoOutcome, axeyum_solver::ParetoOutcome>();

    assert_same_function!(models::minimize_model, axeyum_solver::minimize_model);
    assert_same_function!(maxsat::max_satisfiable, axeyum_solver::max_satisfiable);
    assert_same_function!(objectives::maximize_bv, axeyum_solver::maximize_bv);
    assert_same_function!(
        objectives::optimize_lia_pareto,
        axeyum_solver::optimize_lia_pareto
    );
}

#[cfg(feature = "full")]
#[test]
fn smtlib_namespace_preserves_root_aliases() {
    assert_same_type::<axeyum_solver::smtlib::SmtLibOutcome, axeyum_solver::SmtLibOutcome>();
    assert_same_type::<axeyum_solver::smtlib::SmtLibModel, axeyum_solver::SmtLibModel>();

    assert_same_function!(
        axeyum_solver::smtlib::solve_smtlib,
        axeyum_solver::solve_smtlib
    );
    assert_same_function!(
        axeyum_solver::smtlib::optimize_smtlib,
        axeyum_solver::optimize_smtlib
    );
    assert_same_function!(
        axeyum_solver::smtlib::solve_smtlib_incremental,
        axeyum_solver::solve_smtlib_incremental
    );
    assert_same_function!(
        axeyum_solver::smtlib::word_route_verdict,
        axeyum_solver::word_route_verdict
    );
}

#[cfg(feature = "full")]
#[test]
fn interpolation_namespaces_preserve_root_aliases() {
    use axeyum_solver::interpolation::{
        bitvectors, linear_integer, linear_real, uflia, uflra, uninterpreted_functions,
    };

    assert_same_type::<
        axeyum_solver::interpolation::InterpolantOutcome,
        axeyum_solver::InterpolantOutcome,
    >();
    assert_same_type::<
        bitvectors::QfBvInterpolantCertificate,
        axeyum_solver::QfBvInterpolantCertificate,
    >();
    assert_same_type::<
        uninterpreted_functions::QfUfInterpolantCertificate,
        axeyum_solver::QfUfInterpolantCertificate,
    >();
    assert_same_type::<
        linear_integer::LiaInterpolantCertificate,
        axeyum_solver::LiaInterpolantCertificate,
    >();
    assert_same_type::<
        linear_real::LraInterpolantCertificate,
        axeyum_solver::LraInterpolantCertificate,
    >();
    assert_same_type::<
        uflia::UfliaInterpolantCertificate,
        axeyum_solver::UfliaInterpolantCertificate,
    >();
    assert_same_type::<
        uflra::UflraInterpolantCertificate,
        axeyum_solver::UflraInterpolantCertificate,
    >();

    assert_same_function!(
        bitvectors::qf_bv_interpolant,
        axeyum_solver::qf_bv_interpolant
    );
    assert_same_function!(
        uninterpreted_functions::qf_uf_interpolant,
        axeyum_solver::qf_uf_interpolant
    );
    assert_same_function!(
        linear_integer::lia_interpolant_cnf,
        axeyum_solver::lia_interpolant_cnf
    );
    assert_same_function!(linear_real::lra_interpolant, axeyum_solver::lra_interpolant);
    assert_same_function!(uflia::uflia_interpolant, axeyum_solver::uflia_interpolant);
    assert_same_function!(uflra::uflra_interpolant, axeyum_solver::uflra_interpolant);
}
