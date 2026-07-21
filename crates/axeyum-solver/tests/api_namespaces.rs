//! Public proof-namespace compatibility gates.
//!
//! The grouped paths are the canonical documentation surface. Historical root
//! paths remain source-compatible aliases while downstream consumers migrate.

use std::any::TypeId;

fn assert_same_type<T: 'static, U: 'static>() {
    assert_eq!(TypeId::of::<T>(), TypeId::of::<U>());
}

#[test]
fn qfbv_proof_namespace_preserves_root_aliases() {
    assert_same_type::<axeyum_solver::proofs::UnsatProof, axeyum_solver::UnsatProof>();
    assert_same_type::<axeyum_solver::proofs::UnsatProofOutcome, axeyum_solver::UnsatProofOutcome>(
    );

    assert_eq!(
        axeyum_solver::proofs::export_qf_bv_unsat_proof as *const (),
        axeyum_solver::export_qf_bv_unsat_proof as *const (),
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

    assert_eq!(
        axeyum_solver::proofs::alethe::prove_qf_bv_unsat_alethe as *const (),
        axeyum_solver::prove_qf_bv_unsat_alethe as *const (),
    );
    assert_eq!(
        axeyum_solver::proofs::evidence::produce_evidence as *const (),
        axeyum_solver::produce_evidence as *const (),
    );
    assert_eq!(
        axeyum_solver::proofs::faithfulness::check_qf_bv_faithfulness as *const (),
        axeyum_solver::check_qf_bv_faithfulness as *const (),
    );
    assert_eq!(
        axeyum_solver::proofs::lean::prove_unsat_to_lean_module as *const (),
        axeyum_solver::prove_unsat_to_lean_module as *const (),
    );
}
