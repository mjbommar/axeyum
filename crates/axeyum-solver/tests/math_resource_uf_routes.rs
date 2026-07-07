//! Resource-backed `QF_UF` proof-route regressions for math curriculum packs.
//!
//! These tests keep equality-heavy educational resources tied to Axeyum's
//! zero-trust Alethe route: the solver may search with EUF, but the accepted
//! evidence must re-derive the congruence conflict without a trusted reduction
//! step.

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, Evidence, SolverConfig, check_auto, prove_qf_uf_unsat_alethe};

const EQUIVALENCE_CLASSES_QUOTIENT_CONGRUENCE: &str = include_str!(
    "../../../artifacts/examples/math/equivalence-classes-v0/smt2/quotient-map-congruence-conflict.smt2"
);
const RELATIONS_FUNCTIONS_SINGLE_VALUED_CONFLICT: &str = include_str!(
    "../../../artifacts/examples/math/relations-functions-v0/smt2/function-single-valued-conflict.smt2"
);
const FINITE_GROUPS_OPERATION_CONGRUENCE: &str = include_str!(
    "../../../artifacts/examples/math/finite-groups-v0/smt2/group-operation-congruence-conflict.smt2"
);
const FUNCTION_COMPOSITION_APPLICATION_CONFLICT: &str = include_str!(
    "../../../artifacts/examples/math/function-composition-v0/smt2/composition-application-conflict.smt2"
);
const FINITE_ALGEBRA_HOMOMORPHISM_PRESERVATION: &str = include_str!(
    "../../../artifacts/examples/math/finite-algebra-homomorphisms-v0/smt2/homomorphism-preservation-congruence-conflict.smt2"
);
const FINITE_ALGEBRA_HOMOMORPHISM_BAD_GROUP_MAP: &str = include_str!(
    "../../../artifacts/examples/math/finite-algebra-homomorphisms-v0/smt2/bad-group-homomorphism-alethe-conflict.smt2"
);
const FINITE_MONOIDS_ASSOCIATIVITY_FAILURE: &str = include_str!(
    "../../../artifacts/examples/math/finite-monoids-v0/smt2/nonassociative-table-alethe-conflict.smt2"
);
const FINITE_ORDER_LATTICES_BAD_PARTIAL_ORDER: &str = include_str!(
    "../../../artifacts/examples/math/finite-order-lattices-v0/smt2/bad-partial-order-antisymmetry-conflict.smt2"
);
const FINITE_SPECIALIZATION_ORDER_BAD_T0: &str = include_str!(
    "../../../artifacts/examples/math/finite-specialization-order-v0/smt2/bad-t0-antisymmetry-alethe-conflict.smt2"
);
const FINITE_SIMPLICIAL_COHOMOLOGY_BAD_COBOUNDARY: &str = include_str!(
    "../../../artifacts/examples/math/finite-simplicial-cohomology-v0/smt2/bad-coboundary-value-alethe-conflict.smt2"
);
const FINITE_UNIVERSAL_COEFFICIENT_BAD_H1_ZERO: &str = include_str!(
    "../../../artifacts/examples/math/finite-universal-coefficient-shadow-v0/smt2/bad-uct-h1-zero-alethe-conflict.smt2"
);
const FINITE_PERMUTATION_GROUPS_BAD_NONBIJECTION: &str = include_str!(
    "../../../artifacts/examples/math/finite-permutation-groups-v0/smt2/bad-nonbijection-injectivity-conflict.smt2"
);
const FINITE_VECTOR_SPACES_BAD_SUBSPACE: &str = include_str!(
    "../../../artifacts/examples/math/finite-vector-spaces-v0/smt2/bad-subspace-addition-closure-conflict.smt2"
);
const FINITE_DUAL_SPACES_BAD_COVECTOR: &str = include_str!(
    "../../../artifacts/examples/math/finite-dual-spaces-v0/smt2/bad-covector-additivity-conflict.smt2"
);
const FINITE_MODULES_BAD_SUBMODULE: &str = include_str!(
    "../../../artifacts/examples/math/finite-modules-v0/smt2/bad-submodule-scalar-closure-conflict.smt2"
);
const FINITE_IDEALS_BAD_IDEAL: &str = include_str!(
    "../../../artifacts/examples/math/finite-ideals-v0/smt2/bad-ideal-additive-closure-conflict.smt2"
);
const FINITE_IDEALS_QUOTIENT_REPRESENTATIVE_CONGRUENCE: &str = include_str!(
    "../../../artifacts/examples/math/finite-ideals-v0/smt2/quotient-ring-representative-congruence-conflict.smt2"
);
const FINITE_TENSOR_PRODUCTS_BAD_BILINEAR: &str = include_str!(
    "../../../artifacts/examples/math/finite-tensor-products-v0/smt2/bad-bilinear-left-additivity-conflict.smt2"
);
const FINITE_GROUP_ACTIONS_BAD_IDENTITY: &str = include_str!(
    "../../../artifacts/examples/math/finite-group-actions-v0/smt2/bad-identity-action-alethe-conflict.smt2"
);
const FINITE_GROUP_ACTIONS_BAD_COMPATIBILITY: &str = include_str!(
    "../../../artifacts/examples/math/finite-group-actions-v0/smt2/bad-compatibility-action-alethe-conflict.smt2"
);
const FINITE_CONTINUOUS_MAPS_BAD_PREIMAGE: &str = include_str!(
    "../../../artifacts/examples/math/finite-continuous-maps-v0/smt2/bad-preimage-membership-alethe-conflict.smt2"
);
const FINITE_QUOTIENT_TOPOLOGY_BAD_FIBER_REPRESENTATIVE: &str = include_str!(
    "../../../artifacts/examples/math/finite-quotient-topology-v0/smt2/bad-fiber-representative-alethe-conflict.smt2"
);
const FINITE_QUOTIENT_TOPOLOGY_BAD_OPEN: &str = include_str!(
    "../../../artifacts/examples/math/finite-quotient-topology-v0/smt2/bad-quotient-open-alethe-conflict.smt2"
);

#[test]
fn equivalence_classes_quotient_map_congruence_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "equivalence-classes-v0 quotient-map congruence",
        EQUIVALENCE_CLASSES_QUOTIENT_CONGRUENCE,
    );
}

#[test]
fn relations_functions_single_valued_conflict_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "relations-functions-v0 function single-valued conflict",
        RELATIONS_FUNCTIONS_SINGLE_VALUED_CONFLICT,
    );
}

#[test]
fn finite_groups_operation_congruence_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-groups-v0 group operation congruence",
        FINITE_GROUPS_OPERATION_CONGRUENCE,
    );
}

#[test]
fn function_composition_application_conflict_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "function-composition-v0 composition application conflict",
        FUNCTION_COMPOSITION_APPLICATION_CONFLICT,
    );
}

#[test]
fn finite_algebra_homomorphism_preservation_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-algebra-homomorphisms-v0 homomorphism preservation conflict",
        FINITE_ALGEBRA_HOMOMORPHISM_PRESERVATION,
    );
}

#[test]
fn finite_algebra_homomorphism_bad_group_map_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-algebra-homomorphisms-v0 bad group homomorphism",
        FINITE_ALGEBRA_HOMOMORPHISM_BAD_GROUP_MAP,
    );
}

#[test]
fn finite_monoids_associativity_failure_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-monoids-v0 associativity failure",
        FINITE_MONOIDS_ASSOCIATIVITY_FAILURE,
    );
}

#[test]
fn finite_order_lattices_bad_partial_order_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-order-lattices-v0 bad partial order",
        FINITE_ORDER_LATTICES_BAD_PARTIAL_ORDER,
    );
}

#[test]
fn finite_specialization_order_bad_t0_antisymmetry_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-specialization-order-v0 bad T0 antisymmetry",
        FINITE_SPECIALIZATION_ORDER_BAD_T0,
    );
}

#[test]
fn finite_simplicial_cohomology_bad_coboundary_value_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-simplicial-cohomology-v0 bad coboundary value",
        FINITE_SIMPLICIAL_COHOMOLOGY_BAD_COBOUNDARY,
    );
}

#[test]
fn finite_universal_coefficient_bad_h1_zero_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-universal-coefficient-shadow-v0 bad H1 zero",
        FINITE_UNIVERSAL_COEFFICIENT_BAD_H1_ZERO,
    );
}

#[test]
fn finite_permutation_groups_bad_nonbijection_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-permutation-groups-v0 bad nonbijection",
        FINITE_PERMUTATION_GROUPS_BAD_NONBIJECTION,
    );
}

#[test]
fn finite_vector_spaces_bad_subspace_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-vector-spaces-v0 bad subspace",
        FINITE_VECTOR_SPACES_BAD_SUBSPACE,
    );
}

#[test]
fn finite_dual_spaces_bad_covector_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-dual-spaces-v0 bad covector",
        FINITE_DUAL_SPACES_BAD_COVECTOR,
    );
}

#[test]
fn finite_modules_bad_submodule_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-modules-v0 bad submodule",
        FINITE_MODULES_BAD_SUBMODULE,
    );
}

#[test]
fn finite_ideals_bad_ideal_emits_checked_alethe() {
    assert_resource_euf_alethe("finite-ideals-v0 bad ideal", FINITE_IDEALS_BAD_IDEAL);
}

#[test]
fn finite_ideals_quotient_representative_congruence_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-ideals-v0 quotient representative congruence",
        FINITE_IDEALS_QUOTIENT_REPRESENTATIVE_CONGRUENCE,
    );
}

#[test]
fn finite_tensor_products_bad_bilinear_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-tensor-products-v0 bad bilinear map",
        FINITE_TENSOR_PRODUCTS_BAD_BILINEAR,
    );
}

#[test]
fn finite_group_actions_bad_identity_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-group-actions-v0 bad identity action",
        FINITE_GROUP_ACTIONS_BAD_IDENTITY,
    );
}

#[test]
fn finite_group_actions_bad_compatibility_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-group-actions-v0 bad compatibility action",
        FINITE_GROUP_ACTIONS_BAD_COMPATIBILITY,
    );
}

#[test]
fn finite_continuous_maps_bad_preimage_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-continuous-maps-v0 bad preimage membership",
        FINITE_CONTINUOUS_MAPS_BAD_PREIMAGE,
    );
}

#[test]
fn finite_quotient_topology_bad_fiber_representative_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-quotient-topology-v0 bad fiber representative",
        FINITE_QUOTIENT_TOPOLOGY_BAD_FIBER_REPRESENTATIVE,
    );
}

#[test]
fn finite_quotient_topology_bad_open_emits_checked_alethe() {
    assert_resource_euf_alethe(
        "finite-quotient-topology-v0 bad quotient open",
        FINITE_QUOTIENT_TOPOLOGY_BAD_OPEN,
    );
}

#[test]
fn qf_uf_resource_route_rejects_tampered_alethe_certificate() {
    let script = parse_script(EQUIVALENCE_CLASSES_QUOTIENT_CONGRUENCE)
        .expect("equivalence-classes-v0 quotient congruence artifact parses");
    let assertions = script.checked_flat_view().to_vec();
    let proof = prove_qf_uf_unsat_alethe(&script.arena, &assertions)
        .expect("resource obligation emits a pure EUF Alethe proof");
    let evidence = Evidence::UnsatAletheProof(proof.clone());
    assert!(evidence.check(&script.arena, &assertions).unwrap());

    let mut tampered = proof;
    tampered.pop();
    let bogus = Evidence::UnsatAletheProof(tampered);
    assert!(
        !matches!(bogus.check(&script.arena, &assertions), Ok(true)),
        "removing the closing Alethe command must make the certificate reject"
    );
}

fn assert_resource_euf_alethe(label: &str, smt2: &str) {
    let mut script = parse_script(smt2)
        .unwrap_or_else(|error| panic!("{label}: resource SMT-LIB artifact parses: {error}"));
    let assertions = script.checked_flat_view().to_vec();

    assert_eq!(
        check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
        "{label}: resource obligation must be unsat"
    );

    let proof = prove_qf_uf_unsat_alethe(&script.arena, &assertions)
        .unwrap_or_else(|| panic!("{label}: resource obligation emits a pure EUF Alethe proof"));
    let evidence = Evidence::UnsatAletheProof(proof);
    assert!(evidence.is_certified());
    assert!(
        evidence.check(&script.arena, &assertions).unwrap(),
        "{label}: Alethe certificate must independently re-check"
    );
}
