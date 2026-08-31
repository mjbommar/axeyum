//! Finite A0 equivalence queries and decoded-model controls.

use axeyum_machine::a0::decode_state;
use axeyum_machine_evidence::{
    EvidenceError, a0_equivalence_report, check_a0_equivalence,
    check_a0_equivalence_corrupt_model_control, check_a0_equivalence_destination_control,
    write_json,
};

#[test]
fn clear_pair_checks_both_observations_and_replays_models() {
    let directory = tempfile::tempdir().unwrap();
    let package = directory.path().join("package.json");
    let report_path = directory.path().join("report.json");
    write_json(&package, &axeyum_machine_evidence::semantic_package()).unwrap();
    let report = a0_equivalence_report(&package).unwrap();
    assert_eq!(report.result_only.verdict, "equivalent");
    assert_eq!(report.result_only.cases_checked, 4096);
    assert_eq!(report.destination_mutation.verdict, "counterexample");
    assert_eq!(
        report
            .destination_mutation
            .counterexample
            .as_ref()
            .unwrap()
            .first_difference,
        "r0"
    );
    assert_eq!(report.full_state_without_premise.verdict, "counterexample");
    let flag_witness = report
        .full_state_without_premise
        .counterexample
        .as_ref()
        .unwrap();
    assert_eq!(flag_witness.first_difference, "carry");
    let initial = decode_state(&flag_witness.initial_state).unwrap();
    assert!(initial.conditions.zero);
    assert!(initial.conditions.carry);
    assert_eq!(report.full_state_with_premise.verdict, "equivalent");
    assert_eq!(report.full_state_with_premise.cases_checked, 256);

    write_json(&report_path, &report).unwrap();
    assert_eq!(
        check_a0_equivalence(&package, &report_path).unwrap(),
        report
    );
    assert!(matches!(
        check_a0_equivalence_destination_control(&package, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    assert!(matches!(
        check_a0_equivalence_corrupt_model_control(&package, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
}
