//! Complete tiny-language A0 minimality and coverage controls.

use axeyum_machine_evidence::{
    EvidenceError, a0_minimality_report, check_a0_minimality,
    check_a0_minimality_language_omission_control, check_a0_minimality_witness_control,
    semantic_package, write_json,
};

#[test]
fn width_eight_add_two_language_is_exhausted_and_controls_fire() {
    let directory = tempfile::tempdir().unwrap();
    let package = directory.path().join("package.json");
    let report_path = directory.path().join("report.json");
    write_json(&package, &semantic_package()).unwrap();
    let report = a0_minimality_report(&package).unwrap();
    assert_eq!(report.language.alphabet.len(), 6);
    assert_eq!(report.minimum_cost, 2);
    assert_eq!(
        report
            .strata
            .iter()
            .map(|stratum| (
                stratum.candidates_checked,
                stratum.behavior_classes,
                stratum.correct_candidates
            ))
            .collect::<Vec<_>>(),
        [(1, 1, 0), (6, 5, 0), (36, 11, 4)]
    );
    assert_eq!(report.witness[0].label, "add r0,r0,r1");
    assert_eq!(report.witness[1], report.witness[0]);
    assert_eq!(
        report.witness_results,
        (2_u64..258).map(|x| x & 0xff).collect::<Vec<_>>()
    );

    write_json(&report_path, &report).unwrap();
    assert_eq!(check_a0_minimality(&package, &report_path).unwrap(), report);
    assert!(matches!(
        check_a0_minimality_witness_control(&package, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    assert!(matches!(
        check_a0_minimality_language_omission_control(&package, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
}
