//! End-to-end controls for the first A0 observation artifact.

use std::{fs, path::PathBuf};

use axeyum_machine_evidence::{
    EvidenceError, check_observation_omission_control, check_observation_separation,
    observation_separation_report, semantic_package, write_json,
};

fn path(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "axeyum-machine-observation-{}-{name}",
        std::process::id()
    ))
}

#[test]
fn report_recomputes_and_component_omission_fires() {
    let package_path = path("package.json");
    let report_path = path("report.json");
    write_json(&package_path, &semantic_package()).unwrap();
    let report = observation_separation_report(&package_path).unwrap();
    assert!(report.narrow_equal);
    assert!(!report.broad_equal);
    assert_eq!(report.separating_register, Some(3));
    assert_eq!(
        (report.left_value, report.right_value),
        (Some(19), Some(20))
    );
    write_json(&report_path, &report).unwrap();

    assert_eq!(
        check_observation_separation(&package_path, &report_path).unwrap(),
        report
    );
    assert!(matches!(
        check_observation_omission_control(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(package_path).unwrap();
    fs::remove_file(report_path).unwrap();
}
