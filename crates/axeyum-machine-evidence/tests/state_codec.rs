//! End-to-end controls for canonical complete-state artifacts.

use std::{fs, path::PathBuf};

use axeyum_machine_evidence::{
    EvidenceError, check_state_codec, check_state_codec_trailing_byte_control, semantic_package,
    state_codec_report, write_json,
};

fn path(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "axeyum-machine-state-codec-{}-{name}",
        std::process::id()
    ))
}

#[test]
fn report_recomputes_and_trailing_byte_fires() {
    let package_path = path("package.json");
    let report_path = path("report.json");
    write_json(&package_path, &semantic_package()).unwrap();
    let report = state_codec_report(&package_path).unwrap();
    assert_eq!(report.states_checked, 48);
    assert_eq!(report.malformed_encodings_rejected, 10);
    assert!(report.all_outcomes_checked);
    assert!(report.passed);
    write_json(&report_path, &report).unwrap();

    assert_eq!(
        check_state_codec(&package_path, &report_path).unwrap(),
        report
    );
    assert!(matches!(
        check_state_codec_trailing_byte_control(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(package_path).unwrap();
    fs::remove_file(report_path).unwrap();
}
