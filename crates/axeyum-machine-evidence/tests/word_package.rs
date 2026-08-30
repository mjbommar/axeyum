//! End-to-end controls for the reusable A0 word package.

use std::{fs, path::PathBuf};

use axeyum_machine_evidence::{
    EvidenceError, check_word_package, check_word_package_signed_zero_extension_control,
    semantic_package, word_package_report, write_json,
};

fn path(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "axeyum-machine-word-package-{}-{name}",
        std::process::id()
    ))
}

#[test]
fn report_recomputes_and_signed_zero_extension_fires() {
    let package_path = path("package.json");
    let report_path = path("report.json");
    write_json(&package_path, &semantic_package()).unwrap();
    let report = word_package_report(&package_path).unwrap();
    assert_eq!(report.source_words_checked, 65_822);
    assert!(report.operation_checks > 1_000_000);
    assert!(report.passed);
    write_json(&report_path, &report).unwrap();

    assert_eq!(
        check_word_package(&package_path, &report_path).unwrap(),
        report
    );
    assert!(matches!(
        check_word_package_signed_zero_extension_control(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(package_path).unwrap();
    fs::remove_file(report_path).unwrap();
}
