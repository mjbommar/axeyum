//! End-to-end controls for the first finite A0 evidence route.

use std::{fs, path::PathBuf};

use axeyum_machine_evidence::{
    EvidenceError, check_word_roundtrip, check_word_roundtrip_reversed_control, semantic_package,
    word_roundtrip_report, write_json,
};

fn path(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "axeyum-machine-evidence-{}-{name}",
        std::process::id()
    ))
}

#[test]
fn report_recomputes_and_reversed_byte_order_fires() {
    let package_path = path("package.json");
    let report_path = path("report.json");
    write_json(&package_path, &semantic_package()).unwrap();
    let report = word_roundtrip_report(&package_path).unwrap();
    assert_eq!(report.values_checked, 65_792);
    assert!(report.passed);
    write_json(&report_path, &report).unwrap();

    assert_eq!(
        check_word_roundtrip(&package_path, &report_path).unwrap(),
        report
    );
    assert!(matches!(
        check_word_roundtrip_reversed_control(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(package_path).unwrap();
    fs::remove_file(report_path).unwrap();
}

#[test]
fn source_digest_mutation_is_rejected() {
    let package_path = path("mutated-package.json");
    let mut package = semantic_package();
    let replacement = if package.source_sha256.starts_with('0') {
        "1"
    } else {
        "0"
    };
    package.source_sha256.replace_range(..1, replacement);
    write_json(&package_path, &package).unwrap();
    assert!(matches!(
        word_roundtrip_report(&package_path),
        Err(EvidenceError::SemanticPackageMismatch(_))
    ));
    fs::remove_file(package_path).unwrap();
}
