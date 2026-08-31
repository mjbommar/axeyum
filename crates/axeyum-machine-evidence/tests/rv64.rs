//! End-to-end controls for the source-pinned RV64I evidence routes.

use std::{fs, path::PathBuf};

use axeyum_machine_evidence::{
    EvidenceError, check_rv64_branch_base_control, check_rv64_execution, check_rv64_source,
    check_rv64_source_digest_control, rv64_execution_report, rv64_source_report, write_json,
};

fn path(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "axeyum-machine-rv64-evidence-{}-{name}",
        std::process::id()
    ))
}

#[test]
fn source_pin_recomputes_and_digest_control_fires() {
    let report_path = path("source.json");
    let report = rv64_source_report();
    assert_eq!(report.source_release, "20260120");
    assert_eq!(report.rv64i_version, "2.1");
    assert_eq!(report.selected_forms.len(), 12);
    assert_eq!(report.source_pages, 696);
    write_json(&report_path, &report).unwrap();
    assert_eq!(check_rv64_source(&report_path).unwrap(), report);
    assert!(matches!(
        check_rv64_source_digest_control(&report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(report_path).unwrap();
}

#[test]
fn decoder_step_report_replays_and_branch_control_fires() {
    let report_path = path("execution.json");
    let report = rv64_execution_report().unwrap();
    assert_eq!(report.forms_executed, 12);
    assert_eq!(report.book_encodings.len(), 13);
    assert_eq!(report.xor_results, [0, 0x0123_4567_89ab_cdef, 7]);
    assert!(report.semantic_checks_passed);
    assert_eq!(report.trap_classes_checked, 5);
    assert_eq!(report.mutations_rejected, 3);
    write_json(&report_path, &report).unwrap();
    assert_eq!(check_rv64_execution(&report_path).unwrap(), report);

    let mut tampered = report.clone();
    tampered.book_encodings[0].bytes.reverse();
    write_json(&report_path, &tampered).unwrap();
    assert!(matches!(
        check_rv64_execution(&report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));

    write_json(&report_path, &report).unwrap();
    assert!(matches!(
        check_rv64_branch_base_control(&report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(report_path).unwrap();
}
