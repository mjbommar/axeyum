//! End-to-end controls for the source-pinned x86-64 evidence routes.

use std::{fs, path::PathBuf};

use axeyum_machine_evidence::{
    EvidenceError, check_x64_branch_base_control, check_x64_execution, check_x64_source,
    check_x64_source_digest_control, write_json, x64_execution_report, x64_source_report,
};

fn path(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "axeyum-machine-x64-evidence-{}-{name}",
        std::process::id()
    ))
}

#[test]
fn source_pin_recomputes_and_digest_control_fires() {
    let report_path = path("source.json");
    let report = x64_source_report();
    assert_eq!(report.source_revision, "325383-092US");
    assert_eq!(report.selected_forms.len(), 17);
    assert_eq!(report.source_pages, 2_573);
    write_json(&report_path, &report).unwrap();
    assert_eq!(check_x64_source(&report_path).unwrap(), report);
    assert!(matches!(
        check_x64_source_digest_control(&report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(report_path).unwrap();
}

#[test]
fn decoder_step_report_replays_and_branch_control_fires() {
    let report_path = path("execution.json");
    let report = x64_execution_report().unwrap();
    assert_eq!(report.forms_executed, 17);
    assert_eq!(report.book_encodings.len(), 28);
    assert_eq!(report.xor_results, [0, 0x0123_4567_89ab_cdef, 7]);
    assert_eq!(report.count_result, 0);
    assert_eq!(report.leaf_result, 42);
    assert_eq!(report.nonleaf_result, 7);
    assert!(report.nonleaf_rbx_restored);
    assert_eq!(report.absolute_results, [7, 7]);
    assert!(report.semantic_checks_passed);
    assert_eq!(report.trap_classes_checked, 3);
    assert_eq!(report.mutations_rejected, 4);
    write_json(&report_path, &report).unwrap();
    assert_eq!(check_x64_execution(&report_path).unwrap(), report);

    let mut tampered = report.clone();
    tampered.book_encodings[0].bytes.reverse();
    write_json(&report_path, &tampered).unwrap();
    assert!(matches!(
        check_x64_execution(&report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));

    write_json(&report_path, &report).unwrap();
    assert!(matches!(
        check_x64_branch_base_control(&report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(report_path).unwrap();
}
