//! End-to-end controls for A0 addition, memory, and branch artifacts.

use std::{fs, path::PathBuf};

use axeyum_machine_evidence::{
    EvidenceError, add_step_report, branch_trace_report, check_add_step,
    check_add_wrong_destination_control, check_branch_target_control, check_branch_trace,
    check_memory_byte_order_control, check_memory_trace, memory_trace_report, semantic_package,
    write_json,
};

fn path(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "axeyum-machine-flagship-{}-{name}",
        std::process::id()
    ))
}

#[test]
fn exhaustive_addition_recomputes_and_wrong_destination_fires() {
    let package_path = path("add-package.json");
    let report_path = path("add-report.json");
    write_json(&package_path, &semantic_package()).unwrap();
    let report = add_step_report(&package_path).unwrap();
    assert_eq!(report.cases_checked, 65_536);
    assert_eq!(report.destination, 2);
    assert!(report.passed);
    write_json(&report_path, &report).unwrap();
    assert_eq!(check_add_step(&package_path, &report_path).unwrap(), report);
    assert!(matches!(
        check_add_wrong_destination_control(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(package_path).unwrap();
    fs::remove_file(report_path).unwrap();
}

#[test]
fn memory_trace_recomputes_and_byte_order_control_fires() {
    let package_path = path("memory-package.json");
    let report_path = path("memory-report.json");
    write_json(&package_path, &semantic_package()).unwrap();
    let report = memory_trace_report(&package_path).unwrap();
    assert_eq!(report.stored_bytes, [0xcd, 0xab]);
    assert_eq!(report.loaded_word, 0xabcd);
    assert!(report.boundary_trapped);
    assert!(report.no_partial_write);
    write_json(&report_path, &report).unwrap();
    assert_eq!(
        check_memory_trace(&package_path, &report_path).unwrap(),
        report
    );
    assert!(matches!(
        check_memory_byte_order_control(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(package_path).unwrap();
    fs::remove_file(report_path).unwrap();
}

#[test]
fn branch_trace_recomputes_and_wrong_target_fires() {
    let package_path = path("branch-package.json");
    let report_path = path("branch-report.json");
    write_json(&package_path, &semantic_package()).unwrap();
    let report = branch_trace_report(&package_path).unwrap();
    assert_eq!(report.taken_pcs, [0, 8, 8]);
    assert_eq!(report.untaken_pcs, [0, 4, 4]);
    assert_eq!(report.taken_stop, "halted");
    assert_eq!(report.untaken_stop, "halted");
    write_json(&report_path, &report).unwrap();
    assert_eq!(
        check_branch_trace(&package_path, &report_path).unwrap(),
        report
    );
    assert!(matches!(
        check_branch_target_control(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(package_path).unwrap();
    fs::remove_file(report_path).unwrap();
}
