//! End-to-end controls for the source-derived A0 memory-frame theorem.

use std::{fs, path::PathBuf};

use axeyum_machine_evidence::{
    EvidenceError, check_symbolic_memory, check_symbolic_memory_partial_store_control,
    semantic_package, symbolic_memory_report, write_json,
};

fn path(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "axeyum-machine-symbolic-memory-{}-{name}",
        std::process::id()
    ))
}

#[test]
fn frame_certificates_recheck_and_partial_store_control_replays() {
    let package_path = path("package.json");
    let report_path = path("report.json");
    write_json(&package_path, &semantic_package()).unwrap();
    let report = symbolic_memory_report(&package_path).unwrap();
    assert_eq!(
        report
            .proofs
            .iter()
            .map(|proof| proof.width)
            .collect::<Vec<_>>(),
        [8, 16, 24, 32, 40, 48, 56, 64]
    );
    assert!(report.proofs.iter().all(|proof| proof.lrat.is_some()));
    assert!(
        report
            .partial_store_counterexample
            .correct_store_preserved_memory
    );
    assert!(
        report
            .partial_store_counterexample
            .symbolic_mutation_satisfiable
    );
    assert_ne!(
        report.partial_store_counterexample.original_first_byte,
        report.partial_store_counterexample.mutated_first_byte
    );
    write_json(&report_path, &report).unwrap();
    assert_eq!(
        check_symbolic_memory(&package_path, &report_path).unwrap(),
        report
    );

    let mut tampered = report.clone();
    tampered.proofs[0].drat.push_str("not-a-drat-clause\n");
    write_json(&report_path, &tampered).unwrap();
    assert!(matches!(
        check_symbolic_memory(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));

    write_json(&report_path, &report).unwrap();
    assert!(matches!(
        check_symbolic_memory_partial_store_control(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(package_path).unwrap();
    fs::remove_file(report_path).unwrap();
}
