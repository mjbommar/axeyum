//! End-to-end controls for A0 addition, memory, and branch artifacts.

use std::{fs, path::PathBuf};

use axeyum_machine_evidence::{
    EvidenceError, add_step_report, branch_trace_report, check_add_step,
    check_add_wrong_destination_control, check_branch_target_control, check_branch_trace,
    check_decoder_reserved_bit_control, check_decoder_roundtrip, check_memory_byte_order_control,
    check_memory_trace, check_run_classification, check_run_false_halt_control,
    check_step_coverage, check_step_hidden_write_control, check_step_mutation_suite_control,
    check_symbolic_addition, check_symbolic_addition_inverted_carry_control,
    decoder_roundtrip_report, memory_trace_report, run_classification_report, semantic_package,
    step_coverage_report, symbolic_addition_report, write_json,
};

fn path(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "axeyum-machine-flagship-{}-{name}",
        std::process::id()
    ))
}

#[test]
fn symbolic_addition_certificates_recheck_and_mutation_replays() {
    let package_path = path("symbolic-add-package.json");
    let report_path = path("symbolic-add-report.json");
    write_json(&package_path, &semantic_package()).unwrap();
    let report = symbolic_addition_report(&package_path).unwrap();
    assert_eq!(
        report
            .proofs
            .iter()
            .map(|proof| proof.width)
            .collect::<Vec<_>>(),
        [8, 16, 24, 32, 40, 48, 56, 64]
    );
    assert!(report.proofs.iter().all(|proof| proof.lrat.is_some()));
    assert!(report.inverted_carry_counterexample.replayed_through_step);
    assert_ne!(
        report.inverted_carry_counterexample.concrete_carry,
        report.inverted_carry_counterexample.mutated_carry
    );
    write_json(&report_path, &report).unwrap();
    assert_eq!(
        check_symbolic_addition(&package_path, &report_path).unwrap(),
        report
    );
    let mut tampered = report.clone();
    tampered.proofs[0].drat.push_str("not-a-drat-clause\n");
    write_json(&report_path, &tampered).unwrap();
    assert!(matches!(
        check_symbolic_addition(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    write_json(&report_path, &report).unwrap();
    assert!(matches!(
        check_symbolic_addition_inverted_carry_control(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(package_path).unwrap();
    fs::remove_file(report_path).unwrap();
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

#[test]
fn runner_classifications_recompute_and_false_halt_fires() {
    let package_path = path("run-package.json");
    let report_path = path("run-report.json");
    write_json(&package_path, &semantic_package()).unwrap();
    let report = run_classification_report(&package_path).unwrap();
    assert_eq!(report.halted_stop, "halted");
    assert_eq!(report.trapped_stop, "trapped");
    assert_eq!(report.exhausted_stop, "bound-exhausted");
    assert_eq!(report.prefix_stop, "prefix-returned");
    assert_eq!(report.zero_bound_states, 1);
    assert!(report.resumed_equals_whole);
    write_json(&report_path, &report).unwrap();
    assert_eq!(
        check_run_classification(&package_path, &report_path).unwrap(),
        report
    );
    assert!(matches!(
        check_run_false_halt_control(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(package_path).unwrap();
    fs::remove_file(report_path).unwrap();
}

#[test]
fn decoder_roundtrip_is_exhaustive_and_reserved_bit_fires() {
    let package_path = path("decoder-package.json");
    let report_path = path("decoder-report.json");
    write_json(&package_path, &semantic_package()).unwrap();
    let report = decoder_roundtrip_report(&package_path).unwrap();
    assert_eq!(report.families, 17);
    assert_eq!(report.instructions_checked, 41_409);
    assert_eq!(report.unique_encodings, report.instructions_checked);
    assert!(report.roundtrip_passed);
    assert_eq!(report.reserved_mutations_rejected, 82_818);
    assert_eq!(report.unused_field_controls_rejected, 8);
    assert!(report.unknown_opcode_rejected);
    write_json(&report_path, &report).unwrap();
    assert_eq!(
        check_decoder_roundtrip(&package_path, &report_path).unwrap(),
        report
    );
    assert!(matches!(
        check_decoder_reserved_bit_control(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(package_path).unwrap();
    fs::remove_file(report_path).unwrap();
}

#[test]
fn step_coverage_recomputes_and_hidden_write_fires() {
    let package_path = path("step-package.json");
    let report_path = path("step-report.json");
    write_json(&package_path, &semantic_package()).unwrap();
    let report = step_coverage_report(&package_path).unwrap();
    assert_eq!(report.families_executed, 17);
    assert_eq!(report.effect_rows_checked, 17);
    assert_eq!(report.trap_controls_checked, 4);
    assert!(report.terminal_stutter_checked);
    assert!(report.frame_checks_passed);
    assert!(report.effects_passed);
    write_json(&report_path, &report).unwrap();
    assert_eq!(
        check_step_coverage(&package_path, &report_path).unwrap(),
        report
    );
    assert!(matches!(
        check_step_hidden_write_control(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    assert!(matches!(
        check_step_mutation_suite_control(&package_path, &report_path),
        Err(EvidenceError::SemanticMismatch(_))
    ));
    fs::remove_file(package_path).unwrap();
    fs::remove_file(report_path).unwrap();
}
