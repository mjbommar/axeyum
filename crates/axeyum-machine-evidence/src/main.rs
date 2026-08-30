//! Command-line producer and checker for machine evidence artifacts.

use std::{env, path::Path};

use axeyum_machine_evidence::{
    add_step_report, branch_trace_report, check_add_step, check_add_wrong_destination_control,
    check_branch_target_control, check_branch_trace, check_memory_byte_order_control,
    check_memory_trace, check_observation_omission_control, check_observation_separation,
    check_run_classification, check_run_false_halt_control, check_word_roundtrip,
    check_word_roundtrip_reversed_control, memory_trace_report, observation_separation_report,
    run_classification_report, semantic_package, word_roundtrip_report, write_json,
};

fn main() {
    if let Err(error) = run() {
        eprintln!("axeyum-machine-evidence: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().skip(1).collect();
    match args.as_slice() {
        [command, output] if command == "emit-a0-package" => {
            write_json(Path::new(output), &semantic_package())?;
            println!("emitted A0 semantic package: {output}");
        }
        [command, package, output] if command == "emit-word-roundtrip" => {
            let report = word_roundtrip_report(Path::new(package))?;
            write_json(Path::new(output), &report)?;
            println!(
                "word-roundtrip: PASS: values={} result_sha256={}",
                report.values_checked, report.result_sha256
            );
        }
        [command, package, report] if command == "check-word-roundtrip" => {
            let checked = check_word_roundtrip(Path::new(package), Path::new(report))?;
            println!(
                "word-roundtrip: PASS: values={} result_sha256={}",
                checked.values_checked, checked.result_sha256
            );
        }
        [command, package, report] if command == "control-word-roundtrip-reversed" => {
            check_word_roundtrip_reversed_control(Path::new(package), Path::new(report))?;
            return Err("control-failure: reversed byte order was accepted".into());
        }
        [command, package, output] if command == "emit-observation-separation" => {
            let report = observation_separation_report(Path::new(package))?;
            write_json(Path::new(output), &report)?;
            println!(
                "observation-separation: PASS: narrow_equal={} broad_equal={} separator=r{}",
                report.narrow_equal,
                report.broad_equal,
                report
                    .separating_register
                    .expect("declared witness separates")
            );
        }
        [command, package, report] if command == "check-observation-separation" => {
            let checked = check_observation_separation(Path::new(package), Path::new(report))?;
            println!(
                "observation-separation: PASS: narrow_equal={} broad_equal={} separator=r{}",
                checked.narrow_equal,
                checked.broad_equal,
                checked
                    .separating_register
                    .expect("checked witness separates")
            );
        }
        [command, package, report] if command == "control-observation-omission" => {
            check_observation_omission_control(Path::new(package), Path::new(report))?;
            return Err("control-failure: omitted requested register was accepted".into());
        }
        [command, package, output] if command == "emit-add-step" => {
            let report = add_step_report(Path::new(package))?;
            write_json(Path::new(output), &report)?;
            println!(
                "add-step: PASS: cases={} destination=r{} result_sha256={}",
                report.cases_checked, report.destination, report.result_sha256
            );
        }
        [command, package, report] if command == "check-add-step" => {
            let checked = check_add_step(Path::new(package), Path::new(report))?;
            println!(
                "add-step: PASS: cases={} destination=r{} result_sha256={}",
                checked.cases_checked, checked.destination, checked.result_sha256
            );
        }
        [command, package, report] if command == "control-add-wrong-destination" => {
            check_add_wrong_destination_control(Path::new(package), Path::new(report))?;
            return Err("control-failure: wrong addition destination was accepted".into());
        }
        [command, package, output] if command == "emit-memory-trace" => {
            let report = memory_trace_report(Path::new(package))?;
            write_json(Path::new(output), &report)?;
            println!(
                "memory-trace: PASS: loaded={:#x} boundary_trapped={} no_partial_write={}",
                report.loaded_word, report.boundary_trapped, report.no_partial_write
            );
        }
        [command, package, report] if command == "check-memory-trace" => {
            let checked = check_memory_trace(Path::new(package), Path::new(report))?;
            println!(
                "memory-trace: PASS: loaded={:#x} boundary_trapped={} no_partial_write={}",
                checked.loaded_word, checked.boundary_trapped, checked.no_partial_write
            );
        }
        [command, package, report] if command == "control-memory-byte-order" => {
            check_memory_byte_order_control(Path::new(package), Path::new(report))?;
            return Err("control-failure: reversed stored bytes were accepted".into());
        }
        [command, package, output] if command == "emit-branch-trace" => {
            let report = branch_trace_report(Path::new(package))?;
            write_json(Path::new(output), &report)?;
            println!(
                "branch-trace: PASS: taken={:?} untaken={:?}",
                report.taken_pcs, report.untaken_pcs
            );
        }
        [command, package, report] if command == "check-branch-trace" => {
            let checked = check_branch_trace(Path::new(package), Path::new(report))?;
            println!(
                "branch-trace: PASS: taken={:?} untaken={:?}",
                checked.taken_pcs, checked.untaken_pcs
            );
        }
        [command, package, report] if command == "control-branch-target" => {
            check_branch_target_control(Path::new(package), Path::new(report))?;
            return Err("control-failure: wrong branch target was accepted".into());
        }
        [command, package, output] if command == "emit-run-classification" => {
            let report = run_classification_report(Path::new(package))?;
            write_json(Path::new(output), &report)?;
            println!(
                "run-classification: PASS: halt={} trap={} exhausted={} prefix={} resumed={}",
                report.halted_stop,
                report.trapped_stop,
                report.exhausted_stop,
                report.prefix_stop,
                report.resumed_equals_whole
            );
        }
        [command, package, report] if command == "check-run-classification" => {
            let checked = check_run_classification(Path::new(package), Path::new(report))?;
            println!(
                "run-classification: PASS: halt={} trap={} exhausted={} prefix={} resumed={}",
                checked.halted_stop,
                checked.trapped_stop,
                checked.exhausted_stop,
                checked.prefix_stop,
                checked.resumed_equals_whole
            );
        }
        [command, package, report] if command == "control-run-false-halt" => {
            check_run_false_halt_control(Path::new(package), Path::new(report))?;
            return Err("control-failure: running prefix was accepted as halted".into());
        }
        _ => {
            return Err("usage: axeyum-machine-evidence emit-a0-package OUTPUT | \
                 emit-word-roundtrip PACKAGE OUTPUT | check-word-roundtrip PACKAGE REPORT | \
                 control-word-roundtrip-reversed PACKAGE REPORT | \
                 emit-observation-separation PACKAGE OUTPUT | \
                 check-observation-separation PACKAGE REPORT | \
                 control-observation-omission PACKAGE REPORT | \
                 emit-add-step PACKAGE OUTPUT | check-add-step PACKAGE REPORT | \
                 control-add-wrong-destination PACKAGE REPORT | \
                 emit-memory-trace PACKAGE OUTPUT | check-memory-trace PACKAGE REPORT | \
                 control-memory-byte-order PACKAGE REPORT | \
                 emit-branch-trace PACKAGE OUTPUT | check-branch-trace PACKAGE REPORT | \
                 control-branch-target PACKAGE REPORT | \
                 emit-run-classification PACKAGE OUTPUT | \
                 check-run-classification PACKAGE REPORT | \
                 control-run-false-halt PACKAGE REPORT"
                .into());
        }
    }
    Ok(())
}
