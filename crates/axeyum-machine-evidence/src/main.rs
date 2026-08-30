//! Command-line producer and checker for machine evidence artifacts.

use std::{env, path::Path};

use axeyum_machine_evidence::{
    add_step_report, branch_trace_report, check_add_step, check_add_wrong_destination_control,
    check_branch_target_control, check_branch_trace, check_decoder_reserved_bit_control,
    check_decoder_roundtrip, check_memory_byte_order_control, check_memory_trace,
    check_observation_omission_control, check_observation_separation, check_run_classification,
    check_run_false_halt_control, check_state_codec, check_state_codec_trailing_byte_control,
    check_step_coverage, check_step_hidden_write_control, check_step_mutation_suite_control,
    check_symbolic_addition, check_symbolic_addition_inverted_carry_control, check_word_package,
    check_word_package_signed_zero_extension_control, check_word_roundtrip,
    check_word_roundtrip_reversed_control, decoder_roundtrip_report, memory_trace_report,
    observation_separation_report, run_classification_report, semantic_package, state_codec_report,
    step_coverage_report, symbolic_addition_report, word_package_report, word_roundtrip_report,
    write_json,
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
        [command, package, output] if command == "emit-word-package" => {
            let report = word_package_report(Path::new(package))?;
            write_json(Path::new(output), &report)?;
            println!(
                "word-package: PASS: words={} operations={} result_sha256={}",
                report.source_words_checked, report.operation_checks, report.result_sha256
            );
        }
        [command, package, report] if command == "check-word-package" => {
            let checked = check_word_package(Path::new(package), Path::new(report))?;
            println!(
                "word-package: PASS: words={} operations={} result_sha256={}",
                checked.source_words_checked, checked.operation_checks, checked.result_sha256
            );
        }
        [command, package, report] if command == "control-word-package-signed-zero-extension" => {
            check_word_package_signed_zero_extension_control(
                Path::new(package),
                Path::new(report),
            )?;
            return Err("control-failure: signed zero extension was accepted".into());
        }
        [command, package, output] if command == "emit-state-codec" => {
            let report = state_codec_report(Path::new(package))?;
            write_json(Path::new(output), &report)?;
            println!(
                "state-codec: PASS: states={} malformed-rejected={} outcomes=all result_sha256={}",
                report.states_checked, report.malformed_encodings_rejected, report.result_sha256
            );
        }
        [command, package, report] if command == "check-state-codec" => {
            let checked = check_state_codec(Path::new(package), Path::new(report))?;
            println!(
                "state-codec: PASS: states={} malformed-rejected={} outcomes=all result_sha256={}",
                checked.states_checked, checked.malformed_encodings_rejected, checked.result_sha256
            );
        }
        [command, package, report] if command == "control-state-codec-trailing-byte" => {
            check_state_codec_trailing_byte_control(Path::new(package), Path::new(report))?;
            return Err("control-failure: trailing state byte was accepted".into());
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
                "memory-trace: PASS: loaded={:#x} boundary_trapped={} no_partial_write={} sparse_wrap={:?} sparse_hole_trapped={}",
                report.loaded_word,
                report.boundary_trapped,
                report.no_partial_write,
                report.sparse.wrapped_addresses,
                report.sparse.hole_trapped
            );
        }
        [command, package, report] if command == "check-memory-trace" => {
            let checked = check_memory_trace(Path::new(package), Path::new(report))?;
            println!(
                "memory-trace: PASS: loaded={:#x} boundary_trapped={} no_partial_write={} sparse_wrap={:?} sparse_hole_trapped={}",
                checked.loaded_word,
                checked.boundary_trapped,
                checked.no_partial_write,
                checked.sparse.wrapped_addresses,
                checked.sparse.hole_trapped
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
        [command, package, output] if command == "emit-decoder-roundtrip" => {
            let report = decoder_roundtrip_report(Path::new(package))?;
            write_json(Path::new(output), &report)?;
            println!(
                "decoder-roundtrip: PASS: instructions={} unique={} reserved_rejected={} unused_rejected={}",
                report.instructions_checked,
                report.unique_encodings,
                report.reserved_mutations_rejected,
                report.unused_field_controls_rejected
            );
        }
        [command, package, report] if command == "check-decoder-roundtrip" => {
            let checked = check_decoder_roundtrip(Path::new(package), Path::new(report))?;
            println!(
                "decoder-roundtrip: PASS: instructions={} unique={} reserved_rejected={} unused_rejected={}",
                checked.instructions_checked,
                checked.unique_encodings,
                checked.reserved_mutations_rejected,
                checked.unused_field_controls_rejected
            );
        }
        [command, package, report] if command == "control-decoder-reserved-bit" => {
            check_decoder_reserved_bit_control(Path::new(package), Path::new(report))?;
            return Err("control-failure: reserved-bit encoding was accepted".into());
        }
        [command, package, output] if command == "emit-step-coverage" => {
            let report = step_coverage_report(Path::new(package))?;
            write_json(Path::new(output), &report)?;
            println!(
                "step-coverage: PASS: families={} effects={} traps={} stutter={} frame={}",
                report.families_executed,
                report.effect_rows_checked,
                report.trap_controls_checked,
                report.terminal_stutter_checked,
                report.frame_checks_passed
            );
        }
        [command, package, report] if command == "check-step-coverage" => {
            let checked = check_step_coverage(Path::new(package), Path::new(report))?;
            println!(
                "step-coverage: PASS: families={} effects={} traps={} stutter={} frame={}",
                checked.families_executed,
                checked.effect_rows_checked,
                checked.trap_controls_checked,
                checked.terminal_stutter_checked,
                checked.frame_checks_passed
            );
        }
        [command, package, report] if command == "control-step-hidden-write" => {
            check_step_hidden_write_control(Path::new(package), Path::new(report))?;
            return Err("control-failure: undeclared register write was accepted".into());
        }
        [command, package, report] if command == "control-step-mutation-suite" => {
            check_step_mutation_suite_control(Path::new(package), Path::new(report))?;
            return Err("control-failure: step mutation suite was accepted".into());
        }
        [command, package, output] if command == "emit-symbolic-addition" => {
            let report = symbolic_addition_report(Path::new(package))?;
            write_json(Path::new(output), &report)?;
            println!(
                "symbolic-addition: PASS: widths={} counterexample=({}, {}) replayed={}",
                report.proofs.len(),
                report.inverted_carry_counterexample.lhs,
                report.inverted_carry_counterexample.rhs,
                report.inverted_carry_counterexample.replayed_through_step
            );
        }
        [command, package, report] if command == "check-symbolic-addition" => {
            let checked = check_symbolic_addition(Path::new(package), Path::new(report))?;
            println!(
                "symbolic-addition: PASS: widths={} LRAT=all counterexample-replayed={}",
                checked.proofs.len(),
                checked.inverted_carry_counterexample.replayed_through_step
            );
        }
        [command, package, report] if command == "control-symbolic-addition-inverted-carry" => {
            check_symbolic_addition_inverted_carry_control(Path::new(package), Path::new(report))?;
            return Err("control-failure: inverted symbolic carry was accepted".into());
        }
        _ => {
            return Err("usage: axeyum-machine-evidence emit-a0-package OUTPUT | \
                 emit-word-roundtrip PACKAGE OUTPUT | check-word-roundtrip PACKAGE REPORT | \
                 control-word-roundtrip-reversed PACKAGE REPORT | \
                 emit-word-package PACKAGE OUTPUT | check-word-package PACKAGE REPORT | \
                 control-word-package-signed-zero-extension PACKAGE REPORT | \
                 emit-state-codec PACKAGE OUTPUT | check-state-codec PACKAGE REPORT | \
                 control-state-codec-trailing-byte PACKAGE REPORT | \
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
                 control-run-false-halt PACKAGE REPORT | \
                 emit-decoder-roundtrip PACKAGE OUTPUT | \
                 check-decoder-roundtrip PACKAGE REPORT | \
                 control-decoder-reserved-bit PACKAGE REPORT | \
                 emit-step-coverage PACKAGE OUTPUT | check-step-coverage PACKAGE REPORT | \
                 control-step-hidden-write PACKAGE REPORT | \
                 control-step-mutation-suite PACKAGE REPORT | \
                 emit-symbolic-addition PACKAGE OUTPUT | \
                 check-symbolic-addition PACKAGE REPORT | \
                 control-symbolic-addition-inverted-carry PACKAGE REPORT"
                .into());
        }
    }
    Ok(())
}
