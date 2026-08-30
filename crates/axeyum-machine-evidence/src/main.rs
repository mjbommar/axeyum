//! Command-line producer and checker for machine evidence artifacts.

use std::{env, path::Path};

use axeyum_machine_evidence::{
    check_word_roundtrip, check_word_roundtrip_reversed_control, semantic_package,
    word_roundtrip_report, write_json,
};

fn main() {
    if let Err(error) = run() {
        eprintln!("axeyum-machine-evidence: {error}");
        std::process::exit(1);
    }
}

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
        _ => {
            return Err("usage: axeyum-machine-evidence emit-a0-package OUTPUT | \
                 emit-word-roundtrip PACKAGE OUTPUT | check-word-roundtrip PACKAGE REPORT | \
                 control-word-roundtrip-reversed PACKAGE REPORT"
                .into());
        }
    }
    Ok(())
}
