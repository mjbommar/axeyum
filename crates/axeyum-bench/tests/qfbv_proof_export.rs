//! Process-level checks for the standalone standard proof exporter.

use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

use axeyum_cnf::{check_drat, parse_dimacs, parse_drat};
use serde_json::Value;

fn temp_dir(label: &str) -> PathBuf {
    let unique = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "axeyum-qfbv-proof-export-{label}-{}-{unique}",
        std::process::id()
    ));
    fs::create_dir_all(&path).unwrap();
    path
}

fn script(verdict: &str, second_value: &str) -> String {
    format!(
        "(set-logic QF_BV)\n\
         (set-info :status {verdict})\n\
         (declare-fun x () (_ BitVec 4))\n\
         (assert (= x #x0))\n\
         (assert (= x {second_value}))\n\
         (check-sat)\n"
    )
}

#[test]
fn exports_standard_dimacs_drat_and_a_self_checked_manifest() {
    let root = temp_dir("unsat");
    let input = root.join("query.smt2");
    let out = root.join("proof");
    fs::write(&input, script("unsat", "#x1")).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_qfbv-proof-export"))
        .arg(&input)
        .arg(&out)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "export failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let manifest: Value = serde_json::from_slice(&fs::read(out.join("manifest.json")).unwrap())
        .expect("manifest parses");
    assert_eq!(manifest["schema"], "axeyum.qfbv-proof-export.v1");
    assert_eq!(manifest["outcome"], "unsat");
    assert_eq!(manifest["self_rechecked"], true);
    assert_eq!(manifest["artifacts"]["dimacs"]["path"], "problem.cnf");
    assert_eq!(manifest["artifacts"]["drat"]["path"], "proof.drat");

    let formula = parse_dimacs(&fs::read_to_string(out.join("problem.cnf")).unwrap()).unwrap();
    let proof = parse_drat(&fs::read_to_string(out.join("proof.drat")).unwrap()).unwrap();
    assert!(check_drat(&formula, &proof).unwrap());
    fs::remove_dir_all(root).unwrap();
}

#[test]
fn refuses_existing_output_and_satisfiable_queries_without_partial_artifacts() {
    let root = temp_dir("reject");
    let unsat = root.join("unsat.smt2");
    let sat = root.join("sat.smt2");
    fs::write(&unsat, script("unsat", "#x1")).unwrap();
    fs::write(&sat, script("sat", "#x0")).unwrap();

    let existing = root.join("existing");
    fs::create_dir(&existing).unwrap();
    let overwrite = Command::new(env!("CARGO_BIN_EXE_qfbv-proof-export"))
        .arg(&unsat)
        .arg(&existing)
        .output()
        .unwrap();
    assert!(!overwrite.status.success());
    assert!(String::from_utf8_lossy(&overwrite.stderr).contains("refusing to overwrite"));
    assert!(fs::read_dir(&existing).unwrap().next().is_none());

    let sat_out = root.join("sat-proof");
    let sat_result = Command::new(env!("CARGO_BIN_EXE_qfbv-proof-export"))
        .arg(&sat)
        .arg(&sat_out)
        .output()
        .unwrap();
    assert!(!sat_result.status.success());
    assert!(String::from_utf8_lossy(&sat_result.stderr).contains("satisfiable"));
    assert!(!sat_out.exists());

    let scoped = root.join("scoped.smt2");
    fs::write(
        &scoped,
        "(set-logic QF_BV)\n\
         (declare-fun x () (_ BitVec 4))\n\
         (push 1)\n\
         (assert (= x #x0))\n\
         (assert (= x #x1))\n\
         (check-sat)\n",
    )
    .unwrap();
    let scoped_out = root.join("scoped-proof");
    let scoped_result = Command::new(env!("CARGO_BIN_EXE_qfbv-proof-export"))
        .arg(&scoped)
        .arg(&scoped_out)
        .output()
        .unwrap();
    assert!(!scoped_result.status.success());
    assert!(String::from_utf8_lossy(&scoped_result.stderr).contains("flat assertion"));
    assert!(!scoped_out.exists());
    fs::remove_dir_all(root).unwrap();
}
