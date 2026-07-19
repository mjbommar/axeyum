//! Export one flat `QF_BV` SMT-LIB query as standard DIMACS + DRAT evidence.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use axeyum_smtlib::{ScriptCommand, parse_script};
use axeyum_solver::{UnsatProofOutcome, export_qf_bv_unsat_proof};
use serde_json::{Value as JsonValue, json};
use sha2::{Digest, Sha256};

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("qfbv-proof-export: {error}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let mut args = env::args_os().skip(1);
    let input = args
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| usage("missing INPUT.smt2"))?;
    let output = args
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| usage("missing OUTPUT-DIRECTORY"))?;
    if args.next().is_some() {
        return Err(usage("unexpected extra argument"));
    }
    if output.exists() {
        return Err(format!("refusing to overwrite {}", output.display()));
    }

    let source = fs::read(&input).map_err(|error| format!("read {}: {error}", input.display()))?;
    let text = std::str::from_utf8(&source)
        .map_err(|error| format!("{} is not UTF-8: {error}", input.display()))?;
    let script =
        parse_script(text).map_err(|error| format!("parse {}: {error}", input.display()))?;
    if script.logic.as_deref() != Some("QF_BV") {
        return Err(format!("{} must declare set-logic QF_BV", input.display()));
    }
    if script.check_sats != 1 {
        return Err(format!(
            "{} must contain exactly one check-sat command",
            input.display()
        ));
    }
    if script
        .commands
        .iter()
        .any(|command| !matches!(command, ScriptCommand::Assert(_) | ScriptCommand::CheckSat))
    {
        return Err(format!(
            "{} must be a flat assertion script without push/pop/reset/check-sat-assuming",
            input.display()
        ));
    }
    if script.assertions.is_empty() {
        return Err(format!("{} contains no parsed assertions", input.display()));
    }

    let proof = match export_qf_bv_unsat_proof(&script.arena, &script.assertions)
        .map_err(|error| format!("proof export failed: {error}"))?
    {
        UnsatProofOutcome::Proved(proof) => proof,
        UnsatProofOutcome::Satisfiable => {
            return Err("query is satisfiable; no unsat proof exists".to_owned());
        }
        UnsatProofOutcome::Inconclusive => {
            return Err("proof search was inconclusive; no proof artifact written".to_owned());
        }
    };
    if !proof
        .recheck()
        .map_err(|error| format!("consumer-side self-recheck failed: {error}"))?
    {
        return Err("consumer-side self-recheck rejected the exported proof".to_owned());
    }

    fs::create_dir_all(&output).map_err(|error| format!("create {}: {error}", output.display()))?;
    write(&output.join("problem.cnf"), proof.dimacs.as_bytes())?;
    write(&output.join("proof.drat"), proof.drat.as_bytes())?;
    let lrat = match proof.lrat.as_deref() {
        Some(raw) => {
            write(&output.join("proof.lrat"), raw.as_bytes())?;
            Some(artifact_record("proof.lrat", raw.as_bytes()))
        }
        None => None,
    };
    let manifest = json!({
        "schema": "axeyum.qfbv-proof-export.v1",
        "outcome": "unsat",
        "source": {
            "path": input,
            "bytes": source.len(),
            "sha256": prefixed_hash(&source),
            "logic": script.logic,
            "assertions": script.assertions.len(),
            "check_sat_commands": script.check_sats,
        },
        "self_rechecked": true,
        "assurance": "standard clausal DIMACS/DRAT; source-to-CNF reduction remains separately trusted or end-to-end certified",
        "artifacts": {
            "dimacs": artifact_record("problem.cnf", proof.dimacs.as_bytes()),
            "drat": artifact_record("proof.drat", proof.drat.as_bytes()),
            "lrat": lrat,
        },
    });
    let rendered = serde_json::to_string_pretty(&manifest)
        .map_err(|error| format!("render manifest: {error}"))?
        + "\n";
    write(&output.join("manifest.json"), rendered.as_bytes())?;
    print!("{rendered}");
    Ok(())
}

fn usage(detail: &str) -> String {
    format!("{detail}; usage: qfbv-proof-export INPUT.smt2 OUTPUT-DIRECTORY")
}

fn write(path: &Path, raw: &[u8]) -> Result<(), String> {
    fs::write(path, raw).map_err(|error| format!("write {}: {error}", path.display()))
}

fn artifact_record(path: &str, raw: &[u8]) -> JsonValue {
    json!({
        "path": path,
        "bytes": raw.len(),
        "sha256": prefixed_hash(raw),
    })
}

fn prefixed_hash(raw: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let digest = Sha256::digest(raw);
    let mut encoded = String::with_capacity("sha256:".len() + digest.len() * 2);
    encoded.push_str("sha256:");
    for byte in digest {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}
