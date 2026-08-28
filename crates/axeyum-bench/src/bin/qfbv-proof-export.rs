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
    if let Some(offending) = script.commands.iter().find(|command| !is_flat(command)) {
        return Err(format!(
            "{} must be a flat assertion script without push/pop/reset/check-sat-assuming; \
             found {}",
            input.display(),
            command_name(offending)
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

/// Whether `command` leaves the flat, single-`check-sat` assertion view — the
/// one thing this exporter can honestly claim a DRAT proof is *about*.
///
/// Written as an **exhaustive** match with no wildcard arm, deliberately. The
/// predicate this replaced was `matches!(command, Assert(_) | CheckSat)`, an
/// allowlist of two: correct when the exporter landed (`ba9ff7c6c`, 2026-07-19),
/// and silently wrong from `81361cdd1` (2026-08-21) onward, which made
/// `set-logic` and `set-option` **positional** `ScriptCommand`s rather than
/// parser-side metadata. From that commit the binary could not succeed on any
/// input at all: it *requires* `(set-logic QF_BV)` ten lines above, then
/// refused the script for containing a `set-logic` command. Both tests in
/// `tests/qfbv_proof_export.rs` went red and stayed red.
///
/// A wildcard would have let that happen again. With every variant named, a new
/// `ScriptCommand` fails to compile here until someone decides which side of the
/// line it falls on — which is the decision that was skipped last time.
fn is_flat(command: &ScriptCommand) -> bool {
    match command {
        // Assertions and the single decision point are the flat view itself.
        ScriptCommand::Assert(_) | ScriptCommand::CheckSat => true,
        // Recorded positionally by the parser, but they neither add nor remove
        // an assertion, so the CNF this exporter proves is unchanged by them.
        // `set-logic` in particular is *mandatory* for this binary.
        ScriptCommand::SetLogic(_) | ScriptCommand::SetOption { .. } | ScriptCommand::Echo(_) => {
            true
        }
        // Output commands. They report on the preceding `check-sat` and cannot
        // change what was decided; this binary simply does not answer them.
        ScriptCommand::GetAssertions
        | ScriptCommand::GetModel
        | ScriptCommand::GetValue(_)
        | ScriptCommand::GetUnsatCore
        | ScriptCommand::GetProof
        | ScriptCommand::UnansweredOutput(_) => true,
        // These move the assertion stack, or decide something other than the
        // conjunction of every assertion in the file. A DRAT proof over the flat
        // CNF would then be a proof about a different problem.
        ScriptCommand::Push(_)
        | ScriptCommand::Pop(_)
        | ScriptCommand::CheckSatAssuming(_)
        | ScriptCommand::ResetAssertions => false,
    }
}

/// The SMT-LIB spelling of `command`, for the refusal message. Naming the
/// offender is the difference between a five-minute fix and a month unnoticed.
fn command_name(command: &ScriptCommand) -> &'static str {
    match command {
        ScriptCommand::Assert(_) => "assert",
        ScriptCommand::Push(_) => "push",
        ScriptCommand::Pop(_) => "pop",
        ScriptCommand::CheckSat => "check-sat",
        ScriptCommand::CheckSatAssuming(_) => "check-sat-assuming",
        ScriptCommand::ResetAssertions => "reset-assertions",
        ScriptCommand::GetAssertions => "get-assertions",
        ScriptCommand::SetLogic(_) => "set-logic",
        ScriptCommand::SetOption { .. } => "set-option",
        ScriptCommand::GetModel => "get-model",
        ScriptCommand::GetValue(_) => "get-value",
        ScriptCommand::GetUnsatCore => "get-unsat-core",
        ScriptCommand::GetProof => "get-proof",
        ScriptCommand::Echo(_) => "echo",
        ScriptCommand::UnansweredOutput(keyword) => {
            // Borrowed as `&'static` is impossible here; the keyword is only
            // ever one of a fixed parser-side set, so name the class instead.
            let _ = keyword;
            "an unanswered output command"
        }
    }
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
