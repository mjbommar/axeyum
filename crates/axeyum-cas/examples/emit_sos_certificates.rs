//! Emit the committed sum-of-squares certificate artifacts.
//!
//! ```text
//! usage: emit_sos_certificates [<id> ...] [--check]
//! ```
//!
//! With `--check` nothing is written and a differing file is an error, which is
//! how a gate can assert that the artifacts under `artifacts/sos-certificates/`
//! still match the corpus they were emitted from.
//!
//! Every artifact is **checked before it is written**. Emitting a certificate
//! this binary could not itself re-derive would put a file on disk that looks
//! like evidence and is not.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use axeyum_cas::sos::{self, corpus, json};

const DIRECTORY: &str = "artifacts/sos-certificates";

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("emit_sos_certificates: {message}");
            ExitCode::FAILURE
        }
    }
}

fn run() -> Result<(), String> {
    let mut wanted: Vec<String> = Vec::new();
    let mut check_only = false;
    for argument in std::env::args().skip(1) {
        if argument == "--check" {
            check_only = true;
        } else if argument.starts_with("--") {
            return Err(format!("unknown flag `{argument}`"));
        } else {
            wanted.push(argument);
        }
    }

    let directory = Path::new(DIRECTORY);
    if !check_only {
        std::fs::create_dir_all(directory)
            .map_err(|error| format!("cannot create {DIRECTORY}: {error}"))?;
    }

    let artifacts = corpus::all();
    if !wanted.is_empty() {
        for id in &wanted {
            if !artifacts.iter().any(|artifact| artifact.id() == id) {
                return Err(format!("no certificate with id `{id}` in the corpus"));
            }
        }
    }

    let mut written = 0usize;
    let mut unchanged = 0usize;
    let mut examined = 0usize;
    for artifact in &artifacts {
        if !wanted.is_empty() && !wanted.iter().any(|id| id == artifact.id()) {
            continue;
        }
        examined += 1;
        let report = sos::check(artifact).map_err(|message| {
            format!(
                "{} does not check, refusing to emit: {message}",
                artifact.id()
            )
        })?;
        let text = json::to_json(artifact);
        let path: PathBuf = directory.join(format!("{}.json", artifact.id()));
        let current = std::fs::read_to_string(&path).ok();
        if current.as_deref() == Some(text.as_str()) {
            unchanged += 1;
            println!(
                "unchanged  {}  ({} obligations)",
                path.display(),
                report.len()
            );
            continue;
        }
        if check_only {
            return Err(format!(
                "{} differs from the corpus; re-emit it rather than hand-editing",
                path.display()
            ));
        }
        std::fs::write(&path, &text)
            .map_err(|error| format!("cannot write {}: {error}", path.display()))?;
        written += 1;
        println!(
            "written    {}  ({} obligations)",
            path.display(),
            report.len()
        );
    }

    if examined == 0 {
        return Err(
            "no certificate was examined; a run that emits nothing is not a run that agreed".into(),
        );
    }
    println!("{written} written, {unchanged} unchanged, {examined} examined");
    Ok(())
}
