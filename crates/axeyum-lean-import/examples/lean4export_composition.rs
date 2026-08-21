//! Compose theorem roots from one proof-isolated Lean export into another.

use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    ImportLimits, compose_checked_theorem_slice, import_ndjson, verify_checked_theorem_composition,
};

fn main() {
    if let Err(error) = run() {
        eprintln!("lean4export-composition: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: lean4export_composition <source.ndjson> <target.ndjson> <root>+")?;
    let target_path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: lean4export_composition <source.ndjson> <target.ndjson> <root>+")?;
    let roots = arguments
        .map(|root| {
            root.into_string()
                .map_err(|_| "root name is not valid UTF-8".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    if roots.is_empty() {
        return Err("at least one theorem root is required".to_owned());
    }
    let source_bytes = fs::read(source_path).map_err(|error| error.to_string())?;
    let target_bytes = fs::read(target_path).map_err(|error| error.to_string())?;
    let source = import_ndjson(Cursor::new(source_bytes), ImportLimits::default())
        .map_err(|error| format!("source import failed: {error:?}"))?;
    let target = import_ndjson(Cursor::new(target_bytes), ImportLimits::default())
        .map_err(|error| format!("target import failed: {error:?}"))?;
    if !source.report().axioms.is_empty() {
        return Err(format!(
            "source export is not proof-isolated: {:?}",
            source.report().axioms
        ));
    }
    if !target.report().axioms.is_empty() {
        return Err(format!(
            "target export is not proof-isolated: {:?}",
            target.report().axioms
        ));
    }
    let source_kernel = source.kernel();
    let target_kernel = target.kernel();
    let root_refs = roots.iter().map(String::as_str).collect::<Vec<_>>();
    let completed = compose_checked_theorem_slice(source_kernel, target_kernel, &root_refs)
        .map_err(|error| format!("composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        source_kernel,
        target_kernel,
        completed.kernel(),
        completed.receipt(),
    )
    .map_err(|error| format!("composition replay failed: {error:?}"))?;
    if completed
        .receipt()
        .added_theorems
        .iter()
        .any(|theorem| !theorem.axiom_footprint.is_empty())
    {
        return Err("composition added an assumption-bearing theorem".to_owned());
    }
    print!(
        "{}",
        completed
            .receipt()
            .to_pretty_json()
            .map_err(|error| error.to_string())?
    );
    Ok(())
}
