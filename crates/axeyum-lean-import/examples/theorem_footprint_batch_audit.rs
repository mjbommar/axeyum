//! Audit an ordered batch of theorem roots from one Lean export stream.
//!
//! This is deliberately a read-only measurement tool. It imports the stream
//! once and emits declaration identities, direct theorem dependencies, and
//! kernel-derived axiom footprints. It never renders theorem types, values, or
//! proof expressions. A separately frozen plan/result checker must bind any
//! invocation to a particular stream, root set, budget, and successor action.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, canonical_declaration_sha256, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const USAGE: &str = "usage: theorem_footprint_batch_audit <stream.ndjson> <root>...";

fn main() {
    if let Err(error) = run() {
        eprintln!("theorem-footprint-batch-audit: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let roots = arguments
        .map(|argument| {
            argument
                .into_string()
                .map_err(|_| "theorem root is not valid UTF-8".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    if roots.is_empty() {
        return Err(USAGE.to_owned());
    }
    let distinct = roots.iter().collect::<BTreeSet<_>>();
    if distinct.len() != roots.len() {
        return Err("theorem roots must be distinct".to_owned());
    }

    let bytes = fs::read(&path).map_err(|error| error.to_string())?;
    let stream_bytes = bytes.len();
    let stream_sha256 = sha256(&bytes);
    let completed = import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("stream import failed: {error:?}"))?;
    let kernel = completed.kernel();
    let rows = roots
        .iter()
        .map(|name| audit_theorem(kernel, name))
        .collect::<Result<Vec<_>, _>>()?;

    let mut counts = BTreeMap::from([
        ("empty-footprint", 0_u64),
        ("other-assumption-bearing", 0),
        ("propext-bearing", 0),
    ]);
    for row in &rows {
        let classification = row["class"].as_str().ok_or("audit row lacks a class")?;
        *counts
            .get_mut(classification)
            .ok_or("audit row has an unknown class")? += 1;
    }
    let mut stream_axioms = completed.report().axioms.clone();
    stream_axioms.sort();
    let result = json!({
        "schema_version": 1,
        "kind": "axeyum-theorem-footprint-batch-audit",
        "input": {
            "path": path,
            "sha256": stream_sha256,
            "bytes": stream_bytes,
            "stream_axioms": stream_axioms,
        },
        "ordered_roots": roots,
        "summary": {
            "population": rows.len(),
            "class_counts": counts,
            "all_roots_empty": rows.iter().all(|row| row["class"] == "empty-footprint"),
        },
        "rows": rows,
        "rendered_material": {
            "proof_terms": 0,
            "theorem_types": 0,
            "theorem_values": 0,
        },
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn audit_theorem(kernel: &Kernel, expected_name: &str) -> Result<Value, String> {
    let matches = kernel
        .environment()
        .iter()
        .filter_map(|(&name, declaration)| {
            (kernel.display_name(name).to_string() == expected_name).then_some((name, declaration))
        })
        .collect::<Vec<_>>();
    let [(name, declaration)] = matches.as_slice() else {
        return match matches.len() {
            0 => Err(format!("requested root is absent: {expected_name}")),
            count => Err(format!(
                "requested root is ambiguous: {expected_name} ({count} matches)"
            )),
        };
    };
    if !matches!(declaration, Declaration::Theorem { .. }) {
        return Err(format!("requested root is not a theorem: {expected_name}"));
    }
    let mut footprint = rendered_names(kernel, &kernel.axiom_footprint(*name));
    let mut dependencies = rendered_names(kernel, &kernel.theorem_dependencies(*name));
    footprint.sort();
    dependencies.sort();
    let classification = if footprint.is_empty() {
        "empty-footprint"
    } else if footprint.iter().any(|axiom| axiom == "propext") {
        "propext-bearing"
    } else {
        "other-assumption-bearing"
    };
    Ok(json!({
        "name": expected_name,
        "declaration_sha256": canonical_declaration_sha256(kernel, *name)
            .map_err(|error| error.clone())?,
        "axiom_footprint": footprint,
        "direct_theorem_dependencies": dependencies,
        "class": classification,
    }))
}

fn rendered_names(kernel: &Kernel, names: &[axeyum_lean_kernel::NameId]) -> Vec<String> {
    names
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect()
}

fn sha256(bytes: &[u8]) -> String {
    let mut digest = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut digest, "{byte:02x}").expect("writing a digest into a String cannot fail");
    }
    digest
}
