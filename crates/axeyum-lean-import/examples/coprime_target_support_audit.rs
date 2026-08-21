//! Audit the three preregistered target-side coprime cancellation roots.
//!
//! The root-selected proof stream is read once into the importer. This example
//! emits identities, theorem dependencies, and axiom footprints only; it never
//! renders expressions or theorem values.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, canonical_declaration_sha256, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const STREAM_SHA256: &str = "5d5f7293590ad4f6b43a8bb4cc16fbca4873c2f3ceb0f775dad787d1888d8f9d";
const PLAN_SHA256: &str = "2d90479e4a9fa45fbd2b753e167f48593ef434bf4080abeb885bc0e89b388ff5";
const ROOTS: [&str; 3] = [
    "Nat.Coprime.coprime_dvd_left",
    "Nat.Coprime.dvd_of_dvd_mul_left",
    "Nat.Coprime.eq_1",
];

fn main() {
    if let Err(error) = run() {
        eprintln!("coprime-target-support-audit: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: coprime_target_support_audit <coprime-roots.ndjson>")?;
    if arguments.next().is_some() {
        return Err("usage: coprime_target_support_audit <coprime-roots.ndjson>".to_owned());
    }
    let bytes = fs::read(&path).map_err(|error| error.to_string())?;
    let mut stream_sha256 = String::with_capacity(64);
    for byte in Sha256::digest(&bytes) {
        write!(&mut stream_sha256, "{byte:02x}")
            .expect("writing a digest into a String cannot fail");
    }
    if stream_sha256 != STREAM_SHA256 {
        return Err("root-selected proof stream identity changed".to_owned());
    }
    let completed = import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("stream import failed: {error:?}"))?;
    let kernel = completed.kernel();
    let rows = ROOTS
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
    let stream_axioms = completed.report().axioms.clone();
    let result = json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-coprime-target-cancellation-root-audit-result",
        "state": "three-target-roots-classified-no-support-authority",
        "plan": {
            "path": "artifacts/autogenesis/coprime-target-cancellation-root-audit-plan-v1.json",
            "sha256": PLAN_SHA256,
        },
        "input": {
            "path": path,
            "sha256": STREAM_SHA256,
            "bytes": 1_162_279,
            "mode": "0444",
            "stream_axioms": stream_axioms,
        },
        "summary": {
            "population": rows.len(),
            "class_counts": counts,
            "all_roots_empty": rows.iter().all(|row| row["class"] == "empty-footprint"),
        },
        "rows": rows,
        "authority": {
            "exporter_invocations": 1,
            "importer_runs": 1,
            "proof_bearing_stream_reads": 1,
            "proof_terms_rendered": 0,
            "theorem_values_rendered": 0,
            "authored_support_compilations": 0,
            "new_theorem_submissions": 0,
            "exact_target_submissions": 0,
            "executor_invocations": 0,
            "support_theorem_credit": 0,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
            "retries": 0,
        },
        "limitations": "The result classifies three official target-side roots. It neither proves the composed cancellation statement nor changes the bottom-up Euclidean foundation boundary.",
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn audit_theorem(kernel: &Kernel, expected_name: &str) -> Result<Value, String> {
    let (name, declaration) = kernel
        .environment()
        .iter()
        .find_map(|(&name, declaration)| {
            (kernel.display_name(name).to_string() == expected_name).then_some((name, declaration))
        })
        .ok_or_else(|| format!("preregistered root is absent: {expected_name}"))?;
    if !matches!(declaration, Declaration::Theorem { .. }) {
        return Err(format!(
            "preregistered root is not a theorem: {expected_name}"
        ));
    }
    let mut footprint = rendered_names(kernel, &kernel.axiom_footprint(name));
    let mut dependencies = rendered_names(kernel, &kernel.theorem_dependencies(name));
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
        "declaration_sha256": canonical_declaration_sha256(kernel, name)
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
