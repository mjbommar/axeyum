//! Export and independently reimport the native integer left-unit/sign laws.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, canonical_declaration_sha256, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel, Lean4ExportMetadata, NameId, build_int_prelude};
use serde_json::json;
use sha2::{Digest, Sha256};

const TARGETS: [&str; 2] = ["Int.one_mul", "Int.neg_one_mul"];
const USAGE: &str = "usage: int_left_unit_sign_native_capsule <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-left-unit-sign-native-capsule: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let output = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    if arguments.next().is_some() || output.exists() {
        return Err(USAGE.to_owned());
    }

    let mut kernel = Kernel::new();
    let prelude = build_int_prelude(&mut kernel)
        .map_err(|error| format!("native Int prelude build failed: {error:?}"))?;
    let roots = [prelude.one_mul, prelude.neg_one_mul];
    let expected = roots
        .iter()
        .map(|&name| theorem_evidence(&kernel, name))
        .collect::<Result<Vec<_>, _>>()?;
    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &roots)
        .map_err(|error| format!("root-selected export failed: {error}"))?;

    for pass in 1..=2 {
        let imported = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh capsule import {pass} failed: {error:?}"))?;
        let observed = TARGETS
            .iter()
            .map(|target| find_name(imported.kernel(), target))
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .map(|name| theorem_evidence(imported.kernel(), name))
            .collect::<Result<Vec<_>, _>>()?;
        if observed != expected {
            return Err(format!("fresh import {pass} changed theorem evidence"));
        }
    }

    fs::write(&output, &bytes).map_err(|error| format!("capsule write failed: {error}"))?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-native-int-left-unit-sign-capsule",
            "state": "exported-and-twice-freshly-imported-empty-footprint",
            "capsule": {
                "bytes": bytes.len(),
                "sha256": hex_sha256(bytes.as_bytes()),
                "fresh_imports": 2
            },
            "theorems": expected,
            "Fibonacci_target_submissions": 0,
            "fact_status_changes": 0,
            "ledger_writes": 0
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn theorem_evidence(kernel: &Kernel, name: NameId) -> Result<serde_json::Value, String> {
    if !matches!(
        kernel.environment().get(name),
        Some(Declaration::Theorem { .. })
    ) {
        return Err(format!("{} is not a theorem", kernel.display_name(name)));
    }
    let mut footprint = names(kernel, &kernel.axiom_footprint(name));
    let mut dependencies = names(kernel, &kernel.theorem_dependencies(name));
    footprint.sort();
    dependencies.sort();
    if !footprint.is_empty() {
        return Err(format!(
            "{} has a non-empty axiom footprint: {footprint:?}",
            kernel.display_name(name)
        ));
    }
    Ok(json!({
        "name": kernel.display_name(name).to_string(),
        "declaration_sha256": canonical_declaration_sha256(kernel, name)?,
        "axiom_footprint": footprint,
        "direct_theorem_dependencies": dependencies
    }))
}

fn names(kernel: &Kernel, values: &[NameId]) -> Vec<String> {
    values
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect()
}

fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    let matches = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [name] => Ok(*name),
        [] => Err(format!("declaration is absent: {expected}")),
        _ => Err(format!("declaration is ambiguous: {expected}")),
    }
}

fn hex_sha256(bytes: &[u8]) -> String {
    let mut digest = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut digest, "{byte:02x}").expect("writing a digest cannot fail");
    }
    digest
}
