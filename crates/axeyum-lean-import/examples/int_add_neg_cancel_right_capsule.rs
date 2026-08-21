//! Export and freshly reimport native axiom-free integer right cancellation.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, canonical_declaration_sha256, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel, Lean4ExportMetadata, NameId, build_int_prelude};
use serde_json::json;
use sha2::{Digest, Sha256};

const TARGET: &str = "Int.add_neg_cancel_right";
const USAGE: &str = "usage: int_add_neg_cancel_right_capsule <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-add-neg-cancel-right-capsule: {error}");
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
    let expected = theorem_evidence(&kernel, prelude.add_neg_cancel_right)?;
    let bytes = kernel
        .render_lean4export_ndjson_roots(
            &Lean4ExportMetadata::axeyum("4.30.0"),
            &[prelude.add_neg_cancel_right],
        )
        .map_err(|error| format!("root-selected export failed: {error}"))?;

    let imported = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
        .map_err(|error| format!("fresh capsule import failed: {error:?}"))?;
    let imported_target = find_name(imported.kernel(), TARGET)?;
    let observed = theorem_evidence(imported.kernel(), imported_target)?;
    if observed != expected {
        return Err("fresh import changed theorem evidence".to_owned());
    }
    fs::write(&output, &bytes).map_err(|error| format!("capsule write failed: {error}"))?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-native-int-cancellation-capsule",
            "state": "exported-and-freshly-imported-empty-footprint",
            "capsule": {
                "bytes": bytes.len(),
                "sha256": hex_sha256(bytes.as_bytes()),
                "fresh_imports": 1
            },
            "theorem": expected,
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
