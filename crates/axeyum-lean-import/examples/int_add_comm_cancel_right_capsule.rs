//! Export and freshly reimport native integer commutativity and right cancellation.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, canonical_declaration_sha256, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel, Lean4ExportMetadata, NameId, build_int_prelude};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const ADD_COMM: &str = "Int.add_comm";
const CANCEL_RIGHT: &str = "Int.add_neg_cancel_right";
const USAGE: &str = "usage: int_add_comm_cancel_right_capsule <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-add-comm-cancel-right-capsule: {error}");
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
    let expected = [
        theorem_evidence(&kernel, prelude.add_comm)?,
        theorem_evidence(&kernel, prelude.add_neg_cancel_right)?,
    ];
    if expected.iter().any(|row| {
        row.get("axiom_footprint")
            .and_then(Value::as_array)
            .is_none_or(|footprint| !footprint.is_empty())
    }) {
        return Err("native algebra root reaches assumptions".to_owned());
    }

    let bytes = kernel
        .render_lean4export_ndjson_roots(
            &Lean4ExportMetadata::axeyum("4.30.0"),
            &[prelude.add_comm, prelude.add_neg_cancel_right],
        )
        .map_err(|error| format!("root-selected export failed: {error}"))?;

    for pass in 1..=2 {
        let imported = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh capsule import {pass} failed: {error:?}"))?;
        let observed = [
            theorem_evidence(imported.kernel(), find_name(imported.kernel(), ADD_COMM)?)?,
            theorem_evidence(
                imported.kernel(),
                find_name(imported.kernel(), CANCEL_RIGHT)?,
            )?,
        ];
        if observed != expected {
            return Err(format!(
                "fresh capsule import {pass} changed theorem evidence"
            ));
        }
    }

    fs::write(&output, &bytes).map_err(|error| format!("capsule write failed: {error}"))?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-native-int-commutativity-cancellation-capsule",
            "state": "exported-and-twice-reimported-empty-footprint",
            "capsule": {
                "bytes": bytes.len(),
                "sha256": hex_sha256(bytes.as_bytes()),
                "fresh_imports": 2
            },
            "theorems": expected,
            "execution": {
                "complete_invocations": 1,
                "native_prelude_builds": 1,
                "exports": 1,
                "fresh_imports": 2,
                "retries": 0
            },
            "Fibonacci_target_submissions": 0,
            "fact_status_changes": 0,
            "ledger_writes": 0
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn theorem_evidence(kernel: &Kernel, name: NameId) -> Result<Value, String> {
    if !matches!(
        kernel.environment().get(name),
        Some(Declaration::Theorem { .. })
    ) {
        return Err(format!("{} is not a theorem", kernel.display_name(name)));
    }
    Ok(json!({
        "name": kernel.display_name(name).to_string(),
        "declaration_sha256": canonical_declaration_sha256(kernel, name)?,
        "axiom_footprint": names(kernel, &kernel.axiom_footprint(name)),
        "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(name))
    }))
}

fn names(kernel: &Kernel, values: &[NameId]) -> Vec<String> {
    let mut rendered = values
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect::<Vec<_>>();
    rendered.sort();
    rendered
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
