//! Export the accepted Fibonacci successor-addition theorem as a checked capsule.

#[path = "support/fib_gcd_shift.rs"]
#[allow(dead_code)]
mod fib_gcd_shift;

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice, import_ndjson,
    verify_checked_theorem_composition,
};
use axeyum_lean_kernel::{Declaration, Kernel, Lean4ExportMetadata, NameId, build_nat_prelude};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const RECURRENCE_SHA256: &str = "5220ace53dcbf0b89121ba72c8e63cc7dcb2a2d7836b313bc597607859d78674";
const RECURRENCE: &str = "Axeyum.Autogenesis.fibAddTwo";
const USAGE: &str = "usage: fib_addition_capsule <fib-recurrence.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("fib-addition-capsule: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let recurrence_path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let output_path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    if arguments.next().is_some() || output_path.exists() {
        return Err(USAGE.to_owned());
    }
    let recurrence = import_bound(&recurrence_path)?;
    if !recurrence.report().axioms.is_empty() {
        return Err("recurrence stream is not proof-isolated".to_owned());
    }
    let mut native = Kernel::new();
    let prelude = build_nat_prelude(&mut native)
        .map_err(|error| format!("native Nat prelude build failed: {error:?}"))?;
    let with_recurrence =
        compose_checked_theorem_slice(recurrence.kernel(), &native, &[RECURRENCE])
            .map_err(|error| format!("recurrence composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        recurrence.kernel(),
        &native,
        with_recurrence.kernel(),
        with_recurrence.receipt(),
    )
    .map_err(|error| format!("recurrence composition did not replay: {error:?}"))?;
    let addition =
        fib_gcd_shift::reconstruct_addition_twice(with_recurrence.kernel(), &prelude, RECURRENCE)?;
    let capsule = export_checked_capsule(
        &addition.kernel,
        fib_gcd_shift::ADDITION_TARGET,
        &output_path,
    )?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-fibonacci-addition-portable-capsule",
            "state": "fibonacci-addition-exported-and-reimported-empty-footprint",
            "recurrence_stream_sha256": RECURRENCE_SHA256,
            "recurrence_composition_receipt_sha256": with_recurrence.receipt().receipt_sha256,
            "reconstruction": addition.evidence,
            "portable_capsule": capsule,
            "exact_target_submissions": 0,
            "target_credit": 0,
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn export_checked_capsule(kernel: &Kernel, root: &str, output: &Path) -> Result<Value, String> {
    let root_name = find_name(kernel, root)?;
    let expected = theorem_evidence(kernel, root_name)?;
    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[root_name])
        .map_err(|error| format!("root-selected capsule export failed: {error}"))?;
    for pass in 1..=2 {
        let imported = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("capsule import {pass} failed: {error:?}"))?;
        let imported_name = find_name(imported.kernel(), root)?;
        if theorem_evidence(imported.kernel(), imported_name)? != expected {
            return Err(format!("capsule import {pass} changed theorem evidence"));
        }
    }
    fs::write(output, &bytes).map_err(|error| format!("capsule write failed: {error}"))?;
    Ok(json!({
        "root": root,
        "bytes": bytes.len(),
        "sha256": hex_sha256(bytes.as_bytes()),
        "fresh_imports": 2,
        "theorem": expected,
        "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
    }))
}

fn theorem_evidence(kernel: &Kernel, name: NameId) -> Result<Value, String> {
    if !matches!(
        kernel.environment().get(name),
        Some(Declaration::Theorem { .. })
    ) {
        return Err(format!("{} is not a theorem", kernel.display_name(name)));
    }
    let mut footprint = kernel
        .axiom_footprint(name)
        .into_iter()
        .map(|dependency| kernel.display_name(dependency).to_string())
        .collect::<Vec<_>>();
    let mut dependencies = kernel
        .theorem_dependencies(name)
        .into_iter()
        .map(|dependency| kernel.display_name(dependency).to_string())
        .collect::<Vec<_>>();
    footprint.sort();
    dependencies.sort();
    Ok(
        json!({"name": kernel.display_name(name).to_string(), "declaration_sha256": canonical_declaration_sha256(kernel, name)?, "axiom_footprint": footprint, "direct_theorem_dependencies": dependencies}),
    )
}

fn import_bound(path: &Path) -> Result<axeyum_lean_import::CompletedImport, String> {
    let bytes =
        fs::read(path).map_err(|error| format!("recurrence stream read failed: {error}"))?;
    let actual = hex_sha256(&bytes);
    if actual != RECURRENCE_SHA256 {
        return Err(format!("recurrence identity changed: {actual}"));
    }
    import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("recurrence import failed: {error:?}"))
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
        write!(&mut digest, "{byte:02x}").expect("writing a digest into a String cannot fail");
    }
    digest
}
