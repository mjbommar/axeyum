//! Compose the clean constructor proof and specialize the exact `Int.fib_neg` theorem.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice, import_ndjson,
    specialize_checked_theorem, verify_checked_theorem_composition,
    verify_checked_theorem_specialization,
};
use axeyum_lean_kernel::{Declaration, Kernel, Lean4ExportMetadata, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const RESIDUAL_STREAM_SHA256: &str =
    "607614dcd5a9843102ad2f2e8cddffda673603a3852dc544b61ca13e703ba420";
const BRANCH_STREAM_SHA256: &str =
    "1ac583c0fded419966c964e5cf52be55f2f8397b4a7d82a208bb94d3144830fa";
const RESIDUAL: &str = "Axeyum.Autogenesis.intFibNegFunctionResidualV1";
const POS_BRANCH: &str = "Axeyum.Autogenesis.intFibNegPositiveBranchV1";
const NEG_BRANCH: &str = "Axeyum.Autogenesis.intFibNegNegativeBranchV1";
const FIB: &str = "Int.fib";
const TARGET: &str = "Int.fib_neg";
const RESIDUAL_DECL_SHA256: &str =
    "370a37c020c431310a8dcc40b6117f49e332cba77d9a6efc3387a90176c5b0a4";
const POS_BRANCH_DECL_SHA256: &str =
    "9762cd8b5b9b7c84ffad1c8074e04d4308d3ed4b9c294d906d25664894798ab2";
const NEG_BRANCH_DECL_SHA256: &str =
    "e5fb7bd4b9c712618af0c0375ba0ad9d2b4717c89f104464c27039c4e2f523fd";
const USAGE: &str =
    "usage: int_fib_neg_exact_composition <residual.ndjson> <branches.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-fib-neg-exact-composition: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let residual_path = path(&mut arguments)?;
    let branches_path = path(&mut arguments)?;
    let output_path = path(&mut arguments)?;
    if arguments.next().is_some() || output_path.exists() {
        return Err(USAGE.to_owned());
    }

    let residual = import_bound(
        &residual_path,
        RESIDUAL_STREAM_SHA256,
        "clean function residual",
    )?;
    let branches = import_bound(
        &branches_path,
        BRANCH_STREAM_SHA256,
        "clean concrete branches",
    )?;
    for (label, completed) in [
        ("clean function residual", &residual),
        ("clean concrete branches", &branches),
    ] {
        if !completed.report().axioms.is_empty() {
            return Err(format!("{label} stream reaches assumptions"));
        }
    }
    require_exact_empty(residual.kernel(), RESIDUAL, RESIDUAL_DECL_SHA256)?;
    require_exact_empty(branches.kernel(), POS_BRANCH, POS_BRANCH_DECL_SHA256)?;
    require_exact_empty(branches.kernel(), NEG_BRANCH, NEG_BRANCH_DECL_SHA256)?;

    let composed = compose_checked_theorem_slice(residual.kernel(), branches.kernel(), &[RESIDUAL])
        .map_err(|error| format!("residual composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        residual.kernel(),
        branches.kernel(),
        composed.kernel(),
        composed.receipt(),
    )
    .map_err(|error| format!("residual composition replay failed: {error:?}"))?;
    let composition_receipt = composed.receipt().receipt_sha256.clone();
    let mut staging = composed.kernel().clone();
    require_empty(&staging, find_name(&staging, RESIDUAL)?, RESIDUAL)?;

    let generic = find_name(&staging, RESIDUAL)?;
    let arguments = [FIB, POS_BRANCH, NEG_BRANCH]
        .iter()
        .map(|name| find_name(&staging, name))
        .collect::<Result<Vec<_>, _>>()?;
    let target = nested_name(&mut staging, &["Int", "fib_neg"]);
    let specialized = specialize_checked_theorem(&staging, generic, &arguments, target)
        .map_err(|error| format!("exact specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &staging,
        specialized.kernel(),
        generic,
        &arguments,
        target,
        specialized.receipt(),
    )
    .map_err(|error| format!("exact specialization replay failed: {error:?}"))?;
    let specialization_receipt = specialized.receipt().receipt_sha256.clone();
    let kernel = specialized.kernel();
    let target = find_name(kernel, TARGET)?;
    require_empty(kernel, target, TARGET)?;
    let evidence = theorem_evidence(kernel, target)?;

    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
        .map_err(|error| format!("exact target export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh exact import {pass} failed: {error:?}"))?;
        let replay_target = find_name(replay.kernel(), TARGET)?;
        if theorem_evidence(replay.kernel(), replay_target)? != evidence {
            return Err(format!("fresh exact import {pass} changed evidence"));
        }
    }
    fs::write(&output_path, &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-int-fib-neg-exact-composition",
            "state": "exact-int-fib-neg-specialized-exported-and-reimported-empty-footprint",
            "input_sha256": {
                "function_residual": RESIDUAL_STREAM_SHA256,
                "concrete_branches": BRANCH_STREAM_SHA256,
            },
            "composition_receipt_sha256": composition_receipt,
            "specialization_receipt_sha256": specialization_receipt,
            "target": evidence,
            "capsule": {
                "path": output_path,
                "bytes": bytes.len(),
                "sha256": hex_sha256(bytes.as_bytes()),
                "fresh_imports": 2,
            },
            "execution": {
                "complete_invocations": 1,
                "input_stream_reads": 2,
                "composition_operations": 1,
                "composition_replays": 1,
                "specialization_operations": 1,
                "specialization_replays": 1,
                "capsule_exports": 1,
                "fresh_imports": 2,
                "exact_target_submissions": 1,
                "retries": 0,
                "ledger_writes": 0,
            },
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn require_exact_empty(kernel: &Kernel, name: &str, expected: &str) -> Result<(), String> {
    let theorem = find_name(kernel, name)?;
    require_empty(kernel, theorem, name)?;
    let observed = canonical_declaration_sha256(kernel, theorem)?;
    if observed == expected {
        Ok(())
    } else {
        Err(format!(
            "{name} identity changed: expected {expected}, got {observed}"
        ))
    }
}

fn require_empty(kernel: &Kernel, theorem: NameId, label: &str) -> Result<(), String> {
    if !matches!(
        kernel.environment().get(theorem),
        Some(Declaration::Theorem { .. })
    ) {
        return Err(format!("{label} is not a theorem"));
    }
    let footprint = names(kernel, &kernel.axiom_footprint(theorem));
    if footprint.is_empty() {
        Ok(())
    } else {
        Err(format!("{label} reaches assumptions: {footprint:?}"))
    }
}

fn theorem_evidence(kernel: &Kernel, theorem: NameId) -> Result<Value, String> {
    Ok(json!({
        "name": kernel.display_name(theorem).to_string(),
        "declaration_sha256": canonical_declaration_sha256(kernel, theorem)?,
        "axiom_footprint": names(kernel, &kernel.axiom_footprint(theorem)),
        "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(theorem)),
    }))
}

fn path(arguments: &mut impl Iterator<Item = std::ffi::OsString>) -> Result<PathBuf, String> {
    arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| USAGE.to_owned())
}

fn import_bound(
    path: &Path,
    expected: &str,
    label: &str,
) -> Result<axeyum_lean_import::CompletedImport, String> {
    let bytes = fs::read(path).map_err(|error| format!("{label} read failed: {error}"))?;
    let actual = hex_sha256(&bytes);
    if actual != expected {
        return Err(format!(
            "{label} identity changed: expected {expected}, got {actual}"
        ));
    }
    import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("{label} import failed: {error:?}"))
}

fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    let found = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match found.as_slice() {
        [name] => Ok(*name),
        [] => Err(format!("declaration is absent: {expected}")),
        _ => Err(format!("declaration is ambiguous: {expected}")),
    }
}

fn nested_name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    parts
        .iter()
        .fold(kernel.anon(), |prefix, part| kernel.name_str(prefix, *part))
}

fn names(kernel: &Kernel, values: &[NameId]) -> Vec<String> {
    let mut names = values
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect::<Vec<_>>();
    names.sort();
    names
}

fn hex_sha256(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut output, "{byte:02x}").expect("String writes cannot fail");
    }
    output
}
