//! Compose and specialize the exact integer Fibonacci recurrence corollary.

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

const RECURRENCE_SHA256: &str = "0fbbb4d55ed862f7feb1b8efa3bf45eed24269067b3702c727d05e45c8947219";
const CANCELLATION_SHA256: &str =
    "42683af8480ea4d7bef42b32ecab3f3d43a2228c8a30f8b73417bbda6eca4fa2";
const RESIDUAL_SHA256: &str = "69b5c02680e30e4ef31a368a6b86dd33a6997249a8538bcae60c3e3e9b2b58f1";

const FIB: &str = "Int.fib";
const RECURRENCE: &str = "Int.fib_add_two";
const CANCELLATION: &str = "Int.add_neg_cancel_right";
const RESIDUAL: &str = "Axeyum.Autogenesis.intFibEqAddTwoSubAddOneResidualV2";
const TARGET: &str = "Int.fib_eq_fib_add_two_sub_fib_add_one";
const USAGE: &str = "usage: int_fib_recurrence_corollary_composition <recurrence.ndjson> <cancellation.ndjson> <residual.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-fib-recurrence-corollary-composition: {error}");
        std::process::exit(1);
    }
}

// Keeping compose -> replay -> specialize -> replay linear makes the exact
// assurance order auditable in one place.
#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let recurrence_path = path(&mut arguments)?;
    let cancellation_path = path(&mut arguments)?;
    let residual_path = path(&mut arguments)?;
    let output_path = path(&mut arguments)?;
    if arguments.next().is_some() || output_path.exists() {
        return Err(USAGE.to_owned());
    }

    let recurrence = import_bound(&recurrence_path, RECURRENCE_SHA256, "recurrence")?;
    let cancellation = import_bound(&cancellation_path, CANCELLATION_SHA256, "cancellation")?;
    let residual = import_bound(&residual_path, RESIDUAL_SHA256, "residual")?;
    for (label, imported, root) in [
        ("recurrence", &recurrence, RECURRENCE),
        ("cancellation", &cancellation, CANCELLATION),
        ("residual", &residual, RESIDUAL),
    ] {
        require_empty(
            imported.kernel(),
            find_name(imported.kernel(), root)?,
            label,
        )?;
    }

    let mut kernel = recurrence.kernel().clone();
    if optional_name(&kernel, TARGET)?.is_some() {
        return Err("exact target already exists before composition".to_owned());
    }
    let residual_composition =
        compose_checked_theorem_slice(residual.kernel(), &kernel, &[RESIDUAL])
            .map_err(|error| format!("residual composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        residual.kernel(),
        &kernel,
        residual_composition.kernel(),
        residual_composition.receipt(),
    )
    .map_err(|error| format!("residual composition replay failed: {error:?}"))?;
    kernel = residual_composition.kernel().clone();

    let cancellation_composition =
        compose_checked_theorem_slice(cancellation.kernel(), &kernel, &[CANCELLATION])
            .map_err(|error| format!("cancellation composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        cancellation.kernel(),
        &kernel,
        cancellation_composition.kernel(),
        cancellation_composition.receipt(),
    )
    .map_err(|error| format!("cancellation composition replay failed: {error:?}"))?;
    kernel = cancellation_composition.kernel().clone();

    if optional_name(&kernel, TARGET)?.is_some() {
        return Err("exact target appeared before specialization".to_owned());
    }
    let generic = find_name(&kernel, RESIDUAL)?;
    let specialization_arguments = [
        find_name(&kernel, FIB)?,
        find_name(&kernel, RECURRENCE)?,
        find_name(&kernel, CANCELLATION)?,
    ];
    let target_name = nested_name(&mut kernel, &["Int", "fib_eq_fib_add_two_sub_fib_add_one"]);
    let specialized =
        specialize_checked_theorem(&kernel, generic, &specialization_arguments, target_name)
            .map_err(|error| format!("exact specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &kernel,
        specialized.kernel(),
        generic,
        &specialization_arguments,
        target_name,
        specialized.receipt(),
    )
    .map_err(|error| format!("exact specialization replay failed: {error:?}"))?;
    kernel = specialized.kernel().clone();

    let target = find_name(&kernel, TARGET)?;
    require_empty(&kernel, target, TARGET)?;
    let target_evidence = evidence(&kernel, target)?;
    let expected_dependencies = [CANCELLATION, RECURRENCE, RESIDUAL];
    if names(&kernel, &kernel.theorem_dependencies(target)) != expected_dependencies {
        return Err("exact target dependency set changed".to_owned());
    }

    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
        .map_err(|error| format!("exact target export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh target import {pass} failed: {error:?}"))?;
        let replay_target = find_name(replay.kernel(), TARGET)?;
        if evidence(replay.kernel(), replay_target)? != target_evidence {
            return Err(format!("fresh target import {pass} changed evidence"));
        }
    }
    fs::write(&output_path, &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-int-fib-recurrence-corollary-exact-composition",
            "state": "exact-target-specialized-exported-and-reimported-empty-footprint",
            "input_sha256": {
                "recurrence": RECURRENCE_SHA256,
                "cancellation": CANCELLATION_SHA256,
                "residual": RESIDUAL_SHA256,
            },
            "composition_receipts": {
                "residual": residual_composition.receipt().receipt_sha256,
                "cancellation": cancellation_composition.receipt().receipt_sha256,
            },
            "specialization_receipt_sha256": specialized.receipt().receipt_sha256,
            "target": target_evidence,
            "capsule": {
                "bytes": bytes.len(),
                "sha256": hex_sha256(bytes.as_bytes()),
                "fresh_imports": 2
            },
            "execution": {
                "complete_invocations": 1,
                "target_submissions": 1,
                "exports": 1,
                "fresh_imports": 2,
                "retries": 0
            },
            "rendered_material": {
                "proof_terms": 0,
                "theorem_types": 0,
                "theorem_values": 0
            },
            "fact_status_changes": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn path(arguments: &mut impl Iterator<Item = std::ffi::OsString>) -> Result<PathBuf, String> {
    arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| USAGE.to_owned())
}

fn import_bound(
    path: &Path,
    expected_sha256: &str,
    label: &str,
) -> Result<axeyum_lean_import::CompletedImport, String> {
    let bytes = fs::read(path).map_err(|error| format!("{label} read failed: {error}"))?;
    let actual = hex_sha256(&bytes);
    if actual != expected_sha256 {
        return Err(format!(
            "{label} identity changed: expected {expected_sha256}, got {actual}"
        ));
    }
    import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("{label} import failed: {error:?}"))
}

fn require_empty(kernel: &Kernel, theorem: NameId, label: &str) -> Result<(), String> {
    let footprint = names(kernel, &kernel.axiom_footprint(theorem));
    if footprint.is_empty() {
        Ok(())
    } else {
        Err(format!("{label} reaches assumptions: {footprint:?}"))
    }
}

fn evidence(kernel: &Kernel, theorem: NameId) -> Result<Value, String> {
    if !matches!(
        kernel.environment().get(theorem),
        Some(Declaration::Theorem { .. })
    ) {
        return Err(format!("{} is not a theorem", kernel.display_name(theorem)));
    }
    Ok(json!({
        "name": kernel.display_name(theorem).to_string(),
        "declaration_sha256": canonical_declaration_sha256(kernel, theorem)?,
        "axiom_footprint": names(kernel, &kernel.axiom_footprint(theorem)),
        "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(theorem)),
    }))
}

fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    optional_name(kernel, expected)?.ok_or_else(|| format!("declaration is absent: {expected}"))
}

fn optional_name(kernel: &Kernel, expected: &str) -> Result<Option<NameId>, String> {
    let found = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match found.as_slice() {
        [name] => Ok(Some(*name)),
        [] => Ok(None),
        _ => Err(format!("declaration is ambiguous: {expected}")),
    }
}

fn nested_name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    parts
        .iter()
        .fold(kernel.anon(), |prefix, part| kernel.name_str(prefix, *part))
}

fn names(kernel: &Kernel, values: &[NameId]) -> Vec<String> {
    let mut rendered = values
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect::<Vec<_>>();
    rendered.sort();
    rendered
}

fn hex_sha256(bytes: &[u8]) -> String {
    let mut output = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut output, "{byte:02x}").expect("String writes cannot fail");
    }
    output
}
