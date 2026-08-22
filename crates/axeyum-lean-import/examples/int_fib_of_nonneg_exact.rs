//! Compose the exact, empty-footprint nonnegative integer Fibonacci theorem.

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

const BASE_SHA256: &str = "f0e34ecb1dff747938b7f1079c307af5f4e79e7a67e3bc514feee03e4f30656d";
const RESIDUAL_SHA256: &str = "f47b2e9cfe00a1b98a365197c03bd96e346ca40f97677920e1caafc5f605d3db";
const NAT_CAST_DECL_SHA256: &str =
    "73b8742709bbb1b91780f41ff4a475b5b3f0b1c2981999c868b53fc38334bea3";
const RESIDUAL_DECL_SHA256: &str =
    "2373556137e8144c5927501b5fe2eaa4fa3ac7357cdd5d58d89b21e43e13e605";

const NAT_CAST: &str = "Int.fib_natCast";
const RESIDUAL: &str = "Axeyum.Autogenesis.intFibOfNonnegResidualV1";
const TARGET: &str = "Int.fib_of_nonneg";
const USAGE: &str =
    "usage: int_fib_of_nonneg_exact <clean-definition.ndjson> <residual.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-fib-of-nonneg-exact: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let base_path = path(&mut arguments)?;
    let residual_path = path(&mut arguments)?;
    let output_path = path(&mut arguments)?;
    if arguments.next().is_some() || output_path.exists() {
        return Err(USAGE.to_owned());
    }

    let base = import_bound(&base_path, BASE_SHA256, "clean definition")?;
    let residual = import_bound(&residual_path, RESIDUAL_SHA256, "qualified residual")?;
    for (label, completed) in [
        ("clean definition", &base),
        ("qualified residual", &residual),
    ] {
        if !completed.report().axioms.is_empty() {
            return Err(format!("{label} stream reaches assumptions"));
        }
    }
    require_bound_root(base.kernel(), NAT_CAST, NAT_CAST_DECL_SHA256)?;
    require_bound_root(residual.kernel(), RESIDUAL, RESIDUAL_DECL_SHA256)?;

    let mut kernel = base.kernel().clone();
    if optional_name(&kernel, TARGET)?.is_some() {
        return Err("exact target exists before composition".to_owned());
    }
    let composition = compose_checked_theorem_slice(residual.kernel(), &kernel, &[RESIDUAL])
        .map_err(|error| format!("residual composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        residual.kernel(),
        &kernel,
        composition.kernel(),
        composition.receipt(),
    )
    .map_err(|error| format!("residual composition replay failed: {error:?}"))?;
    kernel = composition.kernel().clone();

    let generic = find_name(&kernel, RESIDUAL)?;
    let specialization_arguments = [
        find_name(&kernel, "Int.fib")?,
        find_name(&kernel, "Nat.fib")?,
        find_name(&kernel, NAT_CAST)?,
    ];
    let target_name = nested_name(&mut kernel, &["Int", "fib_of_nonneg"]);
    let specialization =
        specialize_checked_theorem(&kernel, generic, &specialization_arguments, target_name)
            .map_err(|error| format!("exact specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &kernel,
        specialization.kernel(),
        generic,
        &specialization_arguments,
        target_name,
        specialization.receipt(),
    )
    .map_err(|error| format!("exact specialization replay failed: {error:?}"))?;
    kernel = specialization.kernel().clone();

    let target = find_name(&kernel, TARGET)?;
    require_empty(&kernel, target, TARGET)?;
    let target_evidence = evidence(&kernel, target)?;
    if names(&kernel, &kernel.theorem_dependencies(target)) != sorted(&[RESIDUAL, NAT_CAST]) {
        return Err("exact target dependency set changed".to_owned());
    }

    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
        .map_err(|error| format!("target export failed: {error}"))?;
    for pass in 1..=2 {
        let imported = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh target import {pass} failed: {error:?}"))?;
        let replay_target = find_name(imported.kernel(), TARGET)?;
        if evidence(imported.kernel(), replay_target)? != target_evidence {
            return Err(format!("fresh target import {pass} changed evidence"));
        }
    }
    fs::write(&output_path, &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-int-fib-of-nonneg-exact",
            "state": "exact-target-specialized-exported-and-twice-reimported-empty-footprint",
            "input_sha256": {"base": BASE_SHA256, "residual": RESIDUAL_SHA256},
            "composition_receipt_sha256": composition.receipt().receipt_sha256,
            "specialization_receipt_sha256": specialization.receipt().receipt_sha256,
            "target": target_evidence,
            "capsule": {"path": output_path, "bytes": bytes.len(), "sha256": hex_sha256(bytes.as_bytes()), "fresh_imports": 2},
            "execution": {"complete_invocations": 1, "input_stream_reads": 2, "composition_operations": 1, "composition_replays": 1, "specializations": 1, "specialization_replays": 1, "target_exports": 1, "fresh_imports": 2, "retries": 0, "ledger_writes": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
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

fn require_bound_root(
    kernel: &Kernel,
    rendered: &str,
    expected_sha256: &str,
) -> Result<(), String> {
    let theorem = find_name(kernel, rendered)?;
    require_empty(kernel, theorem, rendered)?;
    let actual = canonical_declaration_sha256(kernel, theorem)?;
    if actual == expected_sha256 {
        Ok(())
    } else {
        Err(format!(
            "{rendered} identity changed: expected {expected_sha256}, got {actual}"
        ))
    }
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

fn optional_name(kernel: &Kernel, expected: &str) -> Result<Option<NameId>, String> {
    match find_name(kernel, expected) {
        Ok(name) => Ok(Some(name)),
        Err(error) if error == format!("declaration is absent: {expected}") => Ok(None),
        Err(error) => Err(error),
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

fn sorted(values: &[&str]) -> Vec<String> {
    let mut rendered = values
        .iter()
        .map(|value| (*value).to_owned())
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
