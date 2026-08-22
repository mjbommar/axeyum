//! Construct exact, empty-footprint `Nat.fib_eq_zero` from sealed inputs.

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

const HASHES: [&str; 2] = [
    "ec85c45183bec3c1fe4cbd0d015c76a5ded6dbbfa4be9b279d59870da12566a0",
    "766a4bef3cc1231dfb1f59174ebe463262900d46e6bc9bed186da18600952357",
];
const RESIDUAL: &str = "Axeyum.Autogenesis.natFibEqZeroResidualV1";
const ZERO_SUPPORT: &str = "Axeyum.Autogenesis.natFibZeroV1";
const TARGET: &str = "Nat.fib_eq_zero";
const USAGE: &str =
    "usage: nat_fib_eq_zero_exact <nat-fib-pos.ndjson> <residual.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-fib-eq-zero-exact: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let paths = (0..3)
        .map(|_| path(&mut arguments))
        .collect::<Result<Vec<_>, _>>()?;
    if arguments.next().is_some() || paths[2].exists() || paths[2].parent().is_none() {
        return Err(USAGE.to_owned());
    }
    let base = import_bound(&paths[0], HASHES[0], "Nat.fib_pos")?;
    let residual = import_bound(&paths[1], HASHES[1], "residual")?;
    if !base.report().axioms.is_empty() || !residual.report().axioms.is_empty() {
        return Err("an input stream reaches assumptions".to_owned());
    }

    let mut kernel = base.kernel().clone();
    if optional_name(&kernel, TARGET)?.is_some() {
        return Err("exact target exists before construction".to_owned());
    }
    let composed = compose_checked_theorem_slice(residual.kernel(), &kernel, &[RESIDUAL])
        .map_err(|error| format!("residual composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        residual.kernel(),
        &kernel,
        composed.kernel(),
        composed.receipt(),
    )
    .map_err(|error| format!("residual composition replay failed: {error:?}"))?;
    let composition_receipt = composed.receipt().receipt_sha256.clone();
    kernel = composed.kernel().clone();

    let generic = find_name(&kernel, RESIDUAL)?;
    let argument_names = ["Nat.fib", ZERO_SUPPORT, "Nat.fib_pos", "Nat.zero_lt_succ"]
        .iter()
        .map(|name| find_name(&kernel, name))
        .collect::<Result<Vec<_>, _>>()?;
    let target = nested_name(&mut kernel, &["Nat", "fib_eq_zero"]);
    let specialized = specialize_checked_theorem(&kernel, generic, &argument_names, target)
        .map_err(|error| format!("target specialization declined: {error:?}"))?;
    verify_checked_theorem_specialization(
        &kernel,
        specialized.kernel(),
        generic,
        &argument_names,
        target,
        specialized.receipt(),
    )
    .map_err(|error| format!("target specialization replay failed: {error:?}"))?;
    let specialization_receipt = specialized.receipt().receipt_sha256.clone();
    kernel = specialized.kernel().clone();

    let target = find_name(&kernel, TARGET)?;
    let target_evidence = evidence(&kernel, target)?;
    let expected_dependencies = [RESIDUAL, ZERO_SUPPORT, "Nat.fib_pos", "Nat.zero_lt_succ"];
    if names(&kernel, &kernel.theorem_dependencies(target)) != sorted(&expected_dependencies) {
        return Err("exact target dependency set changed".to_owned());
    }
    if !kernel.axiom_footprint(target).is_empty() {
        return Err("exact target reaches assumptions".to_owned());
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
    let output_parent = paths[2].parent().ok_or(USAGE)?;
    fs::create_dir(output_parent).map_err(|error| format!("output directory failed: {error}"))?;
    fs::write(&paths[2], &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-nat-fib-eq-zero-exact",
            "state": "exact-target-specialized-exported-and-twice-reimported-empty-footprint",
            "input_sha256": HASHES,
            "composition_receipt_sha256": composition_receipt,
            "specialization_receipt_sha256": specialization_receipt,
            "target": target_evidence,
            "capsule": {"path": paths[2], "bytes": bytes.len(), "sha256": hex_sha256(bytes.as_bytes()), "fresh_imports": 2},
            "execution": {"complete_invocations": 1, "input_stream_reads": 2, "composition_operations": 1, "composition_replays": 1, "specializations": 1, "specialization_replays": 1, "target_exports": 1, "fresh_imports": 2, "retries": 0, "fact_status_changes": 0, "ledger_writes": 0},
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
