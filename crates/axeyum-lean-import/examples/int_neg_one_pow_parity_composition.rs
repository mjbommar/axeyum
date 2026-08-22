//! Compose clean raw-power and modulo supports into exact minus-one power parity.

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

const BRIDGE_SHA256: &str = "3b6fe9b5be8457ec5d9d02fe3dfe8c263240ddcba8bdeba4c5988c5079bf1442";
const RAW_SHA256: &str = "051c38c0001b01fa375c97aec93857e6afb173b89a852162a71939bf9683cde5";
const PARITY_SHA256: &str = "0e310823ba37adfbd9087c0da2f85ad57261228d601d9388800cf069b5b2ce82";

const BRIDGE: &str = "Axeyum.Autogenesis.intNegOnePowParityBridgeV2";
const RAW: &str = "Axeyum.Autogenesis.intNegOnePowRawV2";
const MOD_CASES: &str = "Axeyum.IntFib.modCases";
const SUCC_ONE: &str = "Axeyum.IntFib.succOne";
const SUCC_ZERO: &str = "Axeyum.IntFib.succZero";
const TARGET: &str = "Axeyum.Autogenesis.intNegOnePowParityV1";

const USAGE: &str = "usage: int_neg_one_pow_parity_composition <bridge.ndjson> <raw.ndjson> <parity.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-neg-one-pow-parity-composition: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let bridge_path = path(&mut arguments)?;
    let raw_path = path(&mut arguments)?;
    let parity_path = path(&mut arguments)?;
    let output_path = path(&mut arguments)?;
    if arguments.next().is_some() || output_path.exists() {
        return Err(USAGE.to_owned());
    }

    let bridge = import_bound(&bridge_path, BRIDGE_SHA256, "bridge")?;
    let raw = import_bound(&raw_path, RAW_SHA256, "raw power")?;
    let parity = import_bound(&parity_path, PARITY_SHA256, "parity")?;
    for (label, completed) in [
        ("bridge", &bridge),
        ("raw power", &raw),
        ("parity", &parity),
    ] {
        if !completed.report().axioms.is_empty() {
            return Err(format!("{label} stream reaches assumptions"));
        }
    }

    let mut kernel = bridge.kernel().clone();
    require_empty(&kernel, find_name(&kernel, BRIDGE)?, BRIDGE)?;
    let raw_composition = compose_checked_theorem_slice(raw.kernel(), &kernel, &[RAW])
        .map_err(|error| format!("raw-power composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        raw.kernel(),
        &kernel,
        raw_composition.kernel(),
        raw_composition.receipt(),
    )
    .map_err(|error| format!("raw-power composition replay failed: {error:?}"))?;
    let raw_receipt = raw_composition.receipt().receipt_sha256.clone();
    kernel = raw_composition.kernel().clone();

    let parity_roots = [MOD_CASES, SUCC_ONE, SUCC_ZERO];
    let parity_composition = compose_checked_theorem_slice(parity.kernel(), &kernel, &parity_roots)
        .map_err(|error| format!("parity composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        parity.kernel(),
        &kernel,
        parity_composition.kernel(),
        parity_composition.receipt(),
    )
    .map_err(|error| format!("parity composition replay failed: {error:?}"))?;
    let parity_receipt = parity_composition.receipt().receipt_sha256.clone();
    kernel = parity_composition.kernel().clone();

    let generic = find_name(&kernel, BRIDGE)?;
    let specialization_arguments = [
        find_name(&kernel, RAW)?,
        find_name(&kernel, MOD_CASES)?,
        find_name(&kernel, SUCC_ONE)?,
        find_name(&kernel, SUCC_ZERO)?,
    ];
    if optional_name(&kernel, TARGET)?.is_some() {
        return Err("exact target exists before specialization".to_owned());
    }
    let target_name = nested_name(
        &mut kernel,
        &["Axeyum", "Autogenesis", "intNegOnePowParityV1"],
    );
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
    let specialization_receipt = specialized.receipt().receipt_sha256.clone();
    kernel = specialized.kernel().clone();

    let target = find_name(&kernel, TARGET)?;
    require_empty(&kernel, target, TARGET)?;
    let target_evidence = evidence(&kernel, target)?;
    let expected_dependencies = [BRIDGE, RAW, MOD_CASES, SUCC_ONE, SUCC_ZERO];
    if names(&kernel, &kernel.theorem_dependencies(target)) != expected_dependencies {
        return Err("exact target dependency set changed".to_owned());
    }

    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
        .map_err(|error| format!("target export failed: {error}"))?;
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
            "kind": "axeyum-exact-neg-one-power-parity-composition",
            "state": "exact-target-specialized-exported-and-reimported-empty-footprint",
            "input_sha256": {
                "bridge": BRIDGE_SHA256,
                "raw_power": RAW_SHA256,
                "parity": PARITY_SHA256,
            },
            "composition_receipt_sha256": {
                "raw_power": raw_receipt,
                "parity": parity_receipt,
            },
            "specialization_receipt_sha256": specialization_receipt,
            "target": target_evidence,
            "capsule": {
                "path": output_path,
                "bytes": bytes.len(),
                "sha256": hex_sha256(bytes.as_bytes()),
                "fresh_imports": 2,
            },
            "execution": {
                "complete_invocations": 1,
                "input_stream_reads": 3,
                "composition_operations": 2,
                "composition_replays": 2,
                "specialization_operations": 1,
                "specialization_replays": 1,
                "capsule_exports": 1,
                "fresh_capsule_imports": 2,
                "retries": 0,
                "ledger_writes": 0,
            },
            "rendered_material": {
                "proof_terms": 0,
                "theorem_types": 0,
                "theorem_values": 0,
            },
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
