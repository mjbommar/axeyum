//! Rebuild the exact integer-even decision instance over clean `Int.even_iff`.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice_with_target_leaves,
    import_ndjson, verify_checked_theorem_composition_with_target_leaves,
};
use axeyum_lean_kernel::{Declaration, Kernel, Lean4ExportMetadata, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const CARRIER_SHA256: &str = "cbf4e87694ecfc5422cbdcf2ee219db37905168d414a8a479236604fb02315f7";
const CLEAN_IFF_SHA256: &str = "faa3a54842b1e4883e85fc153b8be8059257ff07ce137bc3c618352b13641d51";
const INSTANCE_DECL_SHA256: &str =
    "c01ed8edfc717e6cc0119a5c824cf94ad6fd1fb0b322487a28036b41b0713c61";
const CLEAN_IFF_DECL_SHA256: &str =
    "6ec4a6f5577bc3602d13ff02907469045f0987323f6f9f84f8c4b7b23c243c13";

const CARRIER: &str = "Axeyum.Autogenesis.intEvenDecisionCarrierV1";
const INSTANCE: &str = "Int.instDecidablePredEven";
const HELPER: &str = "Int.instDecidablePredEven._proof_1";
const EVEN_IFF: &str = "Int.even_iff";

const USAGE: &str = "usage: int_even_decision_clean_composition <carrier.ndjson> <clean-iff.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-even-decision-clean-composition: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let carrier_path = path(&mut arguments)?;
    let clean_iff_path = path(&mut arguments)?;
    let output_path = path(&mut arguments)?;
    if arguments.next().is_some() || output_path.exists() {
        return Err(USAGE.to_owned());
    }

    let carrier = import_bound(&carrier_path, CARRIER_SHA256, "carrier")?;
    let clean_iff = import_bound(&clean_iff_path, CLEAN_IFF_SHA256, "clean Iff")?;
    if !clean_iff.report().axioms.is_empty() {
        return Err("clean Iff stream reaches assumptions".to_owned());
    }
    let clean_iff_name = find_name(clean_iff.kernel(), EVEN_IFF)?;
    require_theorem_empty(clean_iff.kernel(), clean_iff_name, EVEN_IFF)?;
    if canonical_declaration_sha256(clean_iff.kernel(), clean_iff_name)? != CLEAN_IFF_DECL_SHA256 {
        return Err("clean Int.even_iff identity changed".to_owned());
    }

    let composed = compose_checked_theorem_slice_with_target_leaves(
        carrier.kernel(),
        clean_iff.kernel(),
        &[CARRIER],
        &[EVEN_IFF],
    )
    .map_err(|error| format!("target-leaf composition declined: {error:?}"))?;
    verify_checked_theorem_composition_with_target_leaves(
        carrier.kernel(),
        clean_iff.kernel(),
        composed.kernel(),
        composed.receipt(),
    )
    .map_err(|error| format!("target-leaf composition replay failed: {error:?}"))?;
    let receipt_sha256 = composed.receipt().receipt_sha256.clone();
    if composed.receipt().target_theorem_leaves != [EVEN_IFF] {
        return Err("target-leaf receipt changed".to_owned());
    }
    let kernel = composed.kernel();
    let evidence = decision_evidence(kernel)?;

    let carrier_name = find_name(kernel, CARRIER)?;
    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[carrier_name])
        .map_err(|error| format!("clean decision export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh decision import {pass} failed: {error:?}"))?;
        if decision_evidence(replay.kernel())? != evidence {
            return Err(format!("fresh decision import {pass} changed evidence"));
        }
    }
    fs::write(&output_path, &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-clean-int-even-decision-composition",
            "state": "exact-instance-reconstructed-with-clean-target-leaf-and-reimported",
            "input_sha256": {
                "carrier": CARRIER_SHA256,
                "clean_even_iff": CLEAN_IFF_SHA256,
            },
            "target_leaf_composition_receipt_sha256": receipt_sha256,
            "evidence": evidence,
            "capsule": {
                "path": output_path,
                "bytes": bytes.len(),
                "sha256": hex_sha256(bytes.as_bytes()),
                "fresh_imports": 2,
            },
            "execution": {
                "complete_invocations": 1,
                "input_stream_reads": 2,
                "target_leaf_compositions": 1,
                "target_leaf_replays": 1,
                "capsule_exports": 1,
                "fresh_imports": 2,
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

fn decision_evidence(kernel: &Kernel) -> Result<Value, String> {
    let instance = find_name(kernel, INSTANCE)?;
    if !matches!(
        kernel.environment().get(instance),
        Some(Declaration::Definition { .. })
    ) {
        return Err("Int.instDecidablePredEven is not a definition".to_owned());
    }
    let instance_sha256 = canonical_declaration_sha256(kernel, instance)?;
    if instance_sha256 != INSTANCE_DECL_SHA256 {
        return Err(format!(
            "decision instance identity changed: expected {INSTANCE_DECL_SHA256}, got {instance_sha256}"
        ));
    }
    let even_iff = find_name(kernel, EVEN_IFF)?;
    let even_iff_sha256 = canonical_declaration_sha256(kernel, even_iff)?;
    if even_iff_sha256 != CLEAN_IFF_DECL_SHA256 {
        return Err("composed kernel does not retain clean Int.even_iff".to_owned());
    }
    let helper = find_name(kernel, HELPER)?;
    let carrier = find_name(kernel, CARRIER)?;
    require_theorem_empty(kernel, helper, HELPER)?;
    require_theorem_empty(kernel, carrier, CARRIER)?;
    Ok(json!({
        "instance": declaration_evidence(kernel, instance)?,
        "helper": theorem_evidence(kernel, helper)?,
        "carrier": theorem_evidence(kernel, carrier)?,
        "clean_even_iff": theorem_evidence(kernel, even_iff)?,
    }))
}

fn declaration_evidence(kernel: &Kernel, declaration: NameId) -> Result<Value, String> {
    Ok(json!({
        "name": kernel.display_name(declaration).to_string(),
        "kind": match kernel.environment().get(declaration) {
            Some(Declaration::Definition { .. }) => "definition",
            _ => "unexpected",
        },
        "declaration_sha256": canonical_declaration_sha256(kernel, declaration)?,
    }))
}

fn theorem_evidence(kernel: &Kernel, theorem: NameId) -> Result<Value, String> {
    Ok(json!({
        "name": kernel.display_name(theorem).to_string(),
        "declaration_sha256": canonical_declaration_sha256(kernel, theorem)?,
        "axiom_footprint": names(kernel, &kernel.axiom_footprint(theorem)),
        "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(theorem)),
    }))
}

fn require_theorem_empty(kernel: &Kernel, theorem: NameId, label: &str) -> Result<(), String> {
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
