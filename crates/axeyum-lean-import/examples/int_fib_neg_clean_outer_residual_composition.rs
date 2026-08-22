//! Qualify the parameterized `Int.fib_neg` constructor residual in the clean kernel.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice, import_ndjson,
    verify_checked_theorem_composition,
};
use axeyum_lean_kernel::{Declaration, Kernel, Lean4ExportMetadata, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const RESIDUAL_SHA256: &str = "ba8493ff4fa32e0c8ec1a085d797dc1fe39713e5f98295cebdb1eaaa54cde707";
const CLEAN_NATCAST_SHA256: &str =
    "6c803eff520a62d6925db5ed30f78714d9923281becfd78239cc28278bc9159f";
const CLEAN_DECISION_SHA256: &str =
    "29053dba3b90cecf5a70ba347ea7dba81a19990f715e69d5fc0a1c60cb9a6c07";

const RESIDUAL: &str = "Axeyum.Autogenesis.intFibNegOuterResidualV2";
const NATCAST: &str = "Int.fib_neg_natCast";
const USAGE: &str = "usage: int_fib_neg_clean_outer_residual_composition \
    <residual.ndjson> <clean-natcast.ndjson> <clean-decision.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-fib-neg-clean-outer-residual-composition: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let residual_path = path(&mut arguments)?;
    let natcast_path = path(&mut arguments)?;
    let decision_path = path(&mut arguments)?;
    let output_path = path(&mut arguments)?;
    if arguments.next().is_some() || output_path.exists() {
        return Err(USAGE.to_owned());
    }

    let residual = import_bound(&residual_path, RESIDUAL_SHA256, "outer residual")?;
    let natcast = import_bound(&natcast_path, CLEAN_NATCAST_SHA256, "clean natCast")?;
    let decision = import_bound(&decision_path, CLEAN_DECISION_SHA256, "clean decision")?;
    for (label, completed) in [("clean natCast", &natcast), ("clean decision", &decision)] {
        if !completed.report().axioms.is_empty() {
            return Err(format!("{label} stream reaches assumptions"));
        }
    }

    let support = compose_checked_theorem_slice(natcast.kernel(), decision.kernel(), &[NATCAST])
        .map_err(|error| format!("natCast support composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        natcast.kernel(),
        decision.kernel(),
        support.kernel(),
        support.receipt(),
    )
    .map_err(|error| format!("natCast support composition replay failed: {error:?}"))?;
    let support_receipt_sha256 = support.receipt().receipt_sha256.clone();

    let completed = compose_checked_theorem_slice(residual.kernel(), support.kernel(), &[RESIDUAL])
        .map_err(|error| format!("clean residual composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        residual.kernel(),
        support.kernel(),
        completed.kernel(),
        completed.receipt(),
    )
    .map_err(|error| format!("clean residual composition replay failed: {error:?}"))?;
    let residual_receipt_sha256 = completed.receipt().receipt_sha256.clone();
    let kernel = completed.kernel();
    let root = find_name(kernel, RESIDUAL)?;
    require_empty_theorem(kernel, root, RESIDUAL)?;
    let evidence = theorem_evidence(kernel, root)?;

    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[root])
        .map_err(|error| format!("clean residual export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh residual import {pass} failed: {error:?}"))?;
        let replay_root = find_name(replay.kernel(), RESIDUAL)?;
        if theorem_evidence(replay.kernel(), replay_root)? != evidence {
            return Err(format!("fresh residual import {pass} changed evidence"));
        }
    }
    fs::write(&output_path, &bytes).map_err(|error| format!("residual write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-clean-int-fib-neg-outer-residual-composition",
            "state": "parameterized-constructor-residual-composed-exported-and-reimported-empty-footprint",
            "input_sha256": {
                "outer_residual": RESIDUAL_SHA256,
                "clean_natcast": CLEAN_NATCAST_SHA256,
                "clean_decision": CLEAN_DECISION_SHA256,
            },
            "support_composition_receipt_sha256": support_receipt_sha256,
            "residual_composition_receipt_sha256": residual_receipt_sha256,
            "root": evidence,
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
                "support_submissions": 1,
                "capsule_exports": 1,
                "fresh_imports": 2,
                "exact_target_submissions": 0,
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

fn require_empty_theorem(kernel: &Kernel, theorem: NameId, label: &str) -> Result<(), String> {
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
