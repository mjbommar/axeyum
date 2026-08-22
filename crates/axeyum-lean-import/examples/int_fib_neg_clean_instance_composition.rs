//! Rebuild exact `Int.fib_neg` over clean natCast and integer-evenness support.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice,
    compose_checked_theorem_slice_with_target_leaves, import_ndjson,
    verify_checked_theorem_composition, verify_checked_theorem_composition_with_target_leaves,
};
use axeyum_lean_kernel::{Declaration, Kernel, Lean4ExportMetadata, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const OFFICIAL_SHA256: &str = "7df7f5dce9c7159f9c468b6f47f13be3e589fb2c1559af554ce73cc48b18730e";
const CLEAN_NATCAST_SHA256: &str =
    "6c803eff520a62d6925db5ed30f78714d9923281becfd78239cc28278bc9159f";
const CLEAN_DECISION_SHA256: &str =
    "29053dba3b90cecf5a70ba347ea7dba81a19990f715e69d5fc0a1c60cb9a6c07";

const DECISION_DECL_SHA256: &str =
    "c01ed8edfc717e6cc0119a5c824cf94ad6fd1fb0b322487a28036b41b0713c61";
const NATCAST_DECL_SHA256: &str =
    "db090b11cf74c91607d5d0aabe43d364f9260c41f7de6bcd460cc59907deb087";
const EVEN_IFF_DECL_SHA256: &str =
    "6ec4a6f5577bc3602d13ff02907469045f0987323f6f9f84f8c4b7b23c243c13";

const TARGET: &str = "Int.fib_neg";
const NATCAST: &str = "Int.fib_neg_natCast";
const EVEN_IFF: &str = "Int.even_iff";
const DECISION: &str = "Int.instDecidablePredEven";
const TARGET_LEAVES: [&str; 2] = [EVEN_IFF, NATCAST];

const USAGE: &str = "usage: int_fib_neg_clean_instance_composition \
    <official-root.ndjson> <clean-natcast.ndjson> <clean-decision.ndjson> <output.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-fib-neg-clean-instance-composition: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let official_path = path(&mut arguments)?;
    let clean_natcast_path = path(&mut arguments)?;
    let clean_decision_path = path(&mut arguments)?;
    let output_path = path(&mut arguments)?;
    if arguments.next().is_some() || output_path.exists() {
        return Err(USAGE.to_owned());
    }

    let official = import_bound(&official_path, OFFICIAL_SHA256, "official target")?;
    let clean_natcast = import_bound(&clean_natcast_path, CLEAN_NATCAST_SHA256, "clean natCast")?;
    let clean_decision = import_bound(
        &clean_decision_path,
        CLEAN_DECISION_SHA256,
        "clean decision",
    )?;
    for (label, completed) in [
        ("clean natCast", &clean_natcast),
        ("clean decision", &clean_decision),
    ] {
        if !completed.report().axioms.is_empty() {
            return Err(format!("{label} stream reaches assumptions"));
        }
    }

    let official_target = find_name(official.kernel(), TARGET)?;
    let official_target_sha256 = canonical_declaration_sha256(official.kernel(), official_target)?;
    require_clean_theorem(clean_natcast.kernel(), NATCAST, NATCAST_DECL_SHA256)?;
    require_clean_decision(clean_decision.kernel())?;

    let support =
        compose_checked_theorem_slice(clean_natcast.kernel(), clean_decision.kernel(), &[NATCAST])
            .map_err(|error| format!("natCast support composition declined: {error:?}"))?;
    verify_checked_theorem_composition(
        clean_natcast.kernel(),
        clean_decision.kernel(),
        support.kernel(),
        support.receipt(),
    )
    .map_err(|error| format!("natCast support composition replay failed: {error:?}"))?;
    let support_receipt_sha256 = support.receipt().receipt_sha256.clone();
    require_clean_decision(support.kernel())?;
    require_clean_theorem(support.kernel(), NATCAST, NATCAST_DECL_SHA256)?;

    if optional_name(support.kernel(), TARGET)?.is_some() {
        return Err("exact Int.fib_neg exists before target composition".to_owned());
    }
    let target_composition = compose_checked_theorem_slice_with_target_leaves(
        official.kernel(),
        support.kernel(),
        &[TARGET],
        &TARGET_LEAVES,
    )
    .map_err(|error| format!("target-leaf composition declined: {error:?}"))?;
    verify_checked_theorem_composition_with_target_leaves(
        official.kernel(),
        support.kernel(),
        target_composition.kernel(),
        target_composition.receipt(),
    )
    .map_err(|error| format!("target-leaf composition replay failed: {error:?}"))?;
    if target_composition.receipt().target_theorem_leaves != TARGET_LEAVES {
        return Err("target-leaf receipt changed".to_owned());
    }
    let target_receipt_sha256 = target_composition.receipt().receipt_sha256.clone();
    let kernel = target_composition.kernel();

    require_clean_decision(kernel)?;
    require_clean_theorem(kernel, NATCAST, NATCAST_DECL_SHA256)?;
    require_clean_theorem(kernel, EVEN_IFF, EVEN_IFF_DECL_SHA256)?;
    let target = find_name(kernel, TARGET)?;
    require_empty_theorem(kernel, target, TARGET)?;
    let target_sha256 = canonical_declaration_sha256(kernel, target)?;
    if target_sha256 != official_target_sha256 {
        return Err(format!(
            "exact target identity changed: expected {official_target_sha256}, got {target_sha256}"
        ));
    }
    let evidence = complete_evidence(kernel)?;

    let bytes = kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
        .map_err(|error| format!("exact target export failed: {error}"))?;
    for pass in 1..=2 {
        let replay = import_ndjson(Cursor::new(bytes.as_bytes()), ImportLimits::default())
            .map_err(|error| format!("fresh target import {pass} failed: {error:?}"))?;
        if complete_evidence(replay.kernel())? != evidence {
            return Err(format!("fresh target import {pass} changed evidence"));
        }
    }
    fs::write(&output_path, &bytes).map_err(|error| format!("target write failed: {error}"))?;

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-exact-clean-int-fib-neg-composition",
            "state": "exact-target-composed-over-clean-instance-exported-and-reimported",
            "input_sha256": {
                "official_target": OFFICIAL_SHA256,
                "clean_natcast": CLEAN_NATCAST_SHA256,
                "clean_decision": CLEAN_DECISION_SHA256,
            },
            "support_composition_receipt_sha256": support_receipt_sha256,
            "target_leaf_composition_receipt_sha256": target_receipt_sha256,
            "target_leaves": TARGET_LEAVES,
            "evidence": evidence,
            "capsule": {
                "path": output_path,
                "bytes": bytes.len(),
                "sha256": hex_sha256(bytes.as_bytes()),
                "fresh_imports": 2,
            },
            "execution": {
                "complete_invocations": 1,
                "input_stream_reads": 3,
                "support_compositions": 1,
                "support_replays": 1,
                "target_leaf_compositions": 1,
                "target_leaf_replays": 1,
                "target_submissions": 1,
                "capsule_exports": 1,
                "fresh_target_imports": 2,
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

fn complete_evidence(kernel: &Kernel) -> Result<Value, String> {
    require_clean_decision(kernel)?;
    let target = find_name(kernel, TARGET)?;
    require_empty_theorem(kernel, target, TARGET)?;
    Ok(json!({
        "target": theorem_evidence(kernel, target)?,
        "decision": declaration_evidence(kernel, find_name(kernel, DECISION)?)?,
        "clean_natcast": theorem_evidence(kernel, find_name(kernel, NATCAST)?)?,
        "clean_even_iff": theorem_evidence(kernel, find_name(kernel, EVEN_IFF)?)?,
    }))
}

fn require_clean_decision(kernel: &Kernel) -> Result<(), String> {
    let decision = find_name(kernel, DECISION)?;
    if !matches!(
        kernel.environment().get(decision),
        Some(Declaration::Definition { .. })
    ) {
        return Err("Int.instDecidablePredEven is not a definition".to_owned());
    }
    let actual = canonical_declaration_sha256(kernel, decision)?;
    if actual == DECISION_DECL_SHA256 {
        Ok(())
    } else {
        Err(format!(
            "clean decision identity changed: expected {DECISION_DECL_SHA256}, got {actual}"
        ))
    }
}

fn require_clean_theorem(kernel: &Kernel, name: &str, expected_sha256: &str) -> Result<(), String> {
    let theorem = find_name(kernel, name)?;
    require_empty_theorem(kernel, theorem, name)?;
    let actual = canonical_declaration_sha256(kernel, theorem)?;
    if actual == expected_sha256 {
        Ok(())
    } else {
        Err(format!(
            "{name} identity changed: expected {expected_sha256}, got {actual}"
        ))
    }
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
