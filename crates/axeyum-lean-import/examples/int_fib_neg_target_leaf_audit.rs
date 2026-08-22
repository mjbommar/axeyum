//! Measure official `Int.fib_neg` with the clean negative-natural theorem as a target leaf.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::{Path, PathBuf};

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, compose_checked_theorem_slice_with_target_leaves,
    import_ndjson, verify_checked_theorem_composition,
};
use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const SOURCE_SHA256: &str = "7df7f5dce9c7159f9c468b6f47f13be3e589fb2c1559af554ce73cc48b18730e";
const TARGET_SHA256: &str = "6c803eff520a62d6925db5ed30f78714d9923281becfd78239cc28278bc9159f";
const ROOT: &str = "Int.fib_neg";
const LEAF: &str = "Int.fib_neg_natCast";
const USAGE: &str =
    "usage: int_fib_neg_target_leaf_audit <official-root.ndjson> <clean-leaf.ndjson>";

fn main() {
    if let Err(error) = run() {
        eprintln!("int-fib-neg-target-leaf-audit: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = path(&mut arguments)?;
    let target_path = path(&mut arguments)?;
    if arguments.next().is_some() {
        return Err(USAGE.to_owned());
    }
    let source = import_bound(&source_path, SOURCE_SHA256, "official root")?;
    let target = import_bound(&target_path, TARGET_SHA256, "clean target leaf")?;
    if !target.report().axioms.is_empty() {
        return Err("clean target-leaf stream reaches assumptions".to_owned());
    }
    let source_len = source.kernel().environment().len();
    let target_len = target.kernel().environment().len();

    let outcome = match compose_checked_theorem_slice_with_target_leaves(
        source.kernel(),
        target.kernel(),
        &[ROOT],
        &[LEAF],
    ) {
        Ok(completed) => {
            verify_checked_theorem_composition(
                source.kernel(),
                target.kernel(),
                completed.kernel(),
                completed.receipt(),
            )
            .map_err(|error| format!("composition replay failed: {error:?}"))?;
            let root = find_name(completed.kernel(), ROOT)?;
            json!({
                "class": "accepted-private-clone",
                "receipt_sha256": completed.receipt().receipt_sha256,
                "root": evidence(completed.kernel(), root)?,
                "added_theorem_count": completed.receipt().added_theorems.len(),
                "reused_target_leaf": LEAF
            })
        }
        Err(error) => json!({
            "class": "declined-without-publication",
            "error": format!("{error:?}"),
            "reused_target_leaf": LEAF
        }),
    };
    if source.kernel().environment().len() != source_len
        || target.kernel().environment().len() != target_len
    {
        return Err("audit changed an input kernel".to_owned());
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-int-fib-neg-target-leaf-audit",
            "input_sha256": {"official_root": SOURCE_SHA256, "clean_leaf": TARGET_SHA256},
            "outcome": outcome,
            "execution": {"complete_invocations": 1, "source_stream_reads": 1, "target_stream_reads": 1, "composition_attempts": 1, "exports": 0, "exact_target_submissions": 0, "fact_status_changes": 0, "ledger_writes": 0, "retries": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0}
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
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

fn path(arguments: &mut impl Iterator<Item = std::ffi::OsString>) -> Result<PathBuf, String> {
    arguments
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| USAGE.to_owned())
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
        "direct_theorem_dependencies": names(kernel, &kernel.theorem_dependencies(theorem))
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
