//! Report a non-rendering declaration path from one root to one dependency.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, checked_reused_declaration_compatibility,
    import_ndjson,
};
use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const USAGE: &str = "usage: declaration_dependency_path_audit <source.ndjson> <target.ndjson> <root> <blocked-dependency>";

fn main() {
    if let Err(error) = run() {
        eprintln!("declaration-dependency-path-audit: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let target_path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let root = text_argument(arguments.next(), USAGE)?;
    let blocked = text_argument(arguments.next(), USAGE)?;
    if arguments.next().is_some() {
        return Err(USAGE.to_owned());
    }
    let source_bytes = fs::read(&source_path).map_err(|error| error.to_string())?;
    let target_bytes = fs::read(&target_path).map_err(|error| error.to_string())?;
    let source_sha256 = sha256(&source_bytes);
    let target_sha256 = sha256(&target_bytes);
    let source = import_ndjson(Cursor::new(source_bytes), ImportLimits::default())
        .map_err(|error| format!("source import failed: {error:?}"))?;
    let target = import_ndjson(Cursor::new(target_bytes), ImportLimits::default())
        .map_err(|error| format!("target import failed: {error:?}"))?;
    let source_root = find_name(source.kernel(), &root)?;
    let blocked_name = find_name(source.kernel(), &blocked)?;
    let root_closure = source.kernel().declaration_dependency_closure(source_root);
    if !root_closure.contains(&blocked_name) {
        return Err(format!(
            "{blocked} is absent from the dependency closure of {root}"
        ));
    }
    let mut carriers = root_closure
        .iter()
        .copied()
        .filter_map(|candidate| {
            let closure = source.kernel().declaration_dependency_closure(candidate);
            (candidate == blocked_name || closure.contains(&blocked_name))
                .then_some((candidate, closure.len()))
        })
        .collect::<Vec<_>>();
    carriers.sort_by_key(|(name, closure_size)| {
        (
            *closure_size,
            source.kernel().display_name(*name).to_string(),
        )
    });
    let rows = carriers
        .iter()
        .map(|&(name, closure_size)| {
            audit_carrier(source.kernel(), target.kernel(), name, closure_size)
        })
        .collect::<Result<Vec<_>, _>>()?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-declaration-dependency-path-audit",
            "inputs": {
                "source": {"path": source_path, "sha256": source_sha256},
                "target": {"path": target_path, "sha256": target_sha256},
                "root": root,
                "blocked_dependency": blocked,
            },
            "root_closure_size": root_closure.len(),
            "carrier_count": rows.len(),
            "carriers_nearest_first": rows,
            "execution": {"source_reads": 1, "target_reads": 1, "kernel_submissions": 0, "retries": 0},
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn audit_carrier(
    source: &Kernel,
    target: &Kernel,
    name: NameId,
    closure_size: usize,
) -> Result<Value, String> {
    let rendered = source.display_name(name).to_string();
    let declaration = source
        .environment()
        .get(name)
        .ok_or_else(|| format!("source carrier disappeared: {rendered}"))?;
    let source_identity = canonical_declaration_sha256(source, name)?;
    let target_name = optional_name(target, &rendered)?;
    let target_evidence = target_name
        .map(|target_name| {
            let identity = canonical_declaration_sha256(target, target_name)?;
            let compatibility = if identity == source_identity {
                "exact-declaration".to_owned()
            } else {
                checked_reused_declaration_compatibility(source, target, &rendered).map_or_else(
                    |error| format!("declined:{error:?}"),
                    |receipt| receipt.compatibility.as_str().to_owned(),
                )
            };
            Ok::<_, String>(json!({"declaration_sha256": identity, "compatibility": compatibility}))
        })
        .transpose()?;
    let mut footprint = if matches!(declaration, Declaration::Theorem { .. }) {
        source
            .axiom_footprint(name)
            .into_iter()
            .map(|dependency| source.display_name(dependency).to_string())
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    };
    footprint.sort();
    Ok(json!({
        "name": rendered,
        "kind": declaration_kind(declaration),
        "source_declaration_sha256": source_identity,
        "source_closure_size": closure_size,
        "source_axiom_footprint": footprint,
        "target": target_evidence,
    }))
}

fn declaration_kind(declaration: &Declaration) -> &'static str {
    match declaration {
        Declaration::Axiom { .. } => "axiom",
        Declaration::Definition { .. } => "definition",
        Declaration::Theorem { .. } => "theorem",
        Declaration::Opaque { .. } => "opaque",
        Declaration::Quotient { .. } => "quotient",
        Declaration::Inductive { .. } => "inductive",
        Declaration::Constructor { .. } => "constructor",
        Declaration::Recursor { .. } => "recursor",
    }
}

fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    optional_name(kernel, expected)?.ok_or_else(|| format!("declaration is absent: {expected}"))
}

fn optional_name(kernel: &Kernel, expected: &str) -> Result<Option<NameId>, String> {
    let matches = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [name] => Ok(Some(*name)),
        [] => Ok(None),
        _ => Err(format!("declaration is ambiguous: {expected}")),
    }
}

fn text_argument(value: Option<std::ffi::OsString>, usage: &str) -> Result<String, String> {
    value
        .ok_or(usage)?
        .into_string()
        .map_err(|_| "argument is not valid UTF-8".to_owned())
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .fold(String::with_capacity(64), |mut digest, byte| {
            write!(digest, "{byte:02x}").expect("writing to a String cannot fail");
            digest
        })
}
