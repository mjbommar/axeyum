//! Report non-rendering declaration carriers from one root to multiple blockers.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, canonical_declaration_sha256, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const USAGE: &str =
    "usage: declaration_blocker_path_batch_audit <source.ndjson> <root> <blocker>...";

fn main() {
    if let Err(error) = run() {
        eprintln!("declaration-blocker-path-batch-audit: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let root = text_argument(arguments.next())?;
    let blockers = arguments
        .map(|argument| text_argument(Some(argument)))
        .collect::<Result<Vec<_>, _>>()?;
    if blockers.is_empty() || blockers.iter().collect::<BTreeSet<_>>().len() != blockers.len() {
        return Err("blockers must be a nonempty distinct list".to_owned());
    }
    let bytes = fs::read(&path).map_err(|error| error.to_string())?;
    let input_sha256 = sha256(&bytes);
    let completed = import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("source import failed: {error:?}"))?;
    let kernel = completed.kernel();
    let root_name = find_name(kernel, &root)?;
    let root_closure = kernel.declaration_dependency_closure(root_name);
    let rows = blockers
        .iter()
        .map(|blocked| audit_blocker(kernel, &root_closure, blocked))
        .collect::<Result<Vec<_>, _>>()?;
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-declaration-blocker-path-batch-audit",
            "input": {"path": path, "sha256": input_sha256},
            "root": {
                "name": root,
                "kind": declaration_kind(kernel.environment().get(root_name).ok_or("root disappeared")?),
                "declaration_sha256": canonical_declaration_sha256(kernel, root_name)?,
                "closure_size": root_closure.len(),
            },
            "ordered_blockers": blockers,
            "blocker_rows": rows,
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn audit_blocker(kernel: &Kernel, root_closure: &[NameId], blocked: &str) -> Result<Value, String> {
    let blocked_name = find_name(kernel, blocked)?;
    if !root_closure.contains(&blocked_name) {
        return Err(format!("{blocked} is absent from the dependency closure"));
    }
    let mut carriers = root_closure
        .iter()
        .copied()
        .filter_map(|candidate| {
            let closure = kernel.declaration_dependency_closure(candidate);
            (candidate == blocked_name || closure.contains(&blocked_name))
                .then_some((candidate, closure.len()))
        })
        .collect::<Vec<_>>();
    carriers.sort_by_key(|(name, size)| (*size, kernel.display_name(*name).to_string()));
    let rows = carriers
        .into_iter()
        .map(|(name, closure_size)| {
            let declaration = kernel
                .environment()
                .get(name)
                .ok_or("carrier disappeared")?;
            Ok::<_, String>(json!({
                "name": kernel.display_name(name).to_string(),
                "kind": declaration_kind(declaration),
                "declaration_sha256": canonical_declaration_sha256(kernel, name)?,
                "closure_size": closure_size,
            }))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(json!({"name": blocked, "carrier_count": rows.len(), "carriers_nearest_first": rows}))
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
    let matches = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [name] => Ok(*name),
        [] => Err(format!("declaration is absent: {expected}")),
        _ => Err(format!("declaration is ambiguous: {expected}")),
    }
}

fn text_argument(value: Option<std::ffi::OsString>) -> Result<String, String> {
    value
        .ok_or(USAGE)?
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
