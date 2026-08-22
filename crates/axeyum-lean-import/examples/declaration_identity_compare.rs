//! Compare one named declaration across two imported streams without rendering it.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, checked_reused_declaration_compatibility,
    import_ndjson,
};
use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use serde_json::json;
use sha2::{Digest, Sha256};

const USAGE: &str =
    "usage: declaration_identity_compare <source.ndjson> <target.ndjson> <declaration>";

fn main() {
    if let Err(error) = run() {
        eprintln!("declaration-identity-compare: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let target_path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let declaration = text_argument(arguments.next())?;
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

    let source_name = find_name(source.kernel(), &declaration)?;
    let target_name = find_name(target.kernel(), &declaration)?;
    let source_declaration = source
        .kernel()
        .environment()
        .get(source_name)
        .ok_or_else(|| format!("source declaration disappeared: {declaration}"))?;
    let target_declaration = target
        .kernel()
        .environment()
        .get(target_name)
        .ok_or_else(|| format!("target declaration disappeared: {declaration}"))?;
    let source_identity = canonical_declaration_sha256(source.kernel(), source_name)?;
    let target_identity = canonical_declaration_sha256(target.kernel(), target_name)?;
    let checked =
        checked_reused_declaration_compatibility(source.kernel(), target.kernel(), &declaration)
            .map_err(|error| format!("checked compatibility declined: {error:?}"))?;
    let compatibility = if source_identity == target_identity {
        "exact-declaration"
    } else {
        checked.compatibility.as_str()
    };

    let result = json!({
        "schema_version": 1,
        "kind": "axeyum-declaration-identity-comparison",
        "inputs": {
            "source": {"path": source_path, "sha256": source_sha256},
            "target": {"path": target_path, "sha256": target_sha256},
            "declaration": declaration,
        },
        "source": {
            "kind": declaration_kind(source_declaration),
            "declaration_sha256": source_identity,
        },
        "target": {
            "kind": declaration_kind(target_declaration),
            "declaration_sha256": target_identity,
        },
        "compatibility": compatibility,
        "checked_reused_declaration_compatibility": checked.compatibility.as_str(),
        "execution": {
            "source_reads": 1,
            "target_reads": 1,
            "importer_runs": 2,
            "kernel_submissions": 0,
            "retries": 0,
            "ledger_writes": 0,
        },
        "rendered_material": {
            "proof_terms": 0,
            "declaration_types": 0,
            "declaration_values": 0,
        },
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(|error| error.to_string())?
    );
    Ok(())
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

fn text_argument(value: Option<std::ffi::OsString>) -> Result<String, String> {
    value
        .ok_or(USAGE)?
        .into_string()
        .map_err(|_| "declaration name is not valid UTF-8".to_owned())
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .fold(String::with_capacity(64), |mut digest, byte| {
            write!(digest, "{byte:02x}").expect("writing to a String cannot fail");
            digest
        })
}
