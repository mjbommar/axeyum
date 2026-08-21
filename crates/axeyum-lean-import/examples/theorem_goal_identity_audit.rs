//! Emit hash-only identity and assurance metadata for one imported theorem.
//!
//! This deliberately never renders the theorem type, value, or proof. It is a
//! narrow bridge from an already sealed capsule to operation registration when
//! the original observation omitted the canonical kernel type hash.

use std::fmt::Write as _;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, canonical_expression_sha256, import_ndjson,
};
use axeyum_lean_kernel::Declaration;
use serde_json::json;
use sha2::{Digest, Sha256};

const USAGE: &str = "usage: theorem_goal_identity_audit <stream.ndjson> <theorem>";

fn main() {
    if let Err(error) = run() {
        eprintln!("theorem-goal-identity-audit: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
    let expected_name = arguments
        .next()
        .ok_or(USAGE)?
        .into_string()
        .map_err(|_| "theorem name is not valid UTF-8".to_owned())?;
    if arguments.next().is_some() {
        return Err(USAGE.to_owned());
    }

    let bytes = fs::read(&path).map_err(|error| error.to_string())?;
    let stream_bytes = bytes.len();
    let stream_sha256 = sha256(&bytes);
    let completed = import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("stream import failed: {error:?}"))?;
    let kernel = completed.kernel();
    let matches = kernel
        .environment()
        .iter()
        .filter_map(|(&name, declaration)| {
            (kernel.display_name(name).to_string() == expected_name).then_some((name, declaration))
        })
        .collect::<Vec<_>>();
    let [(name, declaration)] = matches.as_slice() else {
        return match matches.len() {
            0 => Err(format!("requested theorem is absent: {expected_name}")),
            count => Err(format!(
                "requested theorem is ambiguous: {expected_name} ({count} matches)"
            )),
        };
    };
    let Declaration::Theorem { ty, .. } = declaration else {
        return Err(format!(
            "requested declaration is not a theorem: {expected_name}"
        ));
    };
    let mut footprint = kernel
        .axiom_footprint(*name)
        .iter()
        .map(|&dependency| kernel.display_name(dependency).to_string())
        .collect::<Vec<_>>();
    let mut dependencies = kernel
        .theorem_dependencies(*name)
        .iter()
        .map(|&dependency| kernel.display_name(dependency).to_string())
        .collect::<Vec<_>>();
    footprint.sort();
    dependencies.sort();

    let result = json!({
        "schema_version": 1,
        "kind": "axeyum-theorem-goal-identity-audit",
        "input": {
            "path": path,
            "bytes": stream_bytes,
            "sha256": stream_sha256,
        },
        "theorem": {
            "name": expected_name,
            "canonical_type_sha256": canonical_expression_sha256(kernel, *ty)?,
            "canonical_declaration_sha256": canonical_declaration_sha256(kernel, *name)?,
            "axiom_footprint": footprint,
            "direct_theorem_dependencies": dependencies,
        },
        "rendered_material": {
            "proof_terms": 0,
            "theorem_types": 0,
            "theorem_values": 0,
        },
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn sha256(bytes: &[u8]) -> String {
    let mut digest = String::with_capacity(64);
    for byte in Sha256::digest(bytes) {
        write!(&mut digest, "{byte:02x}").expect("writing a digest into a String cannot fail");
    }
    digest
}
