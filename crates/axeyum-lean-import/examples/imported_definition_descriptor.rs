//! Describe one exact imported transparent definition for semantic transport.

use std::env;
use std::fs;
use std::io::Cursor;

use axeyum_lean_import::{
    ImportLimits, canonical_alpha_expression_sha256, canonical_declaration_sha256,
    canonical_expression_sha256, import_ndjson,
};
use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use serde_json::json;

fn main() {
    if let Err(error) = run() {
        eprintln!("imported-definition-descriptor: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = env::args().skip(1);
    let path = arguments.next().ok_or_else(usage)?;
    let requested = arguments.next().ok_or_else(usage)?;
    if arguments.next().is_some() {
        return Err(usage());
    }
    let bytes = fs::read(&path).map_err(|error| format!("cannot read {path}: {error}"))?;
    let completed = import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("cannot import {path}: {error:?}"))?;
    let (kernel, report) = completed.into_parts();
    let name = find_name(&kernel, &requested)?;
    let declaration = kernel
        .environment()
        .get(name)
        .ok_or_else(|| format!("{requested} disappeared"))?;
    let (ty, value, reducibility) = match declaration {
        Declaration::Definition {
            ty, value, hint, ..
        } => (*ty, *value, format!("{hint:?}")),
        _ => return Err(format!("{requested} is not a definition")),
    };
    let identity = report
        .declaration_identities
        .iter()
        .find(|identity| identity.name == requested)
        .ok_or_else(|| format!("{requested} has no import identity"))?;
    let dependencies: Vec<_> = kernel
        .declaration_dependencies(name)
        .into_iter()
        .map(|dependency| kernel.display_name(dependency).to_string())
        .collect();
    let footprint: Vec<_> = kernel
        .axiom_footprint(name)
        .into_iter()
        .map(|dependency| kernel.display_name(dependency).to_string())
        .collect();
    let output = json!({
        "schema_version": 1,
        "kind": "axeyum-imported-definition-descriptor",
        "name": requested,
        "canonical_type": kernel.render_lean(ty),
        "canonical_value": kernel.render_lean(value),
        "type_expression_sha256": canonical_expression_sha256(&kernel, ty)?,
        "alpha_type_expression_sha256": canonical_alpha_expression_sha256(&kernel, ty)?,
        "value_expression_sha256": canonical_expression_sha256(&kernel, value)?,
        "alpha_value_expression_sha256": canonical_alpha_expression_sha256(&kernel, value)?,
        "declaration_content_sha256": canonical_declaration_sha256(&kernel, name)?,
        "direct_dependency_sha256": identity.dependency_sha256,
        "direct_declaration_dependencies": dependencies,
        "reducibility": reducibility,
        "axiom_footprint": footprint,
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&output)
            .map_err(|error| format!("cannot render descriptor: {error}"))?
    );
    Ok(())
}

fn usage() -> String {
    "usage: imported_definition_descriptor <stream> <name>".to_owned()
}

fn find_name(kernel: &Kernel, requested: &str) -> Result<NameId, String> {
    let found: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(name, _)| {
            (kernel.display_name(*name).to_string() == requested).then_some(*name)
        })
        .collect();
    match found.as_slice() {
        [name] => Ok(*name),
        [] => Err(format!("{requested} is absent")),
        _ => Err(format!("{requested} is ambiguous")),
    }
}
