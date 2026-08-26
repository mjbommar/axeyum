//! Describe one exact imported theorem candidate for footprint-aware retrieval.

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
        eprintln!("imported-candidate-descriptor: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = env::args().skip(1);
    let path = arguments
        .next()
        .ok_or_else(|| "usage: imported_candidate_descriptor <stream> <name>".to_owned())?;
    let requested = arguments
        .next()
        .ok_or_else(|| "usage: imported_candidate_descriptor <stream> <name>".to_owned())?;
    if arguments.next().is_some() {
        return Err("usage: imported_candidate_descriptor <stream> <name>".to_owned());
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
    if !matches!(declaration, Declaration::Theorem { .. }) {
        return Err(format!("{requested} is not a theorem"));
    }
    let identity = report
        .declaration_identities
        .iter()
        .find(|identity| identity.name == requested)
        .ok_or_else(|| format!("{requested} has no import identity"))?;
    let direct_theorems: Vec<_> = kernel
        .theorem_dependencies(name)
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
        "kind": "axeyum-imported-candidate-descriptor",
        "name": requested,
        "canonical_type": kernel.render_lean(declaration.ty()),
        "type_expression_sha256": canonical_expression_sha256(&kernel, declaration.ty())?,
        "alpha_type_expression_sha256": canonical_alpha_expression_sha256(&kernel, declaration.ty())?,
        "declaration_content_sha256": canonical_declaration_sha256(&kernel, name)?,
        "direct_dependency_sha256": identity.dependency_sha256,
        "direct_theorem_dependencies": direct_theorems,
        "axiom_footprint": footprint,
        "axiom_free": kernel.axiom_footprint(name).is_empty(),
    });
    println!(
        "{}",
        serde_json::to_string_pretty(&output)
            .map_err(|error| format!("cannot render descriptor: {error}"))?
    );
    Ok(())
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
