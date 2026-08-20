//! Import one format-3.1 `lean4export` stream and print its assurance-separated
//! inventory.

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, canonical_declaration_sha256, import_ndjson};
use axeyum_lean_kernel::Declaration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: lean4export_import <export.ndjson|-> [theorem]")?;
    let theorem = arguments
        .next()
        .map(|value| {
            value
                .into_string()
                .map_err(|_| "theorem name is not valid UTF-8")
        })
        .transpose()?;
    if arguments.next().is_some() {
        return Err("usage: lean4export_import <export.ndjson|-> [theorem]".into());
    }
    let reader: Box<dyn BufRead> = if path.as_os_str() == "-" {
        Box::new(BufReader::new(std::io::stdin()))
    } else {
        Box::new(BufReader::new(File::open(&path)?))
    };
    let completed = import_ndjson(reader, ImportLimits::default())?;
    let report = completed.report();
    let axioms = if report.axioms.is_empty() {
        "none".to_owned()
    } else {
        report.axioms.join(",")
    };
    println!(
        "LEAN4EXPORT_IMPORT|format={}|lean={}|names={}|levels={}|exprs={}|decl_records={}|admitted={}|axioms={}|identity={}|axiom_ids={}|declaration_ids={}",
        report.format_version,
        report.lean_version,
        report.names,
        report.levels,
        report.expressions,
        report.declaration_records,
        report.admitted_declarations,
        axioms,
        report.identity_version,
        report.axiom_identities.len(),
        report.declaration_identities.len(),
    );
    if let Some(theorem) = theorem {
        let kernel = completed.kernel();
        let name = kernel
            .environment()
            .iter()
            .find_map(|(&name, declaration)| {
                (kernel.display_name(name).to_string() == theorem).then_some((name, declaration))
            })
            .ok_or_else(|| format!("theorem not found: {theorem}"))?;
        if !matches!(name.1, Declaration::Theorem { .. }) {
            return Err(format!("declaration is not a theorem: {theorem}").into());
        }
        let axiom_footprint = rendered_names(kernel, &kernel.axiom_footprint(name.0));
        let theorem_dependencies = rendered_names(kernel, &kernel.theorem_dependencies(name.0));
        println!(
            "LEAN4EXPORT_THEOREM|name={theorem}|identity={}|axiom_free={}|axiom_footprint={}|direct_theorem_dependencies={}",
            canonical_declaration_sha256(kernel, name.0)?,
            axiom_footprint.is_empty(),
            joined_or_none(&axiom_footprint),
            joined_or_none(&theorem_dependencies),
        );
    }
    Ok(())
}

fn rendered_names(
    kernel: &axeyum_lean_kernel::Kernel,
    names: &[axeyum_lean_kernel::NameId],
) -> Vec<String> {
    names
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect()
}

fn joined_or_none(names: &[String]) -> String {
    if names.is_empty() {
        "none".to_owned()
    } else {
        names.join(",")
    }
}
