//! Audit named theorem roots without rendering their types or values.

use std::collections::BTreeMap;
use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, canonical_declaration_sha256, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use serde_json::json;

fn main() {
    if let Err(error) = run() {
        eprintln!("theorem-root-audit: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: theorem_root_audit <export.ndjson> <theorem>...")?;
    let roots = arguments
        .map(|value| value.into_string().map_err(|_| "theorem name is not UTF-8"))
        .collect::<Result<Vec<_>, _>>()?;
    if roots.is_empty() {
        return Err("at least one theorem root is required".into());
    }

    let completed = import_ndjson(BufReader::new(File::open(&path)?), ImportLimits::default())?;
    let kernel = completed.kernel();
    let names = kernel
        .environment()
        .iter()
        .map(|(&name, declaration)| (kernel.display_name(name).to_string(), (name, declaration)))
        .collect::<BTreeMap<_, _>>();
    let mut rows = Vec::with_capacity(roots.len());
    for root in roots {
        let (rendered, &(name, declaration)) = names
            .get_key_value(&root)
            .ok_or_else(|| format!("theorem not found: {root}"))?;
        if !matches!(declaration, Declaration::Theorem { .. }) {
            return Err(format!("declaration is not a theorem: {rendered}").into());
        }
        let footprint = rendered_names(kernel, &kernel.axiom_footprint(name));
        let dependencies = rendered_names(kernel, &kernel.theorem_dependencies(name));
        rows.push(json!({
            "name": rendered,
            "declaration_sha256": canonical_declaration_sha256(kernel, name)?,
            "axiom_footprint": footprint,
            "direct_theorem_dependencies": dependencies,
        }));
    }
    let report = completed.report();
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-lean-import-theorem-root-audit",
            "report": {
                "format_version": report.format_version,
                "lean_version": report.lean_version,
                "names": report.names,
                "levels": report.levels,
                "expressions": report.expressions,
                "declaration_records": report.declaration_records,
                "admitted_declarations": report.admitted_declarations,
                "axioms": report.axioms,
            },
            "roots": rows,
        }))?
    );
    Ok(())
}

fn rendered_names(kernel: &Kernel, names: &[NameId]) -> Vec<String> {
    let mut rendered = names
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect::<Vec<_>>();
    rendered.sort();
    rendered
}
