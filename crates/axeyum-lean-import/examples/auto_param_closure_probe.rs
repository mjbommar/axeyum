//! Diagnostic for one checked normalized root closure.

use std::fs::File;
use std::io::BufReader;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::{Declaration, Lean4ExportMetadata};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let path = std::env::args().nth(1).ok_or("missing stream")?;
    let root = std::env::args().nth(2).ok_or("missing root")?;
    let completed = import_ndjson(BufReader::new(File::open(path)?), ImportLimits::default())?;
    let (mut kernel, _) = completed.into_parts();
    let name = kernel
        .environment()
        .iter()
        .find_map(|(&name, _)| (kernel.display_name(name).to_string() == root).then_some(name))
        .ok_or("root absent")?;
    let (closure, report) = kernel.root_declaration_closure_checked_auto_param_binders(&[name])?;
    println!("report={report:?}");
    for dependency in closure {
        let declaration = kernel
            .environment()
            .get(dependency)
            .expect("closure member");
        let kind = match declaration {
            Declaration::Axiom { .. } => Some("axiom"),
            Declaration::Theorem { .. } => Some("theorem"),
            Declaration::Opaque { .. } => Some("opaque"),
            Declaration::Quotient { .. } => Some("quotient"),
            _ => None,
        };
        if let Some(kind) = kind {
            println!("trusted={} kind={kind}", kernel.display_name(dependency));
        }
    }
    if let Some(output) = std::env::args().nth(3) {
        let (stream, _) = kernel.render_lean4export_ndjson_roots_checked_auto_param_binders(
            &Lean4ExportMetadata::axeyum("4.30.0"),
            &[name],
        )?;
        std::fs::write(output, stream)?;
    }
    Ok(())
}
