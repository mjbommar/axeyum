//! One-shot probe: import a `lean4export` NDJSON stream and print
//! `Kernel::render_lean` of one declaration's type plus its
//! `Kernel::axiom_footprint`, in the exact shape `imported_fact_evidence.rs`
//! pins for `imported-kernel-lean` facts.
//!
//! ```sh
//! cargo run --release -p axeyum-lean-import --example row4_import_probe -- \
//!   <stream.ndjson> <declaration>
//! ```

use std::fs;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::Declaration;
use sha2::{Digest, Sha256};

fn hex(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        let _ = write!(out, "{b:02x}");
    }
    out
}

fn main() {
    if let Err(error) = run() {
        eprintln!("row4-import-probe: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let path = arguments
        .next()
        .map(PathBuf::from)
        .ok_or("usage: row4_import_probe <stream.ndjson> <declaration>")?;
    let declaration_name = arguments
        .next()
        .and_then(|argument| argument.into_string().ok())
        .ok_or("usage: row4_import_probe <stream.ndjson> <declaration>")?;

    let bytes = fs::read(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    let digest = hex(&Sha256::digest(&bytes));

    let completed = import_ndjson(bytes.as_slice(), ImportLimits::default())
        .map_err(|e| format!("{}: import failed: {e}", path.display()))?;
    let (kernel, report) = completed.into_parts();

    let name = kernel
        .environment()
        .iter()
        .map(|(_, d)| d.name())
        .find(|&n| kernel.display_name(n).to_string() == declaration_name)
        .ok_or_else(|| format!("{}: {declaration_name} not admitted", path.display()))?;
    let declaration = kernel.environment().get(name).expect("just found");
    let ty = match declaration {
        Declaration::Theorem { ty, .. } => *ty,
        other => return Err(format!("{declaration_name} is {other:?}, not a theorem")),
    };
    let rendered = kernel.render_lean(ty);
    let footprint: Vec<String> = kernel
        .axiom_footprint(name)
        .into_iter()
        .map(|n| kernel.display_name(n).to_string())
        .collect();

    println!(
        "AXEYUM-IMPORT-PROBE|decl={}|sha256={}|lean={}|githash={}|exporter={}|admitted={}|declared_records={}|lean_axioms={}",
        declaration_name,
        digest,
        report.lean_version,
        report.lean_githash,
        report.exporter_version,
        report.admitted_declarations,
        report.declaration_records,
        if footprint.is_empty() {
            "none".to_owned()
        } else {
            footprint.join(",")
        },
    );
    println!("TYPE|{rendered}");
    Ok(())
}
