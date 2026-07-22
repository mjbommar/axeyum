//! Import one format-3.1 `lean4export` stream and print its assurance-separated
//! inventory.

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::Kernel;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let path = std::env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .ok_or("usage: lean4export_import <export.ndjson|->")?;
    let reader: Box<dyn BufRead> = if path.as_os_str() == "-" {
        Box::new(BufReader::new(std::io::stdin()))
    } else {
        Box::new(BufReader::new(File::open(&path)?))
    };
    let mut kernel = Kernel::new();
    let report = import_ndjson(reader, &mut kernel, ImportLimits::default())?;
    let axioms = if report.axioms.is_empty() {
        "none".to_owned()
    } else {
        report.axioms.join(",")
    };
    println!(
        "LEAN4EXPORT_IMPORT|format={}|lean={}|names={}|levels={}|exprs={}|decl_records={}|admitted={}|axioms={}",
        report.format_version,
        report.lean_version,
        report.names,
        report.levels,
        report.expressions,
        report.declaration_records,
        report.admitted_declarations,
        axioms,
    );
    Ok(())
}
