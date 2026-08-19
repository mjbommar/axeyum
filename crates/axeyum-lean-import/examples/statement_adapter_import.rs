//! Import one proof-isolated `definition : Prop := statement` stream and print
//! its checked goal identity.

use std::fmt::Write;
use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, import_statement_ndjson};
use sha2::{Digest, Sha256};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut args = std::env::args_os().skip(1);
    let path = args
        .next()
        .map(PathBuf::from)
        .ok_or("usage: statement_adapter_import <export.ndjson> <target-definition>")?;
    let target = args
        .next()
        .ok_or("usage: statement_adapter_import <export.ndjson> <target-definition>")?
        .into_string()
        .map_err(|_| "target definition must be UTF-8")?;
    if args.next().is_some() {
        return Err("usage: statement_adapter_import <export.ndjson> <target-definition>".into());
    }
    let completed = import_statement_ndjson(
        BufReader::new(File::open(path)?),
        ImportLimits::default(),
        &target,
    )?;
    let report = completed.report();
    let identity = report
        .declaration_identities
        .iter()
        .find(|identity| identity.name == target)
        .ok_or("checked target identity is absent")?;
    let rendered = completed.kernel().render_lean(completed.goal());
    let goal_sha256 = Sha256::digest(rendered.as_bytes()).iter().fold(
        String::with_capacity(64),
        |mut output, byte| {
            write!(output, "{byte:02x}").expect("writing to a String cannot fail");
            output
        },
    );
    println!(
        "STATEMENT_ADAPTER_IMPORT|target={target}|goal_sha256={goal_sha256}|target_content_sha256={}|dependencies={}|declarations={}|axioms={}|lean={}",
        identity.content_sha256,
        identity.dependencies.len(),
        report.declaration_identities.len(),
        report.axiom_identities.len(),
        report.lean_version,
    );
    println!("GOAL|{rendered}");
    Ok(())
}
