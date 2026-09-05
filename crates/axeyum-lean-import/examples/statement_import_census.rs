//! Census a batch of proof-isolated statement streams through
//! [`axeyum_lean_import::import_statement_ndjson`], one row per stream, and
//! report the TYPED outcome of each.
//!
//! `statement_goal_record` answers the same question for ONE stream and exits
//! nonzero on a decline, which is right for a producer and wrong for a census:
//! a census needs the distribution, so a decline here is a recorded row and the
//! run continues. Nothing is admitted that the gate refused, and no decline is
//! paraphrased -- the `Debug` form of the typed error is carried through.
//!
//! Input is a TSV manifest, one row per line:
//!
//! ```text
//! <row-key>\t<target-definition>\t<stream.ndjson>
//! ```
//!
//! Output is JSON Lines on stdout, one object per manifest row, in input order.
//! Exit status is 0 when every manifest row was READ (whatever its verdict) and
//! 2 when the manifest itself could not be used -- the census's finding is in
//! the rows, so a decline must not look like a harness failure.
//!
//! ```sh
//! cargo run --release -p axeyum-lean-import --example statement_import_census -- manifest.tsv
//! ```

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::{Path, PathBuf};

use axeyum_lean_import::{ImportLimits, StatementImportError, import_statement_ndjson};
use serde_json::json;

/// Stack for the census thread.
///
/// Same reason as `lean4export_census`: reduction and inference recurse on term
/// structure and the default 8 MB overflows on real Mathlib closures, which is
/// neither an admission nor a decline and is indistinguishable at the shell
/// from running out of memory.
const CENSUS_STACK_BYTES: usize = 512 * 1024 * 1024;

struct Row {
    key: String,
    target: String,
    path: PathBuf,
}

fn parse_manifest(path: &Path) -> Result<Vec<Row>, String> {
    let file = File::open(path).map_err(|error| format!("cannot open {path:?}: {error}"))?;
    let mut rows = Vec::new();
    for (index, line) in BufReader::new(file).lines().enumerate() {
        let line = line.map_err(|error| format!("{path:?} line {}: {error}", index + 1))?;
        if line.trim().is_empty() || line.starts_with('#') {
            continue;
        }
        let mut fields = line.split('\t');
        let (Some(key), Some(target), Some(stream), None) =
            (fields.next(), fields.next(), fields.next(), fields.next())
        else {
            return Err(format!(
                "{path:?} line {}: expected exactly 3 tab-separated fields",
                index + 1
            ));
        };
        rows.push(Row {
            key: key.to_owned(),
            target: target.to_owned(),
            path: PathBuf::from(stream),
        });
    }
    if rows.is_empty() {
        return Err(format!(
            "{path:?} names no rows; refusing to report an empty census"
        ));
    }
    Ok(rows)
}

/// The stable class name for one typed statement-import refusal.
///
/// Deliberately coarser than the error itself and always carried WITH the
/// verbatim `Debug` form: a class is for counting, the debug string is the
/// evidence, and a reader must be able to recover one from the other.
fn decline_class(error: &StatementImportError) -> &'static str {
    match error {
        StatementImportError::Import(inner) => match inner {
            axeyum_lean_import::ImportError::Io(_) => "stream-io",
            axeyum_lean_import::ImportError::LineLimit { .. }
            | axeyum_lean_import::ImportError::RecordLimit { .. } => "stream-limit",
            axeyum_lean_import::ImportError::Json { .. }
            | axeyum_lean_import::ImportError::Malformed { .. } => "stream-malformed",
            axeyum_lean_import::ImportError::Unsupported { .. } => "unsupported-construct",
            axeyum_lean_import::ImportError::Kernel { .. } => "kernel-rejected",
        },
        StatementImportError::TargetCardinality { .. } => "target-cardinality",
        StatementImportError::TargetNotDefinition { .. } => "target-not-definition",
        StatementImportError::TargetUniverseParameters { .. } => "universe-parameters",
        StatementImportError::TrustedDeclaration { .. } => "trusted-declaration-in-closure",
        StatementImportError::GoalNotProp { .. } => "goal-not-prop",
        StatementImportError::DuplicateCandidate
        | StatementImportError::CandidateIsTarget { .. }
        | StatementImportError::CandidateCardinality { .. }
        | StatementImportError::CandidateHasAxioms { .. } => "candidate-protocol",
    }
}

fn unsupported_code(error: &StatementImportError) -> Option<&'static str> {
    match error {
        StatementImportError::Import(axeyum_lean_import::ImportError::Unsupported {
            code, ..
        }) => Some(code),
        _ => None,
    }
}

fn census() -> Result<(), String> {
    let mut args = std::env::args_os().skip(1).map(PathBuf::from);
    let Some(manifest) = args.next() else {
        return Err("usage: statement_import_census <manifest.tsv>".to_owned());
    };
    if args.next().is_some() {
        return Err("usage: statement_import_census <manifest.tsv>".to_owned());
    }
    let rows = parse_manifest(&manifest)?;

    let limits = ImportLimits::default();
    for row in &rows {
        let started = std::time::Instant::now();
        let file = match File::open(&row.path) {
            Ok(file) => file,
            Err(error) => {
                println!(
                    "{}",
                    json!({
                        "row": row.key,
                        "target": row.target,
                        "outcome": "declined",
                        "class": "stream-absent",
                        "detail": error.to_string(),
                    })
                );
                continue;
            }
        };
        let result = import_statement_ndjson(BufReader::new(file), limits, &row.target);
        let elapsed_ms = started.elapsed().as_millis();
        match result {
            Ok(completed) => {
                let report = completed.report();
                println!(
                    "{}",
                    json!({
                        "row": row.key,
                        "target": row.target,
                        "outcome": "admitted",
                        "class": "admitted",
                        "declaration_records": report.declaration_records,
                        "admitted_declarations": report.admitted_declarations,
                        "names": report.names,
                        "expressions": report.expressions,
                        "elapsed_ms": elapsed_ms,
                    })
                );
            }
            Err(error) => {
                println!(
                    "{}",
                    json!({
                        "row": row.key,
                        "target": row.target,
                        "outcome": "declined",
                        "class": decline_class(&error),
                        "unsupported_code": unsupported_code(&error),
                        "detail": format!("{error:?}"),
                        "display": error.to_string(),
                        "elapsed_ms": elapsed_ms,
                    })
                );
            }
        }
    }
    Ok(())
}

fn main() {
    let worker = std::thread::Builder::new()
        .name("statement-census".to_owned())
        .stack_size(CENSUS_STACK_BYTES)
        .spawn(census)
        .expect("spawn census thread");
    match worker.join() {
        Ok(Ok(())) => {}
        Ok(Err(error)) => {
            eprintln!("{error}");
            std::process::exit(2);
        }
        Err(_) => {
            eprintln!("census thread panicked");
            std::process::exit(2);
        }
    }
}
