//! Import one proof-isolated statement stream and print the ledger-shaped
//! goal record ADR-0604 SS2 asks for, as `artifacts/facts/`-schema JSON.
//!
//! This example is a DEMONSTRATION boundary, not a producer: it prints to
//! stdout and never writes under `artifacts/facts/`. It exists to show that
//! [`axeyum_lean_import::build_statement_goal_record`]'s output round-trips
//! into the fact schema's `formal`/`provenance` shape without inventing any
//! field the crate did not itself compute from the checked kernel.
//!
//! Usage:
//!   statement_goal_record <export.ndjson> <target-definition> \
//!     [--mathlib-commit=<sha>] [--lean4export-commit=<sha>] \
//!     [--fragment=<name>] [--fact-id=<F:id>] [--title=<title>]
//!
//! On success, prints one JSON object shaped like an `artifacts/facts/`
//! entry (`epistemic_status: "open"`, empty `evidence`) to stdout. On a
//! statement-import refusal (e.g. `TrustedDeclaration`), prints a JSON object
//! naming the exact typed refusal instead and exits nonzero -- a decline is
//! reported honestly, never forced into a fact shape it did not earn.

use std::fs::File;
use std::io::BufReader;
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, build_statement_goal_record, import_statement_ndjson};
use serde_json::json;

struct Args {
    path: PathBuf,
    target: String,
    mathlib_commit: Option<String>,
    lean4export_commit: Option<String>,
    fragment: String,
    fact_id: String,
    title: String,
}

fn usage() -> String {
    "usage: statement_goal_record <export.ndjson> <target-definition> \
     [--mathlib-commit=<sha>] [--lean4export-commit=<sha>] [--fragment=<name>] \
     [--fact-id=<F:id>] [--title=<title>]"
        .to_owned()
}

fn parse_args() -> Result<Args, String> {
    let mut positional = Vec::new();
    let mut mathlib_commit = None;
    let mut lean4export_commit = None;
    let mut fragment = "Nat".to_owned();
    let mut fact_id = "F:statement-only-import-worked-example".to_owned();
    let mut title = "Statement-only imported goal (worked example)".to_owned();
    for arg in std::env::args().skip(1) {
        if let Some(value) = arg.strip_prefix("--mathlib-commit=") {
            mathlib_commit = Some(value.to_owned());
        } else if let Some(value) = arg.strip_prefix("--lean4export-commit=") {
            lean4export_commit = Some(value.to_owned());
        } else if let Some(value) = arg.strip_prefix("--fragment=") {
            fragment = value.to_owned();
        } else if let Some(value) = arg.strip_prefix("--fact-id=") {
            fact_id = value.to_owned();
        } else if let Some(value) = arg.strip_prefix("--title=") {
            title = value.to_owned();
        } else {
            positional.push(arg);
        }
    }
    if positional.len() != 2 {
        return Err(usage());
    }
    let target = positional.pop().expect("checked len == 2");
    let path = positional.pop().expect("checked len == 2");
    Ok(Args {
        path: PathBuf::from(path),
        target,
        mathlib_commit,
        lean4export_commit,
        fragment,
        fact_id,
        title,
    })
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = parse_args()?;
    let reader = BufReader::new(File::open(&args.path)?);
    let completed = match import_statement_ndjson(reader, ImportLimits::default(), &args.target) {
        Ok(completed) => completed,
        Err(error) => {
            // A refusal is a complete, honest result -- report it typed, do
            // not attempt to weaken the gate or fabricate a fact shape.
            let decline = json!({
                "outcome": "declined-at-import",
                "target": args.target,
                "decline_reason": format!("{error:?}"),
                "decline_display": error.to_string(),
            });
            println!("{}", serde_json::to_string_pretty(&decline)?);
            std::process::exit(1);
        }
    };
    let record = build_statement_goal_record(&completed, &args.target)?;

    let mut prior_art = json!([]);
    if let (Some(mathlib_commit), Some(lean4export_commit)) =
        (&args.mathlib_commit, &args.lean4export_commit)
    {
        prior_art = json!([{
            "who": "the Mathlib contributors",
            "what": format!("the theorem declaration `{}`", record.target_name),
            "where": format!(
                "mathlib4 commit {mathlib_commit}, exported by lean4export commit {lean4export_commit}"
            ),
            "attribution": "the proposition's TYPE was read from a statement-only import; the proof value was never admitted",
        }]);
    }

    let fact = json!({
        "schema_version": 1,
        "id": args.fact_id,
        "title": args.title,
        "statement": format!(
            "The proposition declared as `{}` in the pinned Mathlib source, imported statement-only.",
            record.target_name
        ),
        "formal": {
            "language": "lean4",
            "statement": record.goal_lean4,
            "fragment": args.fragment,
        },
        "epistemic_status": "open",
        "depends_on": [],
        "evidence": [],
        "provenance": {
            "date": "not-a-fact-file: worked example only, no wall-clock date recorded",
            "established_by": "not established in this ledger",
            "source": format!(
                "statement-only import of `{}` via axeyum_lean_import::import_statement_ndjson",
                record.target_name
            ),
            "prior_art": prior_art,
            "statement_goal_record": {
                "target_name": record.target_name,
                "goal_sha256": record.goal_sha256,
                "target_content_sha256": record.target_content_sha256,
                "target_dependency_count": record.target_dependency_count,
                "admitted_declaration_count": record.admitted_declaration_count,
                "substituted_theorems": record.substituted_theorems,
                "lean_version_claimed_by_exporter": record.lean_version,
                "lean_githash_claimed_by_exporter": record.lean_githash,
                "format_version": record.format_version,
            },
        },
        "notes": "WORKED EXAMPLE emitted by examples/statement_goal_record.rs. Not written under artifacts/facts/ and not a ledger entry. formal.statement is Kernel::render_lean output (kernel-core), never hand-transcribed surface syntax.",
    });
    println!("{}", serde_json::to_string_pretty(&fact)?);
    Ok(())
}
