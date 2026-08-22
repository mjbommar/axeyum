//! Report non-rendering declaration carriers from one root to multiple blockers.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;
use std::fs;
use std::io::{Cursor, Write as _};
use std::path::PathBuf;

use axeyum_lean_import::{ImportLimits, canonical_declaration_sha256, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const USAGE: &str = "usage: declaration_blocker_path_batch_audit \
    [--output <report.json>] <source.ndjson> <root> <blocker>...";

fn main() {
    if let Err(error) = run() {
        eprintln!("declaration-blocker-path-batch-audit: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let arguments = parse_arguments(std::env::args_os().skip(1))?;
    if let Some(output) = &arguments.output
        && output.exists()
    {
        return Err(format!("output already exists: {}", output.display()));
    }
    let bytes = fs::read(&arguments.path).map_err(|error| error.to_string())?;
    let input_sha256 = sha256(&bytes);
    let completed = import_ndjson(Cursor::new(bytes), ImportLimits::default())
        .map_err(|error| format!("source import failed: {error:?}"))?;
    let kernel = completed.kernel();
    let root_name = find_name(kernel, &arguments.root)?;
    let root_closure = kernel.declaration_dependency_closure(root_name);
    let (closure_cache, closure_computations) = build_closure_cache(&root_closure, |candidate| {
        kernel.declaration_dependency_closure(candidate)
    });
    let rows = arguments
        .blockers
        .iter()
        .map(|blocked| audit_blocker(kernel, &root_closure, &closure_cache, blocked))
        .collect::<Result<Vec<_>, _>>()?;
    let report = serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-declaration-blocker-path-batch-audit",
            "input": {"path": arguments.path, "sha256": input_sha256},
            "root": {
                "name": arguments.root,
                "kind": declaration_kind(kernel.environment().get(root_name).ok_or("root disappeared")?),
                "declaration_sha256": canonical_declaration_sha256(kernel, root_name)?,
                "closure_size": root_closure.len(),
            },
            "ordered_blockers": arguments.blockers,
            "blocker_rows": rows,
            "performance": {
                "candidate_closure_computations": closure_computations,
                "candidate_closures_reused_across_blockers": true,
            },
            "rendered_material": {"proof_terms": 0, "theorem_types": 0, "theorem_values": 0},
        }))
        .map_err(|error| error.to_string())?;
    if let Some(output) = &arguments.output {
        write_new_report(output, &report)?;
        println!(
            "DECLARATION_BLOCKER_PATH_BATCH_AUDIT_OK|output={}|blockers={}|closure_computations={}",
            output.display(),
            arguments.blockers.len(),
            closure_computations
        );
    } else {
        println!("{report}");
    }
    Ok(())
}

fn audit_blocker(
    kernel: &Kernel,
    root_closure: &[NameId],
    closure_cache: &BTreeMap<NameId, Vec<NameId>>,
    blocked: &str,
) -> Result<Value, String> {
    let blocked_name = find_name(kernel, blocked)?;
    if !root_closure.contains(&blocked_name) {
        return Ok(json!({
            "name": blocked,
            "present_in_root_closure": false,
            "carrier_count": 0,
            "carriers_nearest_first": [],
        }));
    }
    let mut carriers = root_closure
        .iter()
        .copied()
        .filter_map(|candidate| {
            let closure = closure_cache.get(&candidate)?;
            (candidate == blocked_name || closure.contains(&blocked_name))
                .then_some((candidate, closure.len()))
        })
        .collect::<Vec<_>>();
    carriers.sort_by_key(|(name, size)| (*size, kernel.display_name(*name).to_string()));
    let rows = carriers
        .into_iter()
        .map(|(name, closure_size)| {
            let declaration = kernel
                .environment()
                .get(name)
                .ok_or("carrier disappeared")?;
            Ok::<_, String>(json!({
                "name": kernel.display_name(name).to_string(),
                "kind": declaration_kind(declaration),
                "declaration_sha256": canonical_declaration_sha256(kernel, name)?,
                "closure_size": closure_size,
            }))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(json!({
        "name": blocked,
        "present_in_root_closure": true,
        "carrier_count": rows.len(),
        "carriers_nearest_first": rows,
    }))
}

fn build_closure_cache<F>(
    candidates: &[NameId],
    mut closure: F,
) -> (BTreeMap<NameId, Vec<NameId>>, usize)
where
    F: FnMut(NameId) -> Vec<NameId>,
{
    let cache = candidates
        .iter()
        .copied()
        .map(|candidate| (candidate, closure(candidate)))
        .collect::<BTreeMap<_, _>>();
    let computations = cache.len();
    (cache, computations)
}

struct Arguments {
    output: Option<PathBuf>,
    path: PathBuf,
    root: String,
    blockers: Vec<String>,
}

fn parse_arguments(
    values: impl IntoIterator<Item = std::ffi::OsString>,
) -> Result<Arguments, String> {
    let mut arguments = values.into_iter();
    let first = arguments.next().ok_or(USAGE)?;
    let (output, path) = if first == "--output" {
        let output = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
        let path = arguments.next().map(PathBuf::from).ok_or(USAGE)?;
        (Some(output), path)
    } else {
        (None, PathBuf::from(first))
    };
    let root = text_argument(arguments.next())?;
    let blockers = arguments
        .map(|argument| text_argument(Some(argument)))
        .collect::<Result<Vec<_>, _>>()?;
    if blockers.is_empty() || blockers.iter().collect::<BTreeSet<_>>().len() != blockers.len() {
        return Err("blockers must be a nonempty distinct list".to_owned());
    }
    Ok(Arguments {
        output,
        path,
        root,
        blockers,
    })
}

fn write_new_report(path: &PathBuf, report: &str) -> Result<(), String> {
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("cannot create output {}: {error}", path.display()))?;
    file.write_all(report.as_bytes())
        .and_then(|()| file.write_all(b"\n"))
        .and_then(|()| file.sync_all())
        .map_err(|error| format!("cannot write output {}: {error}", path.display()))
}

fn declaration_kind(declaration: &Declaration) -> &'static str {
    match declaration {
        Declaration::Axiom { .. } => "axiom",
        Declaration::Definition { .. } => "definition",
        Declaration::Theorem { .. } => "theorem",
        Declaration::Opaque { .. } => "opaque",
        Declaration::Quotient { .. } => "quotient",
        Declaration::Inductive { .. } => "inductive",
        Declaration::Constructor { .. } => "constructor",
        Declaration::Recursor { .. } => "recursor",
    }
}

fn find_name(kernel: &Kernel, expected: &str) -> Result<NameId, String> {
    let matches = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == expected).then_some(name)
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [name] => Ok(*name),
        [] => Err(format!("declaration is absent: {expected}")),
        _ => Err(format!("declaration is ambiguous: {expected}")),
    }
}

fn text_argument(value: Option<std::ffi::OsString>) -> Result<String, String> {
    value
        .ok_or(USAGE)?
        .into_string()
        .map_err(|_| "argument is not valid UTF-8".to_owned())
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .fold(String::with_capacity(64), |mut digest, byte| {
            write!(digest, "{byte:02x}").expect("writing to a String cannot fail");
            digest
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::OsString;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn legacy_stdout_arguments_remain_accepted() {
        let arguments = parse_arguments(
            ["source.ndjson", "Root", "Axiom"]
                .into_iter()
                .map(OsString::from),
        )
        .unwrap();
        assert!(arguments.output.is_none());
        assert_eq!(arguments.path, PathBuf::from("source.ndjson"));
        assert_eq!(arguments.root, "Root");
        assert_eq!(arguments.blockers, ["Axiom"]);
    }

    #[test]
    fn explicit_output_is_parseable_and_cannot_be_overwritten() {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "axeyum-blocker-audit-{}-{unique}.json",
            std::process::id()
        ));
        write_new_report(&path, "{\"ok\":true}").unwrap();
        let parsed: Value = serde_json::from_slice(&fs::read(&path).unwrap()).unwrap();
        assert_eq!(parsed, json!({"ok": true}));
        let before = fs::read(&path).unwrap();
        assert!(write_new_report(&path, "{\"ok\":false}").is_err());
        assert_eq!(fs::read(&path).unwrap(), before);
        fs::remove_file(path).unwrap();
    }

    #[test]
    fn candidate_closures_are_computed_once_for_shared_blockers() {
        let mut kernel = Kernel::new();
        let anon = kernel.anon();
        let names = ["a", "b", "c"].map(|part| kernel.name_str(anon, part));
        let mut calls = 0;
        let (cache, computations) = build_closure_cache(&names, |name| {
            calls += 1;
            vec![name]
        });
        assert_eq!(calls, names.len());
        assert_eq!(computations, names.len());
        assert_eq!(cache.len(), names.len());
        for blocker in names {
            assert_eq!(
                cache
                    .values()
                    .filter(|closure| closure.contains(&blocker))
                    .count(),
                1
            );
        }
        assert_eq!(
            calls,
            names.len(),
            "reading shared carriers must not recompute closures"
        );
    }
}
