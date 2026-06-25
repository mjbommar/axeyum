//! Per-file `check_auto_explained` probe for a corpus directory.
//!
//! This complements `measure_corpus`: the measured aggregate is the scoreboard,
//! while this probe shows which files moved and which route declined.
//!
//! ```text
//! cargo run -p axeyum-bench --example explain_corpus -- <dir> [timeout_ms]
//! ```

use std::path::{Path, PathBuf};
use std::time::Duration;

use axeyum_smtlib::parse_script;
use axeyum_solver::{CheckResult, SolverConfig, check_auto_explained};

fn collect_smt2(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut paths: Vec<PathBuf> = entries.filter_map(|e| e.ok().map(|e| e.path())).collect();
    paths.sort();
    for path in paths {
        if path.is_dir() {
            collect_smt2(&path, out);
        } else if path.extension().is_some_and(|ext| ext == "smt2") {
            out.push(path);
        }
    }
}

fn verdict(result: &CheckResult) -> &'static str {
    match result {
        CheckResult::Sat(_) => "sat",
        CheckResult::Unsat => "unsat",
        CheckResult::Unknown(_) => "unknown",
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dir = args
        .get(1)
        .cloned()
        .unwrap_or_else(|| {
            eprintln!("usage: explain_corpus <dir> [timeout_ms]");
            std::process::exit(2);
        })
        .into();
    let dir: PathBuf = dir;
    let timeout_ms: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(10_000);
    let config = SolverConfig::default().with_timeout(Duration::from_millis(timeout_ms));
    let mut files = Vec::new();
    collect_smt2(&dir, &mut files);
    assert!(!files.is_empty(), "no .smt2 under {}", dir.display());

    for path in files {
        let short = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("<non-utf8>");
        let Ok(text) = std::fs::read_to_string(&path) else {
            println!("{short}: read-error");
            continue;
        };
        if ["reset-assertions", "(reset", "(push", "(pop"]
            .iter()
            .any(|kw| text.contains(kw))
        {
            println!("{short}: skipped-scoped");
            continue;
        }
        let Ok(mut script) = parse_script(&text) else {
            println!("{short}: parse-error");
            continue;
        };
        match check_auto_explained(&mut script.arena, &script.assertions, &config) {
            Ok((result, trace)) => {
                println!("{short}: {}", verdict(&result));
                for attempt in trace.attempts() {
                    println!("  {attempt}");
                }
            }
            Err(error) => println!("{short}: error: {error}"),
        }
    }
}
