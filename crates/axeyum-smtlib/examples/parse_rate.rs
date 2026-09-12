//! Parse-rate probe: how many files of a committed list does the SMT-LIB front
//! end actually READ?
//!
//! A division's decide-rate is measured by `scripts/parity-run.sh` through
//! `smtcomp_cli`, which reports a parse failure as `unknown` — the same word it
//! prints for a reasoned give-up and a budget timeout. That collapse is fine for
//! scoring (all three are "not solved") and useless for diagnosis: it cannot
//! distinguish a division we decide badly from one we never read at all. The
//! SMT-LIB `FP` division was in the second category — every one of its 2,669
//! files uses `define-sort` with a quantifier, and binder sorts were parsed
//! against an empty alias map — and nothing in the scored output said so.
//!
//! This prints one line per file, `ok <bytes> <path>` or `err <reason> <path>`,
//! then a summary, and **exits non-zero when any file fails to parse** so a
//! caller cannot mistake a broken division for a clean one.
//!
//! Run with:
//! ```sh
//! cargo run --release -p axeyum-smtlib --example parse_rate -- <list-file>
//! ```
//! where `<list-file>` holds one benchmark path per line (the format of
//! `bench-results/parity-lists/<division>.txt`). `-` reads the list from stdin.

use std::io::Read as _;
use std::process::ExitCode;

use axeyum_smtlib::parse_script;

/// One-word classification of a parse failure, for the summary histogram. The
/// full message is on the per-file line; this only groups them.
fn reason_class(message: &str) -> &'static str {
    if message.starts_with("Unsupported") {
        "unsupported"
    } else if message.starts_with("Syntax") {
        "syntax"
    } else if message.starts_with("DeadlineExceeded") {
        "deadline"
    } else if message.starts_with("Ir") {
        "ir"
    } else {
        "other"
    }
}

fn main() -> ExitCode {
    let Some(list_path) = std::env::args().nth(1) else {
        eprintln!("usage: parse_rate <list-file|->");
        return ExitCode::from(2);
    };
    let list = if list_path == "-" {
        let mut buf = String::new();
        if let Err(e) = std::io::stdin().read_to_string(&mut buf) {
            eprintln!("read error on stdin: {e}");
            return ExitCode::from(2);
        }
        buf
    } else {
        match std::fs::read_to_string(&list_path) {
            Ok(text) => text,
            Err(e) => {
                eprintln!("read error on {list_path}: {e}");
                return ExitCode::from(2);
            }
        }
    };

    let paths: Vec<&str> = list
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .collect();
    if paths.is_empty() {
        // An empty list would otherwise print "0 of 0 parse" and exit 0, which
        // is the shape of a clean result. It is a broken invocation.
        eprintln!("FAIL: {list_path} names no benchmark files");
        return ExitCode::from(2);
    }

    let mut ok = 0usize;
    let mut unreadable = 0usize;
    // Failure classes, in a fixed order so the output is deterministic.
    let classes = ["unsupported", "syntax", "deadline", "ir", "other"];
    let mut counts = [0usize; 5];

    for path in &paths {
        let text = match std::fs::read_to_string(path) {
            Ok(text) => text,
            Err(e) => {
                unreadable += 1;
                println!("err read:{e} {path}");
                continue;
            }
        };
        match parse_script(&text) {
            Ok(_) => {
                ok += 1;
                println!("ok {} {path}", text.len());
            }
            Err(e) => {
                let message = format!("{e:?}");
                let class = reason_class(&message);
                if let Some(i) = classes.iter().position(|c| *c == class) {
                    counts[i] += 1;
                }
                // One line, no newlines inside it: the message is truncated so a
                // pathological error string cannot swamp the output.
                let flat: String = message.chars().filter(|c| *c != '\n').take(200).collect();
                println!("err {class}:{flat} {path}");
            }
        }
    }

    let total = paths.len();
    println!("---");
    println!("parsed {ok} / {total}");
    println!("unreadable {unreadable}");
    for (class, count) in classes.iter().zip(counts.iter()) {
        println!("failed-{class} {count}");
    }

    // The exit status depends on the finding, not on the run completing.
    if ok == total {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
