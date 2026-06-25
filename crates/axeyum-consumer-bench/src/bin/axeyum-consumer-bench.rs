//! `axeyum-consumer-bench` — run the construction-known property corpus through
//! the [`axeyum_property`] SDK, generate the committed scoreboard, and assert the
//! `DISAGREE = 0` soundness floor.
//!
//! Usage:
//! ```text
//! # regenerate the committed scoreboard (default path)
//! cargo run -p axeyum-consumer-bench
//!
//! # write to an explicit path
//! cargo run -p axeyum-consumer-bench -- <out.md>
//!
//! # verify the on-disk scoreboard is up to date (CI / no-write); exit 1 if stale
//! cargo run -p axeyum-consumer-bench -- --check <path.md>
//! ```
//!
//! In every mode the process **panics** if `DISAGREE != 0` (an axeyum verdict
//! contradicts a construction-known status), so the binary doubles as a soundness
//! gate.

use std::path::PathBuf;
use std::process::ExitCode;

use axeyum_consumer_bench::{corpus, render_scoreboard, run_corpus};

/// The default committed scoreboard path, relative to the workspace root.
const DEFAULT_OUT: &str = "docs/consumer-track/property/SCOREBOARD.md";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();

    let (check_only, out_path) = match args.as_slice() {
        [] => (false, PathBuf::from(DEFAULT_OUT)),
        [flag, path] if flag == "--check" => (true, PathBuf::from(path)),
        [flag] if flag == "--check" => (true, PathBuf::from(DEFAULT_OUT)),
        [path] => (false, PathBuf::from(path)),
        _ => {
            eprintln!("usage: axeyum-consumer-bench [--check] [out.md]");
            return ExitCode::from(2);
        }
    };

    let cases = corpus();
    let (rows, agg) = run_corpus(&cases);

    // Human summary on stdout (includes mean time).
    println!("{}", render_scoreboard(&rows, &agg, true));

    // The committed file is timing-free for determinism.
    let committed = render_scoreboard(&rows, &agg, false);

    // Hard soundness floor: this must hold regardless of mode.
    assert_eq!(
        agg.disagree, 0,
        "DISAGREE = {} — an axeyum verdict contradicts a construction-known status (soundness alarm)",
        agg.disagree
    );

    if check_only {
        let on_disk = std::fs::read_to_string(&out_path).unwrap_or_default();
        if on_disk == committed {
            println!("[check] {} is up to date", out_path.display());
            ExitCode::SUCCESS
        } else {
            eprintln!(
                "[check] {} is STALE — regenerate with `cargo run -p axeyum-consumer-bench`",
                out_path.display()
            );
            ExitCode::from(1)
        }
    } else {
        if let Some(parent) = out_path.parent() {
            std::fs::create_dir_all(parent).expect("create scoreboard dir");
        }
        std::fs::write(&out_path, &committed).expect("write scoreboard");
        println!("wrote {}", out_path.display());
        ExitCode::SUCCESS
    }
}
