//! Parameterized "vs SOTA tool" shape — install-gated, never faked.
//!
//! The per-app measured scoreboards (B vs the property fragment, A vs
//! hevm/halmos, C vs Kani) all reduce to the same mechanic from
//! `crates/axeyum-bench/examples/measure_corpus.rs`'s `run_z3`: shell an external
//! binary on an instance, read its verdict, compare to axeyum's, and assert
//! `DISAGREE = 0`. [`ExternalOracle`] captures that shape so a future run drops in
//! cleanly — *without* faking a result when the tool is absent.
//!
//! For App B specifically, the self-contained construction-known corpus already
//! carries its own ground truth, so no external oracle is *needed*; `z3` (which is
//! installed here) is available purely as an optional cross-check via
//! [`ExternalOracle::z3`]. hevm / halmos / Kani are **not installed** and the
//! network is offline, so their scoreboards are recorded as install-gated in
//! `docs/consumer-track/measurement/STATUS.md`.

use std::path::Path;
use std::process::Command;
use std::time::{Duration, Instant};

/// A SOTA tool reachable as an external binary on an SMT-LIB / source file,
/// modelled after the `run_z3` shell in `measure_corpus.rs`.
///
/// This is the drop-in seam for the per-app "vs SOTA" scoreboards. It does **not**
/// fabricate a verdict: [`ExternalOracle::is_available`] reports honestly whether
/// the binary is on `PATH`, and [`ExternalOracle::run`] returns `None` when it is
/// not, so a missing tool yields no row rather than a fake one.
#[derive(Debug, Clone)]
pub struct ExternalOracle {
    /// The binary name (resolved via `PATH`).
    pub binary: String,
    /// Extra args inserted before the file path (e.g. a timeout flag).
    pub args: Vec<String>,
}

/// A shelled tool's verdict on one instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OracleVerdict {
    /// The instance is satisfiable / the property has a counterexample.
    Sat,
    /// The instance is unsatisfiable / the property holds.
    Unsat,
    /// The tool did not decide (timeout, error, or unrecognized output).
    Unknown,
}

impl ExternalOracle {
    /// The `z3` SMT solver with a per-instance wall-clock timeout (seconds),
    /// matching the `run_z3` invocation in `measure_corpus.rs`.
    #[must_use]
    pub fn z3(timeout: Duration) -> Self {
        let secs = timeout.as_secs().max(1);
        Self {
            binary: "z3".to_string(),
            args: vec![format!("-T:{secs}")],
        }
    }

    /// Whether the binary resolves on `PATH` (honest install gate). Uses
    /// `<binary> --version`, falling back to a bare invocation.
    #[must_use]
    pub fn is_available(&self) -> bool {
        Command::new(&self.binary)
            .arg("--version")
            .output()
            .or_else(|_| Command::new(&self.binary).output())
            .is_ok()
    }

    /// Shell the binary on `path` and parse its first non-empty stdout line as a
    /// verdict, timing the call. Returns `None` if the binary is unavailable —
    /// never a fabricated verdict.
    #[must_use]
    pub fn run(&self, path: &Path) -> Option<(OracleVerdict, Duration)> {
        let start = Instant::now();
        let output = Command::new(&self.binary)
            .args(&self.args)
            .arg(path)
            .output()
            .ok()?;
        let elapsed = start.elapsed();
        let stdout = String::from_utf8_lossy(&output.stdout);
        let first = stdout
            .lines()
            .map(str::trim)
            .find(|l| !l.is_empty())
            .unwrap_or("");
        let verdict = match first {
            "sat" => OracleVerdict::Sat,
            "unsat" => OracleVerdict::Unsat,
            _ => OracleVerdict::Unknown,
        };
        Some((verdict, elapsed))
    }
}
