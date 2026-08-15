//! Shared real-Lean toolchain discovery and **skip honesty** for every suite
//! that hands a generated module to an external `lean` binary.
//!
//! Why this file exists. Until 2026-08-14 eight suites carried their own copy of
//! `lean_bin()`, and every copy looked only at `AXEYUM_LEAN_BIN` and `PATH`.
//! Lean 4.30.0 *was* installed on the development host — under
//! `~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean`, which `elan` does
//! not put on `PATH` unless its shim directory is sourced. So `which lean`
//! printed nothing, every suite took its skip path, and `cargo test` printed
//! `ok`. Nothing outside this repository had ever read the exported bytes. When
//! a real Lean was finally pointed at them it REJECTED them (fixed in
//! `a5975725f`: non-requested inductives were rendered as opaque `axiom`s, which
//! have no iota rule, so any `Eq.refl` whose proof had to compute through a
//! recursor failed).
//!
//! Two rules follow, and this module enforces both:
//!
//! 1. **Discover the toolchain.** `AXEYUM_LEAN_BIN` (explicit override), then
//!    `PATH`, then `$ELAN_HOME`/`~/.elan/toolchains/*/bin/lean`, then elan's
//!    shim. An override that does not resolve is an ERROR, never a silent
//!    fall-through to some other binary — otherwise `AXEYUM_LEAN_BIN=/nonexistent`
//!    (the negative control for this very gate) would quietly find the elan
//!    toolchain and prove nothing.
//! 2. **A skipped check must not read as a pass.** Under
//!    `AXEYUM_REQUIRE_LEAN=1` a missing toolchain is a hard failure. Otherwise
//!    the skip prints a machine-detectable [`SKIPPED_MARKER`] line naming how
//!    many checks did NOT run, and every suite that *did* run prints a
//!    [`CHECKED_MARKER`] line with the count that DID.
//!    `scripts/check-lean-gate.sh` sums those markers, so the aggregate gate
//!    reports the number of real-Lean invocations rather than an exit status.
//!
//! Shared by `#[path]` from both `axeyum-lean-kernel/tests/` and
//! `axeyum-solver/tests/` so the discovery logic has exactly one home; the two
//! crates are `publish = false`, so the cross-crate include costs nothing.
#![allow(dead_code)]

use std::fmt::Write as _;
use std::path::PathBuf;

/// Printed by a suite that ran real-Lean checks, with how many.
/// `scripts/check-lean-gate.sh` greps for it and sums the counts.
pub const CHECKED_MARKER: &str = "AXEYUM-LEAN-CHECKED";

/// Printed by a suite that could NOT run its real-Lean checks, with how many it
/// gave up. Never emitted under `AXEYUM_REQUIRE_LEAN=1` — there it is a panic.
pub const SKIPPED_MARKER: &str = "AXEYUM-LEAN-SKIPPED";

/// `AXEYUM_REQUIRE_LEAN=1`: a missing toolchain fails instead of skipping.
/// CI and `scripts/check-lean-gate.sh` set it.
#[must_use]
pub fn lean_required() -> bool {
    std::env::var("AXEYUM_REQUIRE_LEAN").as_deref() == Ok("1")
}

/// Elan's root: `$ELAN_HOME`, else `$HOME/.elan`.
fn elan_root() -> Option<PathBuf> {
    if let Some(home) = std::env::var_os("ELAN_HOME") {
        return Some(PathBuf::from(home));
    }
    std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".elan"))
}

/// Every `lean` an elan installation offers, in a deterministic order:
/// installed toolchains sorted by directory name (highest name first, which is
/// the newest version for elan's `leanprover--lean4---vX.Y.Z` naming), then the
/// `elan` shim as a last resort. The shim resolves through elan's *default*
/// toolchain, which is host state, so a concrete toolchain is preferred.
fn elan_candidates() -> Vec<PathBuf> {
    let Some(root) = elan_root() else {
        return Vec::new();
    };
    let mut toolchains: Vec<PathBuf> = std::fs::read_dir(root.join("toolchains"))
        .into_iter()
        .flatten()
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .collect();
    // Determinism is a public API promise here too: `read_dir` order is the
    // filesystem's, so sort before choosing.
    toolchains.sort();
    let mut candidates: Vec<PathBuf> = toolchains
        .into_iter()
        .rev()
        .map(|dir| dir.join("bin").join("lean"))
        .filter(|candidate| candidate.is_file())
        .collect();
    let shim = root.join("bin").join("lean");
    if shim.is_file() {
        candidates.push(shim);
    }
    candidates
}

/// The first `lean` on `PATH`, if any.
fn path_lean() -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|directory| directory.join("lean"))
        .find(|candidate| candidate.is_file())
}

/// Resolve a `lean` binary. `None` means genuinely unavailable — see the module
/// docs for why an unresolvable `AXEYUM_LEAN_BIN` returns `None` rather than
/// searching on.
#[must_use]
pub fn lean_bin() -> Option<PathBuf> {
    if let Some(raw) = std::env::var_os("AXEYUM_LEAN_BIN") {
        let overridden = PathBuf::from(raw);
        // An explicit override is authoritative in BOTH directions.
        return overridden.is_file().then_some(overridden);
    }
    path_lean().or_else(|| elan_candidates().into_iter().next())
}

/// Human-readable account of where discovery looked, for a skip/failure message.
/// A zero that nobody can attribute is the trap this whole file exists to close.
#[must_use]
pub fn discovery_report() -> String {
    let mut report = String::new();
    match std::env::var_os("AXEYUM_LEAN_BIN") {
        Some(raw) => {
            let path = PathBuf::from(&raw);
            let _ = write!(
                report,
                "AXEYUM_LEAN_BIN={} ({})",
                path.display(),
                if path.is_file() {
                    "resolved"
                } else {
                    "NOT a file -- an explicit override is never overridden by search"
                }
            );
            return report;
        }
        None => report.push_str("AXEYUM_LEAN_BIN unset"),
    }
    let _ = write!(
        report,
        "; PATH lean: {}",
        path_lean().map_or_else(|| "none".to_owned(), |p| p.display().to_string())
    );
    let elan = elan_candidates();
    let _ = write!(report, "; elan candidates: {}", elan.len());
    for candidate in &elan {
        let _ = write!(report, " {}", candidate.display());
    }
    report
}

/// Resolve the binary, or account for the skip.
///
/// `not_checked` is how many real-Lean checks the caller is about to give up on;
/// it is printed so a skip carries a magnitude rather than a shrug. Panics under
/// `AXEYUM_REQUIRE_LEAN=1`.
#[must_use]
pub fn lean_bin_or_skip(tag: &str, not_checked: usize) -> Option<PathBuf> {
    if let Some(bin) = lean_bin() {
        return Some(bin);
    }
    assert!(
        !lean_required(),
        "AXEYUM_REQUIRE_LEAN=1 but no Lean toolchain was found: {tag}: {not_checked} real-Lean \
         check(s) NOT run. Discovery: {}",
        discovery_report()
    );
    println!(
        "{SKIPPED_MARKER} {tag} not_checked={not_checked} -- SKIPPED, this is NOT a pass. Install \
         a toolchain with elan or set AXEYUM_LEAN_BIN. Discovery: {}",
        discovery_report()
    );
    None
}

/// Report how many real-Lean checks a suite actually ran. A suite that reaches
/// this with zero has resolved a binary and then checked nothing, which is the
/// failure mode this gate exists to make impossible.
pub fn report_checked(tag: &str, checked: usize) {
    assert!(
        checked > 0,
        "{tag}: a Lean toolchain was found but ZERO modules were checked -- a green run over \
         nothing is not a gate"
    );
    println!("{CHECKED_MARKER} {tag} checked={checked}");
}
