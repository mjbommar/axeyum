//! Shared real-Lean toolchain **resolution policy**, and **skip honesty**, for
//! every suite that hands a generated module to an external `lean` binary.
//!
//! # Why this file exists (1): a skipped check read as a pass
//!
//! Until 2026-08-14 eight suites carried their own copy of `lean_bin()`, and
//! every copy looked only at `AXEYUM_LEAN_BIN` and `PATH`. Lean 4.30.0 *was*
//! installed on the development host — under
//! `~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean`, which `elan` does
//! not put on `PATH` unless its shim directory is sourced. So `which lean`
//! printed nothing, every suite took its skip path, and `cargo test` printed
//! `ok`. Nothing outside this repository had ever read the exported bytes. When
//! a real Lean was finally pointed at them it REJECTED them (fixed in
//! `a5975725f`).
//!
//! # Why this file exists (2): the toolchain was an unstated environment fact
//!
//! The fix above introduced a second, quieter defect. Discovery searched
//! `PATH`, then elan's toolchains *sorted newest-name-first* — and the shell
//! gate `scripts/check-lean-gate.sh` carried a hand-written copy of that order.
//! Measured on this host on 2026-08-17 with **two** toolchains installed
//! (`v4.30.0` and `v4.34.0-rc1`):
//!
//! * the two implementations disagreed — the shell gate found `PATH`'s lean
//!   (elan's default, 4.30.0) when `~/.elan/bin` happened to be on `PATH`, and
//!   the Rust probe took the newest name, 4.34.0-rc1;
//! * under 4.34, 21 of 77 `lean_crosscheck` families were rejected while all 77
//!   passed under 4.30 (module headers, since fixed in `b760fd6ae`), and
//!   `scripts/lean/replay-lean4export.lean` did not even elaborate
//!   (`Environment.addDeclCore` gained a `maxRecDepth` parameter, since fixed);
//! * so **the gate's verdict depended on which toolchain happened to be
//!   installed and on which entry point ran**, and nothing in the output said
//!   which one produced it.
//!
//! That is this repository's signature failure — a tool whose answer changes
//! with an unstated fact about the machine — so it is closed here, once, for
//! every caller.
//!
//! # The policy
//!
//! **The repository pins its Lean, and the pin is what runs.** The pin is the
//! `lean-toolchain` file at the repository root (the same file `elan` and
//! `lake` read), and resolution is, in order:
//!
//! 1. `AXEYUM_LEAN_BIN` — an explicit override, authoritative in BOTH
//!    directions: if it is set and does not resolve, discovery STOPS and
//!    reports nothing, or `AXEYUM_LEAN_BIN=/nonexistent` (the negative control
//!    for the gate) would quietly find an elan toolchain and prove nothing.
//! 2. The pinned toolchain's own elan directory,
//!    `$ELAN_HOME/toolchains/leanprover--lean4---v4.30.0/bin/lean`.
//! 3. `PATH`'s `lean`, **only if `--version` matches the pin**.
//! 4. Any other installed elan toolchain, in sorted order, **only if
//!    `--version` matches the pin**.
//! 5. elan's shim, **only if `--version` matches the pin**.
//!
//! There is deliberately no "newest wins" step and no unversioned fallback: a
//! host with only 4.34 installed resolves NOTHING and says so, rather than
//! silently checking a different claim. The single escape hatch is step 1,
//! which names a binary explicitly; under `AXEYUM_REQUIRE_LEAN=1` an override
//! that is not the pinned version is a hard, named failure unless
//! `AXEYUM_LEAN_ALLOW_UNPINNED=1` is also set, which is then printed in every
//! toolchain banner.
//!
//! Why "the pin" and not "the newest": several suites are *frozen-source
//! reproductions* that assert an exact toolchain — for example
//! `real_lean_strict_positivity_crosscheck` pins commit
//! `d024af099ca4bf2c86f649261ebf59565dc8c622`, and
//! `real_lean_wire_differential` is a differential against the reference
//! implementation, which is meaningless against "whatever was installed". A
//! blanket "always newest" would break those by design. Moving to a newer Lean
//! is therefore an explicit act: edit `lean-toolchain`, and every suite follows
//! in one commit.
//!
//! # Stating it
//!
//! Every suite that runs prints an [`TOOLCHAIN_MARKER`] line naming the binary,
//! its version, and which policy step found it, next to its
//! [`CHECKED_MARKER`] count. `scripts/check-lean-gate.sh` reads those lines and
//! FAILS if any suite used a different Lean than the one the gate resolved. A
//! result that does not name its checker is not evidence.
//!
//! Shared by `#[path]` from `axeyum-lean-kernel/tests/`,
//! `axeyum-lean-import/tests/` and `axeyum-solver/tests/` so the policy has
//! exactly one home; the crates are `publish = false`, so the cross-crate
//! include costs nothing.
#![allow(dead_code)]

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

/// Printed by a suite that ran real-Lean checks, with how many.
/// `scripts/check-lean-gate.sh` greps for it and sums the counts.
pub const CHECKED_MARKER: &str = "AXEYUM-LEAN-CHECKED";

/// Printed by a suite that could NOT run its real-Lean checks, with how many it
/// gave up. Never emitted under `AXEYUM_REQUIRE_LEAN=1` — there it is a panic.
pub const SKIPPED_MARKER: &str = "AXEYUM-LEAN-SKIPPED";

/// Printed by every suite that resolved a toolchain, naming the binary, the
/// version, and the policy step that found it. `scripts/check-lean-gate.sh`
/// cross-checks these against its own resolution, so two entry points can never
/// again silently check different things.
pub const TOOLCHAIN_MARKER: &str = "AXEYUM-LEAN-TOOLCHAIN";

/// `AXEYUM_REQUIRE_LEAN=1`: a missing toolchain fails instead of skipping.
/// CI and `scripts/check-lean-gate.sh` set it.
#[must_use]
pub fn lean_required() -> bool {
    std::env::var("AXEYUM_REQUIRE_LEAN").as_deref() == Ok("1")
}

/// `AXEYUM_LEAN_ALLOW_UNPINNED=1`: accept an `AXEYUM_LEAN_BIN` whose version is
/// not the pinned one. Deliberately narrow — it only relaxes the *assertion*,
/// never the search, and the disagreement is still printed in every banner.
#[must_use]
pub fn unpinned_allowed() -> bool {
    std::env::var("AXEYUM_LEAN_ALLOW_UNPINNED").as_deref() == Ok("1")
}

/// A resolved toolchain: what ran, and why it was chosen.
#[derive(Clone, Debug)]
pub struct Toolchain {
    /// The `lean` binary.
    pub bin: PathBuf,
    /// The full first line of `lean --version`.
    pub version_line: String,
    /// Which policy step found it, for the banner.
    pub source: &'static str,
    /// Whether `version_line` matches the `lean-toolchain` pin.
    pub matches_pin: bool,
}

impl Toolchain {
    /// The banner line. Every run says which Lean produced its verdicts.
    #[must_use]
    pub fn banner(&self, tag: &str) -> String {
        format!(
            "{TOOLCHAIN_MARKER} {tag} bin={} version={:?} source={} pinned={} matches_pin={}",
            self.bin.display(),
            self.version_line,
            self.source,
            pinned_toolchain().unwrap_or_else(|| "<lean-toolchain missing>".to_owned()),
            self.matches_pin
        )
    }
}

// ---------------------------------------------------------------------------
// The pin.
// ---------------------------------------------------------------------------

/// The repository root, found by walking up from this crate's manifest looking
/// for `lean-toolchain`. `CARGO_MANIFEST_DIR` differs per including crate, so
/// a fixed `../../` would silently break the day a suite moves.
fn repo_lean_toolchain_file() -> Option<PathBuf> {
    let mut directory: Option<&Path> = Some(Path::new(env!("CARGO_MANIFEST_DIR")));
    while let Some(current) = directory {
        let candidate = current.join("lean-toolchain");
        if candidate.is_file() {
            return Some(candidate);
        }
        directory = current.parent();
    }
    None
}

/// The pinned toolchain as `lean-toolchain` spells it, e.g.
/// `leanprover/lean4:v4.30.0`.
#[must_use]
pub fn pinned_toolchain() -> Option<String> {
    let text = std::fs::read_to_string(repo_lean_toolchain_file()?).ok()?;
    let trimmed = text.trim();
    (!trimmed.is_empty()).then(|| trimmed.to_owned())
}

/// The pinned version as `lean --version` spells it, e.g. `4.30.0`.
#[must_use]
pub fn pinned_version() -> Option<String> {
    let toolchain = pinned_toolchain()?;
    let tail = toolchain.rsplit(":v").next()?;
    (tail != toolchain).then(|| tail.to_owned())
}

/// Elan's directory name for a toolchain: `leanprover/lean4:v4.30.0` ->
/// `leanprover--lean4---v4.30.0`.
fn elan_directory_name(toolchain: &str) -> String {
    toolchain.replace('/', "--").replace(':', "---")
}

/// Assert that a `lean --version` line names the PINNED version (from
/// `lean-toolchain`), so a suite measured against the pin cannot silently run
/// against another toolchain. Before 2026-09-03 every crosscheck carried its
/// own literal (`"4.30.0"`), so moving the pin meant editing seven suites and
/// missing one meant a suite that could never pass; now the pin file is the
/// single authority and the suites follow it.
pub fn assert_pinned_version(tag: &str, version_text: &str) {
    let pinned = pinned_version()
        .unwrap_or_else(|| panic!("{tag}: lean-toolchain does not name a `:v<version>` pin"));
    assert!(
        version_text.contains(&format!("version {pinned},")),
        "{tag}: this comparison requires the pinned Lean {pinned}, got: {version_text}"
    );
}

/// `lean --version`'s first line, or `None` if the binary does not run.
#[must_use]
pub fn version_line(bin: &Path) -> Option<String> {
    let output = Command::new(bin).arg("--version").output().ok()?;
    if !output.status.success() {
        return None;
    }
    let text = String::from_utf8_lossy(&output.stdout);
    text.lines().next().map(|line| line.trim().to_owned())
}

/// Does this `--version` line report the pinned version?
///
/// Matched as `version <pin>,` — the trailing comma matters: a bare substring
/// test would let `4.30.0` match a hypothetical `4.30.0-rc1`, and `4.3` match
/// `4.30.0`.
fn is_pinned(version_line: &str) -> bool {
    pinned_version().is_some_and(|pin| version_line.contains(&format!("version {pin},")))
}

// ---------------------------------------------------------------------------
// Resolution.
// ---------------------------------------------------------------------------

/// Elan roots to search. `$ELAN_HOME` if set, then `~/.elan`, then
/// `~/.elan/elan-home` — `scripts/install-pinned-lean.sh` installs into the
/// last one and `scripts/provision-fleet-host.sh` only *symlinks* it into
/// place, so a host provisioned before that symlink landed still resolves.
fn elan_roots() -> Vec<PathBuf> {
    let mut roots = Vec::new();
    if let Some(home) = std::env::var_os("ELAN_HOME") {
        roots.push(PathBuf::from(home));
    }
    if let Some(home) = std::env::var_os("HOME") {
        let dot_elan = PathBuf::from(home).join(".elan");
        roots.push(dot_elan.join("elan-home"));
        roots.push(dot_elan);
    }
    roots.sort();
    roots.dedup();
    roots
}

/// Every `lean` an elan installation offers, in a deterministic order: the
/// PINNED toolchain's directory first, then the remaining toolchains sorted by
/// directory name, then the shim. Order is by policy, not by version sort — the
/// version check below is what actually decides.
fn elan_candidates() -> Vec<(PathBuf, &'static str)> {
    let pinned_directory = pinned_toolchain().map(|toolchain| elan_directory_name(&toolchain));
    let mut pinned: Vec<(PathBuf, &'static str)> = Vec::new();
    let mut others: Vec<PathBuf> = Vec::new();
    let mut shims: Vec<(PathBuf, &'static str)> = Vec::new();
    for root in elan_roots() {
        let mut toolchains: Vec<PathBuf> = std::fs::read_dir(root.join("toolchains"))
            .into_iter()
            .flatten()
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .collect();
        // Determinism is a public API promise here too: `read_dir` order is the
        // filesystem's, so sort before choosing.
        toolchains.sort();
        for directory in toolchains {
            let candidate = directory.join("bin").join("lean");
            if !candidate.is_file() {
                continue;
            }
            let is_pin = pinned_directory.as_deref().is_some_and(|name| {
                directory.file_name().and_then(std::ffi::OsStr::to_str) == Some(name)
            });
            if is_pin {
                pinned.push((candidate, "elan-pinned-toolchain"));
            } else {
                others.push(candidate);
            }
        }
        let shim = root.join("bin").join("lean");
        if shim.is_file() {
            shims.push((shim, "elan-shim"));
        }
    }
    let mut candidates = pinned;
    candidates.extend(others.into_iter().map(|bin| (bin, "elan-other-toolchain")));
    candidates.extend(shims);
    candidates
}

/// The first `lean` on `PATH`, if any.
fn path_lean() -> Option<PathBuf> {
    let path = std::env::var_os("PATH")?;
    std::env::split_paths(&path)
        .map(|directory| directory.join("lean"))
        .find(|candidate| candidate.is_file())
}

fn resolve() -> Option<Toolchain> {
    // 1. Explicit override: authoritative in both directions.
    if let Some(raw) = std::env::var_os("AXEYUM_LEAN_BIN") {
        let overridden = PathBuf::from(raw);
        if !overridden.is_file() {
            return None;
        }
        let version_line =
            version_line(&overridden).unwrap_or_else(|| "<lean --version failed>".to_owned());
        let matches_pin = is_pinned(&version_line);
        return Some(Toolchain {
            bin: overridden,
            version_line,
            source: "AXEYUM_LEAN_BIN",
            matches_pin,
        });
    }

    // 2. The pinned toolchain's own elan directory, then 3/4/5 by version.
    let mut candidates: Vec<(PathBuf, &'static str)> = Vec::new();
    let elan = elan_candidates();
    candidates.extend(
        elan.iter()
            .filter(|(_, source)| *source == "elan-pinned-toolchain")
            .cloned(),
    );
    if let Some(bin) = path_lean() {
        candidates.push((bin, "PATH"));
    }
    candidates.extend(
        elan.into_iter()
            .filter(|(_, source)| *source != "elan-pinned-toolchain"),
    );

    for (bin, source) in candidates {
        let Some(version_line) = version_line(&bin) else {
            continue;
        };
        if is_pinned(&version_line) {
            return Some(Toolchain {
                bin,
                version_line,
                source,
                matches_pin: true,
            });
        }
    }
    None
}

fn resolved() -> Option<&'static Toolchain> {
    static RESOLVED: OnceLock<Option<Toolchain>> = OnceLock::new();
    RESOLVED.get_or_init(resolve).as_ref()
}

/// The resolved toolchain, or `None` if the pin is not installed and no
/// override was given. Resolution runs once per process.
#[must_use]
pub fn lean_toolchain() -> Option<&'static Toolchain> {
    resolved()
}

/// Resolve a `lean` binary. `None` means the pinned toolchain is genuinely
/// unavailable — see the module docs for the policy and why "newest installed"
/// is not part of it.
#[must_use]
pub fn lean_bin() -> Option<PathBuf> {
    resolved().map(|toolchain| toolchain.bin.clone())
}

/// Human-readable account of where resolution looked and what it found, for a
/// skip or failure message. A zero that nobody can attribute is the trap this
/// whole file exists to close.
#[must_use]
pub fn discovery_report() -> String {
    let mut report = String::new();
    let _ = write!(
        report,
        "policy=pinned; lean-toolchain={}",
        pinned_toolchain().unwrap_or_else(|| "<absent>".to_owned())
    );
    match std::env::var_os("AXEYUM_LEAN_BIN") {
        Some(raw) => {
            let path = PathBuf::from(&raw);
            let _ = write!(
                report,
                "; AXEYUM_LEAN_BIN={} ({})",
                path.display(),
                if path.is_file() {
                    "resolved -- an explicit override is authoritative"
                } else {
                    "NOT a file -- an explicit override is never overridden by search"
                }
            );
            return report;
        }
        None => report.push_str("; AXEYUM_LEAN_BIN unset"),
    }
    let _ = write!(
        report,
        "; PATH lean: {}",
        path_lean().map_or_else(
            || "none".to_owned(),
            |bin| format!(
                "{} [{}]",
                bin.display(),
                version_line(&bin).unwrap_or_else(|| "does not run".to_owned())
            )
        )
    );
    let elan = elan_candidates();
    let _ = write!(report, "; elan candidates: {}", elan.len());
    for (bin, source) in &elan {
        let _ = write!(
            report,
            " {}({}) [{}]",
            bin.display(),
            source,
            version_line(bin).unwrap_or_else(|| "does not run".to_owned())
        );
    }
    report
}

/// Resolve the binary, or account for the skip.
///
/// `not_checked` is how many real-Lean checks the caller is about to give up
/// on; it is printed so a skip carries a magnitude rather than a shrug. Panics
/// under `AXEYUM_REQUIRE_LEAN=1`, and also panics — loudly, naming both
/// versions — if the resolved toolchain is not the pinned one, because that is
/// a change in *what got checked* rather than in whether anything did.
#[must_use]
pub fn lean_bin_or_skip(tag: &str, not_checked: usize) -> Option<PathBuf> {
    if let Some(toolchain) = resolved() {
        println!("{}", toolchain.banner(tag));
        assert!(
            toolchain.matches_pin || !lean_required() || unpinned_allowed(),
            "{tag}: TOOLCHAIN MISMATCH. `lean-toolchain` pins {}, but the resolved Lean is {} \
             ({}, via {}). Suites in this repository include frozen-source reproductions that \
             assert an exact toolchain, so running a different one changes WHAT is checked, not \
             just whether it passes. Fix the override, install the pinned toolchain, or set \
             AXEYUM_LEAN_ALLOW_UNPINNED=1 to state the deviation.",
            pinned_toolchain().unwrap_or_else(|| "<lean-toolchain missing>".to_owned()),
            toolchain.version_line,
            toolchain.bin.display(),
            toolchain.source,
        );
        return Some(toolchain.bin.clone());
    }
    assert!(
        !lean_required(),
        "AXEYUM_REQUIRE_LEAN=1 but the PINNED Lean toolchain was not found: {tag}: \
         {not_checked} real-Lean check(s) NOT run. Resolution: {}",
        discovery_report()
    );
    println!(
        "{SKIPPED_MARKER} {tag} not_checked={not_checked} -- SKIPPED, this is NOT a pass. Install \
         the pinned toolchain (`elan toolchain install {}`) or set AXEYUM_LEAN_BIN. Resolution: {}",
        pinned_toolchain().unwrap_or_else(|| "<the toolchain named in lean-toolchain>".to_owned()),
        discovery_report()
    );
    None
}

/// Report how many real-Lean checks a suite actually ran, and which Lean ran
/// them. A suite that reaches this with zero has resolved a binary and then
/// checked nothing, which is the failure mode this gate exists to make
/// impossible.
pub fn report_checked(tag: &str, checked: usize) {
    assert!(
        checked > 0,
        "{tag}: a Lean toolchain was found but ZERO modules were checked -- a green run over \
         nothing is not a gate"
    );
    if let Some(toolchain) = resolved() {
        println!("{}", toolchain.banner(tag));
    }
    println!("{CHECKED_MARKER} {tag} checked={checked}");
}
