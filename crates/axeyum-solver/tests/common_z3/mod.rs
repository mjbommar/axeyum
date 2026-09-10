//! Shared **system Z3 binary** oracle probe for the differential fuzz suites.
//!
//! These suites are the only checks in this repository that compare our
//! verdicts against an independent solver. Every one of them used to hardcode
//! `const Z3_BIN: &str = "/usr/bin/z3"` and, when that path was absent, print a
//! note to stderr and `return` — a **passing** test. One of them said so in
//! words: *"if absent, the differential is impossible and the test is a no-op
//! pass"*.
//!
//! That is the repository's signature defect: on a host without Z3 the only
//! independent cross-check we own is green and empty, and nothing says so.
//! `AXEYUM_REQUIRE_LEAN`, `AXEYUM_REQUIRE_ABC` and `AXEYUM_REQUIRE_CARCARA` all
//! already turn an absent binary into a FAILURE; there was no
//! `AXEYUM_REQUIRE_Z3`. This module is it, modelled on the
//! `AXEYUM_REQUIRE_CARCARA` mode of `tests/carcara_crosscheck.rs` and its gate
//! `scripts/check-carcara-gate.sh`.
//!
//! # Environment
//!
//! - `AXEYUM_Z3_BIN` — path to the Z3 binary. Defaults to [`DEFAULT_Z3_BIN`].
//!   Pointing it at a nonexistent path is how the absence case is exercised on
//!   a host that *has* Z3 (which is every host anyone ever ran these on, which
//!   is why the defect survived).
//! - `AXEYUM_REQUIRE_Z3=1` — an absent binary is a **failure**, not a skip.
//!   `scripts/check-z3-differential-gate.sh` sets it. Unset (the default) keeps
//!   the historical skip so an ordinary developer run is unaffected.
//!
//! # Output contract
//!
//! Each line below is parsed by `scripts/check-z3-differential-gate.sh`; keep
//! the prefixes stable.
//!
//! - `AXEYUM-Z3-BIN bin=<path> version=<line>` — printed once per test process
//!   the first time the oracle is found. Exporting `AXEYUM_Z3_BIN` is an
//!   instruction; this line is the evidence of what was actually used.
//! - `AXEYUM-Z3-SKIPPED [<tag>] …` — the oracle was absent and the run was not
//!   required to have one. A gate that sees this line has adjudicated nothing.

#![allow(dead_code)]

use std::process::{Command, Stdio};
use std::sync::OnceLock;

/// Path used when `AXEYUM_Z3_BIN` is unset — the system package location, which
/// is what all thirteen suites hardcoded.
pub const DEFAULT_Z3_BIN: &str = "/usr/bin/z3";

/// The Z3 binary these suites shell SMT-LIB text into.
///
/// Resolved once per test process from `AXEYUM_Z3_BIN`, else [`DEFAULT_Z3_BIN`].
/// The path is returned whether or not it exists; [`z3_available`] decides that.
pub fn z3_bin() -> &'static str {
    static BIN: OnceLock<String> = OnceLock::new();
    BIN.get_or_init(|| match std::env::var("AXEYUM_Z3_BIN") {
        Ok(p) if !p.is_empty() => p,
        _ => DEFAULT_Z3_BIN.to_string(),
    })
    .as_str()
}

/// Whether `AXEYUM_REQUIRE_Z3=1` is set: an absent oracle is then a FAILURE.
pub fn z3_required() -> bool {
    std::env::var("AXEYUM_REQUIRE_Z3").unwrap_or_default() == "1"
}

/// Prints `AXEYUM-Z3-BIN …` once per test process.
fn banner(bin: &str) {
    static ONCE: OnceLock<()> = OnceLock::new();
    ONCE.get_or_init(|| {
        let version = Command::new(bin)
            .arg("--version")
            .output()
            .ok()
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().replace('\n', " "))
            .filter(|v| !v.is_empty())
            .unwrap_or_else(|| "unknown".to_string());
        println!("AXEYUM-Z3-BIN bin={bin} version={version}");
    });
}

/// Whether the Z3 binary responds to `--version` at all.
fn version_responds(bin: &str) -> bool {
    Command::new(bin)
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .output()
        .is_ok()
}

/// The single adjudication-availability decision, shared by every suite.
///
/// `probe_answered` is the suite's own result of piping a trivial script (its
/// own `(set-logic …)` / `(check-sat)`) at the oracle: `true` when Z3 answered.
/// This preserves each suite's original two-part probe — *answered the trivial
/// script* **or** *responds to `--version`* — exactly.
///
/// Returns `true` when the oracle is usable. Returns `false` (after printing
/// `AXEYUM-Z3-SKIPPED`) when it is absent and `AXEYUM_REQUIRE_Z3` is unset.
///
/// # Panics
///
/// When the oracle is absent and `AXEYUM_REQUIRE_Z3=1`. That panic is the whole
/// point of this module: a skip and an oracle that agreed with us on every
/// single script are otherwise the same observation.
pub fn z3_available(tag: &str, probe_answered: bool) -> bool {
    let bin = z3_bin();
    if probe_answered || version_responds(bin) {
        banner(bin);
        return true;
    }
    assert!(
        !z3_required(),
        "AXEYUM_REQUIRE_Z3=1 but no usable Z3 binary at `{bin}` (suite `{tag}`).\n\
         \n\
         This suite is one of the only checks in this repository that compares our \
         verdicts against an INDEPENDENT solver. Without the binary it adjudicates \
         nothing, and a pass here would be indistinguishable from a Z3 that agreed \
         with us on every script.\n\
         \n\
         Install Z3 (`apt-get install z3`), or point `AXEYUM_Z3_BIN` at one, or \
         unset `AXEYUM_REQUIRE_Z3` and accept that this run establishes nothing \
         about our agreement with Z3."
    );
    eprintln!(
        "AXEYUM-Z3-SKIPPED [{tag}] {bin} unavailable; skipping (no adjudicator). \
         Nothing in this run compares our verdicts against an independent solver. \
         Set AXEYUM_REQUIRE_Z3=1 to make this a failure."
    );
    false
}
