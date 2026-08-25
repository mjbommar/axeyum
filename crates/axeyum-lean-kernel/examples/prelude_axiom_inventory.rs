//! Emit the reconstruction-prelude `Declaration::Axiom` population, as the
//! deliberately narrow half of a two-tool cross-check (see
//! `scripts/gen-lean-axiom-ledger.py`'s module docstring, "Two independent
//! measurements, cross-checked against each other").
//!
//! Output is deterministic tab-separated data:
//! `prelude<TAB>name<TAB>canonical-type-utf8-as-hex`.  Hex keeps the boundary
//! unambiguous without adding a serialization dependency to the zero-dependency
//! kernel crate.  The consumer hashes the decoded canonical type and binds it to
//! the reviewed ledger.  **This row shape is a public contract** —
//! `gen-lean-axiom-ledger.py::parse_axiom_rows` requires exactly three
//! tab-separated fields — so it is unchanged here; do not add a `kind` column
//! to this tool the way `nat_axiom_inventory` has one.
//!
//! # Why `Declaration::Axiom` alone, when `Opaque`/`Quotient` are also trusted
//!
//! This is deliberate, not the bug it looks like in isolation.  The ledger
//! script runs *this* tool for a from-scratch, independently-written
//! `Axiom`-only enumeration and separately runs `nat_axiom_inventory
//! --include-constructed` for the full trusted surface (`axiom` + `opaque` +
//! `quotient`), then cross-checks: per prelude, this tool's `Axiom` row count
//! must equal the other tool's declared `axiom` count, and every row's name
//! and canonical type must match byte-for-byte. A filter bug in either tool
//! shows up as a *disagreement*, not as a smaller number — that only works if
//! the two use genuinely different code paths, which folding `Opaque`/
//! `Quotient` into this tool's own filter would undermine by making it a
//! second copy of the other tool's logic rather than an independent one.
//!
//! Measured 2026-08-25 (`nat_axiom_inventory --include-constructed`, all nine
//! preludes): `opaque=0` and `quotient=0` in every group, `axiom` nonzero only
//! for `axreal` (30) — no prelude builder in this crate calls
//! `Kernel::opaque`/`Kernel::quotient` at all (the only call sites are in
//! `lean_export.rs`, for importing a foreign Lean environment, not for
//! building a prelude). So today `Axiom`-only and the full trusted surface
//! coincide for every prelude this tool measures; they are not guaranteed to
//! stay that way, which is exactly why the second, full-surface tool exists
//! and why the cross-check — not this tool alone — is the actual gate.
//!
//! # Coverage: all nine preludes, not the historical three
//!
//! Until 2026-08-25 this tool built only `axreal`/`integer`/`string`, so the
//! ledger's cross-check was *vacuously* satisfied for the other six preludes:
//! this tool's per-prelude row count for, say, `nat` was always 0 because it
//! never built `nat` at all, and that 0 happened to match
//! `nat_axiom_inventory`'s declared `axiom=0` for the same reason a stopped
//! clock matches the time twice a day. The check still caught *future* drift
//! (a `nat` axiom appearing would break the match), but it gave no
//! independent corroboration of *today's* zero — the exact "never enumerated"
//! versus "enumerated and found empty" trap this project keeps hitting one
//! level up. Extended here to build `logic`, `nat`, `axreal`, `integer`,
//! `rat`, `string` always (all cheap), and `creal`/`complex`/`cpoint` under
//! `--include-constructed` (expensive — see `nat_axiom_inventory`'s module
//! doc for the measured cost), matching that tool's own prelude set and
//! `ALWAYS_BUILT_PRELUDES`/`CONSTRUCTED_PRELUDES` naming. This changes no
//! printed ledger number (every added prelude is currently axiom-free) and
//! does not touch `gen-lean-axiom-ledger.py`: `Measurement.preludes` is
//! already derived from the *other* tool's coverage, not from this one's row
//! labels, so widening this tool's coverage only strengthens the cross-check.
//!
//! # This tool used to be a checker that cannot fail
//!
//! Before 2026-08-25 this example parsed no arguments (any flag, valid or a
//! typo, was silently ignored) and always exited 0 barring a build panic —
//! nothing tied its exit status to what it found. That was survivable only
//! because nothing invokes it as a standalone gate: `gen-lean-axiom-ledger.py`
//! does its own real checking in Python against this tool's stdout, and
//! `scripts/check-prelude-reuse-equivalence.sh` only diffs its output
//! byte-for-byte across a cache flag. But a `--require-axiom-free`/
//! `--expect-axioms` pair matching `nat_axiom_inventory`'s is added below
//! anyway: an inventory tool whose own exit status is silent about its
//! findings invites exactly the direct, unchecked use (a new fact's
//! `checker_command`) that has already produced a checker that cannot fail
//! once in this codebase (`nat_axiom_inventory`, fixed 2026-08-15) and that
//! this file was independently found to still be doing on 2026-08-25.
//!
//! ```sh
//! prelude_axiom_inventory --require-axiom-free nat --require-axiom-free logic
//! prelude_axiom_inventory --expect-axioms axreal=30 --require-axiom-free integer
//! prelude_axiom_inventory --include-constructed --require-axiom-free creal
//! ```
//!
//! A prelude named on the command line that this run does not build is an
//! ERROR with its own message, distinct from a name this tool has never heard
//! of at all — the same distinction `nat_axiom_inventory` draws, for the same
//! reason: collapsing "known, not built this run" and "not a prelude at all"
//! into one message is exactly how a real coverage hole (`cpoint` in that
//! tool, until 2026-08-25) hid behind a typo-shaped error text.
//!
//! `--include-constructed` needs `--release`, same as `nat_axiom_inventory`:
//! measured 2026-08-25, a **debug** build with the flag aborts with "thread
//! 'main' has overflowed its stack" (exit 134) building `creal`/`complex`/
//! `cpoint`'s deep recursion; `--release` builds all three cleanly. This is
//! not new to this change — the same debug-build abort reproduces on
//! unmodified `nat_axiom_inventory --include-constructed` — but it now also
//! applies here since coverage was extended to match.
//!
//! No hard-coded population sizes live here otherwise (ADR-0465). They did:
//! `integer` was pinned at 34, the Int development was proved down to 1, and
//! this example — which `scripts/gen-lean-axiom-ledger.py` shells out to —
//! spent two days exiting 101 because nothing checked its status. An
//! `assert_eq!` in an emit path is not a gate; it is an outage that fires when
//! the number *improves*. The by-value pin for the published ledger total
//! lives in the ledger manifest, derived from this output rather than written
//! down, and enforced by `gen-lean-axiom-ledger.py --check`; the
//! `--expect-axioms`/`--require-axiom-free` flags here are a second,
//! independent check available to any direct caller of this binary.

use std::process::ExitCode;

use axeyum_lean_kernel::{
    Declaration, Kernel, build_arith_prelude, build_complex_prelude, build_cpoint_prelude,
    build_creal_prelude, build_int_prelude, build_logic_prelude, build_nat_prelude,
    build_rat_prelude, build_string_prelude,
};

/// Preludes this example builds on EVERY run, in build order. Mirrors
/// `nat_axiom_inventory::ALWAYS_BUILT_PRELUDES` (module doc: same coverage,
/// deliberately different filter).
const ALWAYS_BUILT_PRELUDES: [&str; 6] = ["logic", "nat", "axreal", "integer", "rat", "string"];

/// Preludes built only under `--include-constructed` (module doc: cost).
const CONSTRUCTED_PRELUDES: [&str; 3] = ["creal", "complex", "cpoint"];

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for &byte in bytes {
        output.push(char::from(DIGITS[usize::from(byte >> 4)]));
        output.push(char::from(DIGITS[usize::from(byte & 0x0f)]));
    }
    output
}

/// One row: prelude label, declaration name, canonical type. Three fields —
/// `gen-lean-axiom-ledger.py::parse_axiom_rows` requires exactly this shape
/// on stdout (module doc); do not widen it.
type Row = (String, String, String);

/// `Declaration::Axiom` only — deliberately, see module doc.
fn inventory(prelude: &str, kernel: &Kernel) -> Vec<Row> {
    let mut rows: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, ty, .. } => Some((
                prelude.to_owned(),
                kernel.display_name(*name).to_string(),
                kernel.render_lean(*ty),
            )),
            _ => None,
        })
        .collect();
    rows.sort();
    rows
}

/// `--require-axiom-free <prelude>`, `--expect-axioms <prelude>=<n>`, and
/// whether the constructed groups were asked for. Same shape as
/// `nat_axiom_inventory::Expectations`.
struct Expectations {
    expected: Vec<(String, usize)>,
    include_constructed: bool,
}

fn parse_args() -> Result<Expectations, String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut expected = Vec::new();
    let mut include_constructed = false;
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--include-constructed" => include_constructed = true,
            "--require-axiom-free" => {
                let label = iter
                    .next()
                    .ok_or_else(|| "--require-axiom-free needs a prelude name".to_owned())?;
                expected.push((label.clone(), 0));
            }
            "--expect-axioms" => {
                let spec = iter
                    .next()
                    .ok_or_else(|| "--expect-axioms needs <prelude>=<n>".to_owned())?;
                let (label, raw) = spec.split_once('=').ok_or_else(|| {
                    format!("--expect-axioms expects <prelude>=<n>, got {spec:?}")
                })?;
                let count = raw
                    .parse()
                    .map_err(|_| format!("--expect-axioms expects a number, got {raw:?}"))?;
                expected.push((label.to_owned(), count));
            }
            other => return Err(format!("unknown argument {other:?}")),
        }
    }
    Ok(Expectations {
        expected,
        include_constructed,
    })
}

type NamedRows = (&'static str, Vec<Row>);

/// The constructed `creal`/`complex`/`cpoint` groups, or empty if not asked
/// for. Mirrors `nat_axiom_inventory::constructed`.
fn constructed(include: bool) -> Vec<NamedRows> {
    if !include {
        return Vec::new();
    }
    let mut creal = Kernel::new();
    let _ = build_creal_prelude(&mut creal).expect("CReal prelude must build");
    let creal_rows = inventory("creal", &creal);

    let mut complex = Kernel::new();
    let _ = build_complex_prelude(&mut complex).expect("Complex prelude must build");
    let complex_rows = inventory("complex", &complex);

    let mut cpoint = Kernel::new();
    let _ = build_cpoint_prelude(&mut cpoint).expect("CPoint prelude must build");
    let cpoint_rows = inventory("cpoint", &cpoint);

    vec![
        (CONSTRUCTED_PRELUDES[0], creal_rows),
        (CONSTRUCTED_PRELUDES[1], complex_rows),
        (CONSTRUCTED_PRELUDES[2], cpoint_rows),
    ]
}

fn main() -> ExitCode {
    let expectations = match parse_args() {
        Ok(expectations) => expectations,
        Err(message) => {
            eprintln!("error: {message}");
            return ExitCode::FAILURE;
        }
    };

    let mut logic_only = Kernel::new();
    let _ = build_logic_prelude(&mut logic_only).expect("logic prelude must build");
    let logic_rows = inventory("logic", &logic_only);

    let mut nat = Kernel::new();
    let _ = build_nat_prelude(&mut nat).expect("Nat prelude must build");
    let nat_rows = inventory("nat", &nat);

    let mut real = Kernel::new();
    let _ = build_arith_prelude(&mut real).expect("AxReal prelude must build");
    let real_rows = inventory("axreal", &real);

    let mut integer = Kernel::new();
    let _ = build_int_prelude(&mut integer).expect("Int prelude must build");
    let integer_rows = inventory("integer", &integer);

    let mut rational = Kernel::new();
    let _ = build_rat_prelude(&mut rational).expect("Rat prelude must build");
    let rational_rows = inventory("rat", &rational);

    let mut string = Kernel::new();
    let logic = build_logic_prelude(&mut string).expect("logic prelude must build");
    let _ = build_string_prelude(&mut string, logic, 2).expect("string prelude must build");
    let string_rows = inventory("string", &string);

    let constructed_rows = constructed(expectations.include_constructed);

    let always_built: [(&str, &Vec<Row>); 6] = [
        (ALWAYS_BUILT_PRELUDES[0], &logic_rows),
        (ALWAYS_BUILT_PRELUDES[1], &nat_rows),
        (ALWAYS_BUILT_PRELUDES[2], &real_rows),
        (ALWAYS_BUILT_PRELUDES[3], &integer_rows),
        (ALWAYS_BUILT_PRELUDES[4], &rational_rows),
        (ALWAYS_BUILT_PRELUDES[5], &string_rows),
    ];
    let mut groups: Vec<(&str, &Vec<Row>)> = always_built.to_vec();
    for (label, rows) in &constructed_rows {
        groups.push((label, rows));
    }
    let groups = groups;

    let mut rows: Vec<_> = groups.iter().flat_map(|(_, r)| (*r).clone()).collect();
    rows.sort();
    rows.dedup();
    for (prelude, name, canonical_type) in &rows {
        println!("{prelude}\t{name}\t{}", hex(canonical_type.as_bytes()));
    }

    for (label, group) in &groups {
        eprintln!("{label}: axiom={}", group.len());
    }

    if check_expectations(&groups, &expectations.expected) {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// Turn the printed numbers into checks and return whether any failed. Same
/// known-vs-unknown distinction as `nat_axiom_inventory::check_expectations`.
fn check_expectations(groups: &[(&str, &Vec<Row>)], expected_list: &[(String, usize)]) -> bool {
    let known_preludes: Vec<&str> = ALWAYS_BUILT_PRELUDES
        .iter()
        .chain(CONSTRUCTED_PRELUDES.iter())
        .copied()
        .collect();
    let mut failed = false;
    for (label, expected) in expected_list {
        let Some((_, group)) = groups.iter().find(|(name, _)| name == label) else {
            if known_preludes.contains(&label.as_str()) {
                eprintln!(
                    "error: {label:?} is a known prelude but was NOT built this run \
                     (known: {}) -- `creal`, `complex`, and `cpoint` need \
                     --include-constructed; refusing to report a check that never ran",
                    known_preludes.join(", ")
                );
            } else {
                eprintln!(
                    "error: {label:?} is not a prelude this tool knows about at all \
                     (known: {}) -- this is a different failure from a known prelude \
                     this run did not build; check the name for a typo",
                    known_preludes.join(", ")
                );
            }
            failed = true;
            continue;
        };
        let found = group.len();
        if found == *expected {
            eprintln!("ok: {label} axiom rows = {found}");
        } else {
            eprintln!(
                "error: {label} axiom rows = {found}, expected {expected} \
                 (a growth means something previously proved is now assumed; a \
                 shrink means this expectation is stale)"
            );
            failed = true;
        }
    }
    failed
}
