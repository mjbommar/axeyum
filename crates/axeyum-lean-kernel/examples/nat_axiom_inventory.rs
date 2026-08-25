//! Emit the axiom population of the **Nat** reconstruction prelude.
//!
//! `prelude_axiom_inventory` covers `real`, `integer` and `string` only, and the
//! ledger (`scripts/gen-lean-axiom-ledger.py`) inherited exactly that coverage
//! until this example was written.  So the layer this project makes its strongest
//! claim about — a Nat
//! development with an empty axiom footprint — was the one layer no inventory
//! measured.  Reading zero Nat rows out of the existing inventory says only
//! "never enumerated", not "axiom-free"; the two are indistinguishable in that
//! output, and the difference is the whole claim.
//!
//! Output is `prelude<TAB>kind<TAB>name<TAB>canonical-type-utf8-as-hex`, sorted.
//! The extra `kind` column against `prelude_axiom_inventory` is deliberate: this
//! enumerates the whole trusted surface, not `Declaration::Axiom` alone (see
//! [`inventory`]).  For `nat` and `logic` an EMPTY body is the expected — and
//! meaningful — result, so the per-prelude counts go to stderr where they cannot
//! contaminate it, and an empty stdout is never ambiguous.
//!
//! `build_nat_prelude` builds the logic prelude first, so the `nat` group covers
//! the whole environment a Nat proof actually rests on; `logic` is enumerated
//! separately so its share is attributable rather than silently folded in.
//!
//! Measured 2026-08-14: `logic` and `nat` are 0 across all three trusted kinds,
//! and `real`/`integer`/`string` reproduced the ledger's then-committed 30/34/1
//! — so the ledger's `Axiom`-only filter is not, in fact, under-binding today.
//! Re-measured 2026-08-15: **30/1/1**. `integer` fell 34 -> 1 as the Int
//! development was proved out, and `prelude_axiom_inventory` still asserted 34,
//! so it had been exiting 101 unnoticed.
//!
//! # Printing a number is not asserting it
//!
//! Until 2026-08-15 this example printed `nat: axiom=0 …` and exited **0**
//! whatever the number was. `axiom_footprint: []` on 31 kernel-lean facts — the
//! headline claim of this project — was therefore asserted by nothing: the
//! `checker_command` could not tell axiom-freedom from a kernel that had grown
//! twenty axioms overnight.
//!
//! Two flags turn the print into a check. Both fail if the named prelude was
//! never enumerated, so a typo is an error rather than a silent pass — the
//! standing trap that "an empty result from a tool that was never pointed at
//! your subject is indistinguishable from a strong negative result".
//!
//! ```sh
//! nat_axiom_inventory --require-axiom-free nat --require-axiom-free logic
//! nat_axiom_inventory --expect-axioms real=30 --expect-axioms integer=1
//! ```
//!
//! `--expect-axioms` is per-prelude and not a blanket zero on purpose:
//! `real=30` and `integer=1` are asserted **by design**, so the honest
//! expectation is the committed number, failing on drift in either direction.
//! Counts are over the whole trusted surface (`axiom` + `opaque` + `quotient`),
//! matching this example's stderr summary rather than `Declaration::Axiom`
//! alone.
//!
//! Measured 2026-08-15: `logic=0`, `nat=0`, `real=30`, `integer=1`, `string=1`.
//!
//! Re-measured 2026-08-17 with `rat` added: `logic=0`, `nat=0`, `integer=0`,
//! **`rat=0`**, `real=30`, `string=1`. `rat` is the ordered field ℚ built over
//! the constructed ℤ (`build_rat_prelude`), and it is enumerated as its own
//! group for exactly the reason this file exists: a zero read off the
//! `integer` row says nothing about the development built on top of it.
//!
//! # `real` here is the AXIOMATIZED package, not the constructed reals
//!
//! The `real=30` row is `build_arith_prelude` — the `Real` sort and its 22
//! ordered-ring laws, *assumed*. The **constructed** ℝ (`CReal`, ADR-0512) and
//! ℂ (`Complex`, ADR-0521) are different developments over different carriers,
//! and until 2026-08-18 this example did not build either, so grepping its
//! output for them returned an empty result that was indistinguishable from a
//! strong negative one — the standing trap this file exists to rule out, one
//! level further down.
//!
//! They are behind `--include-constructed` rather than always on, because they
//! cost real kernel type-checking: measured 2026-08-18, this example runs in
//! 2.3 s without the flag and **2 m 03 s** with it on a debug build, against
//! 0.23 s / 10.3 s on a release build — a 12x profile factor that matters
//! because 28 facts run this example in a `checker_command`. Without the flag,
//! `--require-axiom-free creal` is an **error**, not a silent pass:
//!
//! ```sh
//! nat_axiom_inventory --include-constructed \
//!   --require-axiom-free creal --require-axiom-free complex
//! ```
//!
//! Measured 2026-08-18: `creal=0`, `complex=0`. The self-contained check with
//! the discrimination and non-vacuity witnesses is
//! `creal_setoid_witness` / `complex_ring_witness`; this row exists so the
//! *inventory* covers them too.
//!
//! # Two numbers above are stale, and this example says so rather than quietly
//!
//! Re-measured on the same 2026-08-18 run: `integer=0` (not `1`) and
//! `string=0` (not `1`). `integer` fell when the Int development was proved out
//! and `string` when ADR-0513 made `append` a definition; the doc lines above
//! were written before each. The honest expectations today are
//! `--expect-axioms real=30` and `--require-axiom-free` for every other group.
//!
//! # Where the by-value pin actually lives: the ledger, not the facts
//!
//! Measured 2026-08-18: **28** fact files run this example in a
//! `checker_command` (31 `--require-axiom-free` occurrences), and **none** uses
//! `--expect-axioms`. That reads worse than it is, and it is worth being exact
//! about why, because the obvious remedy is the wrong one:
//!
//! * The two flags are the *same code path* — `--require-axiom-free L` pushes
//!   `(L, 0)` into the same expectation list. The only preludes any fact names
//!   are `nat` (23), `integer` (6) and `logic` (2), and all three measure 0.
//!   `--require-axiom-free nat` therefore already IS `--expect-axioms nat=0`,
//!   and nothing can fall below zero. Rewriting 28 facts would change no bit.
//! * The quantity that *can* move both ways is a global census, not a per-fact
//!   claim. Pinning it in 28 files means 28 redundant measurements of one
//!   number and 28 edits when it legitimately moves — a gate expensive enough
//!   to route around.
//!
//! So the by-value pin lives in `docs/plan/lean-axiom-ledger-v1.json`, derived
//! and gated by `scripts/gen-lean-axiom-ledger.py --check` (in both
//! `scripts/check.sh` and `just check`). Since 2026-08-18 that gate runs this
//! example **with `--include-constructed`**, pins all eight groups by value, and
//! reports a moved number with its DIRECTION: a rise is a regression, a fall is
//! a result the ledger has not published yet. Both fail; only the remedy
//! differs. `EXPECTED_PRELUDES` there lists `creal` and `complex`, so dropping
//! the flag is a gate failure rather than a quieter ledger — a pin for a group
//! the command never builds would pass vacuously.
//!
//! # `cpoint` was a second coverage hole, of exactly the same shape
//!
//! `build_cpoint_prelude` (the constructed-reals plane, ADR-0512's `CReal` one
//! level up) has existed in the crate since the `CPoint` carrier landed, but
//! this example never called it. A `CPoint` fact's `checker_command` asking
//! `nat_axiom_inventory --include-constructed --require-axiom-free cpoint`
//! got `error: "cpoint" is not enumerated by this run` -- not a zero, an
//! error -- and the `CPoint` lane worked around it with `footprint_closure_audit`
//! instead (see that example's module doc), which covers `cpoint` but has no
//! check flags at all and always exits `SUCCESS`.
//!
//! Extended 2026-08-25 to build `cpoint` alongside `creal`/`complex` under
//! `--include-constructed` (own fresh kernel, same independent-rebuild pattern
//! `rat` already uses for `integer`). Measured the same day: `cpoint=0`.
//! `ALWAYS_BUILT_PRELUDES` and `CONSTRUCTED_PRELUDES` below are now the single
//! explicit list this example builds from and reports coverage against --
//! before this change the set was an implicit `vec![...]` literal in `main`,
//! and `scripts/gen-lean-axiom-ledger.py`'s own `EXPECTED_PRELUDES` is the
//! precedent for naming such a list rather than leaving it to be inferred from
//! what a function happens to construct. `--require-axiom-free`/
//! `--expect-axioms` on an unbuilt-but-known prelude and on a genuinely
//! unknown name now print DIFFERENT error text (see `main`), so the two
//! failure shapes this example can hit are distinguishable rather than both
//! reading as "not enumerated".

use std::process::ExitCode;

use axeyum_lean_kernel::{
    Declaration, Kernel, build_arith_prelude, build_complex_prelude, build_cpoint_prelude,
    build_creal_prelude, build_int_prelude, build_logic_prelude, build_nat_prelude,
    build_rat_prelude, build_string_prelude,
};

/// Preludes this example builds on EVERY run, in build order.
///
/// This is the explicit analogue of `EXPECTED_PRELUDES` in
/// `scripts/gen-lean-axiom-ledger.py` -- there the list polices a Python
/// script's coverage of a Rust tool's output; here it is the Rust tool's own
/// coverage of the crate's `build_*_prelude` surface. Before this constant
/// existed the set was implicit in a `vec![...]` literal inside `main`, which
/// is exactly how `cpoint` (added to the crate 2026-08-2x) went unnoticed:
/// nothing enumerated "every prelude this crate ships" to diff against what
/// `main` actually builds.
const ALWAYS_BUILT_PRELUDES: [&str; 6] = ["logic", "nat", "axreal", "integer", "rat", "string"];

/// Preludes built only under `--include-constructed`, in build order.
///
/// `creal` and `complex` cost real kernel type-checking (module doc). `cpoint`
/// (the constructed-real plane, `build_cpoint_prelude`) builds `creal` a
/// SECOND time into its own fresh kernel -- the same independent-rebuild
/// pattern `rat` already uses for `integer` (`build_rat_prelude` calls
/// `build_int_prelude` internally) -- so its trusted-surface count is the
/// whole footprint `CPoint` facts actually rest on, not just its own delta.
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

/// One inventory row: prelude label, declaration kind, name, and the
/// canonical type rendered as Lean source.
type Row = (String, String, String, String);

/// Every declaration admitted **without** a checked proof body.
///
/// `prelude_axiom_inventory` filters on `Declaration::Axiom` alone, but that is
/// not the whole trusted surface: `Opaque` has no proof body to check, and
/// `Quotient` admits the quotient primitives — `Quot.sound` is literally one of
/// the three axioms Lean's own `#print axioms` reports. An `Axiom`-only count
/// can therefore read zero while trusted declarations are present, which is the
/// precise failure this example exists to rule out.
fn inventory(prelude: &str, kernel: &Kernel) -> Vec<Row> {
    let mut rows: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| {
            let (kind, name, ty) = match declaration {
                Declaration::Axiom { name, ty, .. } => ("axiom", name, ty),
                Declaration::Opaque { name, ty, .. } => ("opaque", name, ty),
                Declaration::Quotient { name, ty, .. } => ("quotient", name, ty),
                _ => return None,
            };
            Some((
                prelude.to_owned(),
                kind.to_owned(),
                kernel.display_name(*name).to_string(),
                kernel.render_lean(*ty),
            ))
        })
        .collect();
    rows.sort();
    rows
}

/// `--require-axiom-free <prelude>`, `--expect-axioms <prelude>=<n>`, and
/// whether the constructed ℝ/ℂ groups were asked for.
struct Expectations {
    /// Prelude label -> expected trusted-surface size.
    expected: Vec<(String, usize)>,
    /// `--include-constructed`: also build `CReal` and `Complex`.
    ///
    /// Off by default because the two together cost real kernel type-checking —
    /// measured 2026-08-18 at 2 m 03 s debug / 10.3 s release against 2.3 s /
    /// 0.23 s without — and 28 facts run this example in a `checker_command`.
    /// The axiom ledger passes it (on `--release`, for that 12x); the facts do
    /// not, and the doc comment above says why.
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

/// One built `(prelude-label, rows)` group. Named to keep [`constructed`] and
/// the expectation-check plumbing in `main` under clippy's type-complexity
/// budget rather than passing a bare tuple of `Option<Vec<Row>>`s around.
type NamedRows = (&'static str, Vec<Row>);

/// The **constructed** ℝ, ℂ (ADR-0512, ADR-0521), and the `CPoint` plane over
/// ℝ, or an empty list.
///
/// Separated from `main` because building all three costs real kernel
/// type-checking (module doc), and the reader should see at a glance that the
/// default path does not pay it. `cpoint` was the coverage hole this constant
/// closes: `build_cpoint_prelude` has existed in the crate since the `CPoint`
/// carrier landed, but nothing here called it, so `--require-axiom-free
/// cpoint` errored "not enumerated by this run" rather than reporting a
/// number -- indistinguishable, from the caller's side, between "never
/// measured" and "axiom-free".
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

    // `build_cpoint_prelude` builds `CRealPrelude` first into ITS OWN kernel
    // (see its doc comment) -- an independent rebuild, not a share with the
    // `creal` kernel above -- mirroring the `rat`-rebuilds-`integer` pattern
    // already used for `rat` two groups up. So this row set is the whole
    // trusted surface a CPoint theorem rests on, deduped against `creal`'s
    // rows by `main`'s final `rows.sort(); rows.dedup();`.
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

    // The logic prelude alone, so its own share is attributable rather than
    // folded into Nat's (`build_nat_prelude` builds logic first).
    let mut logic_only = Kernel::new();
    let _ = build_logic_prelude(&mut logic_only).expect("logic prelude must build");
    let logic_rows = inventory("logic", &logic_only);

    let mut nat = Kernel::new();
    let _ = build_nat_prelude(&mut nat).expect("Nat prelude must build");
    let nat_rows = inventory("nat", &nat);

    // The three preludes the existing ledger DOES cover, re-enumerated over the
    // full trusted surface rather than `Axiom` alone. A disagreement with the
    // ledger's committed counts (real=30, integer=1, string=1 as of 2026-08-15)
    // is a finding: it means the ledger binds less than it appears to.
    let mut real = Kernel::new();
    let _ = build_arith_prelude(&mut real).expect("AxReal prelude must build");
    let real_rows = inventory("axreal", &real);

    let mut integer = Kernel::new();
    let _ = build_int_prelude(&mut integer).expect("Int prelude must build");
    let integer_rows = inventory("integer", &integer);

    // ℚ, constructed over the ℤ above. Enumerated separately from `integer`
    // because the two are different claims: `integer` is the carrier the
    // rationals are built FROM, and reading a zero for it says nothing about
    // the ordered field built on top.
    let mut rational = Kernel::new();
    let _ = build_rat_prelude(&mut rational).expect("Rat prelude must build");
    let rational_rows = inventory("rat", &rational);

    let mut string = Kernel::new();
    let logic = build_logic_prelude(&mut string).expect("logic prelude must build");
    let _ = build_string_prelude(&mut string, logic, 2).expect("string prelude must build");
    let string_rows = inventory("string", &string);

    // The CONSTRUCTED ℝ, ℂ, and the CPoint plane, opt-in. `real` above is the
    // axiomatized package and says nothing about these; enumerating them under
    // the same labels would be worse than not enumerating them at all.
    let constructed_rows = constructed(expectations.include_constructed);

    // Built from the two explicit constants above, not from a fresh literal --
    // `ALWAYS_BUILT_PRELUDES`/`CONSTRUCTED_PRELUDES` are the coverage claim;
    // this is what makes the claim and the groups actually built agree by
    // construction rather than by two lists staying in sync by hand.
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
    for (prelude, kind, name, canonical_type) in &rows {
        println!(
            "{prelude}\t{kind}\t{name}\t{}",
            hex(canonical_type.as_bytes())
        );
    }

    for (label, group) in &groups {
        let count = |k: &str| group.iter().filter(|(_, kind, _, _)| kind == k).count();
        eprintln!(
            "{label}: axiom={} opaque={} quotient={} total_trusted={}",
            count("axiom"),
            count("opaque"),
            count("quotient"),
            group.len()
        );
    }

    if check_expectations(&groups, &expectations.expected) {
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// Turn the printed numbers into checks and return whether any failed.
///
/// A prelude named on the command line that this example does not enumerate
/// is an ERROR, never a silent pass: "never enumerated" and "enumerated and
/// found empty" must not print the same zero.
///
/// Two distinct failure shapes, deliberately given two distinct messages
/// (task: "asking about an unknown prelude" vs "asking about a known one
/// that is unbuilt" must be distinguishable, neither silently a zero):
///   - a label this tool has NEVER heard of (a typo, or a prelude that does
///     not exist) -- not in `ALWAYS_BUILT_PRELUDES` or `CONSTRUCTED_PRELUDES`
///     at all;
///   - a label this tool DOES know (it is in one of those two lists) but
///     this run did not build it -- today that is only `creal`/`complex`/
///     `cpoint` without `--include-constructed`, since every
///     `ALWAYS_BUILT_PRELUDES` entry is, per its name, always in `groups`.
///
/// Collapsing these into one message is exactly how `cpoint` hid: a typo'd
/// prelude and a real, un-built one printed the identical sentence.
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
            eprintln!("ok: {label} trusted surface = {found}");
        } else {
            eprintln!(
                "error: {label} trusted surface = {found}, expected {expected} \
                 (a growth means something previously proved is now assumed; a \
                 shrink means this expectation is stale)"
            );
            failed = true;
        }
    }
    failed
}
