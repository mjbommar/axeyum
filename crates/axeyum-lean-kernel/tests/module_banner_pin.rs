//! **The one place a module-header change is seen.**
//!
//! Every Lean module this kernel renders opens with the same fixed banner. That
//! makes it shared text sitting under every golden pin in the workspace at once,
//! and three times now a commit has changed it for a good reason and re-pinned
//! only the golden that happened to sit in a gate:
//!
//! * `0fc7cc357` (2026-08-15) — diagnosed by `6389e0194`, three suites red;
//! * `b760fd6ae` (2026-08-17) +863 bytes, the codegen constants;
//! * `46724faec` (2026-08-18) +777 bytes, `set_option maxRecDepth 65536`.
//!
//! The last two shipped the same +1,640 onto four unrelated goldens, and `main`
//! was red for a day until the first completed `scripts/local-ci.sh` run found
//! it. Every one of those producers was *right*; none had anywhere to notice
//! what else they had moved.
//!
//! So the banner is now pinned as **committed text**, here, once. A header
//! change fails this suite and nothing else — the golden suites pin the module
//! *body* (`tests/support/lean_golden.rs`) and no longer move with the header —
//! and the failure is a text diff of the header itself, which is exactly the
//! thing that should be read and waved through deliberately rather than
//! re-derived from a moved integer.
//!
//! Re-bless, then READ THE DIFF:
//!
//! ```text
//! AXEYUM_BLESS_LEAN_FIXTURES=1 cargo test -p axeyum-lean-kernel --test module_banner_pin
//! git diff crates/axeyum-lean-kernel/tests/fixtures/module-banner
//! ```
//!
//! The same environment variable blesses the seventeen whole-module fixtures in
//! `axeyum-solver` (`src/reconstruct/tests.rs`), so one variable re-pins every
//! blessable golden in the workspace and each one still costs a reviewed diff.

use std::path::{Path, PathBuf};

#[path = "support/lean_golden.rs"]
mod lean_golden;

/// The module name the `Importing` fixture is rendered against. Any fixed name
/// works; it appears verbatim in the banner, which is the point of pinning it.
const IMPORTED_MODULE: &str = "AxeyumShared";

/// `"+1640"` / `"-12"`, without a lossy cast.
fn byte_delta(from: usize, to: usize) -> String {
    if to >= from {
        format!("+{}", to - from)
    } else {
        format!("-{}", from - to)
    }
}

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/module-banner")
}

/// The three shapes, by fixture stem.
fn banners() -> Vec<(&'static str, String)> {
    vec![
        (
            "self-contained",
            axeyum_lean_kernel::self_contained_module_banner(),
        ),
        (
            "shared-prelude",
            axeyum_lean_kernel::shared_prelude_module_banner(),
        ),
        (
            "importing",
            axeyum_lean_kernel::importing_module_banner(IMPORTED_MODULE),
        ),
    ]
}

#[test]
fn every_banner_shape_matches_its_committed_text() {
    let bless = std::env::var("AXEYUM_BLESS_LEAN_FIXTURES").as_deref() == Ok("1");
    let shapes = banners();
    assert_eq!(shapes.len(), 3, "three banner shapes are pinned");
    for (stem, banner) in shapes {
        let path = fixture_dir().join(format!("{stem}.banner"));
        if bless {
            std::fs::create_dir_all(fixture_dir()).expect("create banner fixture directory");
            std::fs::write(&path, &banner).expect("write blessed banner fixture");
            continue;
        }
        let expected = std::fs::read_to_string(&path).unwrap_or_else(|error| {
            panic!(
                "missing module-banner fixture {}: {error}\n\
                 regenerate with AXEYUM_BLESS_LEAN_FIXTURES=1 and review the diff",
                path.display()
            )
        });
        if expected == banner {
            continue;
        }
        let first_difference = expected
            .lines()
            .zip(banner.lines())
            .enumerate()
            .find(|(_, (fixture, rendered))| fixture != rendered)
            .map_or_else(
                || {
                    format!(
                        "line counts differ: fixture {}, rendered {}",
                        expected.lines().count(),
                        banner.lines().count()
                    )
                },
                |(index, (fixture, rendered))| {
                    format!(
                        "first difference at line {}:\n  fixture:  {fixture}\n  rendered: {rendered}",
                        index + 1
                    )
                },
            );
        panic!(
            "the {stem} module banner moved by {} bytes ({} -> {}).\n{first_difference}\n\n\
             This text opens EVERY module this kernel renders, so a change here is a change to \
             every exported module at once. If it is intended: regenerate with \
             AXEYUM_BLESS_LEAN_FIXTURES=1, read `git diff {}`, and say in the commit message what \
             the new lines are for and which Lean version needs them. Golden BODY pins do not \
             move with this and must not be re-pinned for it.",
            byte_delta(expected.len(), banner.len()),
            expected.len(),
            banner.len(),
            fixture_dir().display(),
        );
    }
}

/// The banner fixtures must exist as files on disk. A pin whose fixture
/// directory has been emptied is a green run over nothing, which is this
/// repository's signature failure mode.
#[test]
fn the_banner_fixtures_are_committed_files() {
    if std::env::var("AXEYUM_BLESS_LEAN_FIXTURES").as_deref() == Ok("1") {
        // A bless run WRITES the fixtures; asserting their presence during one
        // is a race against the sibling test, not a check. (It failed exactly
        // that way on the first bless, which is why this is here.)
        println!("blessing: fixture inventory not asserted on a bless run");
        return;
    }
    let found: Vec<PathBuf> = std::fs::read_dir(fixture_dir())
        .expect("the module-banner fixture directory must exist")
        .map(|entry| entry.expect("readable entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "banner"))
        .collect();
    assert_eq!(
        found.len(),
        3,
        "expected one fixture per banner shape, found {found:?}"
    );
    for path in found {
        let text = std::fs::read_to_string(&path).expect("readable banner fixture");
        assert!(
            text.contains("prelude\n"),
            "{}: a module banner must open Lean's `prelude` mode",
            path.display()
        );
    }
}

/// The banner must be exactly the prefix `split_module_banner` removes, in all
/// three shapes — that identity is what lets a golden pin cover the body alone
/// without silently dropping the header from every check in the workspace.
#[test]
fn split_module_banner_removes_exactly_the_banner() {
    for (stem, banner) in banners() {
        let source = format!("{banner}theorem axeyum_refutation : False := body\n");
        let (split_banner, body) = axeyum_lean_kernel::split_module_banner(&source)
            .unwrap_or_else(|| panic!("{stem}: a rendered banner must split"));
        assert_eq!(split_banner, banner, "{stem}: banner half");
        assert_eq!(
            body, "theorem axeyum_refutation : False := body\n",
            "{stem}: body half"
        );
        assert_eq!(
            format!("{split_banner}{body}"),
            source,
            "{stem}: the split is a partition"
        );
    }
}

/// A source that does NOT carry this kernel's banner is refused rather than
/// treated as a body-only pin. Without this, dropping the banner from the golden
/// pins would mean dropping it from every check in the workspace.
#[test]
fn a_foreign_or_mangled_header_is_refused() {
    assert!(axeyum_lean_kernel::split_module_banner("prelude\ntheorem t : False := x\n").is_none());
    assert!(axeyum_lean_kernel::split_module_banner("").is_none());
    let mangled = axeyum_lean_kernel::self_contained_module_banner().replace("prelude\n", "");
    assert!(axeyum_lean_kernel::split_module_banner(&format!("{mangled}body\n")).is_none());
    // The imported module NAME is read from the source, so a query module for any
    // shared development splits -- but the rest of the importing banner is fixed
    // text and one changed byte in it is refused like any other.
    let importing = axeyum_lean_kernel::importing_module_banner(IMPORTED_MODULE);
    assert!(axeyum_lean_kernel::split_module_banner(&format!("{importing}body\n")).is_some());
    let renamed = axeyum_lean_kernel::importing_module_banner("SomeOtherModule");
    assert!(axeyum_lean_kernel::split_module_banner(&format!("{renamed}body\n")).is_some());
    let tampered = importing.replace("noncomputable section", "noncomputable  section");
    assert_ne!(
        tampered, importing,
        "the tamper must actually change a byte"
    );
    assert!(axeyum_lean_kernel::split_module_banner(&format!("{tampered}body\n")).is_none());
}

/// The body pin must REJECT a wrong expectation.
///
/// Deleting the comparison inside [`lean_golden::assert_golden_module`] makes
/// all twenty-five tests in the five golden suites pass — measured, not feared:
/// an assertion's removal is invisible to the assertion. So the helper needs a
/// control of its own, and this is it. Without it the central mechanism of this
/// whole change would be the one thing nothing could catch.
#[test]
#[should_panic(expected = "PROOF BODY moved")]
fn a_wrong_body_pin_is_rejected() {
    let source = format!(
        "{}theorem axeyum_refutation : False := body\n",
        axeyum_lean_kernel::self_contained_module_banner()
    );
    lean_golden::assert_golden_module("control", &source, (1, 2));
}

/// ...and ACCEPT the right one, so the test above cannot be satisfied by a
/// helper that panics unconditionally.
#[test]
fn the_right_body_pin_is_accepted() {
    let body = "theorem axeyum_refutation : False := body\n";
    let source = format!(
        "{}{body}",
        axeyum_lean_kernel::self_contained_module_banner()
    );
    lean_golden::assert_golden_module(
        "control",
        &source,
        (body.len(), lean_golden::fnv1a64(body.as_bytes())),
    );
}

/// The digest the golden pins use, pinned against a hand-computed vector so a
/// changed constant cannot silently re-base every golden at once.
#[test]
fn the_golden_digest_is_fnv1a64() {
    assert_eq!(lean_golden::fnv1a64(b""), 0xcbf2_9ce4_8422_2325);
    assert_eq!(lean_golden::fnv1a64(b"a"), 0xaf63_dc4c_8601_ec8c);
    assert_eq!(lean_golden::fnv1a64(b"foobar"), 0x8594_4171_f739_67e8);
}
