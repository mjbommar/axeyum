//! Byte pins over a **rendered Lean module's proof body**, shared by every
//! golden-module suite in the workspace.
//!
//! # Why the body and not the module
//!
//! Every module this kernel renders opens with a fixed banner: a header comment,
//! `prelude`, `set_option` lines, and Lean's compiler-internal constants. It is
//! the same text in every module, it says nothing about any proof, and it is
//! **under every pin at once**. Twice in two days a commit changed it for a good
//! reason and re-pinned only the golden that happened to sit in a gate:
//!
//! * `b760fd6ae` +863 bytes — `unsafe axiom lcErased/lcAny/lcVoid`, without
//!   which 21 of 77 crosscheck families died under Lean 4.34.0-rc1;
//! * `46724faec` +777 bytes — `set_option maxRecDepth 65536`, without which a
//!   2,897-deep `let` chain blew Lean 4.30.0's default of 512.
//!
//! The same +1,640 landed on four unrelated goldens that nothing ran, `main` was
//! red for a day, and the first completed `scripts/local-ci.sh` run found it
//! (`artifacts/local-ci-runs/a6ee37c6a-s4.json`). `6389e0194` had diagnosed the
//! identical mechanism three days earlier for three of those same four suites.
//! Third recurrence.
//!
//! So a golden pin here covers the bytes whose producer is a *proof* change, and
//! the banner is pinned once, on its own, as committed text
//! (`tests/module_banner_pin.rs`) where a header diff is read and waved through
//! deliberately. A header change now fails exactly one thing and it names itself.
//!
//! The banner is not *dropped* from the check: [`assert_golden_module`] refuses a
//! source that does not begin with the banner this kernel emits, byte for byte.
//! A module with a mangled, hand-edited, or foreign header fails here, loudly,
//! rather than quietly passing a body-only pin.
//!
//! # Why not a committed `.lean` fixture, like `reconstruct::tests`
//!
//! That mechanism is better where it applies, and it is why the seventeen
//! fixtures under `crates/axeyum-solver/tests/fixtures/lean-modules/` rode both
//! header changes without incident — `46724faec` re-blessed all seventeen in one
//! command and the diff was the same +13 lines seventeen times. It does not
//! apply here only because of size: these five goldens render 17 KB, 114 KB,
//! 126 KB, 208 KB and **1.14 MB**, so committing them is ~1.6 MB of generated
//! proof text that churns on every re-bless. A body pin is the cheap half of the
//! same idea; the *validity* half is `lean_crosscheck`, which hands these same
//! families to a real Lean binary under `scripts/check-lean-gate.sh`.
#![allow(dead_code)]

/// `"+1640"` / `"-12"`, without a lossy cast.
#[must_use]
pub fn byte_delta(from: usize, to: usize) -> String {
    if to >= from {
        format!("+{}", to - from)
    } else {
        format!("-{}", from - to)
    }
}

/// FNV-1a 64, the digest every golden pin in this repository already used.
#[must_use]
pub fn fnv1a64(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325_u64, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

/// The rendered module's body: everything after the fixed banner.
///
/// Panics if `source` does not open with a banner this kernel emits, naming the
/// two possibilities so the reader is not left to guess which half moved.
#[must_use]
pub fn golden_module_body<'a>(case: &str, source: &'a str) -> &'a str {
    let Some((_, body)) = axeyum_lean_kernel::split_module_banner(source) else {
        panic!(
            "{case}: the rendered module does not open with this kernel's module banner.\n\
             Either the banner changed and `axeyum_lean_kernel::split_module_banner` was not \
             taught the new shape, or this source was not produced by `render_lean_module*`.\n\
             first 200 bytes of the source:\n{}",
            &source[..source.len().min(200)]
        );
    };
    body
}

/// Pin a rendered Lean module's **proof body** at `(length, fnv1a64)`.
///
/// The banner is excluded from the pinned bytes and asserted separately, so a
/// failure here means **proof text moved** — never that a header line was added.
/// Read the module-level note before re-pinning: the answer to a moved pin is a
/// reason, not a new constant.
pub fn assert_golden_module(case: &str, source: &str, expected: (usize, u64)) {
    let body = golden_module_body(case, source);
    let actual = (body.len(), fnv1a64(body.as_bytes()));
    assert_eq!(
        actual,
        expected,
        "\n{case}: the rendered module's PROOF BODY moved.\n\
         \x20 expected (len, fnv1a64) = ({}, {:#018x})\n\
         \x20 actual   (len, fnv1a64) = ({}, {:#018x})\n\
         \x20 delta                   = {} bytes\n\
         The module banner is NOT part of this pin, so a header-only change \
         (`lean_pp::write_module_banner`) cannot have caused it — that would fail \
         `axeyum-lean-kernel --test module_banner_pin` instead, and nothing else. \
         Something changed the proof text: say what, at this site, before re-pinning.\n",
        expected.0,
        expected.1,
        actual.0,
        actual.1,
        byte_delta(expected.0, actual.0),
    );
}
