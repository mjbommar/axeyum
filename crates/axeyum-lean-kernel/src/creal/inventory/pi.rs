//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/pi.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single pinned array (see
//! that file's module docs and `CLAUDE.md`'s pin-guidance section). Whoever
//! adds a declaration to `crates/axeyum-lean-kernel/src/creal/pi.rs` adds its
//! entry HERE and nowhere else.
//!
//! No pin: this returns a plain `Vec`, not a fixed-size array. Coverage is
//! derived from `kernel.environment()` by
//! `creal_tests::every_creal_declaration_is_checked_and_axiom_free`.

/// `(display name, interned NameId, declaration kind)` for every `CReal`
/// declaration built by `crates/axeyum-lean-kernel/src/creal/pi.rs`.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.piHalfCoef", p.pi_half_coef, "def"),
        ("CReal.piHalfTerm", p.pi_half_term, "def"),
        (
            "CReal.piHalfSeriesPartial",
            p.pi_half_series_partial,
            "def",
        ),
        (
            "CReal.piHalfCoefNonneg",
            p.pi_half_coef_nonneg,
            "theorem",
        ),
        (
            "CReal.piHalfTermNonneg",
            p.pi_half_term_nonneg,
            "theorem",
        ),
        (
            "CReal.piHalfTermLePowHalf",
            p.pi_half_term_le_pow_half,
            "theorem",
        ),
        (
            "CReal.piHalfTermAbsLeDominant",
            p.pi_half_term_abs_le_dominant,
            "theorem",
        ),
        ("CReal.piHalf", p.pi_half, "def"),
        ("CReal.piHalfConverges", p.pi_half_converges, "theorem"),
        ("CReal.pi", p.pi, "def"),
        ("CReal.piHalfLeTwo", p.pi_half_le_two, "theorem"),
        ("CReal.piLeFour", p.pi_le_four, "theorem"),
        ("CReal.twoLePi", p.two_le_pi, "theorem"),
        ("CReal.threeLePi", p.three_le_pi, "theorem"),
    ]
}
