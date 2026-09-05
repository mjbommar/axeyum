//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/power_series.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see `creal/inventory.rs`'s module docs for why: one array meant every
//! `creal/` lane touched the same file, and the pin conflicted or mis-merged
//! eight-plus times in one day). Whoever adds a declaration to
//! `crates/axeyum-lean-kernel/src/creal/power_series.rs` adds its entry HERE
//! and nowhere else.
//!
//! No pin: this returns a plain `Vec`, not a fixed-size array. Coverage is
//! derived from `kernel.environment()` by
//! `creal_tests::every_creal_declaration_is_checked_and_axiom_free`, in both
//! directions, so a per-shard count would only ever compare this list against
//! itself.

/// `(display name, interned NameId, declaration kind)` for every `CReal`
/// declaration built by `crates/axeyum-lean-kernel/src/creal/power_series.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.abs_pow_le", p.power_series.abs_pow_le, "theorem"),
        ("CReal.one_pow", p.power_series.one_pow, "theorem"),
        (
            "CReal.powerSeriesPartial",
            p.power_series.power_series_partial,
            "def",
        ),
        (
            "CReal.powerSeriesTermRadiusBound",
            p.power_series.power_series_term_radius_bound,
            "theorem",
        ),
        (
            "CReal.powerSeriesCauchyWithinRadius",
            p.power_series.power_series_cauchy_within_radius,
            "theorem",
        ),
        (
            "CReal.powerSeriesConvergesWithinRadius",
            p.power_series.power_series_converges_within_radius,
            "theorem",
        ),
        (
            "CReal.expSeriesPartialIsPowerSeries",
            p.power_series.exp_series_partial_is_power_series,
            "theorem",
        ),
        (
            "CReal.cosSeriesPartialIsPowerSeries",
            p.power_series.cos_series_partial_is_power_series,
            "theorem",
        ),
    ]
}
