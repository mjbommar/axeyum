//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/cos_sign.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single pinned array (see
//! `creal/inventory.rs` and `CLAUDE.md`'s pin-guidance section for why).
//! Whoever adds a declaration to
//! `crates/axeyum-lean-kernel/src/creal/cos_sign.rs` adds its entry HERE and
//! nowhere else.
//!
//! No pin: this returns a plain `Vec`, not a fixed-size array. Coverage is
//! checked by `creal_tests::every_creal_declaration_is_checked_and_axiom_free`
//! against `kernel.environment()` directly, in both directions.

/// `(display name, interned NameId, declaration kind)` for every `CReal`
/// declaration built by `crates/axeyum-lean-kernel/src/creal/cos_sign.rs`.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        (
            "CReal.converges_upper_bound_shift",
            p.cos_sign.converges_upper_bound_shift,
            "theorem",
        ),
        (
            "CReal.alternatingUpperBoundTail",
            p.cos_sign.alternating_upper_bound_tail,
            "theorem",
        ),
        (
            "CReal.cosWideTailNonneg",
            p.cos_sign.cos_wide_tail_nonneg,
            "theorem",
        ),
        (
            "CReal.cosWideTailAntitone",
            p.cos_sign.cos_wide_tail_antitone,
            "theorem",
        ),
        (
            "CReal.cosWideSeriesConverges",
            p.cos_sign.cos_wide_series_converges,
            "theorem",
        ),
        (
            "CReal.cosWideNonpositive",
            p.cos_sign.cos_wide_nonpositive,
            "theorem",
        ),
    ]
}
