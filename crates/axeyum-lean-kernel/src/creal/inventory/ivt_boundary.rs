//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/ivt_boundary.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single pinned array (see
//! `creal/inventory.rs` and `CLAUDE.md`'s pin-guidance section). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/ivt_boundary.rs` adds
//! its entry HERE and nowhere else.
//!
//! No pin: this returns a plain `Vec`, not a fixed-size array. Coverage is
//! derived from `kernel.environment()` by
//! `creal_tests::every_creal_declaration_is_checked_and_axiom_free`, both
//! directions.

/// `(display name, interned NameId, declaration kind)` for every `CReal`
/// declaration built by `crates/axeyum-lean-kernel/src/creal/ivt_boundary.rs`.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        (
            "CReal.uniformly_continuous_max",
            p.ivt_boundary.uniformly_continuous_max,
            "theorem",
        ),
        (
            "CReal.uniformly_continuous_min",
            p.ivt_boundary.uniformly_continuous_min,
            "theorem",
        ),
        ("CReal.ivtPlateau", p.ivt_boundary.ivt_plateau, "def"),
        (
            "CReal.ivtPlateau_nonpos_at_zero",
            p.ivt_boundary.ivt_plateau_nonpos_at_zero,
            "theorem",
        ),
        (
            "CReal.ivtPlateau_nonneg_at_one",
            p.ivt_boundary.ivt_plateau_nonneg_at_one,
            "theorem",
        ),
        (
            "CReal.ivtPlateau_uniformly_continuous",
            p.ivt_boundary.ivt_plateau_uniformly_continuous,
            "theorem",
        ),
        (
            "CReal.ivt_exact_root_decides_sign",
            p.ivt_boundary.ivt_exact_root_decides_sign,
            "theorem",
        ),
    ]
}
