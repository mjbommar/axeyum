//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/extreme_value.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single pinned array (see
//! `creal/inventory.rs` and `CLAUDE.md`'s pin-guidance section). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/extreme_value.rs` adds
//! its entry HERE and nowhere else.
//!
//! No pin: this returns a plain `Vec`, not a fixed-size array. Coverage is
//! derived from `kernel.environment()` by
//! `creal_tests::every_creal_declaration_is_checked_and_axiom_free`, both
//! directions.

/// `(display name, interned NameId, declaration kind)` for every `CReal`
/// declaration built by `crates/axeyum-lean-kernel/src/creal/extreme_value.rs`.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.evtLinear", p.extreme_value.evt_linear, "def"),
        (
            "CReal.evt_attained_max_decides_sign",
            p.extreme_value.evt_attained_max_decides_sign,
            "theorem",
        ),
        (
            "CReal.evtLinear_uniformly_continuous",
            p.extreme_value.evt_linear_uniformly_continuous,
            "theorem",
        ),
    ]
}
