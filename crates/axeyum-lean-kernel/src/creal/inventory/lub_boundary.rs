//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/lub_boundary.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single pinned array (see
//! `creal/inventory.rs` and `CLAUDE.md`'s pin-guidance section). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/lub_boundary.rs` adds
//! its entry HERE and nowhere else.
//!
//! No pin: this returns a plain `Vec`, not a fixed-size array. Coverage is
//! derived from `kernel.environment()` by
//! `creal_tests::every_creal_declaration_is_checked_and_axiom_free`, both
//! directions.

/// `(display name, interned NameId, declaration kind)` for every `CReal`
/// declaration built by `crates/axeyum-lean-kernel/src/creal/lub_boundary.rs`.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.lubSet", p.lub_set, "def"),
        ("CReal.lubSet_inhabited", p.lub_set_inhabited, "theorem"),
        ("CReal.lubSet_bounded", p.lub_set_bounded, "theorem"),
        ("CReal.lub_decides_em", p.lub_decides_em, "theorem"),
    ]
}
