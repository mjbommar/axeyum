//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/mvt.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single pinned array
//! (see `creal/inventory.rs`'s module docs). Whoever adds a declaration to
//! `crates/axeyum-lean-kernel/src/creal/mvt.rs` adds its entry HERE and
//! nowhere else.
//!
//! No pin: this returns a plain `Vec`. Coverage is derived from
//! `kernel.environment()` directly by
//! `creal_tests::every_creal_declaration_is_checked_and_axiom_free`.

/// `(display name, interned NameId, declaration kind)` for every `CReal`
/// declaration built by `crates/axeyum-lean-kernel/src/creal/mvt.rs`.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![(
        "CReal.mvt_interiorExtremum",
        p.mvt.mvt_interior_extremum,
        "theorem",
    )]
}
