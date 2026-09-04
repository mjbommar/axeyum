//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/omniscience.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single pinned array (see
//! `creal/inventory.rs` and `CLAUDE.md`'s pin-guidance section). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/omniscience.rs` adds its
//! entry HERE and nowhere else.
//!
//! No pin: this returns a plain `Vec`, not a fixed-size array. Coverage is
//! derived from `kernel.environment()` by
//! `creal_tests::every_creal_declaration_is_checked_and_axiom_free`, both
//! directions.

/// `(display name, interned NameId, declaration kind)` for every `CReal`
/// declaration built by `crates/axeyum-lean-kernel/src/creal/omniscience.rs`.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        (
            "CReal.le_total_of_order_decision",
            p.omniscience.le_total_of_order_decision,
            "theorem",
        ),
        (
            "CReal.trichotomy_of_order_decision",
            p.omniscience.trichotomy_of_order_decision,
            "theorem",
        ),
        (
            "CReal.apart_of_not_equiv_of_order_decision",
            p.omniscience.apart_of_not_equiv_of_order_decision,
            "theorem",
        ),
        (
            "CReal.abs_cases_of_order_decision",
            p.omniscience.abs_cases_of_order_decision,
            "theorem",
        ),
    ]
}
