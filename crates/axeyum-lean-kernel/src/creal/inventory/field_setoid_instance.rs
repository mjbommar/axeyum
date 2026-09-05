//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/field_setoid_instance.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single pinned array
//! (see `creal/inventory.rs`'s module docs for why). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/field_setoid_instance.rs`
//! adds its entry HERE and nowhere else.

/// `(display name, interned NameId, declaration kind)` for every `CReal`
/// declaration built by
/// `crates/axeyum-lean-kernel/src/creal/field_setoid_instance.rs` (ADR-1627).
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.apart_compat", p.field_s.apart_compat, "thm"),
        ("CReal.one_apart_zero", p.field_s.one_apart_zero, "thm"),
        (
            "CReal.pos_of_neg_lt_zero",
            p.field_s.pos_of_neg_lt_zero,
            "thm",
        ),
        ("CReal.mulInvEx", p.field_s.mul_inv_ex, "thm"),
        ("CReal.fieldS", p.field_s.field_s, "def"),
    ]
}
