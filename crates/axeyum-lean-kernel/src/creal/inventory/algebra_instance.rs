//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/algebra_instance.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single pinned array
//! (see `creal/inventory.rs`'s module docs for why). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/algebra_instance.rs`
//! adds its entry HERE and nowhere else.

/// `(display name, interned NameId, declaration kind)` for every `CReal`
/// declaration built by
/// `crates/axeyum-lean-kernel/src/creal/algebra_instance.rs`.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.commRingS", p.comm_ring_s, "def"),
        ("CReal.orderedRingS", p.ordered_ring_s, "def"),
    ]
}
