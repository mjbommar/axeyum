//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/supremum.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single pinned array (see
//! `creal/inventory.rs` and `CLAUDE.md`'s pin-guidance section). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/supremum.rs` adds its
//! entry HERE and nowhere else.
//!
//! No pin: this returns a plain `Vec`, not a fixed-size array. Coverage is
//! derived from `kernel.environment()` by
//! `creal_tests::every_creal_declaration_is_checked_and_axiom_free`, both
//! directions.

/// `(display name, interned NameId, declaration kind)` for every `CReal`
/// declaration built by `crates/axeyum-lean-kernel/src/creal/supremum.rs`.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.maxRange", p.max_range, "def"),
        ("CReal.maxRange_zero", p.max_range_zero, "theorem"),
        ("CReal.maxRange_succ", p.max_range_succ, "theorem"),
        ("CReal.maxRange_self_le", p.max_range_self_le, "theorem"),
        ("CReal.maxRange_mono", p.max_range_mono, "theorem"),
        ("CReal.maxRange_ub", p.max_range_ub, "theorem"),
        ("CReal.maxRange_transport", p.max_range_transport, "theorem"),
        ("CReal.meshLevelCount", p.mesh_level_count, "def"),
        (
            "CReal.meshLevelCount_zero",
            p.mesh_level_count_zero,
            "theorem",
        ),
        (
            "CReal.meshLevelCount_succ",
            p.mesh_level_count_succ,
            "theorem",
        ),
        ("CReal.meshMax", p.mesh_max, "def"),
        ("CReal.meshMax_step_le", p.mesh_max_step_le, "theorem"),
        ("CReal.meshMax_mono", p.mesh_max_mono, "theorem"),
        ("CReal.expOfModulus", p.exp_of_modulus, "def"),
        ("CReal.trueExpOfModulus", p.true_exp_of_modulus, "def"),
        (
            "CReal.trueExpOfModulus_zero",
            p.true_exp_of_modulus_zero,
            "theorem",
        ),
        (
            "CReal.trueExpOfModulus_succ",
            p.true_exp_of_modulus_succ,
            "theorem",
        ),
        (
            "CReal.trueExpOfModulus_step_le",
            p.true_exp_of_modulus_step_le,
            "theorem",
        ),
        (
            "CReal.trueExpOfModulus_mono",
            p.true_exp_of_modulus_mono,
            "theorem",
        ),
        (
            "CReal.expOfModulus_le_trueExpOfModulus",
            p.exp_of_modulus_le_true_exp_of_modulus,
            "theorem",
        ),
        (
            "CReal.meshPoint_near_coarse",
            p.mesh_point_near_coarse,
            "theorem",
        ),
    ]
}
