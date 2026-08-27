//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/uniform_continuity.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/uniform_continuity.rs` adds its entry HERE and nowhere else — this
//! file is the only one that needs touching for a change confined to that
//! module.
//!
//! No pin: this returns a plain `Vec`, not a fixed-size array. The count that
//! used to guard against a forgotten registration is superseded by
//! `creal_tests::every_creal_declaration_is_checked_and_axiom_free`, which
//! derives coverage from `kernel.environment()` directly (both directions: a
//! declaration missing from every shard, and a shard entry naming a
//! declaration that no longer exists) plus a duplicate-across-shards check
//! `creal/inventory.rs::all_entries` cannot express with a fixed length
//! anyway. A per-shard pin would only ever compare this list against itself —
//! exactly the blind spot documented in this crate's own history.

/// `(display name, interned NameId, declaration kind)` for every `CReal`
/// declaration built by `crates/axeyum-lean-kernel/src/creal/uniform_continuity.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.abs_add_le", p.abs_add_le, "theorem"),
        (
            "CReal.UniformlyContinuousOn",
            p.uniformly_continuous_on,
            "inductive",
        ),
        ("UniformlyContinuousOn.mk", p.uc_mk, "ctor"),
        ("UniformlyContinuousOn.rec", p.uc_rec, "recursor"),
        ("UniformlyContinuousOn.modulus", p.uc_modulus, "def"),
        ("UniformlyContinuousOn.spec", p.uc_spec, "theorem"),
        (
            "CReal.uniformly_continuous_id",
            p.uniformly_continuous_id,
            "theorem",
        ),
        (
            "CReal.uniformly_continuous_const",
            p.uniformly_continuous_const,
            "theorem",
        ),
        (
            "CReal.uniformly_continuous_add",
            p.uniformly_continuous_add,
            "theorem",
        ),
        (
            "CReal.uniformly_continuous_neg",
            p.uniformly_continuous_neg,
            "theorem",
        ),
        (
            "CReal.uniformly_continuous_sub",
            p.uniformly_continuous_sub,
            "theorem",
        ),
        (
            "CReal.uniformly_continuous_mul",
            p.uniformly_continuous_mul,
            "theorem",
        ),
        (
            "CReal.uniformly_continuous_sq",
            p.uniformly_continuous_sq,
            "theorem",
        ),
        ("CReal.bounded_on_id_unit", p.bounded_on_id_unit, "theorem"),
        (
            "CReal.uniformly_continuous_poly_example",
            p.uniformly_continuous_poly_example,
            "theorem",
        ),
        (
            "CReal.mag_bound_le_sumRange_of_lt",
            p.mag_bound_le_sum_range_of_lt,
            "theorem",
        ),
        ("CReal.bucketIndex", p.bucket_index, "def"),
        (
            "CReal.bucketIndexFloorLower",
            p.bucket_index_floor_lower,
            "theorem",
        ),
        (
            "CReal.bucketIndexFloorUpper",
            p.bucket_index_floor_upper,
            "theorem",
        ),
        ("CReal.bucketClampUpper", p.bucket_clamp_upper, "theorem"),
        ("CReal.bucketClampLower", p.bucket_clamp_lower, "theorem"),
        ("CReal.bucketIndexBound", p.bucket_index_bound, "theorem"),
        ("CReal.sampleUpperBound", p.sample_upper_bound, "theorem"),
        ("CReal.sampleLowerBound", p.sample_lower_bound, "theorem"),
        (
            "CReal.bounded_of_uniformly_continuous",
            p.bounded_of_uniformly_continuous,
            "theorem",
        ),
    ]
}
