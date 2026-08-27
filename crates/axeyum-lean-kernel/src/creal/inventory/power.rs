//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/power.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/power.rs` adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal/power.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.pow", p.pow, "def"),
        ("CReal.pow_zero", p.pow_zero, "theorem"),
        ("CReal.pow_succ", p.pow_succ, "theorem"),
        ("CReal.pow_add", p.pow_add, "theorem"),
        ("CReal.pow_congr", p.pow_congr, "theorem"),
        ("CReal.pow_nonneg", p.pow_nonneg, "theorem"),
        ("CReal.pow_le_one", p.pow_le_one, "theorem"),
        ("CReal.mul_sub_one_geom", p.mul_sub_one_geom, "theorem"),
        ("CReal.geom_sum_bounded", p.geom_sum_bounded, "theorem"),
        (
            "CReal.pow_le_pow_of_le_one",
            p.pow_le_pow_of_le_one,
            "theorem",
        ),
        (
            "CReal.mul_sub_one_geom_tail",
            p.mul_sub_one_geom_tail,
            "theorem",
        ),
        ("CReal.geom_tail_bounded", p.geom_tail_bounded, "theorem"),
        (
            "CReal.one_le_pow_of_one_le",
            p.one_le_pow_of_one_le,
            "theorem",
        ),
        (
            "CReal.pow_le_pow_of_one_le",
            p.pow_le_pow_of_one_le,
            "theorem",
        ),
        ("CReal.pow_pos", p.pow_pos, "theorem"),
        ("CReal.pow_succ_lt_one", p.pow_succ_lt_one, "theorem"),
        ("CReal.pow_succ_gt_one", p.pow_succ_gt_one, "theorem"),
        (
            "CReal.not_apart_one_of_pow_succ_eq_one",
            p.not_apart_one_of_pow_succ_eq_one,
            "theorem",
        ),
    ]
}
