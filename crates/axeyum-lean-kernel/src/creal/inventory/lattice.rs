//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/lattice.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/lattice.rs` adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal/lattice.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.max", p.max, "def"),
        ("CReal.min", p.min, "def"),
        ("CReal.abs", p.abs, "def"),
        ("CReal.le_max_left", p.le_max_left, "theorem"),
        ("CReal.le_max_right", p.le_max_right, "theorem"),
        ("CReal.max_le", p.max_le, "theorem"),
        ("CReal.min_le_left", p.min_le_left, "theorem"),
        ("CReal.min_le_right", p.min_le_right, "theorem"),
        ("CReal.le_min", p.le_min, "theorem"),
        ("CReal.max_congr", p.max_congr, "theorem"),
        ("CReal.min_congr", p.min_congr, "theorem"),
        ("CReal.abs_congr", p.abs_congr, "theorem"),
        ("CReal.le_abs_self", p.le_abs_self, "theorem"),
        ("CReal.neg_le_abs", p.neg_le_abs, "theorem"),
        ("CReal.abs_le", p.abs_le, "theorem"),
        ("CReal.abs_nonneg", p.abs_nonneg, "theorem"),
        (
            "CReal.not_le_zero_neg_one",
            p.not_le_zero_neg_one,
            "theorem",
        ),
        (
            "CReal.not_equiv_abs_neg_one",
            p.not_equiv_abs_neg_one,
            "theorem",
        ),
    ]
}
