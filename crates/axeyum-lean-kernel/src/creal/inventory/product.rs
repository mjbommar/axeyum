//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/product.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/product.rs` adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal/product.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.bound", p.bound, "def"),
        ("CReal.bound_within", p.bound_within, "theorem"),
        ("CReal.mulShift", p.mul_shift, "def"),
        ("CReal.mul", p.mul, "def"),
        ("CReal.ofRat_mul", p.of_rat_mul, "theorem"),
        ("CReal.mul_comm", p.mul_comm, "theorem"),
        ("CReal.mul_one", p.mul_one, "theorem"),
        ("CReal.mul_zero", p.mul_zero, "theorem"),
        ("CReal.mul_nonneg", p.mul_nonneg, "theorem"),
        ("CReal.sq_nonneg", p.sq_nonneg, "theorem"),
        ("CReal.neg_mul_neg", p.neg_mul_neg, "theorem"),
        ("CReal.mul_self_abs", p.mul_self_abs, "theorem"),
        (
            "CReal.not_equiv_mul_one_one_zero",
            p.not_equiv_mul_one_one_zero,
            "theorem",
        ),
        ("CReal.Equiv.of_bounded", p.equiv_of_bounded, "theorem"),
        ("CReal.mul_congr", p.mul_congr, "theorem"),
        ("CReal.left_distrib", p.left_distrib, "theorem"),
        ("CReal.mul_assoc", p.mul_assoc, "theorem"),
        (
            "CReal.mul_le_mul_of_nonneg_left",
            p.mul_le_mul_of_nonneg_left,
            "theorem",
        ),
    ]
}
