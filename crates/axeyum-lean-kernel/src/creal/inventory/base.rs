//! Inventory shard for `crates/axeyum-lean-kernel/src/creal.rs` (the base algebra, declared directly rather than through a `creal/*.rs` submodule).
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal.rs` (the base algebra, declared directly rather than through a `creal/*.rs` submodule) adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal.rs` (the base algebra, declared directly rather than through a `creal/*.rs` submodule).
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("Within", p.within, "def"),
        ("Regular", p.regular_pred, "inductive-or-def"),
        ("CReal", p.creal, "inductive"),
        ("CReal.mk", p.mk, "ctor"),
        ("CReal.rec", p.rec, "recursor"),
        ("CReal.seq", p.seq, "def"),
        ("CReal.regular", p.regular, "theorem"),
        ("CReal.Equiv", p.equiv, "def"),
        ("Equiv.refl", p.equiv_refl, "theorem"),
        ("Equiv.symm", p.equiv_symm, "theorem"),
        ("Equiv.trans", p.equiv_trans, "theorem"),
        ("CReal.ofRat", p.of_rat, "def"),
        ("Equiv.not_zero_one", p.not_zero_one, "theorem"),
        ("CReal.zero", p.zero, "def"),
        ("CReal.one", p.one, "def"),
        ("Equiv.of_pointwise", p.equiv_of_pointwise, "theorem"),
        ("CReal.neg", p.neg, "def"),
        ("CReal.neg_congr", p.neg_congr, "theorem"),
        ("CReal.neg_le_neg", p.neg_le_neg, "theorem"),
        ("CReal.add", p.add, "def"),
        ("CReal.add_congr", p.add_congr, "theorem"),
        ("CReal.add_comm", p.add_comm, "theorem"),
        ("CReal.add_neg", p.add_neg, "theorem"),
        ("CReal.add_zero", p.add_zero, "theorem"),
        ("CReal.add_assoc", p.add_assoc, "theorem"),
        ("CReal.ofRat_add", p.of_rat_add, "theorem"),
        ("CReal.ofRat_neg", p.of_rat_neg, "theorem"),
        ("CReal.ofRat_sub", p.of_rat_sub, "theorem"),
        ("CReal.le", p.le, "def"),
        ("CReal.le_refl", p.le_refl, "theorem"),
        ("CReal.le_trans", p.le_trans, "theorem"),
        ("CReal.add_le_add", p.add_le_add, "theorem"),
        ("CReal.le_of_equiv", p.le_of_equiv, "theorem"),
        ("CReal.equiv_of_le_le", p.equiv_of_le_le, "theorem"),
        ("CReal.not_le_one_zero", p.not_le_one_zero, "theorem"),
        ("CReal.le_add_of_nonneg", p.le_add_of_nonneg, "theorem"),
        ("CReal.lt", p.lt, "def"),
        ("CReal.lt_irrefl", p.lt_irrefl, "theorem"),
        ("CReal.lt_trans", p.lt_trans, "theorem"),
        ("CReal.lt_of_lt_of_le", p.lt_of_lt_of_le, "theorem"),
        ("CReal.lt_of_le_of_lt", p.lt_of_le_of_lt, "theorem"),
        ("CReal.le_of_lt", p.le_of_lt, "theorem"),
        ("CReal.zero_lt_one", p.zero_lt_one, "theorem"),
        (
            "CReal.add_lt_add_of_le_of_lt",
            p.add_lt_add_of_le_of_lt,
            "theorem",
        ),
        ("CReal.le_congr", p.le_congr, "theorem"),
        ("CReal.lt_congr", p.lt_congr, "theorem"),
    ]
}
