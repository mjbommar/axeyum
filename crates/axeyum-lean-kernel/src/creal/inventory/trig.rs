//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/trig.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/trig.rs` adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal/trig.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.cosTerm", p.cos_term, "def"),
        ("CReal.cosSeriesPartial", p.cos_series_partial, "def"),
        (
            "CReal.cosTermAbsLeDominant",
            p.cos_term_abs_le_dominant,
            "theorem",
        ),
        ("CReal.cosOne", p.cos_one, "def"),
        ("CReal.cosOneConverges", p.cos_one_converges, "theorem"),
        ("CReal.cosOne_le_four", p.cos_one_le_four, "theorem"),
        ("CReal.neg_four_le_cosOne", p.neg_four_le_cos_one, "theorem"),
        ("CReal.expTerm_antitone", p.exp_term_antitone, "theorem"),
        (
            "CReal.cosOne_alternating_lower",
            p.cos_one_alternating_lower,
            "theorem",
        ),
        (
            "CReal.cosOne_alternating_upper",
            p.cos_one_alternating_upper,
            "theorem",
        ),
        ("CReal.cosOne_nonneg", p.cos_one_nonneg, "theorem"),
        (
            "CReal.cosOne_le_exp_term_zero",
            p.cos_one_le_exp_term_zero,
            "theorem",
        ),
        ("CReal.sinTerm", p.sin_term, "def"),
        ("CReal.sinSeriesPartial", p.sin_series_partial, "def"),
        (
            "CReal.sinTermAbsLeDominant",
            p.sin_term_abs_le_dominant,
            "theorem",
        ),
        ("CReal.sinOne", p.sin_one, "def"),
        ("CReal.sinOneConverges", p.sin_one_converges, "theorem"),
        (
            "CReal.sinOne_alternating_lower",
            p.sin_one_alternating_lower,
            "theorem",
        ),
        (
            "CReal.sinOne_alternating_upper",
            p.sin_one_alternating_upper,
            "theorem",
        ),
        ("CReal.sinOne_nonneg", p.sin_one_nonneg, "theorem"),
        (
            "CReal.sinOne_le_exp_term_one",
            p.sin_one_le_exp_term_one,
            "theorem",
        ),
        (
            "CReal.expTerm_zero_eq_one",
            p.exp_term_zero_eq_one,
            "theorem",
        ),
        ("CReal.expTerm_one_eq_one", p.exp_term_one_eq_one, "theorem"),
    ]
}
