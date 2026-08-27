//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/exponential.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/exponential.rs` adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal/exponential.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        (
            "CReal.geomHalfInvLeafBound",
            p.geom_half_inv_leaf_bound,
            "theorem",
        ),
        (
            "CReal.geomCauchyOrderedHalf",
            p.geom_cauchy_ordered_half,
            "theorem",
        ),
        ("CReal.geomCauchy", p.geom_cauchy, "theorem"),
        ("CReal.expTerm", p.exp_term, "def"),
        ("CReal.expSeriesPartial", p.exp_series_partial, "def"),
        ("CReal.expTerm_le_geom", p.exp_term_le_geom, "theorem"),
        ("CReal.expDominant", p.exp_dominant, "def"),
        (
            "CReal.exp_term_le_dominant",
            p.exp_term_le_dominant,
            "theorem",
        ),
        ("CReal.exp_term_nonneg", p.exp_term_nonneg, "theorem"),
        (
            "CReal.exp_dominant_nonneg",
            p.exp_dominant_nonneg,
            "theorem",
        ),
        (
            "CReal.exp_term_abs_le_dominant",
            p.exp_term_abs_le_dominant,
            "theorem",
        ),
        (
            "CReal.sumRange_pow_half_closed_form",
            p.sum_pow_half_closed_form,
            "theorem",
        ),
        (
            "CReal.cauchyOfPointwiseEquiv",
            p.cauchy_of_pointwise_equiv,
            "theorem",
        ),
        ("CReal.expDominantCauchy", p.exp_dominant_cauchy, "theorem"),
        (
            "CReal.expSeriesPartialConverges",
            p.exp_series_partial_converges,
            "theorem",
        ),
        ("CReal.e", p.e, "def"),
        ("CReal.e_converges", p.e_converges, "theorem"),
        ("CReal.two_le_e", p.two_le_e, "theorem"),
        ("CReal.e_le_four", p.e_le_four, "theorem"),
        ("CReal.e_le_three", p.e_le_three, "theorem"),
    ]
}
