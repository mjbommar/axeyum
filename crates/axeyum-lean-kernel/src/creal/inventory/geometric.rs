//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/geometric.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/geometric.rs` adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal/geometric.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        (
            "CReal.geom_tail_bounded_div",
            p.geom_tail_bounded_div,
            "theorem",
        ),
        ("CReal.geom_tail_within", p.geom_tail_within, "theorem"),
        (
            "CReal.geom_tail_within_le",
            p.geom_tail_within_le,
            "theorem",
        ),
        ("CReal.geom_pair_within", p.geom_pair_within, "theorem"),
        (
            "CReal.pow_le_pow_of_base_le",
            p.pow_le_pow_of_base_le,
            "theorem",
        ),
        ("CReal.ofRat_pow", p.of_rat_pow, "theorem"),
        (
            "CReal.pow_half_le_natDivSucc",
            p.pow_half_le_nat_div_succ,
            "theorem",
        ),
        (
            "CReal.pow_le_natDivSucc_of_lt",
            p.pow_le_nat_div_succ_of_lt,
            "theorem",
        ),
        ("CReal.ratioDecayBound", p.ratio_decay_bound, "theorem"),
        ("CReal.invLeOfPosBound", p.inv_le_of_pos_bound, "theorem"),
        ("CReal.geomYBound", p.geom_y_bound, "theorem"),
        ("CReal.geomYBoundRaw", p.geom_y_bound_raw, "theorem"),
        (
            "CReal.pow_le_natDivSucc_of_gap",
            p.pow_le_nat_div_succ_of_gap,
            "theorem",
        ),
        (
            "CReal.geomCauchyOfLtOrdered",
            p.geom_cauchy_of_lt_ordered,
            "theorem",
        ),
        (
            "CReal.geomCauchyOrderedOfGap",
            p.geom_cauchy_ordered_of_gap,
            "theorem",
        ),
        ("CReal.geomCauchyOfLt", p.geom_cauchy_of_lt, "theorem"),
    ]
}
