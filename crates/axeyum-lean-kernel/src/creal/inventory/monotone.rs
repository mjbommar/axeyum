//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/monotone.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/monotone.rs` adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal/monotone.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        (
            "CReal.sumRange_telescope_ge",
            p.sum_range_telescope_ge,
            "theorem",
        ),
        (
            "CReal.sumRange_telescope_le",
            p.sum_range_telescope_le,
            "theorem",
        ),
        (
            "CReal.hasDerivative_closeOfEquiv",
            p.has_derivative_close_of_equiv,
            "theorem",
        ),
        ("CReal.sumRange_const", p.sum_range_const, "theorem"),
        ("CReal.mesh_count_width", p.mesh_count_width, "theorem"),
        (
            "CReal.subdivisionPoint_in_bounds",
            p.subdivision_point_in_bounds,
            "theorem",
        ),
        (
            "CReal.monotone_of_nonneg_deriv",
            p.monotone_of_nonneg_deriv,
            "theorem",
        ),
        (
            "CReal.strict_mono_of_pos_deriv",
            p.strict_mono_of_pos_deriv,
            "theorem",
        ),
        (
            "CReal.strict_mono_magnitude",
            p.strict_mono_magnitude,
            "theorem",
        ),
        ("CReal.scale_cancel_le", p.scale_cancel_le, "theorem"),
        (
            "CReal.diff_le_of_strict_mono_magnitude",
            p.diff_le_of_strict_mono_magnitude,
            "theorem",
        ),
        (
            "CReal.strict_injective_of_pos_deriv",
            p.strict_injective_of_pos_deriv,
            "theorem",
        ),
        (
            "CReal.inverse_lipschitz_of_pos_deriv",
            p.inverse_lipschitz_of_pos_deriv,
            "theorem",
        ),
        (
            "CReal.constant_of_zero_deriv",
            p.constant_of_zero_deriv,
            "theorem",
        ),
        (
            "CReal.antitone_of_nonpos_deriv",
            p.antitone_of_nonpos_deriv,
            "theorem",
        ),
        (
            "CReal.strict_antitone_of_neg_deriv",
            p.strict_antitone_of_neg_deriv,
            "theorem",
        ),
        ("CReal.strict_mono_comp", p.strict_mono_comp, "theorem"),
    ]
}
