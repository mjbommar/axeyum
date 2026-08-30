//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/ivt.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/ivt.rs` adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal/ivt.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.ivt_step", p.ivt_step, "theorem"),
        ("CReal.ivt_iter", p.ivt_iter, "theorem"),
        ("CReal.ivt_approx", p.ivt_approx, "theorem"),
        ("CReal.ivt_bisect", p.ivt_bisect, "def"),
        ("CReal.ivt_bisect_lo", p.ivt_bisect_lo, "def"),
        ("CReal.ivt_bisect_hi", p.ivt_bisect_hi, "def"),
        (
            "CReal.ivt_bisect_invariant",
            p.ivt_bisect_invariant,
            "theorem",
        ),
        ("CReal.ivt_bisect_diag", p.ivt_bisect_diag, "def"),
        ("CReal.ivt_bisect_diag_lo", p.ivt_bisect_diag_lo, "def"),
        ("CReal.ivt_bisect_diag_hi", p.ivt_bisect_diag_hi, "def"),
        ("CReal.ivt_bisect_approx", p.ivt_bisect_approx, "theorem"),
        (
            "CReal.abs_diff_le_of_small_image",
            p.abs_diff_le_of_small_image,
            "theorem",
        ),
        (
            "CReal.ivt_bisect_cauchy_bound",
            p.ivt_bisect_cauchy_bound,
            "theorem",
        ),
        (
            "CReal.cauchy_of_abs_diff_le",
            p.cauchy_of_abs_diff_le,
            "theorem",
        ),
        (
            "CReal.scaledCauchy_of_abs_diff_le",
            p.scaled_cauchy_of_abs_diff_le,
            "theorem",
        ),
        ("CReal.ivt_bisect_cauchy", p.ivt_bisect_cauchy, "theorem"),
        ("CReal.ivt_exact_root", p.ivt_exact_root, "theorem"),
    ]
}
