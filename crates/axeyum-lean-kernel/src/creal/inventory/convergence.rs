//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/convergence.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/convergence.rs` adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal/convergence.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.Converges", p.converges, "def"),
        ("CReal.converges_unique", p.converges_unique, "theorem"),
        ("CReal.converges_of_close", p.converges_of_close, "theorem"),
        ("CReal.converges_of_const", p.converges_of_const, "theorem"),
        ("CReal.converges_of_equiv", p.converges_of_equiv, "theorem"),
        ("CReal.Cauchy", p.cauchy, "def"),
        ("CReal.converges_cauchy", p.converges_cauchy, "theorem"),
        ("CReal.converges_add", p.converges_add, "theorem"),
        ("CReal.converges_neg", p.converges_neg, "theorem"),
        ("CReal.converges_sub", p.converges_sub, "theorem"),
        ("CReal.converges_squeeze", p.converges_squeeze, "theorem"),
        (
            "CReal.converges_lower_bound",
            p.converges_lower_bound,
            "theorem",
        ),
        (
            "CReal.converges_lower_bound_shift",
            p.converges_lower_bound_shift,
            "theorem",
        ),
        (
            "CReal.converges_upper_bound",
            p.converges_upper_bound,
            "theorem",
        ),
        ("CReal.converges_le", p.converges_le, "theorem"),
        ("CReal.Bounded", p.bounded, "def"),
        ("CReal.converges_bounded", p.converges_bounded, "theorem"),
        ("CReal.converges_mul", p.converges_mul, "theorem"),
        ("CReal.ContinuousAt", p.continuous_at, "def"),
        ("CReal.continuous_id", p.continuous_id, "theorem"),
        ("CReal.continuous_const", p.continuous_const, "theorem"),
        ("CReal.continuous_add", p.continuous_add, "theorem"),
        ("CReal.continuous_mul", p.continuous_mul, "theorem"),
        ("CReal.continuous_comp", p.continuous_comp, "theorem"),
        (
            "CReal.converges_comp_eventually",
            p.converges_comp_eventually,
            "theorem",
        ),
        (
            "CReal.regular_of_scaled_cauchy",
            p.regular_of_scaled_cauchy,
            "theorem",
        ),
        (
            "CReal.converges_of_scaled_cauchy",
            p.converges_of_scaled_cauchy,
            "theorem",
        ),
        (
            "CReal.converges_of_cauchy",
            p.converges_of_cauchy,
            "theorem",
        ),
    ]
}
