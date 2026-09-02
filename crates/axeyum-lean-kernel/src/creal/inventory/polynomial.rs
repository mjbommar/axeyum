//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/polynomial.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/polynomial.rs` adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal/polynomial.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.polyEval", p.polynomial.poly_eval, "def"),
        (
            "CReal.polyEval_zero",
            p.polynomial.poly_eval_zero,
            "theorem",
        ),
        (
            "CReal.polyEval_succ",
            p.polynomial.poly_eval_succ,
            "theorem",
        ),
        ("CReal.polyAdd", p.polynomial.poly_add, "def"),
        (
            "CReal.polyEval_polyAdd",
            p.polynomial.poly_eval_poly_add,
            "theorem",
        ),
        ("CReal.polyScale", p.polynomial.poly_scale, "def"),
        (
            "CReal.polyEval_polyScale",
            p.polynomial.poly_eval_poly_scale,
            "theorem",
        ),
        ("CReal.polyDegreeLt", p.polynomial.poly_degree_lt, "def"),
        (
            "CReal.polyDegreeLt_polyAdd",
            p.polynomial.poly_degree_lt_poly_add,
            "theorem",
        ),
        (
            "CReal.polyDegreeLt_polyScale",
            p.polynomial.poly_degree_lt_poly_scale,
            "theorem",
        ),
    ]
}
