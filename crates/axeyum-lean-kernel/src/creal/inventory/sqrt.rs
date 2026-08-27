//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/sqrt.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/sqrt.rs` adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal/sqrt.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.natSqrt", p.nat_sqrt, "def"),
        ("CReal.natSqrtSpec", p.nat_sqrt_spec, "theorem"),
        ("CReal.natSqrtLe", p.nat_sqrt_le, "theorem"),
        ("CReal.natSqrtLt", p.nat_sqrt_lt, "theorem"),
        ("CReal.sqrtApprox", p.sqrt_approx, "def"),
        (
            "CReal.sqrtApproxSqBracket",
            p.sqrt_approx_sq_bracket,
            "theorem",
        ),
        (
            "CReal.sqrtApproxKRegular",
            p.sqrt_approx_kregular,
            "theorem",
        ),
        ("CReal.sqrt", p.sqrt, "def"),
        ("CReal.sqrt_congr", p.sqrt_congr, "theorem"),
        ("CReal.sqrt_le_sqrt", p.sqrt_le_sqrt, "theorem"),
        ("CReal.sqrt_one", p.sqrt_one, "theorem"),
        ("CReal.sqrt_zero", p.sqrt_zero, "theorem"),
        ("CReal.sqrt_sq", p.sqrt_sq, "theorem"),
        ("CReal.sqrt_nonneg", p.sqrt_nonneg, "theorem"),
        ("CReal.mul_self_sqrt", p.mul_self_sqrt, "theorem"),
        ("CReal.sqrt_mul", p.sqrt_mul, "theorem"),
        ("CReal.le_of_sq_le", p.le_of_sq_le, "theorem"),
    ]
}
