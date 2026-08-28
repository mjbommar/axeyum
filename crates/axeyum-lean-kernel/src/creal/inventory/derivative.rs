//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/derivative.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/derivative.rs` adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal/derivative.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.HasDerivativeOn", p.has_derivative_on, "inductive"),
        ("HasDerivativeOn.mk", p.hd_mk, "ctor"),
        ("HasDerivativeOn.rec", p.hd_rec, "recursor"),
        ("HasDerivativeOn.modulus", p.hd_modulus, "def"),
        ("HasDerivativeOn.spec", p.hd_spec, "theorem"),
        (
            "CReal.hasDerivative_const",
            p.has_derivative_const,
            "theorem",
        ),
        ("CReal.hasDerivative_id", p.has_derivative_id, "theorem"),
        ("CReal.hasDerivative_sq", p.has_derivative_sq, "theorem"),
        ("CReal.hasDerivative_neg", p.has_derivative_neg, "theorem"),
        ("CReal.hasDerivative_add", p.has_derivative_add, "theorem"),
        (
            "CReal.abs_mul_le_of_bounds",
            p.abs_mul_le_of_bounds,
            "theorem",
        ),
        ("CReal.BoundedOn", p.bounded_on, "def"),
        ("CReal.bounded_on_unfold", p.bounded_on_unfold, "theorem"),
        ("CReal.bounded_on_mul", p.bounded_on_mul, "theorem"),
        ("CReal.bounded_on_add", p.bounded_on_add, "theorem"),
        ("CReal.hasDerivative_smul", p.has_derivative_smul, "theorem"),
        ("CReal.hasDerivative_sub", p.has_derivative_sub, "theorem"),
        ("CReal.hasDerivative_mul", p.has_derivative_mul, "theorem"),
        (
            "CReal.hasDerivative_congr",
            p.has_derivative_congr,
            "theorem",
        ),
        (
            "CReal.hasDerivative_pow_two",
            p.has_derivative_pow_two,
            "theorem",
        ),
        ("CReal.hasDerivative_cube", p.has_derivative_cube, "theorem"),
        ("CReal.hasDerivative_pow", p.has_derivative_pow, "theorem"),
        (
            "CReal.hasDerivative_chain",
            p.has_derivative_chain,
            "theorem",
        ),
        (
            "CReal.hasDerivative_chain_id_sq",
            p.has_derivative_chain_id_sq,
            "theorem",
        ),
        (
            "CReal.hasDerivative_integral_const",
            p.has_derivative_integral_const,
            "theorem",
        ),
        (
            "CReal.abs_diff_le_of_deriv_bound",
            p.abs_diff_le_of_deriv_bound,
            "theorem",
        ),
    ]
}
