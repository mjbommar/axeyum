//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/trig_fn.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single pinned array (see
//! `creal/inventory.rs` and `CLAUDE.md`'s pin-guidance section). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/trig_fn.rs` adds its
//! entry HERE and nowhere else.
//!
//! No pin: this returns a plain `Vec`, not a fixed-size array. Coverage is
//! derived from `kernel.environment()` by
//! `creal_tests::every_creal_declaration_is_checked_and_axiom_free`, both
//! directions.

/// `(display name, interned NameId, declaration kind)` for every `CReal`
/// declaration built by `crates/axeyum-lean-kernel/src/creal/trig_fn.rs`.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.cosFnTerm", p.cos_fn_term, "def"),
        ("CReal.cosFnTerm_congr", p.cos_fn_term_congr, "theorem"),
        ("CReal.cosFnTermAbsLe", p.cos_fn_term_abs_le, "theorem"),
        ("CReal.cosFn", p.cos_fn, "def"),
        (
            "CReal.cosFnUniformConverges",
            p.cos_fn_uniform_converges,
            "theorem",
        ),
        (
            "CReal.cosFnTermAbsLeWide",
            p.cos_fn_term_abs_le_wide,
            "theorem",
        ),
        (
            "CReal.cosDominant16Over25",
            p.cos_dominant_16_over_25,
            "def",
        ),
        (
            "CReal.cosDominant16Over25CauchyBody",
            p.cos_dominant_16_over_25_cauchy_body,
            "theorem",
        ),
        ("CReal.powMulDistrib", p.pow_mul_distrib, "theorem"),
        ("CReal.cosFnWide", p.cos_fn_wide, "def"),
        (
            "CReal.cosFnWideUniformConverges",
            p.cos_fn_wide_uniform_converges,
            "theorem",
        ),
    ]
}
