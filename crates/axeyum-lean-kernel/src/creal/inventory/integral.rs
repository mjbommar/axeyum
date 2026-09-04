//! Inventory shard for `crates/axeyum-lean-kernel/src/creal/integral.rs`.
//!
//! Part of the per-module split of `creal_tests.rs`'s single 432-entry pinned
//! array (see that file's module docs and `CLAUDE.md`'s pin-guidance section
//! for why: one array meant every `creal/` lane touched the same file, and the
//! pin conflicted or mis-merged eight-plus times in one day). Whoever adds a
//! declaration to `crates/axeyum-lean-kernel/src/creal/integral.rs` adds its entry HERE and nowhere else — this
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
/// declaration built by `crates/axeyum-lean-kernel/src/creal/integral.rs`.
///
/// `kind` is one of `"theorem"`, `"def"`, `"ctor"`, `"recursor"`,
/// `"inductive"`, `"inductive-or-def"` — read by
/// `creal_tests::every_creal_declaration_is_checked_and_axiom_free` to assert
/// the declaration is the kind it claims and carries an empty axiom
/// footprint.
pub(crate) fn entries(p: crate::CRealPrelude) -> Vec<(&'static str, crate::NameId, &'static str)> {
    vec![
        ("CReal.riemannSum", p.riemann_sum, "def"),
        ("CReal.riemannSum_add", p.riemann_sum_add, "theorem"),
        ("CReal.mul_riemannSum", p.mul_riemann_sum, "theorem"),
        ("CReal.riemannSum_le", p.riemann_sum_le, "theorem"),
        ("CReal.riemannSum_const", p.riemann_sum_const, "theorem"),
        ("CReal.ofNat_le", p.of_nat_le, "theorem"),
        (
            "CReal.riemannSum_sample_in_bounds",
            p.riemann_sample_in_bounds,
            "theorem",
        ),
        ("CReal.riemannSum_le_on", p.riemann_sum_le_on, "theorem"),
        ("CReal.sumRange_reblock", p.sum_range_reblock, "theorem"),
        (
            "CReal.within_of_two_sided_le",
            p.within_of_two_sided_le,
            "theorem",
        ),
        (
            "CReal.le_add_of_abs_sub_le",
            p.le_add_of_abs_sub_le,
            "theorem",
        ),
        (
            "CReal.two_sided_of_abs_sub_le",
            p.two_sided_of_abs_sub_le,
            "theorem",
        ),
        ("CReal.sumRange_double", p.sum_range_double, "theorem"),
        ("CReal.ofNat_add", p.of_nat_add, "theorem"),
        ("CReal.ofNat_mul", p.of_nat_mul, "theorem"),
        ("CReal.mesh_le_of_ge", p.mesh_le_of_ge, "theorem"),
        ("CReal.meshScaledLeOfGe", p.mesh_scaled_le_of_ge, "theorem"),
        (
            "CReal.fineSample_in_bounds",
            p.fine_sample_in_bounds,
            "theorem",
        ),
        ("CReal.fineSample_close", p.fine_sample_close, "theorem"),
        (
            "CReal.fineBlockSum_close",
            p.fine_block_sum_close,
            "theorem",
        ),
        ("CReal.meshReciprocalMul", p.mesh_reciprocal_mul, "theorem"),
        ("CReal.equivAbsDiffLe", p.equiv_abs_diff_le, "theorem"),
        (
            "CReal.samplePoint_reblock",
            p.sample_point_reblock,
            "theorem",
        ),
        (
            "CReal.reblockBlock_eq_fineBlockSum",
            p.reblock_block_eq_fine_block_sum,
            "theorem",
        ),
        (
            "CReal.riemannSum_reblock_close",
            p.riemann_sum_reblock_close,
            "theorem",
        ),
        ("CReal.riemannSum_cauchy", p.riemann_sum_cauchy, "theorem"),
        (
            "CReal.sharedIndexToCanonical",
            p.shared_index_to_canonical,
            "theorem",
        ),
        (
            "CReal.riemannSum_sharedAccuracyClose",
            p.riemann_sum_shared_accuracy_close,
            "theorem",
        ),
        (
            "CReal.riemannSum_sharedAccuracyClose_at",
            p.riemann_sum_shared_accuracy_close_at,
            "theorem",
        ),
        (
            "CReal.riemannSumTotalEpsLe",
            p.riemann_sum_total_eps_le,
            "theorem",
        ),
        (
            "CReal.riemannSumDeepCauchy",
            p.riemann_sum_deep_cauchy,
            "theorem",
        ),
        (
            "CReal.riemannSumDeepCauchyFolded",
            p.riemann_sum_deep_cauchy_folded,
            "theorem",
        ),
        (
            "CReal.riemannSumDeepCauchyCross",
            p.riemann_sum_deep_cauchy_cross,
            "theorem",
        ),
        (
            "CReal.riemannSumDeepCauchyCrossFolded",
            p.riemann_sum_deep_cauchy_cross_folded,
            "theorem",
        ),
        (
            "CReal.riemannSumAddCauchyCross",
            p.riemann_sum_add_cauchy_cross,
            "theorem",
        ),
        ("CReal.integral", p.integral, "def"),
        ("CReal.integral_converges", p.integral_converges, "theorem"),
        ("CReal.integral_const", p.integral_const, "theorem"),
        (
            "CReal.integral_witness_independent",
            p.integral_witness_independent,
            "theorem",
        ),
        ("CReal.integral_add", p.integral_add, "theorem"),
        ("CReal.integral_le", p.integral_le, "theorem"),
        ("CReal.integral_split", p.integral_split, "theorem"),
        ("CReal.splitPointApprox", p.split_point_approx, "theorem"),
        (
            "CReal.integralEndpointClose",
            p.integral_endpoint_close,
            "theorem",
        ),
        (
            "CReal.integralSplitArbitrary",
            p.integral_split_arbitrary,
            "theorem",
        ),
        ("CReal.integral_abs_le", p.integral_abs_le, "theorem"),
        ("CReal.integral_scale", p.integral_scale, "theorem"),
        (
            "CReal.riemannSum_integral_close",
            p.riemann_sum_integral_close,
            "theorem",
        ),
        (
            "CReal.close_within_of_within_indexed",
            p.close_within_of_within_indexed,
            "theorem",
        ),
        (
            "CReal.riemannSum_split_exact",
            p.riemann_sum_split_exact,
            "theorem",
        ),
        (
            "CReal.riemannSum_split_scale_invariant",
            p.riemann_sum_split_scale_invariant,
            "theorem",
        ),
        (
            "CReal.congrOfUniformlyContinuous",
            p.congr_of_uniformly_continuous,
            "theorem",
        ),
        (
            "CReal.riemannSum_split_exact_of_uc",
            p.riemann_sum_split_exact_of_uc,
            "theorem",
        ),
        (
            "CReal.integral_abs_le_of_bound",
            p.integral_abs_le_of_bound,
            "theorem",
        ),
        (
            "CReal.integral_sub_linear_le",
            p.integral_sub_linear_le,
            "theorem",
        ),
        ("CReal.antiderivative", p.antiderivative, "def"),
        (
            "CReal.antiderivative_abs_le",
            p.antiderivative_abs_le,
            "theorem",
        ),
        (
            "CReal.integralSplitAnywhere",
            p.integral_split_anywhere,
            "theorem",
        ),
        (
            "CReal.hasDerivative_antiderivative",
            p.has_derivative_antiderivative,
            "theorem",
        ),
        (
            "CReal.integral_eq_antideriv_diff",
            p.integral_eq_antideriv_diff,
            "theorem",
        ),
        ("CReal.integral_by_parts", p.integral_by_parts, "theorem"),
        (
            "CReal.hasDerivative_antiderivative_of_uc",
            p.has_derivative_antiderivative_of_uc,
            "theorem",
        ),
        (
            "CReal.integral_eq_antideriv_diff_of_uc",
            p.integral_eq_antideriv_diff_of_uc,
            "theorem",
        ),
    ]
}
