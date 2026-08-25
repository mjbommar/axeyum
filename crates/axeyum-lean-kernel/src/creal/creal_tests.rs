//! Tests for the real (setoid) prelude.

use super::{CRealPrelude, build_creal_prelude};
use crate::{Declaration, Kernel};

/// A built `CReal` kernel, as a **clone of one template**.
///
/// The full development is now 96 declarations over the constructed ℚ and takes
/// tens of seconds to type-check; seventeen tests each building it from scratch
/// dominated this crate's test time. The argument for cloning is
/// [`prelude_cache`](crate::prelude_cache)'s, verbatim: prelude construction is
/// a deterministic function of the empty kernel, so the template equals what a
/// fresh build would produce, and every declaration in it entered through
/// `Kernel::add_declaration` under the full type checker exactly once.
/// `creal_prelude_builds` deliberately does **not** use this — it is the test
/// that exercises the real build.
fn built() -> (Kernel, CRealPrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, CRealPrelude)> = OnceLock::new();
    let (kernel, prelude) = TEMPLATE.get_or_init(|| {
        let mut kernel = Kernel::new();
        let prelude = build_creal_prelude(&mut kernel).expect("CReal prelude must build");
        (kernel, prelude)
    });
    (kernel.clone(), *prelude)
}

/// The build itself, with the kernel's rejection **rendered**. A `Debug` of
/// `KernelError` says nothing about what was refused; this says which two types
/// failed to match.
#[test]
fn creal_prelude_builds() {
    let mut kernel = Kernel::new();
    match build_creal_prelude(&mut kernel) {
        Ok(_) => {}
        Err(error) => {
            let nat = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
            let mut dev = crate::NatDev::new(&mut kernel, nat);
            let explained = crate::NatOps::explain(&mut dev, &error);
            panic!("the kernel refused a real proof: {explained}");
        }
    }
}

/// **ADR-0512's headline claim, measured.** A Bishop setoid over `ℚ` costs zero
/// trusted declarations: no `Quot.sound`, no `funext`, no `propext`, no
/// classical axiom, nothing.
#[test]
fn the_constructed_reals_add_no_trusted_declaration() {
    let (kernel, _) = built();
    let trusted: Vec<String> = kernel
        .environment()
        .iter()
        .filter_map(|(_, declaration)| match declaration {
            Declaration::Axiom { name, .. }
            | Declaration::Opaque { name, .. }
            | Declaration::Quotient { name, .. } => Some(kernel.display_name(*name).to_string()),
            _ => None,
        })
        .collect();
    assert!(
        trusted.is_empty(),
        "the real construction must assume nothing, found: {trusted:?}"
    );
}

/// Every declaration is the kind it claims to be and has an empty axiom
/// footprint, read out of the kernel rather than off the diff.
#[test]
fn every_creal_declaration_is_checked_and_axiom_free() {
    let (kernel, p) = built();
    let expected: [(&str, crate::NameId, &str); 200] = [
        ("Within", p.within, "def"),
        ("Regular", p.regular_pred, "inductive-or-def"),
        ("CReal", p.creal, "inductive"),
        ("CReal.mk", p.mk, "ctor"),
        ("CReal.rec", p.rec, "recursor"),
        ("CReal.seq", p.seq, "def"),
        ("CReal.regular", p.regular, "theorem"),
        ("CReal.Equiv", p.equiv, "def"),
        ("Equiv.refl", p.equiv_refl, "theorem"),
        ("Equiv.symm", p.equiv_symm, "theorem"),
        ("Equiv.trans", p.equiv_trans, "theorem"),
        ("CReal.ofRat", p.of_rat, "def"),
        ("Equiv.not_zero_one", p.not_zero_one, "theorem"),
        ("CReal.zero", p.zero, "def"),
        ("CReal.one", p.one, "def"),
        ("Equiv.of_pointwise", p.equiv_of_pointwise, "theorem"),
        ("CReal.neg", p.neg, "def"),
        ("CReal.neg_congr", p.neg_congr, "theorem"),
        ("CReal.neg_le_neg", p.neg_le_neg, "theorem"),
        ("CReal.add", p.add, "def"),
        ("CReal.add_congr", p.add_congr, "theorem"),
        ("CReal.add_comm", p.add_comm, "theorem"),
        ("CReal.add_neg", p.add_neg, "theorem"),
        ("CReal.add_zero", p.add_zero, "theorem"),
        ("CReal.add_assoc", p.add_assoc, "theorem"),
        ("CReal.ofRat_add", p.of_rat_add, "theorem"),
        ("CReal.ofRat_neg", p.of_rat_neg, "theorem"),
        ("CReal.ofRat_sub", p.of_rat_sub, "theorem"),
        ("CReal.le", p.le, "def"),
        ("CReal.le_refl", p.le_refl, "theorem"),
        ("CReal.le_trans", p.le_trans, "theorem"),
        ("CReal.add_le_add", p.add_le_add, "theorem"),
        ("CReal.le_of_equiv", p.le_of_equiv, "theorem"),
        ("CReal.equiv_of_le_le", p.equiv_of_le_le, "theorem"),
        ("CReal.not_le_one_zero", p.not_le_one_zero, "theorem"),
        ("CReal.le_add_of_nonneg", p.le_add_of_nonneg, "theorem"),
        ("CReal.lt", p.lt, "def"),
        ("CReal.lt_irrefl", p.lt_irrefl, "theorem"),
        ("CReal.lt_trans", p.lt_trans, "theorem"),
        ("CReal.lt_of_lt_of_le", p.lt_of_lt_of_le, "theorem"),
        ("CReal.lt_of_le_of_lt", p.lt_of_le_of_lt, "theorem"),
        ("CReal.le_of_lt", p.le_of_lt, "theorem"),
        ("CReal.zero_lt_one", p.zero_lt_one, "theorem"),
        (
            "CReal.add_lt_add_of_le_of_lt",
            p.add_lt_add_of_le_of_lt,
            "theorem",
        ),
        ("CReal.le_congr", p.le_congr, "theorem"),
        ("CReal.lt_congr", p.lt_congr, "theorem"),
        ("CReal.bound", p.bound, "def"),
        ("CReal.bound_within", p.bound_within, "theorem"),
        ("CReal.mulShift", p.mul_shift, "def"),
        ("CReal.mul", p.mul, "def"),
        ("CReal.ofRat_mul", p.of_rat_mul, "theorem"),
        ("CReal.mul_comm", p.mul_comm, "theorem"),
        ("CReal.mul_one", p.mul_one, "theorem"),
        ("CReal.mul_zero", p.mul_zero, "theorem"),
        ("CReal.mul_nonneg", p.mul_nonneg, "theorem"),
        ("CReal.sq_nonneg", p.sq_nonneg, "theorem"),
        ("CReal.neg_mul_neg", p.neg_mul_neg, "theorem"),
        (
            "CReal.not_equiv_mul_one_one_zero",
            p.not_equiv_mul_one_one_zero,
            "theorem",
        ),
        ("CReal.Equiv.of_bounded", p.equiv_of_bounded, "theorem"),
        ("CReal.mul_congr", p.mul_congr, "theorem"),
        ("CReal.left_distrib", p.left_distrib, "theorem"),
        ("CReal.mul_assoc", p.mul_assoc, "theorem"),
        (
            "CReal.mul_le_mul_of_nonneg_left",
            p.mul_le_mul_of_nonneg_left,
            "theorem",
        ),
        ("CReal.Apart", p.apart, "def"),
        ("CReal.apart_symm", p.apart_symm, "theorem"),
        ("CReal.apart_irrefl", p.apart_irrefl, "theorem"),
        ("CReal.apart_congr", p.apart_congr, "theorem"),
        ("CReal.not_equiv_of_apart", p.not_equiv_of_apart, "theorem"),
        ("CReal.apart_zero_one", p.apart_zero_one, "theorem"),
        ("CReal.no_total_inverse", p.no_total_inverse, "theorem"),
        ("CReal.ofRat_le", p.of_rat_le, "theorem"),
        ("CReal.PosBound", p.pos_bound, "def"),
        ("CReal.pos_of_pos_bound", p.pos_of_pos_bound, "theorem"),
        ("CReal.pos_bound_of_lt", p.pos_bound_of_lt, "theorem"),
        ("CReal.ofRat_pos", p.of_rat_pos, "theorem"),
        ("CReal.mul_pos", p.mul_pos, "theorem"),
        ("CReal.invShift", p.inv_shift, "def"),
        ("CReal.inv", p.inv, "def"),
        ("CReal.mul_inv_cancel", p.mul_inv_cancel, "theorem"),
        ("CReal.inv_congr", p.inv_congr, "theorem"),
        (
            "CReal.inv_index_irrelevant",
            p.inv_index_irrelevant,
            "theorem",
        ),
        ("CReal.max", p.max, "def"),
        ("CReal.min", p.min, "def"),
        ("CReal.abs", p.abs, "def"),
        ("CReal.le_max_left", p.le_max_left, "theorem"),
        ("CReal.le_max_right", p.le_max_right, "theorem"),
        ("CReal.max_le", p.max_le, "theorem"),
        ("CReal.min_le_left", p.min_le_left, "theorem"),
        ("CReal.min_le_right", p.min_le_right, "theorem"),
        ("CReal.le_min", p.le_min, "theorem"),
        ("CReal.max_congr", p.max_congr, "theorem"),
        ("CReal.min_congr", p.min_congr, "theorem"),
        ("CReal.abs_congr", p.abs_congr, "theorem"),
        ("CReal.le_abs_self", p.le_abs_self, "theorem"),
        ("CReal.neg_le_abs", p.neg_le_abs, "theorem"),
        ("CReal.abs_le", p.abs_le, "theorem"),
        ("CReal.abs_nonneg", p.abs_nonneg, "theorem"),
        (
            "CReal.not_le_zero_neg_one",
            p.not_le_zero_neg_one,
            "theorem",
        ),
        (
            "CReal.not_equiv_abs_neg_one",
            p.not_equiv_abs_neg_one,
            "theorem",
        ),
        ("CReal.ofNat", p.of_nat, "def"),
        ("CReal.archimedean", p.archimedean, "theorem"),
        ("CReal.rat_approx_upper", p.rat_approx_upper, "theorem"),
        ("CReal.rat_approx_lower", p.rat_approx_lower, "theorem"),
        ("CReal.density", p.density, "theorem"),
        // Convergence (ADR-0512 phase R9). PRESENCE MATTERS AS MUCH AS THE
        // FOOTPRINT here: `axiom_footprint` of an interned-but-never-declared
        // name is vacuously empty, so a declaration silently missing from the
        // build sequence would read as "axiom-free" rather than as absent.
        ("CReal.Converges", p.converges, "def"),
        ("CReal.converges_unique", p.converges_unique, "theorem"),
        ("CReal.converges_of_const", p.converges_of_const, "theorem"),
        ("CReal.Cauchy", p.cauchy, "def"),
        ("CReal.converges_cauchy", p.converges_cauchy, "theorem"),
        // Algebra of limits (ADR-0512 phase R9, continued): the shift bridge
        // (`half_shift_le`, widened to `pub(super)` in `completeness.rs`) let
        // `convergence.rs` land these without re-deriving it.
        ("CReal.converges_add", p.converges_add, "theorem"),
        ("CReal.converges_neg", p.converges_neg, "theorem"),
        ("CReal.converges_sub", p.converges_sub, "theorem"),
        // The squeeze theorem: no shift bridge needed, since `CReal.le` is
        // already stated at the same canonical-sample index `Converges` uses.
        ("CReal.converges_squeeze", p.converges_squeeze, "theorem"),
        // Boundedness and sequential continuity (phase R10).
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
            "CReal.UniformlyContinuousOn",
            p.uniformly_continuous_on,
            "inductive",
        ),
        ("UniformlyContinuousOn.mk", p.uc_mk, "ctor"),
        ("UniformlyContinuousOn.rec", p.uc_rec, "recursor"),
        ("UniformlyContinuousOn.modulus", p.uc_modulus, "def"),
        ("UniformlyContinuousOn.spec", p.uc_spec, "theorem"),
        (
            "CReal.uniformly_continuous_id",
            p.uniformly_continuous_id,
            "theorem",
        ),
        (
            "CReal.uniformly_continuous_const",
            p.uniformly_continuous_const,
            "theorem",
        ),
        (
            "CReal.uniformly_continuous_add",
            p.uniformly_continuous_add,
            "theorem",
        ),
        ("CReal.ratSqLe", p.rat_sq_le, "theorem"),
        ("CReal.ratSqSandwich", p.rat_sq_sandwich, "theorem"),
        (
            "CReal.ratIndexRatioLeOne",
            p.rat_index_ratio_le_one,
            "theorem",
        ),
        ("CReal.ratUnitEqOne", p.rat_unit_eq_one, "theorem"),
        (
            "CReal.eq_zero_of_mul_self_zero",
            p.eq_zero_of_mul_self_zero,
            "theorem",
        ),
        (
            "CReal.eq_zero_of_add_eq_zero_of_nonneg",
            p.eq_zero_of_add_eq_zero_of_nonneg,
            "theorem",
        ),
        ("CReal.natSqrt", p.nat_sqrt, "def"),
        ("CReal.natSqrtSpec", p.nat_sqrt_spec, "theorem"),
        ("CReal.natSqrtLe", p.nat_sqrt_le, "theorem"),
        ("CReal.natSqrtLt", p.nat_sqrt_lt, "theorem"),
        ("CReal.sqrtApprox", p.sqrt_approx, "def"),
        // Bishop's speed-up combinator (creal/speedup.rs).
        ("CReal.KRegular", p.k_regular_pred, "def"),
        ("CReal.speedup", p.speedup, "def"),
        (
            "CReal.regular_of_kregular",
            p.regular_of_kregular,
            "theorem",
        ),
        ("CReal.speedup_close", p.speedup_close, "theorem"),
        // Finite sums over ℝ (creal/series.rs). PRESENCE MATTERS AS MUCH AS
        // THE FOOTPRINT here too — see the convergence block's own comment
        // above.
        ("CReal.sumRange", p.sum_range, "def"),
        ("CReal.sumRange_zero", p.sum_range_zero, "theorem"),
        ("CReal.sumRange_succ", p.sum_range_succ, "theorem"),
        ("CReal.sumRange_congr", p.sum_range_congr, "theorem"),
        ("CReal.sumRange_add", p.sum_range_add, "theorem"),
        ("CReal.mul_sumRange", p.mul_sum_range, "theorem"),
        ("CReal.sumRange_le", p.sum_range_le, "theorem"),
        ("CReal.abs_sumRange_le", p.abs_sum_range_le, "theorem"),
        ("CReal.sumRange_telescope", p.sum_range_telescope, "theorem"),
        ("CReal.sumRange_split", p.sum_range_split, "theorem"),
        ("CReal.sumRange_tail_le", p.sum_range_tail_le, "theorem"),
        (
            "CReal.sumRange_tail_within",
            p.sum_range_tail_within,
            "theorem",
        ),
        (
            "CReal.sumRange_tail_within_le",
            p.sum_range_tail_within_le,
            "theorem",
        ),
        ("CReal.sumRange_seq_zero", p.sum_range_seq_zero, "theorem"),
        ("CReal.sumRange_seq_succ", p.sum_range_seq_succ, "theorem"),
        // Powers, and the geometric series over ℝ (creal/power.rs).
        // PRESENCE MATTERS AS MUCH AS THE FOOTPRINT here too — see the
        // convergence block's own comment above.
        ("CReal.pow", p.pow, "def"),
        ("CReal.pow_zero", p.pow_zero, "theorem"),
        ("CReal.pow_succ", p.pow_succ, "theorem"),
        ("CReal.pow_add", p.pow_add, "theorem"),
        ("CReal.pow_congr", p.pow_congr, "theorem"),
        ("CReal.pow_nonneg", p.pow_nonneg, "theorem"),
        ("CReal.pow_le_one", p.pow_le_one, "theorem"),
        ("CReal.mul_sub_one_geom", p.mul_sub_one_geom, "theorem"),
        ("CReal.geom_sum_bounded", p.geom_sum_bounded, "theorem"),
        (
            "CReal.pow_le_pow_of_le_one",
            p.pow_le_pow_of_le_one,
            "theorem",
        ),
        (
            "CReal.mul_sub_one_geom_tail",
            p.mul_sub_one_geom_tail,
            "theorem",
        ),
        ("CReal.geom_tail_bounded", p.geom_tail_bounded, "theorem"),
        (
            "CReal.one_le_pow_of_one_le",
            p.one_le_pow_of_one_le,
            "theorem",
        ),
        (
            "CReal.pow_le_pow_of_one_le",
            p.pow_le_pow_of_one_le,
            "theorem",
        ),
        ("CReal.pow_pos", p.pow_pos, "theorem"),
        ("CReal.pow_succ_lt_one", p.pow_succ_lt_one, "theorem"),
        ("CReal.pow_succ_gt_one", p.pow_succ_gt_one, "theorem"),
        (
            "CReal.not_apart_one_of_pow_succ_eq_one",
            p.not_apart_one_of_pow_succ_eq_one,
            "theorem",
        ),
        // The derivative, on an interval (creal/derivative.rs). PRESENCE
        // MATTERS AS MUCH AS THE FOOTPRINT here too — see the convergence
        // block's own comment above.
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
    ];
    for (label, name, kind) in expected {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{label} was interned but never declared"));
        match kind {
            "theorem" => assert!(
                matches!(declaration, Declaration::Theorem { .. }),
                "{label} must be a checked Theorem"
            ),
            "def" => assert!(
                matches!(declaration, Declaration::Definition { .. }),
                "{label} must be a Definition"
            ),
            _ => {}
        }
        assert!(
            !matches!(
                declaration,
                Declaration::Axiom { .. } | Declaration::Opaque { .. }
            ),
            "{label} is asserted, not derived"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "{label} rests on {footprint:?}");
    }
}

/// **`CReal.sumRange_tail_within` on a trivial instance**: `f = g` the
/// constant-zero sequence, `m = n = 0`. Not a soundness check on its own
/// (the general theorem is already proved for every `f g m n`, so any
/// instance holds) — it is the sanity check the module documentation's
/// "series.rs" retrospective on `nra_monomial_bound_cert.rs`-style vacuity
/// asks for: instantiate the theorem's own conclusion at a fully CONCRETE,
/// CLOSED term and have the kernel independently `infer` its type, rather
/// than trusting that a universally-quantified statement that type-checks
/// is the statement intended. `Kernel::infer` requires a closed term
/// (`tests.rs::inference_caches_only_closed_successes` pins that an
/// unregistered free variable is refused), which is exactly why this test
/// closes the pointwise hypothesis and both indices to ground terms instead
/// of leaving `f` a free variable.
#[test]
fn sum_range_tail_within_specializes_to_the_zero_series_against_itself() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();

    // zero_fn := λ _ : Nat, CReal.zero.
    let zero_fn = {
        let k_fv = d.fresh_fvar();
        let _k = d.kernel().fvar(k_fv);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        d.lam_fv(k_fv, nat, zero_c)
    };
    let zero_nat = d.num(0);

    // pointwise : ∀ k, le (abs (zero_fn k)) (zero_fn k), via le_abs_self.
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zk = d.apply(zero_fn, &[k]);
        let body = d.lemma(p.le_abs_self, &[zk]);
        d.lam_fv(k_fv, nat, body)
    };

    let instance = d.lemma(
        p.sum_range_tail_within,
        &[zero_fn, zero_fn, zero_nat, zero_nat, pointwise],
    );

    let inferred = d.kernel().infer(instance);
    let ty = inferred.unwrap_or_else(|error| {
        panic!(
            "sumRange_tail_within refused at the trivial f = g = (fun _ => zero), \
             m = n = 0 instance: {error:?}"
        )
    });

    // Not just well-typed: the conclusion the kernel infers is genuinely a
    // `Within` bound, not e.g. `True` or some other vacuous stand-in.
    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Within"),
        "the instantiated conclusion is not a `Within` bound: {rendered}"
    );
}

/// `CReal.sumRange_tail_within_le` on a trivial instance: `f = g` the
/// constant-zero sequence, `a = 0`, `b = 1` — a **non-degenerate** pair
/// (`a ≠ b`), deliberately, so the `Nat.le_dest` witness `k` used internally
/// is `1`, not `0`: an `a = b` instance would exercise `k = 0` only and could
/// pass even if the general `k`-indexed rewrite were broken. Same rationale
/// and same `Kernel::infer`-on-a-closed-term method as
/// [`sum_range_tail_within_specializes_to_the_zero_series_against_itself`].
#[test]
fn sum_range_tail_within_le_specializes_to_the_zero_series_from_0_to_1() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let nat = d.nat_ty();

    // zero_fn := λ _ : Nat, CReal.zero.
    let zero_fn = {
        let k_fv = d.fresh_fvar();
        let _k = d.kernel().fvar(k_fv);
        let zero_c = d.kernel().const_(p.zero, vec![]);
        d.lam_fv(k_fv, nat, zero_c)
    };
    let zero_nat = d.num(0);
    let one_nat = d.num(1);

    // pointwise : ∀ k, le (abs (zero_fn k)) (zero_fn k), via le_abs_self.
    let pointwise = {
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let zk = d.apply(zero_fn, &[k]);
        let body = d.lemma(p.le_abs_self, &[zk]);
        d.lam_fv(k_fv, nat, body)
    };

    // hle : Nat.le 0 1, via Nat.zero_le.
    let zero_le = d.prelude().zero_le;
    let hle = d.lemma(zero_le, &[one_nat]);

    let instance = d.lemma(
        p.sum_range_tail_within_le,
        &[zero_fn, zero_fn, zero_nat, one_nat, pointwise, hle],
    );

    let inferred = d.kernel().infer(instance);
    let ty = inferred.unwrap_or_else(|error| {
        panic!(
            "sumRange_tail_within_le refused at the trivial f = g = (fun _ => zero), \
             a = 0, b = 1 instance: {error:?}"
        )
    });

    let rendered = kernel.render_lean(ty);
    assert!(
        rendered.contains("Within"),
        "the instantiated conclusion is not a `Within` bound: {rendered}"
    );
}

/// The three setoid laws say what ADR-0512 says they say. An empty footprint on
/// a theorem stating something weaker is this repository's standing failure
/// mode, so the rendered types are asserted verbatim.
#[test]
fn the_setoid_laws_have_the_statements_adr_0468_specifies() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.equiv_refl),
        "((x0 : CReal) -> CReal.Equiv x0 x0)"
    );
    assert_eq!(
        rendered(&mut kernel, p.equiv_symm),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Equiv x0 x1) -> CReal.Equiv x1 x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.equiv_trans),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.Equiv x0 x1) -> \
         ((x4 : CReal.Equiv x1 x2) -> CReal.Equiv x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.not_zero_one),
        "Not (CReal.Equiv (CReal.ofRat Rat.zero) (CReal.ofRat Rat.one))"
    );
    // The two of the 22 that hold in `Equiv` form. Asserting these verbatim is
    // what stops "N laws hold" drifting into "N laws are named".
    assert_eq!(
        rendered(&mut kernel, p.add_comm),
        "((x0 : CReal) -> ((x1 : CReal) -> \
         CReal.Equiv (CReal.add x0 x1) (CReal.add x1 x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_neg),
        "((x0 : CReal) -> \
         CReal.Equiv (CReal.add x0 (CReal.neg x0)) CReal.zero)"
    );
    // The two that are NOT pointwise, and are the reason `Equiv` had to be an
    // equivalence relation before any of this was worth stating.
    assert_eq!(
        rendered(&mut kernel, p.add_zero),
        "((x0 : CReal) -> CReal.Equiv (CReal.add x0 CReal.zero) x0)"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_assoc),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> \
         CReal.Equiv (CReal.add (CReal.add x0 x1) x2) \
         (CReal.add x0 (CReal.add x1 x2)))))"
    );
    // The three order laws. Unlike the additive ones these are the `Real`
    // package's statements VERBATIM — none of them mentions `Eq`, so there is
    // no equality to replace by `Equiv` (ADR-0512, Measurement 2).
    assert_eq!(
        rendered(&mut kernel, p.le_refl),
        "((x0 : CReal) -> CReal.le x0 x0)"
    );
    assert_eq!(
        rendered(&mut kernel, p.le_trans),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.le x0 x1) -> \
         ((x4 : CReal.le x1 x2) -> CReal.le x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_le_add),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.le x0 x1) -> ((x5 : CReal.le x2 x3) -> \
         CReal.le (CReal.add x0 x2) (CReal.add x1 x3)))))))"
    );
    // The order is the order OF this setoid, not an unexamined relation that
    // happens to satisfy three laws.
    assert_eq!(
        rendered(&mut kernel, p.le_of_equiv),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Equiv x0 x1) -> CReal.le x0 x1)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.equiv_of_le_le),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.le x0 x1) -> \
         ((x3 : CReal.le x1 x0) -> CReal.Equiv x0 x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.not_le_one_zero),
        "Not (CReal.le CReal.one CReal.zero)"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         CReal.Equiv (CReal.add x0 x2) (CReal.add x1 x3)))))))"
    );
    // The seven strict-order laws, also VERBATIM: like the three `le` laws,
    // none of them mentions `Eq`, so the `Real` package's statement is the
    // statement proved here — no `Equiv` restatement, nothing weakened.
    assert_eq!(
        rendered(&mut kernel, p.lt_irrefl),
        "((x0 : CReal) -> Not (CReal.lt x0 x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_trans),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.lt x0 x1) -> \
         ((x4 : CReal.lt x1 x2) -> CReal.lt x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_of_lt_of_le),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.lt x0 x1) -> \
         ((x4 : CReal.le x1 x2) -> CReal.lt x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_of_le_of_lt),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.le x0 x1) -> \
         ((x4 : CReal.lt x1 x2) -> CReal.lt x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.le_of_lt),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.lt x0 x1) -> CReal.le x0 x1)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.zero_lt_one),
        "CReal.lt CReal.zero CReal.one"
    );
    assert_eq!(
        rendered(&mut kernel, p.add_lt_add_of_le_of_lt),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.le x0 x1) -> ((x5 : CReal.lt x2 x3) -> \
         CReal.lt (CReal.add x0 x2) (CReal.add x1 x3)))))))"
    );
    // The two relation congruences of the setoid telescope's equality slot.
    assert_eq!(
        rendered(&mut kernel, p.le_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         ((x6 : CReal.le x0 x2) -> CReal.le x1 x3)))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.lt_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         ((x6 : CReal.lt x0 x2) -> CReal.lt x1 x3)))))))"
    );
    // The five product laws. Two of the 22 in `Equiv` form, three verbatim —
    // and `mul_nonneg`/`sq_nonneg` are the `Real` package's statements
    // unchanged, so a weakened restatement would show up here as a diff.
    assert_eq!(
        rendered(&mut kernel, p.mul_comm),
        "((x0 : CReal) -> ((x1 : CReal) -> \
         CReal.Equiv (CReal.mul x0 x1) (CReal.mul x1 x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_one),
        "((x0 : CReal) -> CReal.Equiv (CReal.mul x0 CReal.one) x0)"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_zero),
        "((x0 : CReal) -> CReal.Equiv (CReal.mul x0 CReal.zero) CReal.zero)"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_nonneg),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.le CReal.zero x0) -> \
         ((x3 : CReal.le CReal.zero x1) -> CReal.le CReal.zero (CReal.mul x0 x1)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.sq_nonneg),
        "((x0 : CReal) -> CReal.le CReal.zero (CReal.mul x0 x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_assoc),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> \
         CReal.Equiv (CReal.mul (CReal.mul x0 x1) x2) \
         (CReal.mul x0 (CReal.mul x1 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.left_distrib),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> \
         CReal.Equiv (CReal.mul x0 (CReal.add x1 x2)) \
         (CReal.add (CReal.mul x0 x1) (CReal.mul x0 x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_le_mul_of_nonneg_left),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> \
         ((x3 : CReal.le CReal.zero x0) -> ((x4 : CReal.le x1 x2) -> \
         CReal.le (CReal.mul x0 x1) (CReal.mul x0 x2))))))"
    );
    // The fifth congruence obligation — not one of the 22, and the R4
    // prerequisite ADR-0512 calls the setoid's real tax.
    assert_eq!(
        rendered(&mut kernel, p.mul_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         CReal.Equiv (CReal.mul x0 x2) (CReal.mul x1 x3)))))))"
    );
    // The two witnesses that stop the five above being satisfiable by a
    // degenerate product. `ofRat_mul` pins the OPERATION on the embedded `ℚ`;
    // `not_equiv_mul_one_one_zero` exhibits a separated pair by computation.
    assert_eq!(
        rendered(&mut kernel, p.of_rat_mul),
        "((x0 : Rat) -> ((x1 : Rat) -> \
         CReal.Equiv (CReal.mul (CReal.ofRat x0) (CReal.ofRat x1)) \
         (CReal.ofRat (Rat.mul x0 x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.not_equiv_mul_one_one_zero),
        "Not (CReal.Equiv (CReal.mul CReal.one CReal.one) CReal.zero)"
    );
    // The canonical bound is a bound on EVERY sample, not just the zeroth —
    // which is the whole reason `CReal.mul`'s index can be a fixed function of
    // the two factors.
    assert_eq!(
        rendered(&mut kernel, p.bound_within),
        "((x0 : CReal) -> ((x1 : AxNat) -> \
         CReal.Within (CReal.seq x0 x1) \
         (Rat.natDivSucc (AxNat.succ (CReal.bound x0)) AxNat.zero)))"
    );
}

/// **The product is not the degenerate one**, and the check is by computation.
///
/// `CReal.mul_zero`, `CReal.mul_comm` and `CReal.sq_nonneg` all hold — with
/// empty axiom footprints — of `fun _ _ => CReal.zero`. So does every
/// footprint check that only asks whether they were *derived*. This asks the
/// kernel for a closed instance instead: `1 · 1` is `Equiv`-equal to `1`, and
/// `Equiv 1 0` is refuted.
#[test]
fn the_product_is_not_the_constant_zero() {
    let (kernel, p) = built();
    // PRESENCE FIRST. `Kernel::axiom_footprint` of a name that was interned but
    // never declared is the empty vector, which is indistinguishable from
    // "declared and axiom-free" — the failure mode this repository keeps
    // rediscovering. Assert the declaration exists and is a Theorem before
    // reading anything off it.
    assert!(
        matches!(
            kernel.environment().get(p.not_equiv_mul_one_one_zero),
            Some(Declaration::Theorem { .. })
        ),
        "CReal.not_equiv_mul_one_one_zero must be a checked theorem: without it \
         nothing separates any product from zero, and mul_zero / mul_comm / \
         sq_nonneg all still hold of `fun _ _ => zero`"
    );
    assert!(
        matches!(
            kernel.environment().get(p.of_rat_mul),
            Some(Declaration::Theorem { .. })
        ),
        "CReal.ofRat_mul must be a checked theorem: without it nothing pins \
         CReal.mul to Rat.mul anywhere at all"
    );
    let footprint = kernel.axiom_footprint(p.not_equiv_mul_one_one_zero);
    assert!(
        footprint.is_empty(),
        "the product's discrimination witness rests on {:?}",
        footprint
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect::<Vec<_>>()
    );
}

/// The negative control for the product witness: the **same script**, pointed
/// at a claim that is false.
///
/// `Not (Equiv (mul one one) one)` is false — `mul_one` proves the positive
/// form — and it differs from the proved witness in one constant. The kernel
/// must refuse it, which is what says the witness is checking the pair it
/// names rather than any pair.
#[test]
fn the_product_discrimination_route_cannot_refute_mul_one_one_one() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::ops::{rat_eq_rewrite, rmul, rone};

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);

    let cone = d.kernel().const_(p.one, vec![]);
    let product = d.const_app(p.mul, &[cone, cone]);
    let claim = super::equiv(&mut d, p, product, cone);
    let stmt = d.not(claim);

    let unit = rone(&mut d, rat);
    let homomorphism = d.lemma(p.of_rat_mul, &[unit, unit]);
    let square = rmul(&mut d, unit, unit);
    let collapse = d.lemma(rat.mul_one, &[unit]);
    let at_one = rat_eq_rewrite(&mut d, square, unit, collapse, homomorphism, &|d, t| {
        let embedded = d.const_app(p.of_rat, &[t]);
        super::equiv(d, p, product, embedded)
    });
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let reversed = d.lemma(p.equiv_symm, &[product, cone, h]);
    let chained = d.lemma(p.equiv_trans, &[cone, product, cone, reversed, at_one]);
    let absurd = d.lemma(p.not_zero_one, &[chained]);
    let value = d.lam_fv(h_fv, claim, absurd);
    let name = d.kernel().name_str(anon, "Check.not_mul_one_one_one");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stmt,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `Not (CReal.Equiv (mul one one) one)`, which \
         contradicts CReal.mul_one — the product witness proves nothing"
    );
}

/// **`CReal.lt` is the strict order ADR-0512 asks for, not a negation.**
///
/// The definition is asserted verbatim because the two rejected shapes differ
/// from it only in the body: `Not (le y x)` would render as a `Not`, and
/// `∃ n : Nat, …` would quantify over `Nat`. This quantifies over a **rational
/// gap**, which is what makes `le_of_lt` constructive and `lt_trans` carry its
/// witness through untouched.
#[test]
fn lt_quantifies_over_a_positive_rational_gap() {
    let (kernel, p) = built();
    let value = match kernel.environment().get(p.lt).expect("CReal.lt declared") {
        Declaration::Definition { value, .. } => *value,
        other => panic!("{other:?} is not a definition"),
    };
    let rendered = kernel
        .render_lean(value)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(
        rendered,
        "fun (x0 : CReal) => fun (x1 : CReal) => Exists.{1} Rat \
         (fun (x2 : Rat) => And (Rat.lt Rat.zero x2) \
         (CReal.le (CReal.add x0 (CReal.ofRat x2)) x1))"
    );
}

/// **`CReal.lt` is neither empty nor total**, and both halves are needed.
///
/// Six of the seven strict-order laws *consume* a `lt`, so all six hold —
/// footprint-free — of the empty relation. `zero_lt_one` is the only one that
/// produces an inhabitant, and `lt_irrefl` is the only one that refuses a pair.
/// Together they are the discrimination witness the axiom footprint cannot see.
#[test]
fn the_strict_order_discriminates() {
    let (kernel, p) = built();
    for (label, name) in [
        ("CReal.zero_lt_one", p.zero_lt_one),
        ("CReal.lt_irrefl", p.lt_irrefl),
    ] {
        let declaration = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{label} must be declared"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "{label} must be a checked Theorem — an axiom would witness nothing"
        );
        assert!(
            kernel.axiom_footprint(name).is_empty(),
            "{label} must be axiom-free"
        );
    }
}

/// The negative control for `zero_lt_one`: the **same script**, with the two
/// constants swapped.
///
/// `lt one zero` is false, and the script that proves `lt zero one` reaches it
/// through `Rat.zero_add` on the sampled sum `0 + 1`. Pointed at `one + 1` that
/// rewrite does not apply, and the kernel must **refuse** — which is what says
/// the strict order is reading which sequence is being sampled rather than
/// merely assembling a bound.
#[test]
fn the_zero_lt_one_route_cannot_prove_one_lt_zero() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rchain, rcongr, rone, rsymm, rzero};

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);
    let nat = d.nat_ty();

    let zero_rat = rzero(&mut d, rat);
    let one_rat = rone(&mut d, rat);
    // The two changed tokens: the claim is `lt one zero`, not `lt zero one`.
    let zero_real = d.kernel().const_(p.zero, vec![]);
    let one_real = d.kernel().const_(p.one, vec![]);

    let bounded = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sum = radd(&mut d, one_rat, one_rat);
        let quantity = rsub(&mut d, rat, sum, zero_rat);
        let bound = super::div_succ(&mut d, p, 2, n);
        let unpad = d.lemma(rat.zero_add, &[one_rat]);
        let step = rcongr(&mut d, sum, one_rat, unpad, &|d, t| {
            rsub(d, rat, t, zero_rat)
        });
        let degenerate = rsub(&mut d, rat, one_rat, zero_rat);
        let collapse = d.lemma(rat.sub_self, &[one_rat]);
        let (_, to_zero) = rchain(
            &mut d,
            quantity,
            &[(degenerate, step), (zero_rat, collapse)],
        );
        let back = rsymm(&mut d, quantity, zero_rat, to_zero);
        let two = d.num(2);
        let nonneg = d.lemma(rat.zero_le_nat_div_succ, &[two, n]);
        let at_index = rat_eq_rewrite(&mut d, zero_rat, quantity, back, nonneg, &|d, t| {
            crate::rat_prelude::ops::rle(d, rat, t, bound)
        });
        d.lam_fv(n_fv, nat, at_index)
    };
    let positive = crate::rat_prelude::ops::rlt(&mut d, rat, zero_rat, one_rat);
    let embedded = super::embed(&mut d, p, one_rat);
    let shifted = super::cadd(&mut d, p, one_real, embedded);
    let reached = super::cle(&mut d, p, shifted, zero_real);
    let strict = d.lemma(rat.zero_lt_one, &[]);
    let pair = super::and_intro(&mut d, p, positive, reached, strict, bounded);
    let value = super::gap_intro(&mut d, p, one_real, zero_real, one_rat, pair);
    let ty = super::clt(&mut d, p, one_real, zero_real);
    let name = d.kernel().name_str(anon, "Check.one_lt_zero");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `CReal.lt CReal.one CReal.zero`, which contradicts \
         CReal.lt_irrefl through lt_trans — the strict order proves nothing"
    );
}

/// **The carrier is inhabited.** Everything above is a statement about the
/// inhabitants of `CReal`; if `CReal.Regular` had no solutions the carrier
/// would be empty, `refl`/`symm`/`trans` would all hold vacuously, and the
/// axiom footprints would still be empty. `CReal.ofRat` is a *checked*
/// definition, so the kernel accepted a regularity proof for a concrete
/// sequence.
#[test]
fn the_carrier_is_inhabited() {
    let (kernel, p) = built();
    let declaration = kernel
        .environment()
        .get(p.of_rat)
        .expect("CReal.ofRat must be declared");
    assert!(
        matches!(declaration, Declaration::Definition { .. }),
        "CReal.ofRat must be a Definition — an axiom would not witness anything"
    );
}

/// **`CReal.Equiv` discriminates.** An equivalence relation that relates
/// everything is an equivalence relation, and worthless; this exhibits two
/// `CReal`s it separates.
#[test]
fn equiv_is_not_the_total_relation() {
    let (kernel, p) = built();
    assert!(
        matches!(
            kernel.environment().get(p.not_zero_one),
            Some(Declaration::Theorem { .. })
        ),
        "the discrimination witness must be a checked Theorem"
    );
}

/// The negative control for [`equiv_is_not_the_total_relation`]: the same proof
/// route, pointed at a pair `Equiv` does **not** separate.
///
/// `Equiv.not_zero_one` works because `−1/2 ≤ −1` reduces to `Nat.le 1 0`. If
/// the kernel's reduction were not actually deciding that, the identical script
/// with `ofRat 0` on **both** sides would also go through — and it would prove
/// `Not (Equiv x x)`, contradicting `Equiv.refl`. It must be **refused**.
#[test]
fn the_discrimination_route_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::rzero;

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);

    let zero_rat = rzero(&mut d, rat);
    let left = d.const_app(p.of_rat, &[zero_rat]);
    let claim = super::equiv(&mut d, p, left, left);
    let stmt = d.not(claim);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let index = d.num(3);
    let instance = d.apply(h, &[index]);
    let a = super::sample(&mut d, p, left, index);
    let difference = rsub(&mut d, rat, a, a);
    let bound = super::div_succ(&mut d, p, 2, index);
    let (lower, _upper) = super::halves(&mut d, p, difference, bound, instance);
    let zero_nat = d.zero();
    let absurd = d.lemma(rat.int.nat.not_succ_le_zero, &[zero_nat, lower]);
    let value = d.lam_fv(h_fv, claim, absurd);
    let name = d.kernel().name_str(anon, "Check.not_zero_zero");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stmt,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `Not (CReal.Equiv (ofRat 0) (ofRat 0))`, which \
         contradicts CReal.Equiv.refl — the discrimination witness proves nothing"
    );
}

/// The negative control for `add_zero`: the **same script**, pointed at a law
/// that is false.
///
/// `add_zero` is the first law whose two sides are not equal at any index, so
/// what carries it is regularity plus a bound comparison — and a bound
/// comparison is exactly the kind of argument that would still go through if
/// the kernel were not actually looking at which sequence is being sampled.
/// `Equiv (add x one) x` is false, differs from the proved statement in one
/// constant, and must be **refused**.
#[test]
fn the_add_zero_route_cannot_prove_add_one() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;
    use crate::rat_prelude::group::rsub;
    use crate::rat_prelude::ops::{radd, rat_eq_rewrite, rsymm, rzero};

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);
    let carrier = super::creal_ty(&mut d, p);
    let nat = d.nat_ty();

    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    // The one changed token: `CReal.one` where the proved law has `CReal.zero`.
    let one_real = d.kernel().const_(p.one, vec![]);
    let left = d.const_app(p.add, &[x, one_real]);
    let body = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let index = super::shift(&mut d, n);
        let deep = super::sample(&mut d, p, x, index);
        let shallow = super::sample(&mut d, p, x, n);
        let difference = rsub(&mut d, rat, deep, shallow);
        let bound = super::modulus(&mut d, p, index, n);
        let goal_bound = super::div_succ(&mut d, p, 2, n);
        let source = d.lemma(p.regular, &[x, index, n]);
        let order = super::shifted_bound_le(&mut d, p, n);
        let widened = super::weaken(&mut d, p, difference, bound, goal_bound, source, order);
        let zero_rat = rzero(&mut d, rat);
        let padded = radd(&mut d, deep, zero_rat);
        let collapse = d.lemma(rat.add_zero, &[deep]);
        let restore = rsymm(&mut d, padded, deep, collapse);
        let at_index = rat_eq_rewrite(&mut d, deep, padded, restore, widened, &|d, t| {
            let quantity = rsub(d, rat, t, shallow);
            super::within(d, p, quantity, goal_bound)
        });
        d.lam_fv(n_fv, nat, at_index)
    };
    let value = d.lam_fv(x_fv, carrier, body);
    let ty = {
        let conclusion = super::equiv(&mut d, p, left, x);
        d.pi_fv(x_fv, carrier, conclusion)
    };
    let name = d.kernel().name_str(anon, "Check.add_one");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `Equiv (add x one) x`, so the add_zero route is not \
         checking which sequence the shifted index samples"
    );
}

/// **`CReal.le` discriminates.** `le_refl`, `le_trans` and `add_le_add` all
/// hold — footprint-free — of the relation that relates every pair, so an
/// order that separates nothing would satisfy every law proved about it. This
/// is the negative control for `CReal.not_le_one_zero`: the identical script,
/// pointed at `le zero one`, which is TRUE and must therefore be refused as a
/// `Not`.
#[test]
fn the_order_discrimination_route_can_fail() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let rat = p.rat;
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, rat.int);
    let nat_p = rat.int.nat;

    // The two constants, swapped: `le zero one` holds, so `Not` of it does not.
    let one_real = d.kernel().const_(p.one, vec![]);
    let zero_real = d.kernel().const_(p.zero, vec![]);
    let claim = d.const_app(p.le, &[zero_real, one_real]);
    let stmt = d.not(claim);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let index = d.num(3);
    let instance = d.apply(h, &[index]);
    let one_nat = d.num(1);
    let zero_nat = d.zero();
    let stripped = d.lemma(nat_p.le_of_succ_le_succ, &[one_nat, zero_nat, instance]);
    let absurd = d.lemma(nat_p.not_succ_le_zero, &[zero_nat, stripped]);
    let value = d.lam_fv(h_fv, claim, absurd);
    let name = d.kernel().name_str(anon, "Check.not_le_zero_one");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty: stmt,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `Not (CReal.le CReal.zero CReal.one)`, which is false — \
         the order discrimination witness proves nothing"
    );
}

/// **The headline count, read out of the kernel.**
///
/// `CRealPrelude::ordered_ring_laws` is the 22 in the `Real` package's own
/// declaration order — the same order `RatPrelude::ring_laws` uses — and every
/// entry must be a checked `Theorem` with an empty axiom footprint. A dropped,
/// duplicated or demoted law fails here rather than shrinking a sentence in a
/// document nobody re-derives.
#[test]
fn all_twenty_two_ordered_ring_laws_are_checked_theorems_over_creal() {
    let (kernel, p) = built();
    let laws = p.ordered_ring_laws();
    assert_eq!(laws.len(), 22);
    let mut names: Vec<String> = laws
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    names.sort();
    names.dedup();
    assert_eq!(
        names.len(),
        22,
        "the ordered-ring law list must have 22 DISTINCT entries; a repeated \
         name would inflate the count without proving anything"
    );
    for (index, law) in p.ordered_ring_laws().into_iter().enumerate() {
        let rendered = kernel.display_name(law).to_string();
        let declaration = kernel
            .environment()
            .get(law)
            .unwrap_or_else(|| panic!("ring law #{index} ({rendered}) is not declared at all"));
        assert!(
            matches!(declaration, Declaration::Theorem { .. }),
            "ring law #{index} ({rendered}) must be a checked Theorem"
        );
        let footprint: Vec<String> = kernel
            .axiom_footprint(law)
            .into_iter()
            .map(|name| kernel.display_name(name).to_string())
            .collect();
        assert!(
            footprint.is_empty(),
            "ring law #{index} ({rendered}) rests on {footprint:?}"
        );
    }
}

/// The `CReal` and `Rat` law lists are the **same 22 laws in the same order**,
/// name for name under their own namespaces.
///
/// Without this the two lists could drift — `CReal` could quietly omit
/// `mul_assoc` and add a second `mul_comm` — and both would still be "22
/// checked theorems". `build_rat_model_of_arith` pairs `RatPrelude::ring_laws`
/// positionally with the `Real` package, so this is what says `CReal`'s list is
/// the same interface and not merely the same length.
#[test]
fn the_creal_law_list_matches_the_rat_law_list_position_by_position() {
    let (kernel, p) = built();
    let real: Vec<String> = p
        .ordered_ring_laws()
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    let rational: Vec<String> = p
        .rat
        .ring_laws()
        .into_iter()
        .map(|law| kernel.display_name(law).to_string())
        .collect();
    let strip = |full: &str| -> String { full.split('.').skip(1).collect::<Vec<_>>().join(".") };
    let real_tails: Vec<String> = real.iter().map(|name| strip(name)).collect();
    let rational_tails: Vec<String> = rational.iter().map(|name| strip(name)).collect();
    assert_eq!(
        real_tails, rational_tails,
        "CReal's ordered-ring law list must be the SAME 22 laws in the SAME \
         order as Rat's, or the two are not the same interface"
    );
}

/// The apartness laws say what Bishop says they say, rendered verbatim.
///
/// The statements are the point here, not the footprints: `Apart` defined as
/// `Not ∘ Equiv` would satisfy symmetry, irreflexivity and the congruence with
/// an empty footprint apiece, and it is exactly the relation the inverse cannot
/// be defined over. So the *definition* is asserted too, through
/// `CReal.apart_zero_one` — which is `zero_lt_one` under `Or.inl` and could not
/// be proved for a relation that separates nothing.
#[test]
fn the_apartness_laws_have_the_statements_bishop_specifies() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.apart_symm),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Apart x0 x1) -> CReal.Apart x1 x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.apart_irrefl),
        "((x0 : CReal) -> Not (CReal.Apart x0 x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.apart_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         ((x6 : CReal.Apart x0 x2) -> CReal.Apart x1 x3)))))))"
    );
    // ONE-WAY. The converse is Markov's principle; nothing here proves it and
    // nothing here assumes it.
    assert_eq!(
        rendered(&mut kernel, p.not_equiv_of_apart),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Apart x0 x1) -> \
         Not (CReal.Equiv x0 x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.apart_zero_one),
        "CReal.Apart CReal.zero CReal.one"
    );
}

/// **The missing structure is a theorem.** `CReal.no_total_inverse` refutes
/// every total multiplicative inverse at once, so "the inverse is partial"
/// is a proved obstruction rather than a scoping note — the standard
/// `Complex.no_compatible_order` set.
#[test]
fn no_function_on_all_of_creal_is_a_multiplicative_inverse() {
    let (kernel, p) = built();
    let ty = match kernel
        .environment()
        .get(p.no_total_inverse)
        .expect("CReal.no_total_inverse must be declared")
    {
        Declaration::Theorem { ty, .. } => *ty,
        other => panic!("{other:?} is not a theorem"),
    };
    let rendered = kernel
        .render_lean(ty)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(
        rendered,
        "((x0 : ((x0 : CReal) -> CReal)) -> \
         Not (((x1 : CReal) -> CReal.Equiv (CReal.mul x1 (x0 x1)) CReal.one)))"
    );
    let footprint: Vec<String> = kernel
        .axiom_footprint(p.no_total_inverse)
        .into_iter()
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    assert!(
        footprint.is_empty(),
        "the refutation of a total inverse rests on {footprint:?}"
    );
}

/// The negative control for [`no_function_on_all_of_creal_is_a_multiplicative_inverse`]:
/// the **identical script**, with `CReal.one` replaced by `CReal.zero` in the
/// statement, is REFUSED.
///
/// `∀ f, ¬ ∀ x, x · f x ≈ 0` is false — `f := fun _ => zero` satisfies the
/// inner law by `mul_zero` — so a script that proved it would prove anything.
/// The refusal is what says `no_total_inverse` closes on the *content* of
/// `Equiv.not_zero_one` and not on a shape that would go through for any
/// right-hand side.
#[test]
fn the_no_total_inverse_route_cannot_refute_a_universally_zero_product() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let function_ty = d.arrow(carrier, carrier);

    let f_fv = d.fresh_fvar();
    let f = d.kernel().fvar(f_fv);
    // The one changed token: the target of the inner law is `zero`, not `one`.
    let target = d.kernel().const_(p.zero, vec![]);
    let law = {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let applied = d.apply(f, &[x]);
        let product = d.const_app(p.mul, &[x, applied]);
        let claim = d.const_app(p.equiv, &[product, target]);
        d.pi_fv(x_fv, carrier, claim)
    };
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);

    let zero = d.kernel().const_(p.zero, vec![]);
    let reciprocal = d.apply(f, &[zero]);
    let product = d.const_app(p.mul, &[zero, reciprocal]);
    let flipped = d.const_app(p.mul, &[reciprocal, zero]);
    let commuted = d.lemma(p.mul_comm, &[zero, reciprocal]);
    let vanishes = d.lemma(p.mul_zero, &[reciprocal]);
    let collapses = d.lemma(p.equiv_trans, &[product, flipped, zero, commuted, vanishes]);
    let restored = d.lemma(p.equiv_symm, &[product, zero, collapses]);
    let at_zero = d.apply(h, &[zero]);
    let degenerate = d.lemma(p.equiv_trans, &[zero, product, target, restored, at_zero]);
    let refuted = d.lemma(p.not_zero_one, &[]);
    let contradiction = d.apply(refuted, &[degenerate]);

    let value = {
        let with_h = d.lam_fv(h_fv, law, contradiction);
        d.lam_fv(f_fv, function_ty, with_h)
    };
    let ty = {
        let negated = d.not(law);
        d.pi_fv(f_fv, function_ty, negated)
    };
    let name = d.kernel().name_str(anon, "Check.no_total_annihilator");
    let refused = d.kernel().add_declaration(crate::Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted a refutation of `∀ x, x · f x ≈ 0`, which is FALSE \
         (take f := fun _ => zero). The no_total_inverse script would then close \
         for any right-hand side, and its content would be nil."
    );
}

/// **`0 < x` and `∃ k, 1/(k+1) ≤ x` are the same proposition — and that is
/// exactly why the inverse cannot take a `Prop` as its domain.**
///
/// The two directions are asserted verbatim. `pos_bound_of_lt` says the
/// separating modulus always exists; `Exists` is a `Prop`, so `Exists.rec`
/// eliminates only into `Prop` and the `k` can never be extracted into a
/// `CReal`. `PosBound x k` is a `Prop` *about a `Nat` the caller supplies*,
/// which is why a function may take it and still return a `CReal`.
#[test]
fn positivity_and_a_witnessed_modulus_are_the_same_proposition() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.pos_of_pos_bound),
        "((x0 : CReal) -> ((x1 : AxNat) -> ((x2 : CReal.PosBound x0 x1) -> \
         CReal.lt CReal.zero x0)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.pos_bound_of_lt),
        "((x0 : CReal) -> ((x1 : CReal.lt CReal.zero x0) -> \
         Exists.{1} AxNat (fun (x2 : AxNat) => CReal.PosBound x0 x2)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.of_rat_le),
        "((x0 : Rat) -> ((x1 : Rat) -> ((x2 : Rat.le x0 x1) -> \
         CReal.le (CReal.ofRat x0) (CReal.ofRat x1))))"
    );
    for (label, name) in [
        ("ofRat_le", p.of_rat_le),
        ("pos_of_pos_bound", p.pos_of_pos_bound),
        ("pos_bound_of_lt", p.pos_bound_of_lt),
    ] {
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "CReal.{label} rests on {footprint:?}");
    }
}

/// **Positivity is closed under multiplication over the constructed reals**, and
/// the statement is asserted verbatim because `mul_nonneg` — which IS one of the
/// 22 — holds of the zero product and this does not.
#[test]
fn positivity_is_closed_under_multiplication() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.mul_pos),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.lt CReal.zero x0) -> \
         ((x3 : CReal.lt CReal.zero x1) -> CReal.lt CReal.zero (CReal.mul x0 x1)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.of_rat_pos),
        "((x0 : Rat) -> ((x1 : Rat.lt Rat.zero x0) -> \
         CReal.lt CReal.zero (CReal.ofRat x0)))"
    );
    for (label, name) in [("mul_pos", p.mul_pos), ("ofRat_pos", p.of_rat_pos)] {
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "CReal.{label} rests on {footprint:?}");
    }
}

/// **The multiplicative inverse exists, and the modulus is the argument that
/// makes it exist.** Statements asserted verbatim, because a theorem named
/// `mul_inv_cancel` saying something weaker would pass a footprint check.
///
/// Read `CReal.inv`'s type as the whole ADR-0510 argument in one line: the
/// `Nat` is explicit and the `PosBound` is a hypothesis over it, so nothing is
/// ever eliminated out of a `Prop` into `Type` — which is precisely what
/// `Apart x zero` (an `Or`) would demand.
#[test]
fn the_inverse_is_partial_and_its_modulus_is_an_explicit_nat() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    assert_eq!(
        rendered(&mut kernel, p.inv),
        "((x0 : CReal) -> ((x1 : AxNat) -> ((x2 : CReal.PosBound x0 x1) -> CReal)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.inv_shift),
        "((x0 : AxNat) -> AxNat)"
    );
    assert_eq!(
        rendered(&mut kernel, p.mul_inv_cancel),
        "((x0 : CReal) -> ((x1 : AxNat) -> ((x2 : CReal.PosBound x0 x1) -> \
         CReal.Equiv (CReal.mul x0 (CReal.inv x0 x1 x2)) CReal.one)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.inv_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : AxNat) -> ((x3 : AxNat) -> \
         ((x4 : CReal.PosBound x0 x2) -> ((x5 : CReal.PosBound x1 x3) -> \
         ((x6 : CReal.Equiv x0 x1) -> \
         CReal.Equiv (CReal.inv x0 x2 x4) (CReal.inv x1 x3 x5))))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.inv_index_irrelevant),
        "((x0 : CReal) -> ((x1 : AxNat) -> ((x2 : AxNat) -> \
         ((x3 : CReal.PosBound x0 x1) -> ((x4 : CReal.PosBound x0 x2) -> \
         CReal.Equiv (CReal.inv x0 x1 x3) (CReal.inv x0 x2 x4))))))"
    );
    for (label, name) in [
        ("invShift", p.inv_shift),
        ("inv", p.inv),
        ("mul_inv_cancel", p.mul_inv_cancel),
        ("inv_congr", p.inv_congr),
        ("inv_index_irrelevant", p.inv_index_irrelevant),
    ] {
        let footprint: Vec<String> = kernel
            .axiom_footprint(name)
            .into_iter()
            .map(|entry| kernel.display_name(entry).to_string())
            .collect();
        assert!(footprint.is_empty(), "CReal.{label} rests on {footprint:?}");
    }
}

/// **The inverse's domain is inhabited, and the inverse is not the constant
/// zero.** Without this the whole slice is vacuous: every statement about
/// `CReal.inv` is guarded by `PosBound x k`, so if that predicate had no
/// inhabitants `mul_inv_cancel`, `inv_congr` and `inv_index_irrelevant` would
/// all hold, footprint-free, of an operation that never runs.
///
/// Both halves go through the kernel. `PosBound CReal.one 0` is admitted — the
/// modulus `1/(0+1)` is `Rat.one`, so `CReal.le_refl` closes it — and then
/// `∀ h, ¬ Equiv (inv one 0 h) zero` is admitted from `mul_inv_cancel` alone:
/// if `1⁻¹ ≈ 0` then `1 · 1⁻¹ ≈ 1 · 0 ≈ 0` and also `≈ 1`, and
/// `Equiv.not_zero_one` refutes that **by computation**.
#[test]
fn the_inverses_domain_is_inhabited_and_the_inverse_is_not_the_zero_function() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);

    let one = d.kernel().const_(p.one, vec![]);
    let zero = d.kernel().const_(p.zero, vec![]);
    let zero_nat = d.num(0);
    let bound_ty = d.const_app(p.pos_bound, &[one, zero_nat]);
    let bound_proof = d.lemma(p.le_refl, &[one]);
    let name = d.kernel().name_str(anon, "Check.pos_bound_one");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: bound_ty,
        value: bound_proof,
    });
    assert!(
        admitted.is_ok(),
        "CReal.PosBound one 0 is not inhabited, so every theorem about \
         CReal.inv is vacuous: {admitted:?}"
    );

    // `∀ (h : PosBound one 0), ¬ Equiv (inv one 0 h) zero`.
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let reciprocal = d.const_app(p.inv, &[one, zero_nat, h]);
    let claim = d.const_app(p.equiv, &[reciprocal, zero]);
    let he_fv = d.fresh_fvar();
    let he = d.kernel().fvar(he_fv);

    let cancel = d.lemma(p.mul_inv_cancel, &[one, zero_nat, h]);
    let product = d.const_app(p.mul, &[one, reciprocal]);
    let degenerate = d.const_app(p.mul, &[one, zero]);
    let reflexive = d.lemma(p.equiv_refl, &[one]);
    let stepped = d.lemma(p.mul_congr, &[one, one, reciprocal, zero, reflexive, he]);
    let vanish = d.lemma(p.mul_zero, &[one]);
    let collapsed = d.lemma(p.equiv_trans, &[product, degenerate, zero, stepped, vanish]);
    let flipped = d.lemma(p.equiv_symm, &[product, zero, collapsed]);
    let absurd = d.lemma(p.equiv_trans, &[zero, product, one, flipped, cancel]);
    let refuted = d.lemma(p.not_zero_one, &[]);
    let contradiction = d.apply(refuted, &[absurd]);

    let value = {
        let with_he = d.lam_fv(he_fv, claim, contradiction);
        d.lam_fv(h_fv, bound_ty, with_he)
    };
    let ty = {
        let negated = d.not(claim);
        d.pi_fv(h_fv, bound_ty, negated)
    };
    let name = d.kernel().name_str(anon, "Check.inv_one_is_not_zero");
    let admitted = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        admitted.is_ok(),
        "the kernel refused `1⁻¹ is not zero`, which follows from \
         mul_inv_cancel and Equiv.not_zero_one alone: {admitted:?}"
    );
}

/// The negative controls for the inverse: **the same proof terms, pointed at
/// statements one token away, are REFUSED.**
///
/// `∀ x k h, x · x⁻¹ ≈ 0` is false wherever `PosBound` is inhabited — it would
/// give `0 ≈ 1` through `Check.inv_one_is_not_zero`'s argument — and
/// `∀ x k h, x⁻¹ ≈ x` is false at `x = 1 + 1`. If either mutation were
/// accepted, the verbatim statement tests above would be pinning a shape rather
/// than a fact.
#[test]
fn the_inverse_route_cannot_prove_the_one_token_mutations() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let nat = d.nat_ty();
    let zero = d.kernel().const_(p.zero, vec![]);

    // `x · x⁻¹ ≈ 0`, not `≈ 1`.
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let k_fv = d.fresh_fvar();
    let k = d.kernel().fvar(k_fv);
    let bound_ty = d.const_app(p.pos_bound, &[x, k]);
    let h_fv = d.fresh_fvar();
    let h = d.kernel().fvar(h_fv);
    let reciprocal = d.const_app(p.inv, &[x, k, h]);
    let product = d.const_app(p.mul, &[x, reciprocal]);
    let claim = d.const_app(p.equiv, &[product, zero]);
    let ty = {
        let inner = d.pi_fv(h_fv, bound_ty, claim);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(x_fv, carrier, with_k)
    };
    let value = {
        let instance = d.lemma(p.mul_inv_cancel, &[x, k, h]);
        let with_h = d.lam_fv(h_fv, bound_ty, instance);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(x_fv, carrier, with_k)
    };
    let name = d.kernel().name_str(anon, "Check.inv_annihilates");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `x · x⁻¹ ≈ 0`, which with an inhabited PosBound \
         gives 0 ≈ 1 and refutes Equiv.not_zero_one"
    );

    // `x⁻¹ ≈ x`, from the modulus-irrelevance term.
    let claim = d.const_app(p.equiv, &[reciprocal, x]);
    let ty = {
        let inner = d.pi_fv(h_fv, bound_ty, claim);
        let with_k = d.pi_fv(k_fv, nat, inner);
        d.pi_fv(x_fv, carrier, with_k)
    };
    let value = {
        let instance = d.lemma(p.inv_index_irrelevant, &[x, k, k, h, h]);
        let with_h = d.lam_fv(h_fv, bound_ty, instance);
        let with_k = d.lam_fv(k_fv, nat, with_h);
        d.lam_fv(x_fv, carrier, with_k)
    };
    let name = d.kernel().name_str(anon, "Check.inv_is_the_identity");
    let refused = d.kernel().add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    });
    assert!(
        refused.is_err(),
        "the kernel accepted `x⁻¹ ≈ x`, which is FALSE at x = 1 + 1"
    );
}

/// The lattice laws say what ADR-0519 says they say — **rendered types,
/// verbatim**. An empty axiom footprint on a theorem named `max_le` that says
/// something weaker would pass every other check in this file.
#[test]
fn the_lattice_laws_have_the_statements_adr_0490_specifies() {
    let (mut kernel, p) = built();
    let rendered = |kernel: &mut Kernel, name: crate::NameId| -> String {
        let ty = match kernel.environment().get(name).expect("declared") {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => *ty,
            other => panic!("{other:?} is not a theorem or definition"),
        };
        kernel
            .render_lean(ty)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    };
    // The three operations are total functions on ℝ — `max` and `min` binary,
    // `abs` unary. No side condition, so nothing here can be vacuous by an
    // uninhabited guard; what it CAN be is degenerate, which the two
    // discriminations below rule out.
    assert_eq!(
        rendered(&mut kernel, p.max),
        "((x0 : CReal) -> ((x1 : CReal) -> CReal))"
    );
    assert_eq!(
        rendered(&mut kernel, p.min),
        "((x0 : CReal) -> ((x1 : CReal) -> CReal))"
    );
    assert_eq!(rendered(&mut kernel, p.abs), "((x0 : CReal) -> CReal)");

    assert_eq!(
        rendered(&mut kernel, p.le_max_left),
        "((x0 : CReal) -> ((x1 : CReal) -> CReal.le x0 (CReal.max x0 x1)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.le_max_right),
        "((x0 : CReal) -> ((x1 : CReal) -> CReal.le x1 (CReal.max x0 x1)))"
    );
    assert_eq!(
        rendered(&mut kernel, p.max_le),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.le x0 x2) -> \
         ((x4 : CReal.le x1 x2) -> CReal.le (CReal.max x0 x1) x2)))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.min_le_left),
        "((x0 : CReal) -> ((x1 : CReal) -> CReal.le (CReal.min x0 x1) x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.min_le_right),
        "((x0 : CReal) -> ((x1 : CReal) -> CReal.le (CReal.min x0 x1) x1))"
    );
    assert_eq!(
        rendered(&mut kernel, p.le_min),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal.le x2 x0) -> \
         ((x4 : CReal.le x2 x1) -> CReal.le x2 (CReal.min x0 x1))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.max_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         CReal.Equiv (CReal.max x0 x2) (CReal.max x1 x3)))))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.min_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal) -> ((x3 : CReal) -> \
         ((x4 : CReal.Equiv x0 x1) -> ((x5 : CReal.Equiv x2 x3) -> \
         CReal.Equiv (CReal.min x0 x2) (CReal.min x1 x3)))))))"
    );
    // `abs` is stated through `CReal.abs`, not through the `max x (neg x)` it
    // unfolds to — otherwise these would be `max` laws wearing another name.
    assert_eq!(
        rendered(&mut kernel, p.le_abs_self),
        "((x0 : CReal) -> CReal.le x0 (CReal.abs x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.neg_le_abs),
        "((x0 : CReal) -> CReal.le (CReal.neg x0) (CReal.abs x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.abs_le),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.le x0 x1) -> \
         ((x3 : CReal.le (CReal.neg x0) x1) -> CReal.le (CReal.abs x0) x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.abs_nonneg),
        "((x0 : CReal) -> CReal.le CReal.zero (CReal.abs x0))"
    );
    assert_eq!(
        rendered(&mut kernel, p.abs_congr),
        "((x0 : CReal) -> ((x1 : CReal) -> ((x2 : CReal.Equiv x0 x1) -> \
         CReal.Equiv (CReal.abs x0) (CReal.abs x1))))"
    );
    assert_eq!(
        rendered(&mut kernel, p.not_le_zero_neg_one),
        "Not (CReal.le CReal.zero (CReal.neg CReal.one))"
    );
    assert_eq!(
        rendered(&mut kernel, p.not_equiv_abs_neg_one),
        "Not (CReal.Equiv (CReal.abs (CReal.neg CReal.one)) (CReal.neg CReal.one))"
    );
}

/// **The lattice is not degenerate, and `abs` is not the identity.**
///
/// Nothing in this module carries a side condition, so no statement here is
/// vacuous for want of an inhabited guard — the failure mode is the other one:
/// a degenerate operation satisfying every law. `max x y := x` satisfies
/// `le_max_left` by reflexivity; `abs x := x` satisfies `le_abs_self`,
/// `neg_le_abs` and `abs_le`. Both are ruled out **through the kernel**, from
/// the laws alone:
///
/// - `Equiv (max x x) x` — the join is idempotent, by antisymmetry;
/// - `Equiv (max zero one) one` **and** `¬ Equiv (max zero one) zero` — so
///   `max` is not the left projection;
/// - `¬ Equiv (abs (neg one)) (neg one)`, already a kernel theorem, is
///   **consumed** here rather than merely named.
#[test]
fn the_lattice_is_not_degenerate_and_abs_is_not_the_identity() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let zero = d.kernel().const_(p.zero, vec![]);
    let one = d.kernel().const_(p.one, vec![]);

    // `∀ x, Equiv (max x x) x`, by antisymmetry — needs BOTH directions, so a
    // `max` that ignored one argument would still pass but a `max` that
    // returned a constant would not.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let combined = d.const_app(p.max, &[x, x]);
        let up = d.lemma(p.le_max_left, &[x, x]);
        let reflexive = d.lemma(p.le_refl, &[x]);
        let down = d.lemma(p.max_le, &[x, x, x, reflexive, reflexive]);
        let body = d.lemma(p.equiv_of_le_le, &[combined, x, down, up]);
        let value = d.lam_fv(x_fv, carrier, body);
        let ty = {
            let claim = d.const_app(p.equiv, &[combined, x]);
            d.pi_fv(x_fv, carrier, claim)
        };
        let name = d.kernel().name_str(anon, "Check.max_idempotent");
        let admitted = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            admitted.is_ok(),
            "the kernel refused `max x x ≈ x`, which is antisymmetry over \
             le_max_left and max_le: {admitted:?}"
        );
    }

    // `¬ Equiv (max zero one) zero` — `max` is not the left projection. If it
    // were, `one ≤ max zero one ≈ zero` would refute not_le_one_zero.
    {
        let combined = d.const_app(p.max, &[zero, one]);
        let hypothesis = d.const_app(p.equiv, &[combined, zero]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let dominated = d.lemma(p.le_max_right, &[zero, one]);
        let collapsed = d.lemma(p.le_of_equiv, &[combined, zero, h]);
        let absurd = d.lemma(p.le_trans, &[one, combined, zero, dominated, collapsed]);
        let refuted = d.lemma(p.not_le_one_zero, &[]);
        let contradiction = d.apply(refuted, &[absurd]);
        let value = d.lam_fv(h_fv, hypothesis, contradiction);
        let ty = d.not(hypothesis);
        let name = d
            .kernel()
            .name_str(anon, "Check.max_is_not_the_left_projection");
        let admitted = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            admitted.is_ok(),
            "the kernel refused `max 0 1 ≉ 0`, so every lattice law here would \
             hold of the left projection: {admitted:?}"
        );
    }

    // `¬ Equiv (min zero one) one` — and `min` is not the right projection.
    {
        let combined = d.const_app(p.min, &[zero, one]);
        let hypothesis = d.const_app(p.equiv, &[combined, one]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let dominated = d.lemma(p.min_le_left, &[zero, one]);
        let reversed = d.lemma(p.equiv_symm, &[combined, one, h]);
        let lifted = d.lemma(p.le_of_equiv, &[one, combined, reversed]);
        let absurd = d.lemma(p.le_trans, &[one, combined, zero, lifted, dominated]);
        let refuted = d.lemma(p.not_le_one_zero, &[]);
        let contradiction = d.apply(refuted, &[absurd]);
        let value = d.lam_fv(h_fv, hypothesis, contradiction);
        let ty = d.not(hypothesis);
        let name = d
            .kernel()
            .name_str(anon, "Check.min_is_not_the_right_projection");
        let admitted = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            admitted.is_ok(),
            "the kernel refused `min 0 1 ≉ 1`: {admitted:?}"
        );
    }

    // `abs` is not the identity: `not_equiv_abs_neg_one` is CONSUMED, so a
    // deleted or weakened version of it fails here and not only in the
    // inventory.
    {
        let negative = d.const_app(p.neg, &[one]);
        let magnitude = d.const_app(p.abs, &[negative]);
        let claim = d.const_app(p.equiv, &[magnitude, negative]);
        let refuted = d.lemma(p.not_equiv_abs_neg_one, &[]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let contradiction = d.apply(refuted, &[h]);
        let false_ty = d.false_ty();
        let value = d.lam_fv(h_fv, claim, contradiction);
        let ty = d.arrow(claim, false_ty);
        let name = d.kernel().name_str(anon, "Check.abs_is_not_the_identity");
        let admitted = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            admitted.is_ok(),
            "the kernel refused `|−1| ≉ −1`, so `abs x := x` would satisfy \
             everything else proved about abs: {admitted:?}"
        );
    }
}

/// The negative controls for the lattice: **the same proof terms, pointed at
/// statements one token away, are REFUSED.**
///
/// Without these, the verbatim-statement test above pins a shape rather than a
/// fact — a kernel whose conversion checker accepted anything would make every
/// assertion in this file pass.
#[test]
fn the_lattice_route_cannot_prove_the_one_token_mutations() {
    use crate::int_prelude::ops::IntDev;
    use crate::nat_prelude::NatOps;

    let (mut kernel, p) = built();
    let anon = kernel.anon();
    let mut d = IntDev::new(&mut kernel, p.rat.int);
    let carrier = d.kernel().const_(p.creal, vec![]);
    let one = d.kernel().const_(p.one, vec![]);
    let zero = d.kernel().const_(p.zero, vec![]);

    // `max x y ≤ x`, from `le_max_left` — the direction reversed. FALSE at
    // x = 0, y = 1.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let combined = d.const_app(p.max, &[x, y]);
        let claim = d.const_app(p.le, &[combined, x]);
        let value = {
            let instance = d.lemma(p.le_max_left, &[x, y]);
            let with_y = d.lam_fv(y_fv, carrier, instance);
            d.lam_fv(x_fv, carrier, with_y)
        };
        let ty = {
            let with_y = d.pi_fv(y_fv, carrier, claim);
            d.pi_fv(x_fv, carrier, with_y)
        };
        let name = d.kernel().name_str(anon, "Check.max_is_below_its_argument");
        let refused = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            refused.is_err(),
            "the kernel accepted `max x y ≤ x`, which is FALSE at x = 0, y = 1"
        );
    }

    // `|x| ≤ 0`, from `abs_nonneg` — the order reversed. FALSE at x = 1.
    {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let magnitude = d.const_app(p.abs, &[x]);
        let claim = d.const_app(p.le, &[magnitude, zero]);
        let value = {
            let instance = d.lemma(p.abs_nonneg, &[x]);
            d.lam_fv(x_fv, carrier, instance)
        };
        let ty = d.pi_fv(x_fv, carrier, claim);
        let name = d.kernel().name_str(anon, "Check.abs_is_nonpositive");
        let refused = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            refused.is_err(),
            "the kernel accepted `|x| ≤ 0`, which is FALSE at x = 1"
        );
    }

    // `¬ (|1| ≈ 1)` — `not_equiv_abs_neg_one`'s own script with `neg one`
    // replaced by `one`. The statement is FALSE (`|1| ≈ 1` holds), so the
    // discrimination above must NOT generalize.
    {
        let magnitude = d.const_app(p.abs, &[one]);
        let hypothesis = d.const_app(p.equiv, &[magnitude, one]);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let nonneg = d.lemma(p.abs_nonneg, &[one]);
        let reflexive = d.lemma(p.equiv_refl, &[zero]);
        let absurd = d.lemma(
            p.le_congr,
            &[zero, zero, magnitude, one, reflexive, h, nonneg],
        );
        let refuted = d.lemma(p.not_le_zero_neg_one, &[]);
        let contradiction = d.apply(refuted, &[absurd]);
        let value = d.lam_fv(h_fv, hypothesis, contradiction);
        let ty = d.not(hypothesis);
        let name = d.kernel().name_str(anon, "Check.abs_one_is_not_one");
        let refused = d.kernel().add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        });
        assert!(
            refused.is_err(),
            "the kernel accepted `|1| ≉ 1`, which is FALSE — so the abs \
             discrimination would be proving nothing about the sign"
        );
    }
}

/// **The derivative says what it claims, character for character** — the
/// carrier's `spec` and the one nonlinear witness.
///
/// An empty axiom footprint cannot carry either claim. A `spec` whose bound
/// were `1/(e+1)` alone, WITHOUT the `·|y−x|` factor, is a different and much
/// weaker notion (it would not force differentiability at all, only a crude
/// closeness), and it is equally axiom-free. A `hasDerivative_sq` concluding
/// `fun x => x` instead of `fun x => x + x` is simply the wrong derivative and
/// is likewise axiom-free. What separates them is the STATEMENT.
///
/// Three things to read in the pinned `spec`, all load-bearing:
///
/// * **The modulus is a FIELD of the carrier**, appearing in the hypothesis as
///   `HasDerivativeOn.modulus x0 x1 x2 x3 x4 x5`. This is uniform
///   differentiability on `[a,b]`, not a pointwise limit. That is forced, not
///   stylistic: Markov's principle is unavailable here, `Apart` is an `Or`, and
///   `Or`'s recursor does not eliminate into `Type`, so nothing can branch on a
///   real comparison to compute a modulus.
/// * **Four `CReal.le` premises confine BOTH points to `[a,b]`.** Dropping the
///   ones about `y` would make the conclusion a statement about a half-open
///   region and the witnesses would not survive.
/// * **The error bound is `(1/(e+1)) · |y−x|`, a PRODUCT.** This is why the
///   carrier could not reuse `UniformlyContinuousOn`'s rational-constant
///   closeness bound unchanged.
#[test]
fn the_derivative_is_stated_exactly() {
    use crate::env::Declaration;
    let mut k = Kernel::new();
    let p = build_creal_prelude(&mut k).expect("CReal prelude must build");

    let rendered = |k: &Kernel, name: crate::NameId| -> String {
        match k
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{} must be declared", k.display_name(name)))
        {
            Declaration::Theorem { ty, .. } | Declaration::Definition { ty, .. } => {
                k.render_lean(*ty)
            }
            other => panic!("{other:?} is not a theorem or definition"),
        }
    };

    let spec = rendered(&k, p.hd_spec);
    assert!(
        spec.contains(
            "CReal.mul (CReal.ofRat (Rat.natDivSucc (AxNat.succ AxNat.zero) x5)) \
                       (CReal.abs (CReal.add x7 (CReal.neg x6)))"
        ),
        "the error bound must be (1/(e+1))*|y-x|; without the |y-x| factor this \
         is a crude closeness condition, not differentiability: {spec}"
    );
    assert_eq!(
        spec, HAS_DERIVATIVE_ON_SPEC_TYPE,
        "CReal.HasDerivativeOn.spec"
    );

    let sq = rendered(&k, p.has_derivative_sq);
    assert!(
        sq.contains("CReal.add x2 x2"),
        "the derivative of r*r is x+x, not x: {sq}"
    );
    assert_eq!(sq, HAS_DERIVATIVE_SQ_TYPE, "CReal.hasDerivative_sq");
}

/// The pinned type of `CReal.HasDerivativeOn.spec`.
const HAS_DERIVATIVE_ON_SPEC_TYPE: &str = "((x0 : ((x0 : CReal) -> CReal)) -> ((x1 : ((x1 : CReal) -> CReal)) -> ((x2 : CReal) -> ((x3 : CReal) -> ((x4 : CReal.HasDerivativeOn x0 x1 x2 x3) -> ((x5 : AxNat) -> ((x6 : CReal) -> ((x7 : CReal) -> ((x8 : CReal.le x2 x6) -> ((x9 : CReal.le x6 x3) -> ((x10 : CReal.le x2 x7) -> ((x11 : CReal.le x7 x3) -> ((x12 : CReal.le (CReal.abs (CReal.add x7 (CReal.neg x6))) (CReal.ofRat (Rat.natDivSucc (AxNat.succ AxNat.zero) (CReal.HasDerivativeOn.modulus x0 x1 x2 x3 x4 x5)))) -> CReal.le (CReal.abs (CReal.add (CReal.add (x0 x7) (CReal.neg (x0 x6))) (CReal.neg (CReal.mul (x1 x6) (CReal.add x7 (CReal.neg x6)))))) (CReal.mul (CReal.ofRat (Rat.natDivSucc (AxNat.succ AxNat.zero) x5)) (CReal.abs (CReal.add x7 (CReal.neg x6)))))))))))))))))";

/// The pinned type of `CReal.hasDerivative_sq`.
const HAS_DERIVATIVE_SQ_TYPE: &str = "((x0 : CReal) -> ((x1 : CReal) -> CReal.HasDerivativeOn (fun (x2 : CReal) => CReal.mul x2 x2) (fun (x2 : CReal) => CReal.add x2 x2) x0 x1))";
