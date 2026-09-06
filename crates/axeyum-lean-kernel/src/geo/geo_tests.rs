//! Does the kernel accept [`build_geo_prelude`], is every declaration it
//! produces axiom-free, and do the definitions COMPUTE the values their names
//! claim?
//!
//! Three things here are worth more than the count of tests:
//!
//! 1. **The "every declaration" test derives its population from the
//!    ENVIRONMENT**, not from a list in this file — every name rendering under
//!    `Geo.` is collected from `Environment::iter` and the set is required to
//!    equal the set the prelude handle names. A declaration added to
//!    `geo.rs`/`geo/qplane.rs` and forgotten here fails the test; so does one
//!    deleted from the handle. `Environment::contains` is asserted FIRST,
//!    because an empty `Kernel::axiom_footprint` is also what a missing name
//!    returns.
//! 2. **Every `Definition` is evaluated at concrete, small, discriminating
//!    arguments.** The trusted gate cannot tell you a definition is wrong: a
//!    function computing the wrong value has the right type. Each evaluation
//!    test carries its own negative half — `Geo.QPlane.join`'s `a` coefficient
//!    is `y Q - y P`, and it is checked NOT to be `x P - x Q`, which is the
//!    swap the mutation suite runs.
//! 3. **The `Sort 1` universe control** is stated in the open as well as
//!    inside `declare_record`, so deleting it from the spine is visible here.

use super::{
    APART, FIELD_COUNT, FIELD_SUFFIXES, GeoPrelude, JOIN_UNIQUE, L_EQ, LINE, ON, P_EQ, POINT,
    TRIANGLE, TWO_POINTS, build_geo_prelude, incidence_fields,
};
use crate::NatOps;
use crate::{Kernel, on_a_deep_stack};

fn built() -> (Kernel, GeoPrelude) {
    use std::sync::OnceLock;
    static TEMPLATE: OnceLock<(Kernel, GeoPrelude)> = OnceLock::new();
    let (kernel, prelude) = TEMPLATE.get_or_init(|| {
        on_a_deep_stack(|| {
            let mut kernel = Kernel::new();
            let prelude = build_geo_prelude(&mut kernel).expect("Geo prelude must build");
            (kernel, prelude)
        })
    });
    (kernel.clone(), *prelude)
}

/// The build itself, with the kernel's rejection rendered rather than
/// `Debug`-formatted.
#[test]
fn geo_prelude_builds() {
    on_a_deep_stack(|| {
        let mut kernel = Kernel::new();
        match build_geo_prelude(&mut kernel) {
            Ok(_) => {}
            Err(error) => {
                let nat = crate::build_nat_prelude(&mut kernel).expect("Nat prelude must build");
                let mut dev = crate::NatDev::new(&mut kernel, nat);
                let explained = crate::NatOps::explain(&mut dev, &error);
                panic!("the kernel refused a real proof: {explained}");
            }
        }
    });
}

/// Every name this module declares, paired with its label. **Derived from the
/// prelude handle, not from a literal list of names** — the record's 21
/// selectors come from `RecordNames` itself, so a twenty-second field cannot
/// be added without appearing here.
fn all_declarations(p: GeoPrelude) -> Vec<crate::name::NameId> {
    let q = p.qplane;
    let mut out: Vec<crate::name::NameId> = vec![
        p.record.ind,
        p.record.mk,
        p.record.rec,
        p.collinear,
        p.collinear_intro,
        p.collinear_perm,
        p.distinct_lines_meet_once,
        p.triangle_not_collinear,
        p.parallel,
        p.parallel_symm,
        p.parallel_irrefl,
        // --- the rational model -------------------------------------------
        q.qpoint,
        q.qpoint_mk,
        q.qpoint_rec,
        q.qpoint_x,
        q.qpoint_y,
        q.qpoint_eta,
        q.qpoint_ext,
        q.qpoint_eq_trans,
        q.qline0,
        q.qline0_mk,
        q.qline0_rec,
        q.qline0_a,
        q.qline0_b,
        q.qline0_c,
        q.nondeg,
        q.nondeg_or,
        q.qline,
        q.eq_or_ne,
        q.on_raw,
        q.on,
        q.apart,
        q.line_equiv,
        q.line_equiv_refl,
        q.line_equiv_symm,
        q.line_equiv_trans,
        q.on_point,
        q.on_line,
        q.apart_ne,
        q.apart_symm,
        q.apart_congr,
        q.join,
        q.join_on_left,
        q.join_on_right,
        q.join_nondeg,
        q.join_exists,
        q.on_pivot,
        q.on_of_prop,
        q.join_prop,
        q.join_unique,
        q.shift,
        q.shift_on,
        q.shift_apart,
        q.base_point,
        q.two_points,
        q.triangle,
        q.instance,
    ];
    let rp = p.rplane;
    out.extend([
        // --- the real model -----------------------------------------------
        rp.rline0,
        rp.rline0_mk,
        rp.rline0_rec,
        rp.rline0_a,
        rp.rline0_b,
        rp.rline0_c,
        rp.nondeg,
        rp.rline,
        rp.on_raw,
        rp.on,
        rp.apart,
        rp.line_equiv,
        rp.line_equiv_refl,
        rp.line_equiv_symm,
        rp.line_equiv_trans,
        rp.pos_bound_congr,
        rp.not_zero_of_pos_bound,
        rp.cancel_pos_bound,
        rp.point_refl,
        rp.point_symm,
        rp.point_trans,
        rp.on_point,
        rp.on_line,
        rp.apart_ne,
        rp.apart_symm,
        rp.apart_congr,
        rp.join,
        rp.join_on_left,
        rp.join_on_right,
        rp.join_nondeg,
        rp.join_exists,
        rp.pivot_ab,
        rp.defect_ac,
        rp.defect_bc,
        rp.defect_swap,
        rp.on_of_defects,
        rp.join_unique,
        rp.two_points_raw,
        rp.two_points,
        rp.triangle,
        rp.instance,
    ]);
    for i in 0..p.record.field_count() {
        out.push(p.record.sel(i));
    }
    out
}

/// Every declaration exists AND has an empty axiom footprint. The
/// `Environment::contains` assertion comes first on purpose: an empty
/// footprint is also what a *missing* name returns.
#[test]
fn every_declaration_is_present_and_axiom_free() {
    let (kernel, prelude) = built();
    let all = all_declarations(prelude);
    assert_eq!(
        all.len(),
        FIELD_COUNT + 11 + 46 + 41,
        "the declaration list is out of step with the record's field count"
    );
    for name in all {
        let label = kernel.display_name(name).to_string();
        assert!(
            kernel.environment().get(name).is_some(),
            "{label} was never declared"
        );
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} depends on axioms: {footprint:?}"
        );
    }
}

/// **The population comes from the environment, not from this file.** Every
/// name rendering under `Geo.` is collected from `Environment::iter`, and the
/// set is required to equal the set [`all_declarations`] names. A declaration
/// added to the module and forgotten in the handle fails here; so does one
/// listed in the handle that the build never emitted.
#[test]
fn the_handle_names_every_live_geo_declaration() {
    use std::collections::BTreeSet;
    let (kernel, prelude) = built();
    let live: BTreeSet<String> = kernel
        .environment()
        .iter()
        .map(|(name, _)| kernel.display_name(*name).to_string())
        .filter(|rendered| rendered == "Geo" || rendered.starts_with("Geo."))
        .collect();
    // Vacuity floor: an empty `live` would make the set equality trivially
    // true against an empty handle list, and a filter typo produces exactly
    // that.
    assert!(
        live.len() >= 110,
        "only {} declarations render under `Geo.` -- the filter is wrong, or \
         the build stopped early",
        live.len()
    );
    let listed: BTreeSet<String> = all_declarations(prelude)
        .into_iter()
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    let missing: Vec<&String> = live.difference(&listed).collect();
    let phantom: Vec<&String> = listed.difference(&live).collect();
    assert!(
        missing.is_empty() && phantom.is_empty(),
        "declared but not named by the handle: {missing:?}; \
         named by the handle but not declared: {phantom:?}"
    );
}

/// The field list and the suffix table describe the same record.
#[test]
fn field_list_matches_the_suffix_table() {
    let specs = incidence_fields();
    assert_eq!(specs.len(), FIELD_COUNT);
    for (i, spec) in specs.iter().enumerate() {
        assert_eq!(
            spec.suffix, FIELD_SUFFIXES[i],
            "field {i}'s shape and its selector name disagree"
        );
    }
}

/// The field-index constants really do point at the fields their names claim.
#[test]
fn field_indices_name_their_fields() {
    for (index, expected) in [
        (POINT, "point"),
        (LINE, "line"),
        (P_EQ, "pEq"),
        (L_EQ, "lEq"),
        (ON, "on"),
        (APART, "apart"),
        (JOIN_UNIQUE, "joinUnique"),
        (TWO_POINTS, "twoPoints"),
        (TRIANGLE, "triangle"),
    ] {
        assert_eq!(FIELD_SUFFIXES[index], expected);
    }
}

/// **Negative control for the whole record**: the same 21 fields declared at
/// `Sort 1` must be REFUSED. `declare_record` runs this control itself on
/// every build; this test states it in the open so deleting it from
/// `declare_record` is visible here too.
#[test]
fn the_record_is_refused_at_sort_one() {
    on_a_deep_stack(|| {
        use crate::nat_prelude::structures::close_pi;
        let mut kernel = Kernel::new();
        let cpoint = crate::build_cpoint_prelude(&mut kernel).expect("CPoint prelude must build");
        let logic = cpoint.creal.rat.int.logic;
        let l0 = kernel.level_zero();
        let l1 = kernel.level_succ(l0);

        let specs = incidence_fields();
        let fvars: Vec<u64> = (0..specs.len()).map(|i| 10_000 + i as u64).collect();
        let mut ctor_fields: Vec<(u64, crate::expr::ExprId)> = Vec::with_capacity(specs.len());
        let mut vals: Vec<crate::expr::ExprId> = Vec::with_capacity(specs.len());
        for (i, spec) in specs.iter().enumerate() {
            let ty = (spec.build)(&mut kernel, &logic, l1, &vals);
            ctor_fields.push((fvars[i], ty));
            let v = kernel.fvar(fvars[i]);
            vals.push(v);
        }
        let anon = kernel.anon();
        let ind = kernel.name_str(anon, "GeoSortOneControl");
        let mk = kernel.name_str(ind, "mk");
        let sort1 = kernel.sort(l1);
        let ind_const = kernel.const_(ind, vec![]);
        let ctor = close_pi(&mut kernel, &ctor_fields, ind_const);
        assert!(
            kernel
                .add_inductive(ind, &[], 0, sort1, &[(mk, ctor)])
                .is_err(),
            "a record carrying two Sort 1 fields was ACCEPTED at Sort 1 -- the \
             ADR-1495 ConstructorFieldUniverseTooBig guard did not fire"
        );
    });
}

/// `Collinear` really is a definition that unfolds to the three-`on`
/// existential: `collinear_intro`'s conclusion is stated with `Collinear` and
/// its proof is an `Exists.intro`, so the kernel accepted the delta step. This
/// test re-checks the *type* rather than trusting the build: it renders and
/// looks for both the definitional head and the three `on` applications.
#[test]
fn collinear_unfolds_to_the_three_point_existential() {
    let (kernel, prelude) = built();
    let decl = kernel
        .environment()
        .get(prelude.collinear)
        .expect("Collinear must be declared");
    let crate::env::Declaration::Definition { ty, value, .. } = decl else {
        panic!("Collinear must be a Definition, not {decl:?}");
    };
    let rendered = kernel.render_lean(*ty);
    assert!(
        rendered.contains("Geo.Incidence.point"),
        "Collinear's type does not mention the point carrier: {rendered}"
    );
    let body = kernel.render_lean(*value);
    assert!(
        body.contains("Exists"),
        "Collinear does not unfold to an Exists: {body}"
    );
    assert_eq!(
        body.matches("Geo.Incidence.on").count(),
        3,
        "Collinear's body should apply `on` exactly three times: {body}"
    );
}

/// The five derived declarations really are stated over an ARBITRARY
/// structure: each one's type binds `Geo.Incidence` itself, not a model.
#[test]
fn every_derived_theorem_quantifies_over_the_record() {
    let (kernel, prelude) = built();
    for (label, name) in [
        ("Collinear", prelude.collinear),
        ("collinear_intro", prelude.collinear_intro),
        ("collinear_perm", prelude.collinear_perm),
        ("distinct_lines_meet_once", prelude.distinct_lines_meet_once),
        ("triangle_not_collinear", prelude.triangle_not_collinear),
    ] {
        let decl = kernel
            .environment()
            .get(name)
            .unwrap_or_else(|| panic!("{label} must be declared"));
        let ty = match decl {
            crate::env::Declaration::Theorem { ty, .. }
            | crate::env::Declaration::Definition { ty, .. } => *ty,
            other => panic!("{label} is not a theorem or definition: {other:?}"),
        };
        let rendered = kernel.render_lean(ty);
        assert!(
            rendered.contains("Geo.Incidence"),
            "{label} does not quantify over Geo.Incidence: {rendered}"
        );
    }
}

// ---------------------------------------------------------------------------
// Evaluation tests. The trusted gate cannot tell you a `Definition` is wrong —
// a function computing the wrong value has the right type — so every one of
// this module's definitions is pinned here, and every pin carries its own
// negative half.
// ---------------------------------------------------------------------------

/// `Geo.QPoint.x`/`.y` and `Geo.QLine0.a`/`.b`/`.c` pick the field their name
/// claims, at concrete `Rat.zero`/`Rat.one` arguments chosen so a swapped
/// projection reads a DIFFERENT value.
#[test]
fn the_projections_pick_the_field_their_name_claims() {
    use crate::int_prelude::ops::IntDev;
    use crate::rat_prelude::ops::{rone, rzero};
    on_a_deep_stack(|| {
        let (mut kernel, prelude) = built();
        let q = prelude.qplane;
        let rat = prelude.cpoint.creal.rat;
        let mut dev = IntDev::new(&mut kernel, rat.int);
        let d = &mut dev;
        let zero = rzero(d, rat);
        let one = rone(d, rat);

        // (0, 1): x is zero, y is one, and neither is the other.
        let point = d.const_app(q.qpoint_mk, &[zero, one]);
        let got_x = d.const_app(q.qpoint_x, &[point]);
        let got_y = d.const_app(q.qpoint_y, &[point]);
        assert!(d.kernel().def_eq(got_x, zero), "x (mk 0 1) must be 0");
        assert!(!d.kernel().def_eq(got_x, one), "x (mk 0 1) must NOT be 1");
        assert!(d.kernel().def_eq(got_y, one), "y (mk 0 1) must be 1");
        assert!(!d.kernel().def_eq(got_y, zero), "y (mk 0 1) must NOT be 0");

        // (0, 1, 0+1): a is zero, b is one, c is the compound — so `c` cannot
        // pass by accidentally reading `a` or `b`.
        let compound = crate::rat_prelude::ops::radd(d, zero, one);
        let line = d.const_app(q.qline0_mk, &[zero, one, compound]);
        let got_a = d.const_app(q.qline0_a, &[line]);
        let got_b = d.const_app(q.qline0_b, &[line]);
        let got_c = d.const_app(q.qline0_c, &[line]);
        assert!(d.kernel().def_eq(got_a, zero), "a (mk 0 1 (0+1)) must be 0");
        assert!(d.kernel().def_eq(got_b, one), "b (mk 0 1 (0+1)) must be 1");
        assert!(
            d.kernel().def_eq(got_c, compound),
            "c (mk 0 1 (0+1)) must be the third field"
        );
        assert!(
            !d.kernel().def_eq(got_b, zero),
            "b (mk 0 1 (0+1)) must NOT be 0"
        );
    });
}

/// **`Geo.QPlane.join` is `⟨y Q − y P, x P − x Q, y P · x Q − x P · y Q⟩`, in
/// that order.** Checked SYMBOLICALLY, at free-variable points: a concrete
/// pair can make two coefficients coincide, and the mutation this pin exists
/// for is exactly a swap of the first two.
#[test]
fn the_join_coefficients_are_not_swapped() {
    use crate::int_prelude::ops::IntDev;
    use crate::rat_prelude::ops::{radd, rmul, rneg};
    on_a_deep_stack(|| {
        let (mut kernel, prelude) = built();
        let q = prelude.qplane;
        let rat = prelude.cpoint.creal.rat;
        let mut dev = IntDev::new(&mut kernel, rat.int);
        let d = &mut dev;

        let p_fv = d.fresh_fvar();
        let r_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let rp = d.kernel().fvar(r_fv);
        let pxv = d.const_app(q.qpoint_x, &[pt]);
        let pyv = d.const_app(q.qpoint_y, &[pt]);
        let qxv = d.const_app(q.qpoint_x, &[rp]);
        let qyv = d.const_app(q.qpoint_y, &[rp]);

        let expect_a = {
            let n = rneg(d, pyv);
            radd(d, qyv, n)
        };
        let expect_b = {
            let n = rneg(d, qxv);
            radd(d, pxv, n)
        };
        let expect_c = {
            let m1 = rmul(d, pyv, qxv);
            let m2 = rmul(d, pxv, qyv);
            let n = rneg(d, m2);
            radd(d, m1, n)
        };

        let joined = d.const_app(q.join, &[pt, rp]);
        let got_a = d.const_app(q.qline0_a, &[joined]);
        let got_b = d.const_app(q.qline0_b, &[joined]);
        let got_c = d.const_app(q.qline0_c, &[joined]);

        assert!(
            d.kernel().def_eq(got_a, expect_a),
            "join's a coefficient must be `y Q - y P`"
        );
        assert!(
            d.kernel().def_eq(got_b, expect_b),
            "join's b coefficient must be `x P - x Q`"
        );
        assert!(
            d.kernel().def_eq(got_c, expect_c),
            "join's c coefficient must be `y P * x Q - x P * y Q`"
        );
        // The negative half, and it is the mutation the suite runs: the first
        // two coefficients are NOT interchangeable.
        assert!(
            !d.kernel().def_eq(got_a, expect_b),
            "join's a coefficient must NOT be `x P - x Q` -- the swap is live"
        );
        assert!(
            !d.kernel().def_eq(got_b, expect_a),
            "join's b coefficient must NOT be `y Q - y P` -- the swap is live"
        );
    });
}

/// **`Geo.QPlane.shift P l` is `P + (−b, a)`**, the direction ALONG the line
/// and not along its normal. Symbolic again, and the negative half is the
/// coefficient swap that would make it the normal direction.
#[test]
fn the_shift_moves_along_the_line_not_across_it() {
    use crate::int_prelude::ops::IntDev;
    use crate::rat_prelude::ops::{radd, rneg};
    on_a_deep_stack(|| {
        let (mut kernel, prelude) = built();
        let q = prelude.qplane;
        let rat = prelude.cpoint.creal.rat;
        let mut dev = IntDev::new(&mut kernel, rat.int);
        let d = &mut dev;

        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let pxv = d.const_app(q.qpoint_x, &[pt]);
        let pyv = d.const_app(q.qpoint_y, &[pt]);
        let av = d.const_app(q.qline0_a, &[l]);
        let bv = d.const_app(q.qline0_b, &[l]);

        let expect_x = {
            let n = rneg(d, bv);
            radd(d, pxv, n)
        };
        let expect_y = radd(d, pyv, av);
        let wrong_x = {
            let n = rneg(d, av);
            radd(d, pxv, n)
        };

        let moved = d.const_app(q.shift, &[pt, l]);
        let got_x = d.const_app(q.qpoint_x, &[moved]);
        let got_y = d.const_app(q.qpoint_y, &[moved]);
        assert!(
            d.kernel().def_eq(got_x, expect_x),
            "shift's x must be `x P + -(b l)`"
        );
        assert!(
            d.kernel().def_eq(got_y, expect_y),
            "shift's y must be `y P + a l`"
        );
        assert!(
            !d.kernel().def_eq(got_x, wrong_x),
            "shift's x must NOT read the `a` coefficient"
        );
    });
}

/// **`Geo.QPlane.onRaw` pairs each coefficient with the matching coordinate.**
/// The negative half is the pairing swap (`a` against `y`), which type-checks
/// and states a different relation.
#[test]
fn incidence_pairs_each_coefficient_with_its_own_coordinate() {
    use crate::int_prelude::ops::IntDev;
    use crate::rat_prelude::ops::{radd, req, rmul, rzero};
    on_a_deep_stack(|| {
        let (mut kernel, prelude) = built();
        let q = prelude.qplane;
        let rat = prelude.cpoint.creal.rat;
        let mut dev = IntDev::new(&mut kernel, rat.int);
        let d = &mut dev;

        let p_fv = d.fresh_fvar();
        let l_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let l = d.kernel().fvar(l_fv);
        let pxv = d.const_app(q.qpoint_x, &[pt]);
        let pyv = d.const_app(q.qpoint_y, &[pt]);
        let av = d.const_app(q.qline0_a, &[l]);
        let bv = d.const_app(q.qline0_b, &[l]);
        let cv = d.const_app(q.qline0_c, &[l]);
        let zero = rzero(d, rat);

        let expect = {
            let m1 = rmul(d, av, pxv);
            let m2 = rmul(d, bv, pyv);
            let sum = radd(d, m1, m2);
            let lhs = radd(d, sum, cv);
            req(d, lhs, zero)
        };
        let swapped = {
            let m1 = rmul(d, av, pyv);
            let m2 = rmul(d, bv, pxv);
            let sum = radd(d, m1, m2);
            let lhs = radd(d, sum, cv);
            req(d, lhs, zero)
        };
        let got = d.const_app(q.on_raw, &[pt, l]);
        assert!(
            d.kernel().def_eq(got, expect),
            "onRaw must be `a * x P + b * y P + c = 0`"
        );
        assert!(
            !d.kernel().def_eq(got, swapped),
            "onRaw must NOT pair `a` with `y` -- the swap type-checks"
        );
    });
}

// ---------------------------------------------------------------------------
// The real model. Same discipline as the rational one above: every
// `Definition` is pinned at concrete or symbolic arguments, and every pin
// carries the negative half that the mutation suite actually runs.
// ---------------------------------------------------------------------------

/// `Geo.RLine0.a`/`.b`/`.c` pick the field their name claims. The third
/// argument is a compound so `c` cannot pass by reading `a` or `b`.
#[test]
fn the_real_line_projections_pick_the_field_their_name_claims() {
    use crate::creal_point::{rn_cadd, rn_cone, rn_czero};
    use crate::int_prelude::ops::IntDev;
    on_a_deep_stack(|| {
        let (mut kernel, prelude) = built();
        let rp = prelude.rplane;
        let cr = prelude.cpoint.creal;
        let mut dev = IntDev::new(&mut kernel, cr.rat.int);
        let d = &mut dev;
        let zero = rn_czero(d, cr);
        let one = rn_cone(d, cr);
        let compound = rn_cadd(d, cr, zero, one);

        let line = d.const_app(rp.rline0_mk, &[zero, one, compound]);
        let got_a = d.const_app(rp.rline0_a, &[line]);
        let got_b = d.const_app(rp.rline0_b, &[line]);
        let got_c = d.const_app(rp.rline0_c, &[line]);
        assert!(d.kernel().def_eq(got_a, zero), "a (mk 0 1 (0+1)) must be 0");
        assert!(d.kernel().def_eq(got_b, one), "b (mk 0 1 (0+1)) must be 1");
        assert!(
            d.kernel().def_eq(got_c, compound),
            "c (mk 0 1 (0+1)) must be the third field"
        );
        assert!(
            !d.kernel().def_eq(got_b, zero),
            "b (mk 0 1 (0+1)) must NOT be 0"
        );
        // NOT `!def_eq(got_c, one)`: refuting `def_eq` between `0 + 1` and `1`
        // over `CReal` unfolds both into `CReal.mk` with their regularity
        // proofs and does not finish (see the banner further down). The two
        // refutations kept above are `zero` against `one`, which congruence
        // settles at two `Rat` literals. The discrimination for `c` is the
        // structural one: the compound is a different term from either
        // coordinate, and `got_c` matched it.
        assert_ne!(compound, one, "liveness: `0 + 1` must differ from `1`");
        assert_ne!(compound, zero, "liveness: `0 + 1` must differ from `0`");
    });
}

/// **`Geo.RPlane.join` is `⟨y Q − y P, x P − x Q, y P · x Q − x P · y Q⟩`.**
/// Symbolic, at free-variable points, because a concrete pair can make two
/// coefficients coincide — and the swap of the first two is exactly what the

/// **`Geo.RPlane.onRaw` pairs each coefficient with the matching coordinate**,
/// and states an `Equiv`, not an `Eq`: over ℝ there is no decidable equality
/// to state it with. The negative half is the `a`-against-`y` pairing swap,

/// **`Geo.RLine0.Nondeg` is a `PosBound` WITNESS, not a negation.**
///
/// This is the file's load-bearing design decision and the first mutation the
/// suite runs: `(Equiv (a*a + b*b) 0) → False` type-checks perfectly well as a
/// non-degeneracy predicate and is what a ℚ-shaped port would write, but it
/// constructs no modulus, so `CReal.inv` cannot consume it and `joinUnique`'s
/// division does not typecheck. Both halves are asserted.
#[test]
fn real_nondegeneracy_is_a_positive_bound_witness_not_a_negation() {
    use crate::creal_point::{rn_cadd, rn_cmul, rn_czero};
    use crate::int_prelude::ops::IntDev;
    on_a_deep_stack(|| {
        let (mut kernel, prelude) = built();
        let rp = prelude.rplane;
        let cr = prelude.cpoint.creal;
        let logic = cr.rat.int.logic;
        let mut dev = IntDev::new(&mut kernel, cr.rat.int);
        let d = &mut dev;

        let l_fv = d.fresh_fvar();
        let l = d.kernel().fvar(l_fv);
        let av = d.const_app(rp.rline0_a, &[l]);
        let bv = d.const_app(rp.rline0_b, &[l]);
        let norm = {
            let m1 = rn_cmul(d, cr, av, av);
            let m2 = rn_cmul(d, cr, bv, bv);
            rn_cadd(d, cr, m1, m2)
        };

        let expect = {
            let nat = d.nat_ty();
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let pb = d.const_app(cr.pos_bound, &[norm, k]);
            let pred = d.lam_fv(k_fv, nat, pb);
            let one = d.level_one();
            let ex = d.kernel().const_(logic.exists_, vec![one]);
            d.apply(ex, &[nat, pred])
        };
        let negated = {
            let zero = rn_czero(d, cr);
            let eq = d.const_app(cr.equiv, &[norm, zero]);
            let f = d.kernel().const_(logic.false_, vec![]);
            d.arrow(eq, f)
        };
        let got = d.const_app(rp.nondeg, &[l]);
        assert!(
            d.kernel().def_eq(got, expect),
            "Nondeg must be `exists k, PosBound (a*a + b*b) k`"
        );
        assert!(
            !d.kernel().def_eq(got, negated),
            "Nondeg must NOT be `Equiv (a*a + b*b) 0 -> False` -- the negated \
             form is the mutation, and it constructs no modulus for CReal.inv"
        );
    });
}

/// **`Geo.RPlane.Apart` is a `PosBound` on the squared distance**, the same
/// decision one dimension up, and the reason `Geo.Incidence` carries `apart`
/// as its own field rather than deriving it from `pEq`.
#[test]
fn real_apartness_is_a_positive_bound_on_the_squared_distance() {
    use crate::int_prelude::ops::IntDev;
    on_a_deep_stack(|| {
        let (mut kernel, prelude) = built();
        let rp = prelude.rplane;
        let cp = prelude.cpoint;
        let cr = cp.creal;
        let logic = cr.rat.int.logic;
        let mut dev = IntDev::new(&mut kernel, cr.rat.int);
        let d = &mut dev;

        let p_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let qt = d.kernel().fvar(q_fv);
        let dd = d.const_app(cp.dist_sq, &[pt, qt]);

        let expect = {
            let nat = d.nat_ty();
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let pb = d.const_app(cr.pos_bound, &[dd, k]);
            let pred = d.lam_fv(k_fv, nat, pb);
            let one = d.level_one();
            let ex = d.kernel().const_(logic.exists_, vec![one]);
            d.apply(ex, &[nat, pred])
        };
        let negated = {
            let eq = d.const_app(cp.point_equiv, &[pt, qt]);
            let f = d.kernel().const_(logic.false_, vec![]);
            d.arrow(eq, f)
        };
        let got = d.const_app(rp.apart, &[pt, qt]);
        assert!(
            d.kernel().def_eq(got, expect),
            "Apart must be `exists k, PosBound (distSq P Q) k`"
        );
        assert!(
            !d.kernel().def_eq(got, negated),
            "Apart must NOT be `CPoint.Equiv P Q -> False` -- that is the ℚ \
             model's notion and it constructs nothing over ℝ"
        );
    });
}

/// **`CPoint.distSq P Q` IS `(x P − x Q)² + (y P − y Q)²`, definitionally.**
///
/// `pivotAB`'s conclusion is stated over the coordinate expression and
/// `cancelPosBound` is fed the `Apart` witness, which is stated over `distSq`;
/// the whole of `joinUnique` rests on those two being the same term after
/// δ/ι. If `distSq` ever stops unfolding this way the model breaks, and this

/// `Geo.rplane` really is an inhabitant of the record, its point carrier is
/// `CPoint` and its line carrier is `Geo.RLine` — and it is a DIFFERENT model
/// from `Geo.qplane`, which is the whole reason for building it.
#[test]
fn the_real_plane_is_a_second_and_different_model() {
    use crate::int_prelude::ops::IntDev;
    on_a_deep_stack(|| {
        let (mut kernel, prelude) = built();
        let rp = prelude.rplane;
        let q = prelude.qplane;
        let cp = prelude.cpoint;
        let mut dev = IntDev::new(&mut kernel, cp.creal.rat.int);
        let d = &mut dev;

        let model = d.kernel().const_(rp.instance, vec![]);
        let got_point = d.const_app(prelude.record.sel(POINT), &[model]);
        let got_line = d.const_app(prelude.record.sel(LINE), &[model]);
        let cpoint_ty = d.kernel().const_(cp.point, vec![]);
        let rline_ty = d.kernel().const_(rp.rline, vec![]);
        let qpoint_ty = d.kernel().const_(q.qpoint, vec![]);
        assert!(
            d.kernel().def_eq(got_point, cpoint_ty),
            "Geo.rplane's point carrier must be CPoint"
        );
        assert!(
            d.kernel().def_eq(got_line, rline_ty),
            "Geo.rplane's line carrier must be Geo.RLine"
        );
        assert!(
            !d.kernel().def_eq(got_point, qpoint_ty),
            "Geo.rplane's point carrier must NOT be Geo.QPoint -- two models, \
             not one written twice"
        );

        let rational = d.kernel().const_(q.instance, vec![]);
        let q_point = d.const_app(prelude.record.sel(POINT), &[rational]);
        assert!(
            d.kernel().def_eq(q_point, qpoint_ty),
            "Geo.qplane's point carrier must still be Geo.QPoint"
        );
    });
}

/// The record's derived theorems apply to the real model: instantiating
/// `distinct_lines_meet_once` and `triangle_not_collinear` at `Geo.rplane`
/// type-checks, which is the payoff of proving them over an arbitrary
/// structure.
#[test]
fn the_derived_theorems_instantiate_at_the_real_model() {
    use crate::int_prelude::ops::IntDev;
    on_a_deep_stack(|| {
        let (mut kernel, prelude) = built();
        let rp = prelude.rplane;
        let cp = prelude.cpoint;
        let mut dev = IntDev::new(&mut kernel, cp.creal.rat.int);
        let d = &mut dev;

        let model = d.kernel().const_(rp.instance, vec![]);
        for (label, name) in [
            ("Collinear", prelude.collinear),
            ("collinear_intro", prelude.collinear_intro),
            ("collinear_perm", prelude.collinear_perm),
            ("distinct_lines_meet_once", prelude.distinct_lines_meet_once),
            ("triangle_not_collinear", prelude.triangle_not_collinear),
        ] {
            let applied = d.const_app(name, &[model]);
            let inferred = d.kernel().infer(applied);
            assert!(
                inferred.is_ok(),
                "{label} does not apply to Geo.rplane: {inferred:?}"
            );
        }
    });
}

// ---------------------------------------------------------------------------
// Shape pins for the ℝ model's definitions, and the reason they are written
// as STORED-VALUE comparisons rather than as `def_eq` refutations.
//
// **Measured 2026-09-06, and the reason two tests were rewritten**: a negative
// control of the form `!def_eq(correct, wrong)` between two `CReal` ARITHMETIC
// terms does not finish. `dist_sq_unfolds_to_the_coordinate_difference_squares`
// (`!def_eq(distSq P Q, sum-of-coordinates form)`) and the swapped-pairing half
// of the ℝ `onRaw` pin each ran past ten minutes in `--release` and were
// killed, while the ℚ versions of the same two pins finish in seconds. The
// cause is the fallback: when congruence on `CReal.add`/`CReal.mul` fails, the
// kernel unfolds both sides into `CReal.mk` with their regularity proofs and
// compares sequences under a binder. Refuting `def_eq` at `CReal.Equiv` is
// worse again, because `Equiv` itself unfolds to a `∀ n` over `Rat`
// arithmetic.
//
// So the rule these tests follow, and it is a rule about ℝ and not about
// geometry: **over `CReal`, assert `def_eq` only where it SUCCEEDS.** A
// successful `def_eq` is δ/ι plus congruence and is fast; a failing one is a
// search. The discriminating half is done instead on the STORED `Definition`
// value, compared as an interned `ExprId` — exact, `O(1)`, and strictly
// stronger than `def_eq` for a shape claim, since it distinguishes shapes that
// happen to be denotationally equal. Each pin also asserts that the wrong
// shape is a DIFFERENT `ExprId`, so the comparison could have failed.
// ---------------------------------------------------------------------------

/// The stored value of a `Definition`, for the shape pins below.
fn stored_value(kernel: &crate::Kernel, name: crate::name::NameId) -> crate::expr::ExprId {
    let decl = kernel
        .environment()
        .get(name)
        .unwrap_or_else(|| panic!("{} must be declared", kernel.display_name(name)));
    match decl {
        crate::env::Declaration::Definition { value, .. } => *value,
        other => panic!("expected a Definition, found {other:?}"),
    }
}

/// **`Geo.RPlane.onRaw` pairs each coefficient with the matching coordinate**,
/// and states a `CReal.Equiv`, not an `Eq`: over ℝ there is no decidable
/// equality to state it with.
///
/// The negative half is the `a`-against-`y` pairing swap, which type-checks
/// and states a different relation.
#[test]
fn the_real_incidence_relation_pairs_each_coefficient_with_its_own_coordinate() {
    use crate::creal_point::{rn_cadd, rn_cmul, rn_czero};
    use crate::int_prelude::ops::IntDev;
    on_a_deep_stack(|| {
        let (mut kernel, prelude) = built();
        let rp = prelude.rplane;
        let cp = prelude.cpoint;
        let cr = cp.creal;
        let mut dev = IntDev::new(&mut kernel, cr.rat.int);
        let d = &mut dev;

        let point = d.kernel().const_(cp.point, vec![]);
        let line0 = d.kernel().const_(rp.rline0, vec![]);
        let build = |d: &mut IntDev<'_>, swap: bool| -> crate::expr::ExprId {
            let p_fv = d.fresh_fvar();
            let l_fv = d.fresh_fvar();
            let pt = d.kernel().fvar(p_fv);
            let l = d.kernel().fvar(l_fv);
            let av = d.const_app(rp.rline0_a, &[l]);
            let bv = d.const_app(rp.rline0_b, &[l]);
            let cv = d.const_app(rp.rline0_c, &[l]);
            let xv = d.const_app(cp.x, &[pt]);
            let yv = d.const_app(cp.y, &[pt]);
            let (s, t) = if swap { (yv, xv) } else { (xv, yv) };
            let m1 = rn_cmul(d, cr, av, s);
            let m2 = rn_cmul(d, cr, bv, t);
            let sum = rn_cadd(d, cr, m1, m2);
            let lhs = rn_cadd(d, cr, sum, cv);
            let zero = rn_czero(d, cr);
            let body = d.const_app(cr.equiv, &[lhs, zero]);
            let inner = d.lam_fv(l_fv, line0, body);
            d.lam_fv(p_fv, point, inner)
        };
        let expect = build(d, false);
        let swapped = build(d, true);
        let got = stored_value(d.kernel(), rp.on_raw);

        assert_ne!(
            expect, swapped,
            "liveness: the swapped pairing must be a DIFFERENT term, or the \
             comparison below could not fail"
        );
        assert_eq!(
            got, expect,
            "Geo.RPlane.onRaw must be `Equiv (a * x P + b * y P + c) 0`"
        );
        assert_ne!(
            got, swapped,
            "Geo.RPlane.onRaw must NOT pair `a` with `y` -- the swap type-checks \
             and states a different relation"
        );
    });
}

/// **`Geo.RPlane.join` is `⟨y Q − y P, x P − x Q, y P · x Q − x P · y Q⟩`, in
/// that order.** The mutation this pin exists for is a swap of the first two
/// coefficients, which type-checks and yields a different line.
#[test]
fn the_real_join_coefficients_are_in_the_order_the_name_claims() {
    use crate::creal_point::{rn_cadd, rn_cmul, rn_cneg};
    use crate::int_prelude::ops::IntDev;
    on_a_deep_stack(|| {
        let (mut kernel, prelude) = built();
        let rp = prelude.rplane;
        let cp = prelude.cpoint;
        let cr = cp.creal;
        let mut dev = IntDev::new(&mut kernel, cr.rat.int);
        let d = &mut dev;

        let point = d.kernel().const_(cp.point, vec![]);
        let build = |d: &mut IntDev<'_>, swap: bool| -> crate::expr::ExprId {
            let p_fv = d.fresh_fvar();
            let q_fv = d.fresh_fvar();
            let pt = d.kernel().fvar(p_fv);
            let qt = d.kernel().fvar(q_fv);
            let pxv = d.const_app(cp.x, &[pt]);
            let pyv = d.const_app(cp.y, &[pt]);
            let qxv = d.const_app(cp.x, &[qt]);
            let qyv = d.const_app(cp.y, &[qt]);
            let ca = {
                let n = rn_cneg(d, cr, pyv);
                rn_cadd(d, cr, qyv, n)
            };
            let cb = {
                let n = rn_cneg(d, cr, qxv);
                rn_cadd(d, cr, pxv, n)
            };
            let cc = {
                let m1 = rn_cmul(d, cr, pyv, qxv);
                let m2 = rn_cmul(d, cr, pxv, qyv);
                let n = rn_cneg(d, cr, m2);
                rn_cadd(d, cr, m1, n)
            };
            let body = if swap {
                d.const_app(rp.rline0_mk, &[cb, ca, cc])
            } else {
                d.const_app(rp.rline0_mk, &[ca, cb, cc])
            };
            let inner = d.lam_fv(q_fv, point, body);
            d.lam_fv(p_fv, point, inner)
        };
        let expect = build(d, false);
        let swapped = build(d, true);
        let got = stored_value(d.kernel(), rp.join);

        assert_ne!(
            expect, swapped,
            "liveness: the coefficient swap must be a DIFFERENT term"
        );
        assert_eq!(
            got, expect,
            "Geo.RPlane.join must be `(y Q - y P, x P - x Q, y P * x Q - x P * y Q)`"
        );
        assert_ne!(
            got, swapped,
            "Geo.RPlane.join's first two coefficients must NOT be interchanged"
        );
    });
}

/// **`CPoint.distSq P Q` IS `(x P − x Q)² + (y P − y Q)²`, definitionally.**
///
/// `Geo.RPlane.pivotAB`'s conclusion is stated over the coordinate expression
/// and `Geo.RPlane.Apart`'s witness over `CPoint.distSq`; `cancelPosBound`
/// consumes one as the other with no transport at all, so the whole of
/// `joinUnique` rests on this defeq holding. It is asserted in the direction
/// that SUCCEEDS (see the banner above for why the refuting direction is not
/// runnable over `CReal`); the discriminating half is the structural
/// assertion that the sign-flipped form -- which is still a symmetric
/// non-negative quantity and still type-checks -- is a different term.
#[test]
fn dist_sq_is_definitionally_the_coordinate_difference_squares() {
    use crate::creal_point::{rn_cadd, rn_cmul, rn_cneg};
    use crate::int_prelude::ops::IntDev;
    on_a_deep_stack(|| {
        let (mut kernel, prelude) = built();
        let cp = prelude.cpoint;
        let cr = cp.creal;
        let mut dev = IntDev::new(&mut kernel, cr.rat.int);
        let d = &mut dev;

        let p_fv = d.fresh_fvar();
        let q_fv = d.fresh_fvar();
        let pt = d.kernel().fvar(p_fv);
        let qt = d.kernel().fvar(q_fv);
        let pxv = d.const_app(cp.x, &[pt]);
        let pyv = d.const_app(cp.y, &[pt]);
        let qxv = d.const_app(cp.x, &[qt]);
        let qyv = d.const_app(cp.y, &[qt]);
        let u = {
            let n = rn_cneg(d, cr, qxv);
            rn_cadd(d, cr, pxv, n)
        };
        let v = {
            let n = rn_cneg(d, cr, qyv);
            rn_cadd(d, cr, pyv, n)
        };
        let expect = {
            let m1 = rn_cmul(d, cr, u, u);
            let m2 = rn_cmul(d, cr, v, v);
            rn_cadd(d, cr, m1, m2)
        };
        let wrong = {
            let su = rn_cadd(d, cr, pxv, qxv);
            let sv = rn_cadd(d, cr, pyv, qyv);
            let m1 = rn_cmul(d, cr, su, su);
            let m2 = rn_cmul(d, cr, sv, sv);
            rn_cadd(d, cr, m1, m2)
        };
        assert_ne!(
            expect, wrong,
            "liveness: the sum-of-coordinates form must be a DIFFERENT term"
        );
        let got = d.const_app(cp.dist_sq, &[pt, qt]);
        assert!(
            d.kernel().def_eq(got, expect),
            "CPoint.distSq must unfold to `(x P - x Q)^2 + (y P - y Q)^2`"
        );
    });
}
