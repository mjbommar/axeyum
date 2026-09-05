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
        FIELD_COUNT + 8 + 46,
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
        live.len() >= 70,
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
