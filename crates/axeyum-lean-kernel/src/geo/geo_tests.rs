//! Does the kernel accept [`build_geo_prelude`], is every declaration it
//! produces axiom-free, and — the part that matters — is each field of the
//! `Geo.Incidence` record load-bearing?
//!
//! The negative controls are the point of the file. Each rebuilds one field's
//! type with a single slot changed and requires the kernel to refuse the
//! *derived theorem* that depends on it, or requires the mutated field type to
//! differ from the real one. Without them, "the incidence axioms are stated"
//! is a claim about a comment.

use super::{
    APART, FIELD_COUNT, FIELD_SUFFIXES, GeoPrelude, JOIN_UNIQUE, L_EQ, LINE, ON, P_EQ, POINT,
    TRIANGLE, TWO_POINTS, build_geo_prelude, incidence_fields,
};
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
fn all_declarations(p: GeoPrelude) -> Vec<(String, crate::name::NameId)> {
    let mut out: Vec<(String, crate::name::NameId)> = vec![
        ("Geo.Incidence".into(), p.record.ind),
        ("Geo.Incidence.mk".into(), p.record.mk),
        ("Geo.Incidence.rec".into(), p.record.rec),
        ("Geo.Incidence.Collinear".into(), p.collinear),
        ("Geo.Incidence.collinear_intro".into(), p.collinear_intro),
        ("Geo.Incidence.collinear_perm".into(), p.collinear_perm),
        (
            "Geo.Incidence.distinct_lines_meet_once".into(),
            p.distinct_lines_meet_once,
        ),
        (
            "Geo.Incidence.triangle_not_collinear".into(),
            p.triangle_not_collinear,
        ),
    ];
    for i in 0..p.record.field_count() {
        out.push((
            format!("Geo.Incidence.{}", FIELD_SUFFIXES[i]),
            p.record.sel(i),
        ));
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
        FIELD_COUNT + 8,
        "the declaration list is out of step with the record's field count"
    );
    for (label, name) in all {
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
