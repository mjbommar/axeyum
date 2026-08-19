//! Checked controls for ADR-0484's explicit constant-generalization primitive.

use std::io::Cursor;

use axeyum_lean_import::{
    ConstantInstance, ImportLimits, TypeSliceError, generalize_goal_constants,
    import_statement_ndjson, verify_generalized_specialization,
};
use axeyum_lean_kernel::{
    Declaration, ExprId, Kernel, Lean4ExportMetadata, LogicPrelude, NameId, ReducibilityHint,
    build_logic_prelude,
};

const TARGET: &str = "Axeyum.Autogenesis.TypeSlice.target";

struct Fixture {
    kernel: Kernel,
    logic: LogicPrelude,
    carrier: NameId,
    value: NameId,
    goal: ExprId,
}

fn nested_name(kernel: &mut Kernel, components: &[&str]) -> NameId {
    let mut name = kernel.anon();
    for component in components {
        name = kernel.name_str(name, *component);
    }
    name
}

fn equality(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    ty: ExprId,
    lhs: ExprId,
    rhs: ExprId,
) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let eq = kernel.const_(logic.eq, vec![one]);
    let eq = kernel.app(eq, ty);
    let eq = kernel.app(eq, lhs);
    kernel.app(eq, rhs)
}

fn fixture() -> Fixture {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    let carrier = nested_name(&mut kernel, &["Source", "Carrier"]);
    let value = nested_name(&mut kernel, &["Source", "value"]);
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let sort_one = kernel.sort(one);
    kernel
        .add_declaration(Declaration::Axiom {
            name: carrier,
            uparams: vec![],
            ty: sort_one,
        })
        .expect("carrier type must check");
    let carrier_expr = kernel.const_(carrier, vec![]);
    kernel
        .add_declaration(Declaration::Axiom {
            name: value,
            uparams: vec![],
            ty: carrier_expr,
        })
        .expect("carrier value must check");
    let value_expr = kernel.const_(value, vec![]);
    let goal = equality(&mut kernel, &logic, carrier_expr, value_expr, value_expr);
    Fixture {
        kernel,
        logic,
        carrier,
        value,
        goal,
    }
}

fn instance(kernel: &mut Kernel, name: NameId, binder: &str) -> ConstantInstance {
    ConstantInstance {
        name,
        levels: vec![],
        binder_name: nested_name(kernel, &[binder]),
    }
}

#[test]
fn dependency_ordered_data_constants_form_a_closed_prop_and_specialize_exactly() {
    let mut fixture = fixture();
    let carrier = instance(&mut fixture.kernel, fixture.carrier, "Alpha");
    let value = instance(&mut fixture.kernel, fixture.value, "x");
    let generalized =
        generalize_goal_constants(&mut fixture.kernel, fixture.goal, &[carrier, value])
            .expect("ordered data constants must generalize");

    assert_eq!(generalized.binders.len(), 2);
    assert!(!fixture.kernel.has_fvars(generalized.goal));
    assert!(!fixture.kernel.has_loose_bvars(generalized.goal));
    let carrier_expr = fixture.kernel.const_(fixture.carrier, vec![]);
    let value_expr = fixture.kernel.const_(fixture.value, vec![]);
    verify_generalized_specialization(
        &mut fixture.kernel,
        &generalized,
        &[carrier_expr, value_expr],
        fixture.goal,
    )
    .expect("source instances must recover the exact source goal");
    assert!(matches!(
        verify_generalized_specialization(
            &mut fixture.kernel,
            &generalized,
            &[carrier_expr],
            fixture.goal,
        ),
        Err(TypeSliceError::SpecializationArity { .. })
    ));
}

#[test]
fn dependent_constants_in_reverse_order_fail_closed() {
    let mut fixture = fixture();
    let value = instance(&mut fixture.kernel, fixture.value, "x");
    let carrier = instance(&mut fixture.kernel, fixture.carrier, "Alpha");
    let error = generalize_goal_constants(&mut fixture.kernel, fixture.goal, &[value, carrier])
        .expect_err("a forward telescope dependency must be rejected");
    assert!(matches!(error, TypeSliceError::ForwardDependency { .. }));
}

#[test]
fn proof_valued_constants_are_not_turned_into_premises() {
    let mut fixture = fixture();
    let proposition = nested_name(&mut fixture.kernel, &["Source", "P"]);
    let proof = nested_name(&mut fixture.kernel, &["Source", "h"]);
    let prop = fixture.kernel.sort_zero();
    fixture
        .kernel
        .add_declaration(Declaration::Axiom {
            name: proposition,
            uparams: vec![],
            ty: prop,
        })
        .expect("proposition constant must check");
    let proposition_expr = fixture.kernel.const_(proposition, vec![]);
    fixture
        .kernel
        .add_declaration(Declaration::Axiom {
            name: proof,
            uparams: vec![],
            ty: proposition_expr,
        })
        .expect("proof constant must check");
    let proof_expr = fixture.kernel.const_(proof, vec![]);
    let zero = fixture.kernel.level_zero();
    let eq = fixture.kernel.const_(fixture.logic.eq, vec![zero]);
    let eq = fixture.kernel.app(eq, proposition_expr);
    let eq = fixture.kernel.app(eq, proof_expr);
    let goal = fixture.kernel.app(eq, proof_expr);
    let proof = instance(&mut fixture.kernel, proof, "h");
    let error = generalize_goal_constants(&mut fixture.kernel, goal, &[proof])
        .expect_err("proof-valued constants must not become generalized premises");
    assert!(
        matches!(error, TypeSliceError::PropositionValued { .. }),
        "unexpected rejection: {error:?}"
    );
}

#[test]
fn duplicate_and_unused_instances_fail_closed() {
    let mut fixture = fixture();
    let carrier = instance(&mut fixture.kernel, fixture.carrier, "Alpha");
    let duplicate = ConstantInstance {
        binder_name: nested_name(&mut fixture.kernel, &["Again"]),
        ..carrier.clone()
    };
    assert!(matches!(
        generalize_goal_constants(
            &mut fixture.kernel,
            fixture.goal,
            &[carrier.clone(), duplicate]
        ),
        Err(TypeSliceError::DuplicateInstance { .. })
    ));

    let unused = nested_name(&mut fixture.kernel, &["Source", "Unused"]);
    let sort_one = {
        let zero = fixture.kernel.level_zero();
        let one = fixture.kernel.level_succ(zero);
        fixture.kernel.sort(one)
    };
    fixture
        .kernel
        .add_declaration(Declaration::Axiom {
            name: unused,
            uparams: vec![],
            ty: sort_one,
        })
        .expect("unused data type must check");
    let unused = instance(&mut fixture.kernel, unused, "Unused");
    assert!(matches!(
        generalize_goal_constants(&mut fixture.kernel, fixture.goal, &[unused]),
        Err(TypeSliceError::MissingOccurrence { .. })
    ));
}

#[test]
fn universe_instances_of_one_declaration_are_distinct() {
    let mut fixture = fixture();
    let u_name = nested_name(&mut fixture.kernel, &["u"]);
    let u = fixture.kernel.level_param(u_name);
    let u_succ = fixture.kernel.level_succ(u);
    let polymorphic = nested_name(&mut fixture.kernel, &["Source", "Poly"]);
    let polymorphic_ty = fixture.kernel.sort(u_succ);
    fixture
        .kernel
        .add_declaration(Declaration::Axiom {
            name: polymorphic,
            uparams: vec![u_name],
            ty: polymorphic_ty,
        })
        .expect("polymorphic data constant must check");

    let zero = fixture.kernel.level_zero();
    let one = fixture.kernel.level_succ(zero);
    let two = fixture.kernel.level_succ(one);
    let three = fixture.kernel.level_succ(two);
    let c0 = fixture.kernel.const_(polymorphic, vec![zero]);
    let c1 = fixture.kernel.const_(polymorphic, vec![one]);
    let sort_one = fixture.kernel.sort(one);
    let sort_two = fixture.kernel.sort(two);
    let eq0 = fixture.kernel.const_(fixture.logic.eq, vec![two]);
    let eq0 = fixture.kernel.app(eq0, sort_one);
    let eq0 = fixture.kernel.app(eq0, c0);
    let eq0 = fixture.kernel.app(eq0, c0);
    let eq1 = fixture.kernel.const_(fixture.logic.eq, vec![three]);
    let eq1 = fixture.kernel.app(eq1, sort_two);
    let eq1 = fixture.kernel.app(eq1, c1);
    let eq1 = fixture.kernel.app(eq1, c1);
    let and = fixture.kernel.const_(fixture.logic.and, vec![]);
    let and = fixture.kernel.app(and, eq0);
    let goal = fixture.kernel.app(and, eq1);

    let abstraction = ConstantInstance {
        name: polymorphic,
        levels: vec![zero],
        binder_name: nested_name(&mut fixture.kernel, &["C0"]),
    };
    let generalized = generalize_goal_constants(&mut fixture.kernel, goal, &[abstraction])
        .expect("one exact universe instance must generalize independently");
    verify_generalized_specialization(&mut fixture.kernel, &generalized, &[c0], goal)
        .expect("only the selected universe instance must specialize");
}

#[test]
fn generalized_target_transports_to_a_fresh_kernel_without_source_axioms() {
    let mut fixture = fixture();
    let carrier = instance(&mut fixture.kernel, fixture.carrier, "Alpha");
    let value = instance(&mut fixture.kernel, fixture.value, "x");
    let generalized =
        generalize_goal_constants(&mut fixture.kernel, fixture.goal, &[carrier, value])
            .expect("ordered data constants must generalize");
    let target = nested_name(
        &mut fixture.kernel,
        &["Axeyum", "Autogenesis", "TypeSlice", "target"],
    );
    let prop = fixture.kernel.sort_zero();
    fixture
        .kernel
        .add_declaration(Declaration::Definition {
            name: target,
            uparams: vec![],
            ty: prop,
            value: generalized.goal,
            hint: ReducibilityHint::Regular(0),
        })
        .expect("generalized statement definition must check");
    let stream = fixture
        .kernel
        .render_lean4export_ndjson_roots(&Lean4ExportMetadata::axeyum("4.30.0"), &[target])
        .expect("root-selected generalized statement must export");
    let completed = import_statement_ndjson(Cursor::new(stream), ImportLimits::default(), TARGET)
        .expect("proof-free generalized slice must re-admit in a fresh kernel");
    let admitted: Vec<_> = completed
        .report()
        .declaration_identities
        .iter()
        .map(|identity| identity.name.as_str())
        .collect();
    assert!(!admitted.contains(&"Source.Carrier"));
    assert!(!admitted.contains(&"Source.value"));
    assert!(completed.report().axioms.is_empty());
    assert!(!completed.kernel().has_fvars(completed.goal()));
    assert!(!completed.kernel().has_loose_bvars(completed.goal()));
}
