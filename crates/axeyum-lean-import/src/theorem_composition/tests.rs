use axeyum_lean_kernel::{
    BinderInfo, Declaration, InductiveFamilySpec, Kernel, ReducibilityHint, build_logic_prelude,
    build_nat_prelude,
};

use super::*;

fn name(kernel: &mut Kernel, value: &str) -> NameId {
    let anon = kernel.anon();
    kernel.name_str(anon, value)
}

fn add_true_theorem(kernel: &mut Kernel, name: &str) -> NameId {
    let logic = build_logic_prelude(kernel).expect("logic prelude");
    let theorem = self::name(kernel, name);
    let ty = kernel.const_(logic.true_, vec![]);
    let value = kernel.const_(logic.true_intro, vec![]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: theorem,
            uparams: vec![],
            ty,
            value,
        })
        .expect("true theorem");
    theorem
}

fn target_leaf_control_source() -> Kernel {
    let mut source = Kernel::new();
    let source_logic = build_logic_prelude(&mut source).expect("source logic");
    let leaf = add_true_theorem(&mut source, "LeafControl.leaf");
    let root = name(&mut source, "LeafControl.root");
    let true_ty = source.const_(source_logic.true_, vec![]);
    let leaf_proof = source.const_(leaf, vec![]);
    source
        .add_declaration(Declaration::Theorem {
            name: root,
            uparams: vec![],
            ty: true_ty,
            value: leaf_proof,
        })
        .expect("source root checks");
    add_true_theorem(&mut source, "LeafControl.unreachable");
    source
}

#[test]
fn completed_composition_is_axiom_free_deterministic_and_reverifiable() {
    let mut source = Kernel::new();
    add_true_theorem(&mut source, "Composition.root");
    let mut target = Kernel::new();
    build_logic_prelude(&mut target).expect("target logic");
    let target_before = environment_sha256(&target).unwrap();
    let target_len = target.environment().len();

    let first = compose_checked_theorem_slice(&source, &target, &["Composition.root"]).unwrap();
    let second = compose_checked_theorem_slice(&source, &target, &["Composition.root"]).unwrap();
    assert_eq!(first.receipt(), second.receipt());
    assert!(first.receipt().has_valid_digest());
    assert!(first.receipt().to_pretty_json().unwrap().ends_with('\n'));
    assert_eq!(target.environment().len(), target_len);
    assert_eq!(environment_sha256(&target).unwrap(), target_before);
    assert_eq!(first.receipt().added_theorems.len(), 1);
    assert_eq!(first.receipt().added_theorems[0].name, "Composition.root");
    assert!(first.receipt().added_theorems[0].axiom_footprint.is_empty());
    assert!(declaration_names(first.kernel()).contains_key("Composition.root"));
    verify_checked_theorem_composition(&source, &target, first.kernel(), first.receipt()).unwrap();

    assert!(matches!(
        compose_checked_theorem_slice(&source, first.kernel(), &["Composition.root"]),
        Err(CheckedTheoremCompositionError::NoAdditions)
    ));
}

#[test]
fn explicit_target_theorem_leaf_is_compatible_axiom_free_and_replayable() {
    let mut source = Kernel::new();
    let source_logic = build_logic_prelude(&mut source).expect("source logic");
    let source_hidden = add_true_theorem(&mut source, "LeafControl.hidden");
    let source_leaf = name(&mut source, "LeafControl.leaf");
    let true_ty = source.const_(source_logic.true_, vec![]);
    let hidden_proof = source.const_(source_hidden, vec![]);
    source
        .add_declaration(Declaration::Theorem {
            name: source_leaf,
            uparams: vec![],
            ty: true_ty,
            value: hidden_proof,
        })
        .expect("source leaf checks");
    let source_root = name(&mut source, "LeafControl.root");
    let leaf_proof = source.const_(source_leaf, vec![]);
    source
        .add_declaration(Declaration::Theorem {
            name: source_root,
            uparams: vec![],
            ty: true_ty,
            value: leaf_proof,
        })
        .expect("source root checks");

    let mut target = Kernel::new();
    build_logic_prelude(&mut target).expect("target logic");
    add_true_theorem(&mut target, "LeafControl.leaf");
    let target_before = environment_sha256(&target).unwrap();
    let target_len = target.environment().len();
    let completed = compose_checked_theorem_slice_with_target_leaves(
        &source,
        &target,
        &["LeafControl.root"],
        &["LeafControl.leaf"],
    )
    .expect("the explicit target leaf cuts only the source proof behind it");
    assert_eq!(target.environment().len(), target_len);
    assert_eq!(environment_sha256(&target).unwrap(), target_before);
    assert_eq!(
        completed.receipt().schema_version,
        CHECKED_TARGET_LEAF_THEOREM_COMPOSITION_VERSION
    );
    assert_eq!(
        completed.receipt().target_theorem_leaves,
        ["LeafControl.leaf"]
    );
    assert!(
        completed
            .receipt()
            .source_closure
            .contains(&"LeafControl.leaf".to_owned())
    );
    assert!(
        !completed
            .receipt()
            .source_closure
            .contains(&"LeafControl.hidden".to_owned())
    );
    assert_eq!(
        completed
            .receipt()
            .added_theorems
            .iter()
            .map(|row| row.name.as_str())
            .collect::<Vec<_>>(),
        ["LeafControl.root"]
    );
    assert!(
        completed.receipt().added_theorems[0]
            .axiom_footprint
            .is_empty()
    );
    verify_checked_theorem_composition_with_target_leaves(
        &source,
        &target,
        completed.kernel(),
        completed.receipt(),
    )
    .expect("target-leaf receipt replays");

    let full = compose_checked_theorem_slice(&source, &target, &["LeafControl.root"])
        .expect("the uncut control still composes");
    assert!(
        full.receipt()
            .source_closure
            .contains(&"LeafControl.hidden".to_owned())
    );
    assert_eq!(full.receipt().target_theorem_leaves, Vec::<String>::new());

    let mut mutated = completed.receipt().clone();
    mutated.target_theorem_leaves = vec!["LeafControl.hidden".to_owned()];
    assert_eq!(
        verify_checked_theorem_composition_with_target_leaves(
            &source,
            &target,
            completed.kernel(),
            &mutated,
        ),
        Err(CheckedTheoremCompositionError::ReceiptMismatch)
    );
}

#[test]
fn target_theorem_leaf_controls_fail_closed() {
    let source = target_leaf_control_source();

    let mut target = Kernel::new();
    build_logic_prelude(&mut target).expect("target logic");
    add_true_theorem(&mut target, "LeafControl.leaf");
    let before = environment_sha256(&target).unwrap();
    let len = target.environment().len();

    assert!(matches!(
        compose_checked_theorem_slice_with_target_leaves(
            &source,
            &target,
            &["LeafControl.root"],
            &[]
        ),
        Err(CheckedTheoremCompositionError::EmptyTargetTheoremLeaves)
    ));
    assert!(matches!(
        compose_checked_theorem_slice_with_target_leaves(
            &source,
            &target,
            &["LeafControl.root"],
            &["LeafControl.leaf", "LeafControl.leaf"]
        ),
        Err(CheckedTheoremCompositionError::InvalidTargetTheoremLeaf {
            reason: "duplicate",
            ..
        })
    ));
    assert!(matches!(
        compose_checked_theorem_slice_with_target_leaves(
            &source,
            &target,
            &["LeafControl.root"],
            &["LeafControl.missing"]
        ),
        Err(CheckedTheoremCompositionError::InvalidTargetTheoremLeaf {
            reason: "missing from source",
            ..
        })
    ));
    assert!(matches!(
        compose_checked_theorem_slice_with_target_leaves(
            &source,
            &target,
            &["LeafControl.root"],
            &["LeafControl.unreachable"]
        ),
        Err(CheckedTheoremCompositionError::InvalidTargetTheoremLeaf {
            reason: "missing from target",
            ..
        })
    ));
    assert_eq!(target.environment().len(), len);
    assert_eq!(environment_sha256(&target).unwrap(), before);
    add_true_theorem(&mut target, "LeafControl.unreachable");
    assert!(matches!(
        compose_checked_theorem_slice_with_target_leaves(
            &source,
            &target,
            &["LeafControl.root"],
            &["LeafControl.unreachable"]
        ),
        Err(CheckedTheoremCompositionError::Closure(error))
            if error.contains("UnreachableTheoremLeaf")
    ));
}

#[test]
fn target_theorem_leaf_requires_the_same_checked_type() {
    let source = target_leaf_control_source();
    let mut wrong_type_target = Kernel::new();
    let wrong_logic = build_logic_prelude(&mut wrong_type_target).expect("target logic");
    let wrong_leaf = name(&mut wrong_type_target, "LeafControl.leaf");
    let wrong_true = wrong_type_target.const_(wrong_logic.true_, vec![]);
    let wrong_anon = wrong_type_target.anon();
    let wrong_type = wrong_type_target.pi(wrong_anon, wrong_true, wrong_true, BinderInfo::Default);
    let identity = wrong_type_target.bvar(0);
    let wrong_value = wrong_type_target.lam(wrong_anon, wrong_true, identity, BinderInfo::Default);
    wrong_type_target
        .add_declaration(Declaration::Theorem {
            name: wrong_leaf,
            uparams: vec![],
            ty: wrong_type,
            value: wrong_value,
        })
        .expect("wrong-type target control is itself a valid theorem");
    assert!(matches!(
        compose_checked_theorem_slice_with_target_leaves(
            &source,
            &wrong_type_target,
            &["LeafControl.root"],
            &["LeafControl.leaf"]
        ),
        Err(CheckedTheoremCompositionError::TypeShapeMismatch { name, .. })
            if name == "LeafControl.leaf"
    ));
}

#[test]
fn target_theorem_leaf_rejects_an_assumption_footprint() {
    let source = target_leaf_control_source();
    let mut assumption_target = Kernel::new();
    let logic = build_logic_prelude(&mut assumption_target).expect("target logic");
    let assumption = name(&mut assumption_target, "LeafControl.assumption");
    let target_true = assumption_target.const_(logic.true_, vec![]);
    assumption_target
        .add_declaration(Declaration::Axiom {
            name: assumption,
            uparams: vec![],
            ty: target_true,
        })
        .expect("control assumption checks");
    let target_leaf = name(&mut assumption_target, "LeafControl.leaf");
    let assumption_proof = assumption_target.const_(assumption, vec![]);
    assumption_target
        .add_declaration(Declaration::Theorem {
            name: target_leaf,
            uparams: vec![],
            ty: target_true,
            value: assumption_proof,
        })
        .expect("assumption-bearing target leaf checks");
    assert!(matches!(
        compose_checked_theorem_slice_with_target_leaves(
            &source,
            &assumption_target,
            &["LeafControl.root"],
            &["LeafControl.leaf"]
        ),
        Err(
            CheckedTheoremCompositionError::TargetTheoremLeafAxiomFootprint {
                footprint,
                ..
            }
        ) if footprint == ["LeafControl.assumption"]
    ));
}

#[test]
fn roots_fail_closed_and_a_missing_definition_is_checked() {
    let mut source = Kernel::new();
    let logic = build_logic_prelude(&mut source).expect("source logic");
    let target = {
        let mut kernel = Kernel::new();
        build_logic_prelude(&mut kernel).expect("target logic");
        kernel
    };
    add_true_theorem(&mut source, "Composition.duplicate");
    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &[]),
        Err(CheckedTheoremCompositionError::EmptyRoots)
    ));
    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &["missing"]),
        Err(CheckedTheoremCompositionError::MissingRoot(name)) if name == "missing"
    ));
    assert!(matches!(
        compose_checked_theorem_slice(
            &source,
            &target,
            &["Composition.duplicate", "Composition.duplicate"]
        ),
        Err(CheckedTheoremCompositionError::DuplicateRoot(name))
            if name == "Composition.duplicate"
    ));
    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &["True"]),
        Err(CheckedTheoremCompositionError::RootIsNotTheorem(name)) if name == "True"
    ));

    let anon = source.anon();
    let definition = source.name_str(anon, "Composition.payload");
    let prop = source.sort_zero();
    let true_type = source.const_(logic.true_, vec![]);
    source
        .add_declaration(Declaration::Definition {
            name: definition,
            uparams: vec![],
            ty: prop,
            value: true_type,
            hint: ReducibilityHint::Regular(1),
        })
        .unwrap();
    let root = source.name_str(anon, "Composition.definitionRoot");
    let root_type = source.const_(definition, vec![]);
    let proof = source.const_(logic.true_intro, vec![]);
    source
        .add_declaration(Declaration::Theorem {
            name: root,
            uparams: vec![],
            ty: root_type,
            value: proof,
        })
        .unwrap();
    let completed =
        compose_checked_theorem_slice(&source, &target, &["Composition.definitionRoot"]).unwrap();
    assert_eq!(completed.receipt().added_definitions.len(), 1);
    let added = &completed.receipt().added_definitions[0];
    assert_eq!(added.name, "Composition.payload");
    assert_eq!(added.reducibility, "regular:1");
    assert_eq!(
        added.source_declaration_sha256,
        added.target_declaration_sha256
    );
    assert!(
        completed.receipt().added_theorems[0]
            .axiom_footprint
            .is_empty()
    );
    verify_checked_theorem_composition(&source, &target, completed.kernel(), completed.receipt())
        .unwrap();
}

fn source_with_missing_proof_dependency(kind: &str) -> (Kernel, Kernel, &'static str) {
    let mut source = Kernel::new();
    let logic = build_logic_prelude(&mut source).unwrap();
    let mut target = Kernel::new();
    build_logic_prelude(&mut target).unwrap();
    let dependency = name(&mut source, "Composition.missingProof");
    let true_type = source.const_(logic.true_, vec![]);
    let true_intro = source.const_(logic.true_intro, vec![]);
    let declaration = match kind {
        "axiom" => Declaration::Axiom {
            name: dependency,
            uparams: vec![],
            ty: true_type,
        },
        "opaque" => Declaration::Opaque {
            name: dependency,
            uparams: vec![],
            ty: true_type,
            value: true_intro,
        },
        _ => unreachable!(),
    };
    source.add_declaration(declaration).unwrap();
    let root = name(&mut source, "Composition.missingKindRoot");
    let proof = source.const_(dependency, vec![]);
    source
        .add_declaration(Declaration::Theorem {
            name: root,
            uparams: vec![],
            ty: true_type,
            value: proof,
        })
        .unwrap();
    (source, target, "Composition.missingKindRoot")
}

#[test]
fn missing_axiom_opaque_and_recursive_inductive_dependencies_decline() {
    for kind in ["axiom", "opaque"] {
        let (source, target, root) = source_with_missing_proof_dependency(kind);
        assert!(matches!(
            compose_checked_theorem_slice(&source, &target, &[root]),
            Err(CheckedTheoremCompositionError::UnsupportedMissingDeclaration {
                name,
                kind: got,
            }) if name == "Composition.missingProof" && got == kind
        ));
    }

    let mut source = Kernel::new();
    build_nat_prelude(&mut source).unwrap();
    let target = Kernel::new();
    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &["Nat.add_comm"]),
        Err(CheckedTheoremCompositionError::UnsupportedMissingDeclaration { kind, .. })
            if kind == "recursive-inductive"
    ));
}

#[test]
fn complete_nonrecursive_singleton_inductive_is_reconstructed_atomically() {
    let mut source = Kernel::new();
    add_true_theorem(&mut source, "Composition.inductiveRoot");
    let target = Kernel::new();
    let completed =
        compose_checked_theorem_slice(&source, &target, &["Composition.inductiveRoot"]).unwrap();
    assert_eq!(completed.receipt().added_singleton_inductives.len(), 1);
    let package = &completed.receipt().added_singleton_inductives[0];
    assert_eq!(package.family, "True");
    assert_eq!(package.constructors, ["True.intro"]);
    assert_eq!(package.recursor, "True.rec");
    assert_eq!(
        package
            .source_declaration_sha256
            .keys()
            .cloned()
            .collect::<Vec<_>>(),
        ["True", "True.intro", "True.rec"]
    );
    assert_eq!(
        package
            .target_declaration_sha256
            .keys()
            .cloned()
            .collect::<Vec<_>>(),
        ["True", "True.intro", "True.rec"]
    );
    assert!(declaration_names(completed.kernel()).contains_key("True"));
    assert!(declaration_names(completed.kernel()).contains_key("True.intro"));
    assert!(declaration_names(completed.kernel()).contains_key("True.rec"));
    assert!(declaration_names(completed.kernel()).contains_key("Composition.inductiveRoot"));
    assert!(
        completed.receipt().added_theorems[0]
            .axiom_footprint
            .is_empty()
    );
    verify_checked_theorem_composition(&source, &target, completed.kernel(), completed.receipt())
        .unwrap();
}

#[test]
fn missing_definition_precedes_the_singleton_inductive_that_uses_it() {
    let mut source = Kernel::new();
    let zero = source.level_zero();
    let one = source.level_succ(zero);
    let sort_one = source.sort(one);
    let proposition = source.sort_zero();
    let base = name(&mut source, "Composition.BaseProp");
    source
        .add_declaration(Declaration::Definition {
            name: base,
            uparams: vec![],
            ty: sort_one,
            value: proposition,
            hint: ReducibilityHint::Regular(1),
        })
        .unwrap();

    let wrapped = name(&mut source, "Composition.Wrapped");
    let intro = source.name_str(wrapped, "intro");
    let wrapped_sort = source.const_(base, vec![]);
    let wrapped_type = source.const_(wrapped, vec![]);
    source
        .add_inductive(wrapped, &[], 0, wrapped_sort, &[(intro, wrapped_type)])
        .unwrap();
    let root = name(&mut source, "Composition.wrappedRoot");
    let proof = source.const_(intro, vec![]);
    source
        .add_declaration(Declaration::Theorem {
            name: root,
            uparams: vec![],
            ty: wrapped_type,
            value: proof,
        })
        .unwrap();

    let target = Kernel::new();
    let completed = compose_checked_theorem_slice(&source, &target, &["Composition.wrappedRoot"])
        .expect("the definition must be admitted before its dependent package");
    assert_eq!(
        completed
            .receipt()
            .added_definitions
            .iter()
            .map(|row| row.name.as_str())
            .collect::<Vec<_>>(),
        ["Composition.BaseProp"]
    );
    assert_eq!(completed.receipt().added_singleton_inductives.len(), 1);
    assert_eq!(
        completed.receipt().added_singleton_inductives[0].family,
        "Composition.Wrapped"
    );
    assert_eq!(
        completed.receipt().added_theorems[0].name,
        "Composition.wrappedRoot"
    );
    assert!(
        completed.receipt().added_theorems[0]
            .axiom_footprint
            .is_empty()
    );
    verify_checked_theorem_composition(&source, &target, completed.kernel(), completed.receipt())
        .unwrap();

    // The composition is functional: the caller remains unchanged.
    assert!(target.environment().is_empty());
}

#[test]
fn canonical_recursive_acc_is_regenerated_exactly_and_reverified() {
    let mut source = Kernel::new();
    build_logic_prelude(&mut source).unwrap();
    let target = Kernel::new();
    let target_len = target.environment().len();
    let completed = compose_checked_theorem_slice(&source, &target, &["Acc.inv"]).unwrap();

    assert_eq!(target.environment().len(), target_len);
    assert_eq!(completed.receipt().added_singleton_inductives.len(), 1);
    let package = &completed.receipt().added_singleton_inductives[0];
    assert_eq!(package.family, "Acc");
    assert_eq!(package.constructors, ["Acc.intro"]);
    assert_eq!(package.recursor, "Acc.rec");
    assert_eq!(
        package.source_declaration_sha256,
        package.target_declaration_sha256
    );
    assert_eq!(
        completed
            .receipt()
            .added_theorems
            .iter()
            .map(|row| row.name.as_str())
            .collect::<Vec<_>>(),
        ["Acc.inv"]
    );
    assert!(
        completed.receipt().added_theorems[0]
            .axiom_footprint
            .is_empty()
    );
    verify_checked_theorem_composition(&source, &target, completed.kernel(), completed.receipt())
        .unwrap();
}

#[test]
fn official_acc_authority_is_exactly_three_declaration_identities() {
    let accepted = OFFICIAL_LEAN_4_30_ACC_PACKAGE_SHA256.map(str::to_owned);
    assert!(acc_package_identity_is_authorized(&accepted));

    for index in 0..accepted.len() {
        let mut mutated = accepted.clone();
        mutated[index].replace_range(
            ..1,
            if mutated[index].starts_with('0') {
                "1"
            } else {
                "0"
            },
        );
        assert!(!acc_package_identity_is_authorized(&mutated));
    }
    assert!(!acc_package_identity_is_authorized(&accepted[..2]));
}

#[test]
fn incomplete_acc_package_declines_before_admission() {
    let mut source = Kernel::new();
    build_logic_prelude(&mut source).unwrap();
    let names = declaration_names(&source);
    let acc = names["Acc"];
    let missing = [acc, names["Acc.intro"]]
        .into_iter()
        .collect::<BTreeSet<_>>();

    assert!(matches!(
        validate_singleton_inductive(&source, acc, &missing, &names),
        Err(CheckedTheoremCompositionError::UnsupportedMissingDeclaration { kind, .. })
            if kind == "non-singleton-or-partial-inductive-package"
    ));
}

#[test]
fn a_recursive_lookalike_named_acc_has_no_composition_authority() {
    let mut source = Kernel::new();
    let anon = source.anon();
    let prop = source.sort_zero();
    let acc = source.name_str(anon, "Acc");
    let intro = source.name_str(acc, "intro");
    let acc_type = source.const_(acc, vec![]);
    let intro_type = source.pi(anon, acc_type, acc_type, BinderInfo::Default);
    source
        .add_inductive(acc, &[], 0, prop, &[(intro, intro_type)])
        .unwrap();
    let root = name(&mut source, "Composition.fakeAccIdentity");
    let root_type = source.pi(anon, acc_type, acc_type, BinderInfo::Default);
    let root_body = source.bvar(0);
    let root_value = source.lam(anon, acc_type, root_body, BinderInfo::Default);
    source
        .add_declaration(Declaration::Theorem {
            name: root,
            uparams: vec![],
            ty: root_type,
            value: root_value,
        })
        .unwrap();
    let target = Kernel::new();
    let target_len = target.environment().len();

    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &["Composition.fakeAccIdentity"]),
        Err(CheckedTheoremCompositionError::UnsupportedMissingDeclaration { name, kind })
            if name == "Acc" && kind == "recursive-inductive"
    ));
    assert_eq!(target.environment().len(), target_len);
}

#[test]
fn mutual_inductive_package_remains_outside_the_boundary() {
    let mut source = Kernel::new();
    let prop = source.sort_zero();
    let left = name(&mut source, "Composition.MutualLeft");
    let right = name(&mut source, "Composition.MutualRight");
    source
        .add_mutual_inductive(
            &[],
            0,
            &[
                InductiveFamilySpec::new(left, prop, vec![]),
                InductiveFamilySpec::new(right, prop, vec![]),
            ],
        )
        .unwrap();
    let witness = name(&mut source, "Composition.mutualWitness");
    let left_type = source.const_(left, vec![]);
    source
        .add_declaration(Declaration::Axiom {
            name: witness,
            uparams: vec![],
            ty: left_type,
        })
        .unwrap();
    let root = name(&mut source, "Composition.mutualRoot");
    let proof = source.const_(witness, vec![]);
    source
        .add_declaration(Declaration::Theorem {
            name: root,
            uparams: vec![],
            ty: left_type,
            value: proof,
        })
        .unwrap();
    let target = Kernel::new();
    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &["Composition.mutualRoot"]),
        Err(CheckedTheoremCompositionError::UnsupportedMissingDeclaration { kind, .. })
            if kind == "non-singleton-or-partial-inductive-package"
    ));
}

#[test]
fn binder_info_only_type_difference_authorizes_a_fresh_gate_check() {
    fn add_compatible_surface(kernel: &mut Kernel, info: BinderInfo, add_root: bool) {
        let logic = build_logic_prelude(kernel).unwrap();
        let true_type = kernel.const_(logic.true_, vec![]);
        let binder = kernel.anon();
        let surface_type = kernel.pi(binder, true_type, true_type, info);
        let witness = name(kernel, "Composition.surfaceWitness");
        kernel
            .add_declaration(Declaration::Axiom {
                name: witness,
                uparams: vec![],
                ty: surface_type,
            })
            .unwrap();
        if add_root {
            let root = name(kernel, "Composition.compatibleRoot");
            let proof = kernel.const_(witness, vec![]);
            kernel
                .add_declaration(Declaration::Theorem {
                    name: root,
                    uparams: vec![],
                    ty: surface_type,
                    value: proof,
                })
                .unwrap();
        }
    }

    let mut source = Kernel::new();
    add_compatible_surface(&mut source, BinderInfo::Default, true);
    let mut target = Kernel::new();
    add_compatible_surface(&mut target, BinderInfo::Implicit, false);
    let completed =
        compose_checked_theorem_slice(&source, &target, &["Composition.compatibleRoot"]).unwrap();
    let surface = completed
        .receipt()
        .reused_declarations
        .iter()
        .find(|row| row.name == "Composition.surfaceWitness")
        .unwrap();
    assert_ne!(
        surface.source_declaration_sha256,
        surface.target_declaration_sha256
    );
    assert_eq!(
        surface.source_type_shape_sha256,
        surface.target_type_shape_sha256
    );
    assert_eq!(
        completed.receipt().added_theorems[0].axiom_footprint,
        ["Composition.surfaceWitness"]
    );
    assert_eq!(
        surface.compatibility,
        ReusedTypeCompatibility::KernelTypeShape
    );
}

#[test]
fn translated_definitional_equality_authorizes_only_a_fresh_gate_check() {
    fn add_surface(kernel: &mut Kernel, wrapped_witness: bool, add_root: bool) {
        let logic = build_logic_prelude(kernel).unwrap();
        let prop = kernel.sort_zero();
        let true_type = kernel.const_(logic.true_, vec![]);
        let surface = name(kernel, "Composition.DefeqSurface");
        kernel
            .add_declaration(Declaration::Definition {
                name: surface,
                uparams: vec![],
                ty: prop,
                value: true_type,
                hint: ReducibilityHint::Regular(1),
            })
            .unwrap();
        let wrapped_type = kernel.const_(surface, vec![]);
        let witness = name(kernel, "Composition.defeqWitness");
        kernel
            .add_declaration(Declaration::Axiom {
                name: witness,
                uparams: vec![],
                ty: if wrapped_witness {
                    wrapped_type
                } else {
                    true_type
                },
            })
            .unwrap();
        if add_root {
            let root = name(kernel, "Composition.defeqRoot");
            let proof = kernel.const_(witness, vec![]);
            kernel
                .add_declaration(Declaration::Theorem {
                    name: root,
                    uparams: vec![],
                    ty: wrapped_type,
                    value: proof,
                })
                .unwrap();
        }
    }

    let mut source = Kernel::new();
    add_surface(&mut source, true, true);
    let mut target = Kernel::new();
    add_surface(&mut target, false, false);
    let completed =
        compose_checked_theorem_slice(&source, &target, &["Composition.defeqRoot"]).unwrap();
    let witness = completed
        .receipt()
        .reused_declarations
        .iter()
        .find(|row| row.name == "Composition.defeqWitness")
        .unwrap();
    assert_ne!(
        witness.source_type_shape_sha256,
        witness.target_type_shape_sha256
    );
    assert_eq!(
        witness.compatibility,
        ReusedTypeCompatibility::TranslatedDefinitionalEquality
    );
    assert_eq!(
        checked_reused_declaration_compatibility(&source, &target, "Composition.defeqWitness")
            .unwrap(),
        *witness
    );
    assert_eq!(
        completed.receipt().added_theorems[0].axiom_footprint,
        ["Composition.defeqWitness"]
    );
    verify_checked_theorem_composition(&source, &target, completed.kernel(), completed.receipt())
        .unwrap();
}

#[test]
fn a_structural_reuse_mismatch_leaves_the_target_unchanged() {
    let mut source = Kernel::new();
    build_logic_prelude(&mut source).unwrap();
    let mut target = Kernel::new();
    build_logic_prelude(&mut target).unwrap();
    let source_name = name(&mut source, "Composition.P");
    let target_name = name(&mut target, "Composition.P");
    let source_prop = source.sort_zero();
    source
        .add_declaration(Declaration::Axiom {
            name: source_name,
            uparams: vec![],
            ty: source_prop,
        })
        .unwrap();
    let target_type = {
        let zero = target.level_zero();
        let one = target.level_succ(zero);
        target.sort(one)
    };
    target
        .add_declaration(Declaration::Axiom {
            name: target_name,
            uparams: vec![],
            ty: target_type,
        })
        .unwrap();
    let witness_name = name(&mut source, "Composition.p");
    let proposition = source.const_(source_name, vec![]);
    source
        .add_declaration(Declaration::Axiom {
            name: witness_name,
            uparams: vec![],
            ty: proposition,
        })
        .unwrap();
    let root_name = name(&mut source, "Composition.mismatchRoot");
    let witness = source.const_(witness_name, vec![]);
    source
        .add_declaration(Declaration::Theorem {
            name: root_name,
            uparams: vec![],
            ty: proposition,
            value: witness,
        })
        .unwrap();
    let before = environment_sha256(&target).unwrap();
    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &["Composition.mismatchRoot"]),
        Err(CheckedTheoremCompositionError::TypeShapeMismatch { name, .. })
            if name == "Composition.P"
    ));
    assert!(matches!(
        checked_reused_declaration_compatibility(&source, &target, "Composition.P"),
        Err(CheckedTheoremCompositionError::TypeShapeMismatch { name, .. })
            if name == "Composition.P"
    ));
    assert!(matches!(
        checked_reused_declaration_compatibility(&source, &target, "Composition.p"),
        Err(CheckedTheoremCompositionError::MissingTarget(name))
            if name == "Composition.p"
    ));
    assert_eq!(environment_sha256(&target).unwrap(), before);
}

#[test]
fn admission_failure_after_staging_does_not_publish_the_prefix() {
    let mut source = Kernel::new();
    let source_logic = build_logic_prelude(&mut source).unwrap();
    let mut target = Kernel::new();
    let target_logic = build_logic_prelude(&mut target).unwrap();
    let source_definition = name(&mut source, "Composition.switch");
    let target_definition = name(&mut target, "Composition.switch");
    let source_prop = source.sort_zero();
    let target_prop = target.sort_zero();
    let source_true = source.const_(source_logic.true_, vec![]);
    let target_false = target.const_(target_logic.false_, vec![]);
    source
        .add_declaration(Declaration::Definition {
            name: source_definition,
            uparams: vec![],
            ty: source_prop,
            value: source_true,
            hint: ReducibilityHint::Regular(1),
        })
        .unwrap();
    target
        .add_declaration(Declaration::Definition {
            name: target_definition,
            uparams: vec![],
            ty: target_prop,
            value: target_false,
            hint: ReducibilityHint::Regular(1),
        })
        .unwrap();
    let helper = add_true_theorem(&mut source, "Composition.helper");
    let root = name(&mut source, "Composition.lateFailure");
    let root_type = source.const_(source_definition, vec![]);
    let helper_proof = source.const_(helper, vec![]);
    source
        .add_declaration(Declaration::Theorem {
            name: root,
            uparams: vec![],
            ty: root_type,
            value: helper_proof,
        })
        .unwrap();
    let before = environment_sha256(&target).unwrap();
    assert!(matches!(
        compose_checked_theorem_slice(&source, &target, &["Composition.lateFailure"]),
        Err(CheckedTheoremCompositionError::AdmissionRejected { name, .. })
            if name == "Composition.lateFailure"
    ));
    assert_eq!(environment_sha256(&target).unwrap(), before);
    assert!(!declaration_names(&target).contains_key("Composition.helper"));
}

#[test]
fn admission_diagnostics_render_semantics_without_process_local_expression_ids() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).unwrap();
    let expected = kernel.const_(logic.true_, vec![]);
    let got = kernel.const_(logic.false_, vec![]);
    let rendered =
        explain_admission_error(&mut kernel, &KernelError::TypeMismatch { expected, got });
    assert!(rendered.contains("TypeMismatch"));
    assert!(rendered.contains("expected: \"True\""));
    assert!(rendered.contains("got: \"False\""));
    assert!(rendered.contains("first_expected"));
    assert!(!rendered.contains("ExprId"));

    let rendered = explain_admission_error(
        &mut kernel,
        &KernelError::DeclarationValueMismatch {
            declared: expected,
            inferred: got,
        },
    );
    assert!(rendered.contains("declared: \"True\""));
    assert!(rendered.contains("inferred: \"False\""));
    assert!(!rendered.contains("ExprId"));
}

#[test]
fn free_variables_and_receipt_mutations_are_rejected() {
    let mut source = Kernel::new();
    let free = source.fvar(7);
    let mut target = Kernel::new();
    assert_eq!(
        ExpressionTranslator::new(&source, &mut target).expr(free),
        Err(CheckedTheoremCompositionError::FreeVariable)
    );

    let mut source = Kernel::new();
    add_true_theorem(&mut source, "Composition.receiptRoot");
    let mut target = Kernel::new();
    build_logic_prelude(&mut target).unwrap();
    let completed =
        compose_checked_theorem_slice(&source, &target, &["Composition.receiptRoot"]).unwrap();
    let mut changed = completed.receipt().clone();
    changed.target_environment_sha256_after = "00".repeat(32);
    assert_eq!(
        verify_checked_theorem_composition(&source, &target, completed.kernel(), &changed),
        Err(CheckedTheoremCompositionError::ReceiptMismatch)
    );

    let mut changed = completed.receipt().clone();
    changed.reused_declarations[0].compatibility =
        ReusedTypeCompatibility::TranslatedDefinitionalEquality;
    assert_eq!(
        verify_checked_theorem_composition(&source, &target, completed.kernel(), &changed),
        Err(CheckedTheoremCompositionError::ReceiptMismatch)
    );
}
