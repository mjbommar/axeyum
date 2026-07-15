//! Regression for Lean-compatible large-elimination restrictions on `Prop`.
//!
//! Proof irrelevance intentionally identifies every two proofs of the same
//! proposition. Consequently, a proposition with distinguishable constructors
//! must not eliminate into data: otherwise its recursor could distinguish
//! definitionally equal proofs. The inductive remains admissible and retains
//! ordinary case analysis into `Prop`; only its motive universe is restricted.

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprNode, Kernel};

/// Declare a nullary-constructor inductive at the given sort level.
/// `level == 0` is `Prop`; `level == 1` is `Type`.
fn declare_enum_at(
    k: &mut Kernel,
    name: &str,
    ctor_strs: &[&str],
    level: usize,
) -> (axeyum_lean_kernel::NameId, Vec<axeyum_lean_kernel::NameId>) {
    let anon = k.anon();
    let ind_name = k.name_str(anon, name);
    let mut lvl = k.level_zero();
    for _ in 0..level {
        lvl = k.level_succ(lvl);
    }
    let ty = k.sort(lvl);
    let ind_const = k.const_(ind_name, vec![]);
    let ctor_names: Vec<_> = ctor_strs.iter().map(|s| k.name_str(anon, *s)).collect();
    let ctors: Vec<_> = ctor_names.iter().map(|&cn| (cn, ind_const)).collect();
    k.add_inductive(ind_name, &[], 0, ty, &ctors)
        .expect("enum should admit");
    (ind_name, ctor_names)
}

#[test]
fn non_subsingleton_prop_eliminates_only_into_prop() {
    let mut k = Kernel::new();

    let (two_name, two_ctors) = declare_enum_at(&mut k, "Two", &["a", "b"], 0);
    let (answer_name, answer_ctors) = declare_enum_at(&mut k, "Answer", &["yes", "no"], 1);
    let (true_name, true_ctors) = declare_enum_at(&mut k, "True", &["intro"], 0);

    let a = k.const_(two_ctors[0], vec![]);
    let b = k.const_(two_ctors[1], vec![]);
    let yes = k.const_(answer_ctors[0], vec![]);
    let no = k.const_(answer_ctors[1], vec![]);
    let trivial = k.const_(true_ctors[0], vec![]);
    let two = k.const_(two_name, vec![]);
    let answer = k.const_(answer_name, vec![]);
    let true_ = k.const_(true_name, vec![]);
    let rec_name = k.name_str(two_name, "rec");

    // Proof irrelevance remains intentional: the fix must constrain the
    // eliminator rather than weakening definitional equality for proofs.
    assert!(k.def_eq(a, b));

    // A restricted recursor has no fresh elimination-universe parameter.
    match k.environment().get(rec_name).expect("Two.rec") {
        Declaration::Recursor { uparams, .. } => assert!(uparams.is_empty()),
        other => panic!("expected recursor, got {other:?}"),
    }

    let anon = k.anon();
    let rec = k.const_(rec_name, vec![]);

    // Eliminating into data (`Answer : Sort 1`) is rejected at the motive.
    let data_motive = k.lam(anon, two, answer, BinderInfo::Default);
    let illegal = k.app(rec, data_motive);
    let illegal = k.app(illegal, yes);
    let illegal = k.app(illegal, no);
    let illegal = k.app(illegal, a);
    assert!(
        k.infer(illegal).is_err(),
        "a two-constructor Prop must not eliminate into Type"
    );

    // Supplying the old fresh universe argument is rejected explicitly too.
    let zero = k.level_zero();
    let one = k.level_succ(zero);
    let old_shape = k.const_(rec_name, vec![one]);
    assert!(k.infer(old_shape).is_err());

    // Ordinary case analysis into Prop remains well-typed and computes.
    let prop_motive = k.lam(anon, two, true_, BinderInfo::Default);
    let legal = k.const_(rec_name, vec![]);
    let legal = k.app(legal, prop_motive);
    let legal = k.app(legal, trivial);
    let legal = k.app(legal, trivial);
    let legal_a = k.app(legal, a);
    let legal_ty = k.infer(legal_a).expect("Prop elimination should infer");
    let legal_ty = k.whnf(legal_ty);
    assert!(matches!(k.expr_node(legal_ty), ExprNode::Const(n, _) if *n == true_name));
    assert_eq!(k.whnf(legal_a), trivial);
}

/// Generated boundary matrix: vary constructor count and both proof/data field
/// counts. This guards the degenerate `Prop`/universe class as a family instead
/// of preserving only the historical `Two` witness.
#[test]
fn generated_prop_elimination_boundary_matrix() {
    for constructor_count in 0..=3 {
        for data_fields in 0..=2 {
            for proof_fields in 0..=2 {
                let mut k = Kernel::new();
                let anon = k.anon();
                let (_atom, atom_ctors) = declare_enum_at(&mut k, "Atom", &["unit"], 1);
                let atom_value = k.const_(atom_ctors[0], vec![]);
                let atom_type = k.infer(atom_value).expect("Atom.unit should infer");

                let premise_name = k.name_str(anon, "Premise");
                let prop = k.sort_zero();
                k.add_declaration(Declaration::Axiom {
                    name: premise_name,
                    uparams: vec![],
                    ty: prop,
                })
                .unwrap();
                let premise = k.const_(premise_name, vec![]);

                let family = k.name_str(anon, "GeneratedProp");
                let family_type = k.const_(family, vec![]);
                let mut ctors = Vec::new();
                for index in 0..constructor_count {
                    let ctor = k.name_str(family, format!("c{index}"));
                    let mut ctor_type = family_type;
                    for _ in 0..proof_fields {
                        ctor_type = k.pi(anon, premise, ctor_type, BinderInfo::Default);
                    }
                    for _ in 0..data_fields {
                        ctor_type = k.pi(anon, atom_type, ctor_type, BinderInfo::Default);
                    }
                    ctors.push((ctor, ctor_type));
                }
                k.add_inductive(family, &[], 0, prop, &ctors)
                    .expect("generated Prop family should admit");

                let rec = k.name_str(family, "rec");
                let Declaration::Recursor { uparams, .. } =
                    k.environment().get(rec).expect("generated recursor")
                else {
                    panic!("expected recursor");
                };
                let should_large_eliminate =
                    constructor_count == 0 || (constructor_count == 1 && data_fields == 0);
                assert_eq!(
                    uparams.len(),
                    usize::from(should_large_eliminate),
                    "constructors={constructor_count}, data_fields={data_fields}, \
                     proof_fields={proof_fields}"
                );
            }
        }
    }
}
