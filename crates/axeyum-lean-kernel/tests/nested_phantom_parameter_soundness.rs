//! Soundness-negative gates for the erasure route of Lean kernel bug #14576.
//!
//! Nested-inductive specialization instantiates the container's parameters. A
//! parameter occurring in no constructor field is therefore erased from the
//! auxiliary family and every auxiliary constructor, so the temporary expanded
//! group cannot reject an ill-typed argument in that slot. Upstream Lean
//! admitted `False` through exactly this hole. These tests pin both directions:
//! the ill-typed argument is rejected, and the well-typed one still admits.
//!
//! The positive controls are load-bearing. The parameter-domain check runs
//! under the source family's opened parameter binders and skips positions
//! mentioning a family of the group under declaration (those constants are not
//! yet in the environment). A regression in either rule turns a valid nested
//! declaration into a spurious rejection, which only a positive control finds.

use axeyum_lean_kernel::{BinderInfo, ExprId, Kernel, KernelError, NameId};

/// Declares `Unit0 : Type` / `star : Unit0` and
/// `Phantom : Type -> Type -> Type` with `mk : forall a b, b -> Phantom a b`,
/// where `a` occurs in NO constructor field (Lean #14576's phantom parameter).
fn setup(kernel: &mut Kernel) -> (NameId, NameId, NameId) {
    let root = kernel.anon();
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let type_ = kernel.sort(one);

    let unit0 = kernel.name_str(root, "Unit0");
    let star = kernel.name_str(unit0, "star");
    let unit0_const = kernel.const_(unit0, vec![]);
    kernel
        .add_inductive(unit0, &[], 0, type_, &[(star, unit0_const)])
        .expect("Unit0 admits");

    let phantom = kernel.name_str(root, "Phantom");
    let mk = kernel.name_str(phantom, "mk");
    let a = kernel.name_str(root, "a");
    let b = kernel.name_str(root, "b");
    let v = kernel.name_str(root, "v");

    let inner = kernel.pi(b, type_, type_, BinderInfo::Implicit);
    let phantom_ty = kernel.pi(a, type_, inner, BinderInfo::Implicit);

    let phantom_const = kernel.const_(phantom, vec![]);
    let a_ref = kernel.bvar(2);
    let b_ref = kernel.bvar(1);
    let applied = kernel.app(phantom_const, a_ref);
    let result = kernel.app(applied, b_ref);
    let field_dom = kernel.bvar(0);
    let field = kernel.pi(v, field_dom, result, BinderInfo::Default);
    let mk_inner = kernel.pi(b, type_, field, BinderInfo::Implicit);
    let mk_ty = kernel.pi(a, type_, mk_inner, BinderInfo::Implicit);

    kernel
        .add_inductive(phantom, &[], 2, phantom_ty, &[(mk, mk_ty)])
        .expect("Phantom container admits");

    (phantom, star, unit0)
}

/// POSITIVE CONTROL: the same shape with a well-typed phantom argument must
/// admit AND go through nested expansion (proved by the `Rose.rec_1`
/// auxiliary recursor that only the nested path creates).
#[test]
fn well_typed_phantom_parameter_takes_the_nested_path() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (phantom, _star, unit0) = setup(&mut kernel);

    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let type_ = kernel.sort(one);

    let rose = kernel.name_str(root, "Rose");
    let node = kernel.name_str(rose, "node");
    let children = kernel.name_str(root, "children");

    let rose_const = kernel.const_(rose, vec![]);
    // `Unit0 : Type` is a legitimate argument for the phantom slot.
    let good = kernel.const_(unit0, vec![]);
    let ph = kernel.const_(phantom, vec![]);
    let applied = kernel.app(ph, good);
    let nested = kernel.app(applied, rose_const);
    let node_ty = kernel.pi(children, nested, rose_const, BinderInfo::Default);

    kernel
        .add_inductive(rose, &[], 0, type_, &[(node, node_ty)])
        .expect("well-typed nested occurrence admits");

    let aux_rec = kernel.name_str(rose, "rec_1");
    assert!(
        kernel.environment().contains(aux_rec),
        "Rose.rec_1 proves the nested-expansion path was taken"
    );
}

/// NEGATIVE: an ill-typed argument in the phantom slot. This is the exact
/// escape route of Lean #14576 — after specialization the argument occurs
/// nowhere in the auxiliary family or its constructors.
#[test]
fn ill_typed_phantom_parameter_is_rejected_and_rolls_back() {
    let mut kernel = Kernel::new();
    let root = kernel.anon();
    let (phantom, star, _unit0) = setup(&mut kernel);

    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let type_ = kernel.sort(one);

    let rose = kernel.name_str(root, "Rose");
    let node = kernel.name_str(rose, "node");
    let children = kernel.name_str(root, "children");

    let rose_const = kernel.const_(rose, vec![]);
    let star_const = kernel.const_(star, vec![]); // star : Unit0, NOT a Type
    let ph = kernel.const_(phantom, vec![]);
    let applied = kernel.app(ph, star_const);
    let nested = kernel.app(applied, rose_const);
    let node_ty = kernel.pi(children, nested, rose_const, BinderInfo::Default);

    let before = kernel.environment().len();
    let outcome = kernel.add_inductive(rose, &[], 0, type_, &[(node, node_ty)]);
    assert!(
        outcome.is_err(),
        "ill-typed phantom parameter MUST be rejected"
    );
    assert_eq!(
        kernel.environment().len(),
        before,
        "failed nested admission must leave no residue"
    );
    assert!(!kernel.environment().contains(rose));
    assert!(!kernel.environment().contains(node));
    let leaked = kernel
        .environment()
        .iter()
        .map(|(name, _)| kernel.display_name(*name).to_string())
        .filter(|name| name.contains("_nested"))
        .collect::<Vec<_>>();
    assert!(
        leaked.is_empty(),
        "temporary auxiliaries leaked: {leaked:?}"
    );
}

/// Declares `Tree : Type -> Type` with
/// `node : forall (a : Type), Phantom <arg> (Tree a) -> Tree a`, where `<arg>`
/// is built under the single bound parameter `a`.
///
/// This shape exercises both skip rules of the parameter-domain check at once:
/// the source family has a parameter, so the check runs under a nonempty local
/// context of opened parameter binders, and the second nested argument mentions
/// `Tree`, a family of the group being declared, whose constant is not yet in
/// the environment.
fn declare_tree(
    kernel: &mut Kernel,
    phantom: NameId,
    build_arg: impl FnOnce(&mut Kernel) -> ExprId,
) -> Result<NameId, KernelError> {
    let root = kernel.anon();
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let type_ = kernel.sort(one);

    let tree = kernel.name_str(root, "Tree");
    let node = kernel.name_str(tree, "node");
    let a = kernel.name_str(root, "a");
    let children = kernel.name_str(root, "children");

    let tree_ty = kernel.pi(a, type_, type_, BinderInfo::Implicit);

    // Under `a` alone: `Phantom <arg> (Tree a)`.
    let tree_const = kernel.const_(tree, vec![]);
    let a_ref = kernel.bvar(0);
    let tree_a = kernel.app(tree_const, a_ref);
    let arg = build_arg(kernel);
    let ph = kernel.const_(phantom, vec![]);
    let applied = kernel.app(ph, arg);
    let nested = kernel.app(applied, tree_a);

    // Under `a` and `children`: the result `Tree a`, one binder deeper.
    let a_deep = kernel.bvar(1);
    let tree_a_deep = kernel.app(tree_const, a_deep);
    let field = kernel.pi(children, nested, tree_a_deep, BinderInfo::Default);
    let node_ty = kernel.pi(a, type_, field, BinderInfo::Implicit);

    kernel.add_inductive(tree, &[], 1, tree_ty, &[(node, node_ty)])?;
    Ok(tree)
}

/// POSITIVE CONTROL: a closed, well-typed phantom argument under a
/// parameterized source family.
#[test]
fn parameterized_family_with_closed_phantom_argument_admits() {
    let mut kernel = Kernel::new();
    let (phantom, _star, unit0) = setup(&mut kernel);

    let tree = declare_tree(&mut kernel, phantom, |kernel| kernel.const_(unit0, vec![]))
        .expect("closed well-typed phantom argument admits");

    let aux_rec = kernel.name_str(tree, "rec_1");
    assert!(
        kernel.environment().contains(aux_rec),
        "Tree.rec_1 proves the nested-expansion path was taken"
    );
}

/// POSITIVE CONTROL: the phantom argument is the source family's own parameter.
/// After the constructor telescope is opened this is a free variable, so the
/// parameter-domain check must run under the opened binders. Checking it in an
/// empty context would report an unbound variable and reject a valid family.
#[test]
fn parameterized_family_with_fvar_phantom_argument_admits() {
    let mut kernel = Kernel::new();
    let (phantom, _star, _unit0) = setup(&mut kernel);

    let tree = declare_tree(&mut kernel, phantom, |kernel| kernel.bvar(0))
        .expect("the family's own parameter is a valid phantom argument");

    let aux_rec = kernel.name_str(tree, "rec_1");
    assert!(kernel.environment().contains(aux_rec));
}

/// NEGATIVE: the same parameterized shape with an ill-typed phantom argument.
#[test]
fn parameterized_family_with_ill_typed_phantom_argument_is_rejected() {
    let mut kernel = Kernel::new();
    let (phantom, star, _unit0) = setup(&mut kernel);

    let before = kernel.environment().len();
    let outcome = declare_tree(&mut kernel, phantom, |kernel| kernel.const_(star, vec![]));
    assert!(
        outcome.is_err(),
        "ill-typed phantom parameter MUST be rejected under a parameterized family"
    );
    assert_eq!(
        kernel.environment().len(),
        before,
        "failed nested admission must leave no residue"
    );
}
