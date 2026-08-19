//! Adversarial controls for the bounded, untrusted reflexivity proposer.

#[path = "../examples/statement_reflexivity_support/mod.rs"]
mod support;

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, LogicPrelude, build_logic_prelude,
};

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

fn candidate_name(kernel: &mut Kernel, suffix: &str) -> axeyum_lean_kernel::NameId {
    let root = kernel.anon();
    let candidate = kernel.name_str(root, "ReflexivityCandidate");
    kernel.name_str(candidate, suffix)
}

#[test]
fn proposes_and_the_kernel_accepts_generic_reflexivity() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let prop = kernel.sort_zero();
    let variable = kernel.bvar(0);
    let body = equality(&mut kernel, &logic, prop, variable, variable);
    let binder = candidate_name(&mut kernel, "p");
    let goal = kernel.pi(binder, prop, body, BinderInfo::Default);

    let candidate = support::propose_reflexivity(&mut kernel, goal)
        .expect("generic reflexivity should be proposed");
    assert_eq!(candidate.binders, 1);
    assert_eq!(candidate.constructed_nodes, 4);
    let name = candidate_name(&mut kernel, "accepted");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: goal,
            value: candidate.proof,
        })
        .expect("independent kernel must accept the reflexivity term");
    assert!(kernel.axiom_footprint(name).is_empty());
    assert!(kernel.theorem_dependencies(name).is_empty());
}

#[test]
fn declines_a_non_equality_terminal_goal() {
    let mut kernel = Kernel::new();
    build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let prop = kernel.sort_zero();
    let variable = kernel.bvar(0);
    let binder = candidate_name(&mut kernel, "p");
    let goal = kernel.pi(binder, prop, variable, BinderInfo::Default);

    let error = support::propose_reflexivity(&mut kernel, goal)
        .expect_err("a bare proposition must not be treated as equality");
    assert!(error.contains("not constant-headed equality"), "{error}");
}

#[test]
fn declines_a_telescope_beyond_the_fixed_binder_budget() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let prop = kernel.sort_zero();
    let true_const = kernel.const_(logic.true_, vec![]);
    let mut goal = equality(&mut kernel, &logic, prop, true_const, true_const);
    for index in 0..=support::MAX_BINDERS {
        let binder = candidate_name(&mut kernel, &format!("p{index}"));
        goal = kernel.pi(binder, prop, goal, BinderInfo::Default);
    }

    let error = support::propose_reflexivity(&mut kernel, goal)
        .expect_err("a nine-binder telescope must exceed the budget");
    assert_eq!(error, "binder budget exceeded: maximum 8");
}

#[test]
fn independent_kernel_rejects_reflexivity_for_unequal_sides() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let prop = kernel.sort_zero();
    let q = kernel.bvar(0);
    let p = kernel.bvar(1);
    let body = equality(&mut kernel, &logic, prop, p, q);
    let q_name = candidate_name(&mut kernel, "q");
    let inner = kernel.pi(q_name, prop, body, BinderInfo::Default);
    let p_name = candidate_name(&mut kernel, "p");
    let goal = kernel.pi(p_name, prop, inner, BinderInfo::Default);

    let candidate = support::propose_reflexivity(&mut kernel, goal)
        .expect("the untrusted syntactic proposer may emit this candidate");
    let name = candidate_name(&mut kernel, "rejected");
    let result = kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: goal,
        value: candidate.proof,
    });
    assert!(
        result.is_err(),
        "the kernel must reject the invalid candidate"
    );
    assert!(!kernel.environment().contains(name));
}
