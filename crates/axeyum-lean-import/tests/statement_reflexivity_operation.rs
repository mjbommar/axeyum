//! Adversarial controls for the bounded, untrusted reflexivity proposer.

#[path = "../examples/statement_reflexivity_support/mod.rs"]
mod support;

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, LogicPrelude, NameId, ReducibilityHint,
    build_logic_prelude, build_nat_prelude,
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

/// `Nat.rel a b` for a raw 2-arg relation/definition constant such as
/// `NatPrelude::le`/`lt`/`dvd`/`mul`.
fn binary_app(kernel: &mut Kernel, head: NameId, a: ExprId, b: ExprId) -> ExprId {
    let applied = kernel.const_(head, vec![]);
    let applied = kernel.app(applied, a);
    kernel.app(applied, b)
}

/// `Nat.op a` for a raw 1-arg constant such as `NatPrelude::succ`.
fn unary_app(kernel: &mut Kernel, head: NameId, a: ExprId) -> ExprId {
    let applied = kernel.const_(head, vec![]);
    kernel.app(applied, a)
}

/// `NatPrelude` has no `Ne` (this repository's own Nat development never
/// needed one), but the widened producer's `Ne` route is shaped for real
/// Lean4's actual `Ne {α : Sort u} (a b : α) : Prop := Not (Eq.{u} α a b)` —
/// so the adversarial fixtures below declare that exact definition once,
/// against the same kernel/prelude, the same way a real archive stream would
/// carry it in through `import_statement_ndjson`.
fn declare_ne(kernel: &mut Kernel, logic: &LogicPrelude) -> NameId {
    let root = kernel.anon();
    let ne_name = kernel.name_str(root, "Ne");
    let u_name = kernel.name_str(root, "u");
    let u_level = kernel.level_param(u_name);
    let sort_u = kernel.sort(u_level);
    let prop = kernel.sort_zero();

    let alpha_name = kernel.name_str(root, "alpha");
    let a_name = kernel.name_str(root, "a");
    let b_name = kernel.name_str(root, "b");

    // `(alpha : Sort u) -> (a : alpha) -> (b : alpha) -> Prop`, built
    // inside-out so each type annotation gets the right de Bruijn index for
    // its position in the final telescope.
    let b_ty = kernel.bvar(1); // alpha, from inside `a`'s scope (a = bvar 0)
    let a_ty = kernel.bvar(0); // alpha, from inside only `alpha`'s own scope
    let with_b = kernel.pi(b_name, b_ty, prop, BinderInfo::Default);
    let with_a = kernel.pi(a_name, a_ty, with_b, BinderInfo::Default);
    let ty = kernel.pi(alpha_name, sort_u, with_a, BinderInfo::Default);

    // `fun (alpha : Sort u) (a b : alpha) => Not (Eq.{u} alpha a b)`.
    let alpha_bvar = kernel.bvar(2);
    let a_bvar = kernel.bvar(1);
    let b_bvar = kernel.bvar(0);
    let eq_c = kernel.const_(logic.eq, vec![u_level]);
    let eq_c = kernel.app(eq_c, alpha_bvar);
    let eq_c = kernel.app(eq_c, a_bvar);
    let eq_c = kernel.app(eq_c, b_bvar);
    let not_c = kernel.const_(logic.not, vec![]);
    let body = kernel.app(not_c, eq_c);
    let with_b = kernel.lam(b_name, b_ty, body, BinderInfo::Default);
    let with_a = kernel.lam(a_name, a_ty, with_b, BinderInfo::Default);
    let value = kernel.lam(alpha_name, sort_u, with_a, BinderInfo::Default);

    kernel
        .add_declaration(Declaration::Definition {
            name: ne_name,
            uparams: vec![u_name],
            ty,
            value,
            hint: ReducibilityHint::Regular(2),
        })
        .expect("the test fixture's own Ne definition must typecheck");
    ne_name
}

/// `@Ne Nat a b`, instantiating [`declare_ne`]'s universe parameter at
/// `Sort 1` (`Nat`'s own sort).
fn ne_app(kernel: &mut Kernel, ne_name: NameId, nat_ty: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let applied = kernel.const_(ne_name, vec![one]);
    let applied = kernel.app(applied, nat_ty);
    let applied = kernel.app(applied, a);
    kernel.app(applied, b)
}

/// A minimal synthetic stand-in for real Lean4's `LE.le : {α : Type} →
/// [LE α] → α → α → Prop` typeclass method, monomorphic at `Nat` and
/// ignoring its type/instance arguments (`fun ty inst a b => Nat.le a b`).
/// `NatPrelude` has no real `LE` class machinery to import a genuine one
/// from, so this exists purely to exercise the widened producer's
/// **typeclass-form** recognition (`nat_relation_args`'s 4-arg branch) end
/// to end — the 2-arg direct `Nat.le` form is already covered by
/// `NatPrelude::le` itself, but the 4-arg branch is what a real Mathlib `≤`
/// goal actually wire-encodes as, and it needs its own coverage.
fn declare_le_typeclass(kernel: &mut Kernel, nat: NameId, nat_le: NameId) -> NameId {
    let root = kernel.anon();
    let le_name = kernel.name_str(root, "LE.le");
    let ty_name = kernel.name_str(root, "ty");
    let inst_name = kernel.name_str(root, "inst");
    let a_name = kernel.name_str(root, "a");
    let b_name = kernel.name_str(root, "b");

    let zero_level = kernel.level_zero();
    let one_level = kernel.level_succ(zero_level);
    let type_sort = kernel.sort(one_level);
    let prop = kernel.sort_zero();
    let nat_ty = kernel.const_(nat, vec![]); // closed: safe to reuse at any depth

    let pi_b = kernel.pi(b_name, nat_ty, prop, BinderInfo::Default);
    let pi_a = kernel.pi(a_name, nat_ty, pi_b, BinderInfo::Default);
    let pi_inst = kernel.pi(inst_name, nat_ty, pi_a, BinderInfo::Default);
    let ty = kernel.pi(ty_name, type_sort, pi_inst, BinderInfo::Default);

    let a_bvar = kernel.bvar(1);
    let b_bvar = kernel.bvar(0);
    let le_c = kernel.const_(nat_le, vec![]);
    let le_c = kernel.app(le_c, a_bvar);
    let body = kernel.app(le_c, b_bvar);
    let with_b = kernel.lam(b_name, nat_ty, body, BinderInfo::Default);
    let with_a = kernel.lam(a_name, nat_ty, with_b, BinderInfo::Default);
    let with_inst = kernel.lam(inst_name, nat_ty, with_a, BinderInfo::Default);
    let value = kernel.lam(ty_name, type_sort, with_inst, BinderInfo::Default);

    kernel
        .add_declaration(Declaration::Definition {
            name: le_name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
        .expect("the test fixture's own LE.le stand-in must typecheck");
    le_name
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
fn declines_an_unsupported_terminal_head() {
    // `∀ p, Iff p p` -- constant-headed, well-formed, even true, but `Iff` is
    // not one of this producer's five supported heads. This is the shape of
    // the repository's primary must-decline guard
    // (`F:ml430-mutation-1432b2277cf2cc26c1d11cd6`, a boundary-widened
    // `Nat.fib n = 0 ↔ n = 0 ∨ n = 1`): an `Iff` terminal goal must never be
    // routed to `Eq`'s or any other route by mistake, admitted or not.
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let prop = kernel.sort_zero();
    let variable = kernel.bvar(0);
    let body = binary_app(&mut kernel, logic.iff, variable, variable);
    let binder = candidate_name(&mut kernel, "p");
    let goal = kernel.pi(binder, prop, body, BinderInfo::Default);

    let error = support::propose_reflexivity(&mut kernel, goal)
        .expect_err("Iff must never be dispatched to any supported route");
    assert!(
        error.contains("is not a supported reflexivity target"),
        "{error}"
    );
    assert!(error.contains("\"Iff\""), "{error}");
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

// --- Nat.le -----------------------------------------------------------------

#[test]
fn le_admits_a_definitionally_reflexive_goal() {
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let nat_ty = kernel.const_(p.nat, vec![]);
    let n = kernel.bvar(0);
    let body = binary_app(&mut kernel, p.le, n, n); // Nat.le n n
    let n_name = candidate_name(&mut kernel, "n");
    let goal = kernel.pi(n_name, nat_ty, body, BinderInfo::Default);

    let candidate = support::propose_reflexivity(&mut kernel, goal)
        .expect("n <= n must be admitted by the Nat.le route");
    let name = candidate_name(&mut kernel, "le_refl_accepted");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: goal,
            value: candidate.proof,
        })
        .expect("independent kernel must accept the Nat.le.refl term");
    assert!(kernel.axiom_footprint(name).is_empty());
    assert!(kernel.theorem_dependencies(name).is_empty());
}

#[test]
fn le_declines_a_false_successor_goal() {
    // `∀ n, succ n <= n` -- false for every n.
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let nat_ty = kernel.const_(p.nat, vec![]);
    let n = kernel.bvar(0);
    let succ_n = unary_app(&mut kernel, p.succ, n);
    let body = binary_app(&mut kernel, p.le, succ_n, n);
    let n_name = candidate_name(&mut kernel, "n");
    let goal = kernel.pi(n_name, nat_ty, body, BinderInfo::Default);

    // The route is blind to truth: it proposes a candidate on shape alone,
    // and only the independent kernel's own type check catches the lie.
    let candidate = support::propose_reflexivity(&mut kernel, goal)
        .expect("the untrusted Nat.le route may still emit a candidate here");
    let name = candidate_name(&mut kernel, "le_refl_rejected");
    let result = kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: goal,
        value: candidate.proof,
    });
    assert!(result.is_err(), "the kernel must reject succ n <= n");
    assert!(!kernel.environment().contains(name));
}

#[test]
fn le_admits_a_reflexive_goal_via_the_typeclass_form() {
    // `∀ n, LE.le Nat 0 n n` -- the real 4-arg typeclass-method shape a
    // genuine Mathlib `≤` goal wire-encodes as (`nat_relation_args`'s second
    // branch), as opposed to `NatPrelude::le`'s own raw 2-arg form.
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let le_tc_name = declare_le_typeclass(&mut kernel, p.nat, p.le);
    let nat_ty = kernel.const_(p.nat, vec![]);
    let inst_dummy = kernel.const_(p.zero, vec![]);
    let n = kernel.bvar(0);
    let applied = kernel.const_(le_tc_name, vec![]);
    let applied = kernel.app(applied, nat_ty);
    let applied = kernel.app(applied, inst_dummy);
    let applied = kernel.app(applied, n);
    let body = kernel.app(applied, n);
    let n_name = candidate_name(&mut kernel, "n");
    let goal = kernel.pi(n_name, nat_ty, body, BinderInfo::Default);

    let candidate = support::propose_reflexivity(&mut kernel, goal)
        .expect("the 4-arg typeclass form of n <= n must also be admitted");
    let name = candidate_name(&mut kernel, "le_typeclass_accepted");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: goal,
            value: candidate.proof,
        })
        .expect("independent kernel must accept the Nat.le.refl term");
    assert!(kernel.axiom_footprint(name).is_empty());
    assert!(kernel.theorem_dependencies(name).is_empty());
}

#[test]
fn le_declines_a_typeclass_application_over_a_non_nat_type() {
    // `∀ n, LE.le False 0 n n` -- same 4-arg shape, but the type argument is
    // not `Nat`, which must be refused before any construction is attempted
    // (this producer only ever reasons about `Nat`).
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let le_tc_name = declare_le_typeclass(&mut kernel, p.nat, p.le);
    let nat_ty = kernel.const_(p.nat, vec![]);
    let not_nat_ty = kernel.const_(p.logic.false_, vec![]);
    let inst_dummy = kernel.const_(p.zero, vec![]);
    let n = kernel.bvar(0);
    let applied = kernel.const_(le_tc_name, vec![]);
    let applied = kernel.app(applied, not_nat_ty);
    let applied = kernel.app(applied, inst_dummy);
    let applied = kernel.app(applied, n);
    let body = kernel.app(applied, n);
    let n_name = candidate_name(&mut kernel, "n");
    let goal = kernel.pi(n_name, nat_ty, body, BinderInfo::Default);

    let error = support::propose_reflexivity(&mut kernel, goal)
        .expect_err("a typeclass LE.le application over a non-Nat type must be declined");
    assert!(error.contains("not an exact Nat.le application"), "{error}");
}

#[test]
fn le_declines_a_malformed_three_argument_application_without_panicking() {
    // `∀ n, Nat.le Nat n n` -- `Nat.le` (the direct 2-arg name) applied to
    // THREE arguments, the first of which happens to be `Nat` itself. This
    // matches neither the direct 2-arg shape nor the 4-arg typeclass shape,
    // and must be declined cleanly rather than indexing past the end of a
    // 3-element argument list (a malformed or truncated archive record must
    // never crash the producer).
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let nat_ty = kernel.const_(p.nat, vec![]);
    let n = kernel.bvar(0);
    let applied = kernel.const_(p.le, vec![]);
    let applied = kernel.app(applied, nat_ty);
    let applied = kernel.app(applied, n);
    let body = kernel.app(applied, n);
    let n_name = candidate_name(&mut kernel, "n");
    let goal = kernel.pi(n_name, nat_ty, body, BinderInfo::Default);

    let error = support::propose_reflexivity(&mut kernel, goal)
        .expect_err("a malformed 3-argument Nat.le application must be declined, not panic");
    assert!(error.contains("not an exact Nat.le application"), "{error}");
}

// --- Nat.lt -----------------------------------------------------------------

#[test]
fn lt_admits_a_definitionally_successor_goal() {
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let nat_ty = kernel.const_(p.nat, vec![]);
    let n = kernel.bvar(0);
    let succ_n = unary_app(&mut kernel, p.succ, n);
    let body = binary_app(&mut kernel, p.lt, n, succ_n); // Nat.lt n (succ n)
    let n_name = candidate_name(&mut kernel, "n");
    let goal = kernel.pi(n_name, nat_ty, body, BinderInfo::Default);

    let candidate = support::propose_reflexivity(&mut kernel, goal)
        .expect("n < succ n must be admitted by the Nat.lt route");
    let name = candidate_name(&mut kernel, "lt_succ_accepted");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: goal,
            value: candidate.proof,
        })
        .expect("independent kernel must accept the Nat.le.refl (succ n) term");
    assert!(kernel.axiom_footprint(name).is_empty());
    assert!(kernel.theorem_dependencies(name).is_empty());
}

#[test]
fn lt_declines_a_false_goal() {
    // `∀ n, succ n < n` -- false for every n.
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let nat_ty = kernel.const_(p.nat, vec![]);
    let n = kernel.bvar(0);
    let succ_n = unary_app(&mut kernel, p.succ, n);
    let body = binary_app(&mut kernel, p.lt, succ_n, n);
    let n_name = candidate_name(&mut kernel, "n");
    let goal = kernel.pi(n_name, nat_ty, body, BinderInfo::Default);

    let candidate = support::propose_reflexivity(&mut kernel, goal)
        .expect("the untrusted Nat.lt route may still emit a candidate here");
    let name = candidate_name(&mut kernel, "lt_rejected");
    let result = kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: goal,
        value: candidate.proof,
    });
    assert!(result.is_err(), "the kernel must reject succ n < n");
    assert!(!kernel.environment().contains(name));
}

// --- Ne -----------------------------------------------------------------

#[test]
fn ne_admits_a_constructor_mismatch() {
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let ne_name = declare_ne(&mut kernel, &p.logic);
    let nat_ty = kernel.const_(p.nat, vec![]);
    let n = kernel.bvar(0);
    let succ_n = unary_app(&mut kernel, p.succ, n);
    let zero = kernel.const_(p.zero, vec![]);
    let body = ne_app(&mut kernel, ne_name, nat_ty, succ_n, zero); // succ n != 0
    let binder_n = candidate_name(&mut kernel, "n");
    let goal = kernel.pi(binder_n, nat_ty, body, BinderInfo::Default);

    let candidate = support::propose_reflexivity(&mut kernel, goal)
        .expect("succ n != 0 must be admitted by the Ne/noConfusion route");
    let name = candidate_name(&mut kernel, "ne_accepted");
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: goal,
            value: candidate.proof,
        })
        .expect("independent kernel must accept the noConfusion-based Ne term");
    assert!(kernel.axiom_footprint(name).is_empty());
    assert!(kernel.theorem_dependencies(name).is_empty());
}

#[test]
fn ne_declines_a_reflexive_false_goal() {
    // `∀ n, n != n` -- false for every n, and neither side is even
    // constructor-headed (both are the bare bound variable), so this must be
    // declined by the cheap structural guard, never reach `noConfusion`.
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let ne_name = declare_ne(&mut kernel, &p.logic);
    let nat_ty = kernel.const_(p.nat, vec![]);
    let n = kernel.bvar(0);
    let body = ne_app(&mut kernel, ne_name, nat_ty, n, n);
    let binder_n = candidate_name(&mut kernel, "n");
    let goal = kernel.pi(binder_n, nat_ty, body, BinderInfo::Default);

    let error = support::propose_reflexivity(&mut kernel, goal)
        .expect_err("n != n has no constructor mismatch and must be declined before construction");
    assert!(
        error.contains("not a recognized Nat.zero/Nat.succ constructor mismatch"),
        "{error}"
    );
}

#[test]
fn ne_declines_a_same_constructor_false_goal() {
    // `∀ n, succ n != succ n` -- false, and both sides ARE constructor-headed,
    // but by the *same* constructor, which must not be treated as a mismatch.
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let ne_name = declare_ne(&mut kernel, &p.logic);
    let nat_ty = kernel.const_(p.nat, vec![]);
    let n = kernel.bvar(0);
    let succ_n = unary_app(&mut kernel, p.succ, n);
    let body = ne_app(&mut kernel, ne_name, nat_ty, succ_n, succ_n);
    let binder_n = candidate_name(&mut kernel, "n");
    let goal = kernel.pi(binder_n, nat_ty, body, BinderInfo::Default);

    let error = support::propose_reflexivity(&mut kernel, goal).expect_err(
        "succ n != succ n is a same-constructor pair, not a mismatch, and must be declined",
    );
    assert!(
        error.contains("not a recognized Nat.zero/Nat.succ constructor mismatch"),
        "{error}"
    );
}

#[test]
fn ne_declines_a_non_nat_typed_application() {
    // `∀ n, @Ne False (succ n) 0` -- `a`/`b` LOOK Nat-constructor-mismatched
    // (so a buggy route that skipped the type check would still reach and
    // pass the mismatch guard), but the `Ne` application's own type argument
    // is `False`, not `Nat`, which this route must refuse before ever
    // reaching `noConfusion`.
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let ne_name = declare_ne(&mut kernel, &p.logic);
    let nat_ty = kernel.const_(p.nat, vec![]);
    let not_nat_ty = kernel.const_(p.logic.false_, vec![]);
    let n = kernel.bvar(0);
    let succ_n = unary_app(&mut kernel, p.succ, n);
    let zero = kernel.const_(p.zero, vec![]);
    let body = ne_app(&mut kernel, ne_name, not_nat_ty, succ_n, zero);
    let binder_n = candidate_name(&mut kernel, "n");
    let goal = kernel.pi(binder_n, nat_ty, body, BinderInfo::Default);

    let error = support::propose_reflexivity(&mut kernel, goal)
        .expect_err("a False-typed Ne application must be declined regardless of its sides");
    assert!(
        error.contains("Ne route requires a Nat-typed Ne application"),
        "{error}"
    );
}

#[test]
fn ne_declines_a_malformed_two_argument_application_without_panicking() {
    // `∀ n, Ne Nat n` -- `Ne` applied to only TWO arguments (a partial or
    // truncated application), which must be declined cleanly rather than
    // indexing past the end of a 2-element argument list.
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let ne_name = declare_ne(&mut kernel, &p.logic);
    let nat_ty = kernel.const_(p.nat, vec![]);
    let n = kernel.bvar(0);
    let one_level = {
        let z = kernel.level_zero();
        kernel.level_succ(z)
    };
    let applied = kernel.const_(ne_name, vec![one_level]);
    let applied = kernel.app(applied, nat_ty);
    let body = kernel.app(applied, n);
    let binder_n = candidate_name(&mut kernel, "n");
    let goal = kernel.pi(binder_n, nat_ty, body, BinderInfo::Default);

    let error = support::propose_reflexivity(&mut kernel, goal)
        .expect_err("a malformed 2-argument Ne application must be declined, not panic");
    assert!(error.contains("not an exact Ne application"), "{error}");
}

// --- Nat.dvd ------------------------------------------------------------

#[test]
fn dvd_declines_a_non_product_divisor() {
    // `∀ a n, Nat.dvd a n` -- `n` is a bare variable, not a Nat.mul
    // application, so this must be declined before any construction attempt.
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let nat_ty = kernel.const_(p.nat, vec![]);
    let a = kernel.bvar(1);
    let n = kernel.bvar(0);
    let body = binary_app(&mut kernel, p.dvd, a, n);
    let n_name = candidate_name(&mut kernel, "n");
    let inner = kernel.pi(n_name, nat_ty, body, BinderInfo::Default);
    let a_name = candidate_name(&mut kernel, "a");
    let goal = kernel.pi(a_name, nat_ty, inner, BinderInfo::Default);

    let error = support::propose_reflexivity(&mut kernel, goal).expect_err(
        "a divisor that is not a Nat.mul application must be declined before construction",
    );
    assert!(
        error.contains("not a recognized Nat.mul application"),
        "{error}"
    );
}

#[test]
fn dvd_declines_a_const_headed_non_mul_divisor() {
    // `∀ a b, Nat.dvd a (Nat.add a b)` -- the divisor IS a Const-headed,
    // 2-argument application (unlike the bare-variable case above), but the
    // operator is `Nat.add`, not `Nat.mul`. This isolates the arity/name
    // check from the "is it even an application" check above.
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let nat_ty = kernel.const_(p.nat, vec![]);
    let a = kernel.bvar(1);
    let b = kernel.bvar(0);
    let sum = binary_app(&mut kernel, p.add, a, b);
    let body = binary_app(&mut kernel, p.dvd, a, sum);
    let b_name = candidate_name(&mut kernel, "b");
    let inner = kernel.pi(b_name, nat_ty, body, BinderInfo::Default);
    let a_name = candidate_name(&mut kernel, "a");
    let goal = kernel.pi(a_name, nat_ty, inner, BinderInfo::Default);

    let error = support::propose_reflexivity(&mut kernel, goal).expect_err(
        "a Nat.add-headed divisor is not a Nat.mul application and must be declined before construction",
    );
    assert!(
        error.contains("not a recognized Nat.mul application"),
        "{error}"
    );
}

#[test]
fn dvd_declines_a_mismatched_multiplicand() {
    // `∀ a b, Nat.dvd (succ a) (Nat.mul a b)` -- product-shaped, but the
    // claimed divisor (`succ a`) does not match the product's first factor
    // (`a`). A real, satisfiable-looking shape that must still be refused.
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let nat_ty = kernel.const_(p.nat, vec![]);
    let a = kernel.bvar(1);
    let b = kernel.bvar(0);
    let succ_a = unary_app(&mut kernel, p.succ, a);
    let product = binary_app(&mut kernel, p.mul, a, b);
    let body = binary_app(&mut kernel, p.dvd, succ_a, product);
    let b_name = candidate_name(&mut kernel, "b");
    let inner = kernel.pi(b_name, nat_ty, body, BinderInfo::Default);
    let a_name = candidate_name(&mut kernel, "a");
    let goal = kernel.pi(a_name, nat_ty, inner, BinderInfo::Default);

    let error = support::propose_reflexivity(&mut kernel, goal).expect_err(
        "a divisor that does not match the product's first factor must be declined before construction",
    );
    assert!(
        error.contains("does not match the recognized product's first factor"),
        "{error}"
    );
}

#[test]
fn dvd_declines_a_correctly_shaped_goal_via_construction_budget() {
    // `∀ a b, Nat.dvd a (Nat.mul a b)` -- a real `dvd_mul_right`-shaped
    // truth, correctly recognized and multiplicand-matched by both cheap
    // pre-checks, but this producer's from-primitives `Exists` construction
    // costs more nodes than the fixed MAX_CONSTRUCTED_NODES budget allows:
    // 19 fixed nodes plus one Lam per binder, measured here at 21 for this
    // goal's two binders, already past 16 with zero binders. This documents
    // that as a real, honest property of the current budget rather than an
    // unimplemented case: the two guards above are exercised on their own.
    let mut kernel = Kernel::new();
    let p = build_nat_prelude(&mut kernel).expect("nat prelude builds");
    let nat_ty = kernel.const_(p.nat, vec![]);
    let a = kernel.bvar(1);
    let b = kernel.bvar(0);
    let product = binary_app(&mut kernel, p.mul, a, b);
    let body = binary_app(&mut kernel, p.dvd, a, product);
    let b_name = candidate_name(&mut kernel, "b");
    let inner = kernel.pi(b_name, nat_ty, body, BinderInfo::Default);
    let a_name = candidate_name(&mut kernel, "a");
    let goal = kernel.pi(a_name, nat_ty, inner, BinderInfo::Default);

    let error = support::propose_reflexivity(&mut kernel, goal).expect_err(
        "a correctly-shaped Dvd goal must still decline via the fixed construction budget",
    );
    // 19 fixed nodes (the Exists.intro spine, the motive's own Eq
    // application, and the rebuilt `a * q`) plus one Lam per binder (2 here).
    assert_eq!(error, "construction budget exceeded: 21 > 16");
}
