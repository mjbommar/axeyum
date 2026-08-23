//! Adversarial and positive controls for `modeq_family_support`'s
//! [`support::CircularityAudit`] and end-to-end
//! [`support::propose_modeq_family`].

#[path = "../examples/modeq_family_support/mod.rs"]
mod support;

use axeyum_lean_kernel::{BinderInfo, Declaration, Kernel, NameId, ReducibilityHint};

/// Names shared by the circularity fixtures below.
fn names(kernel: &mut Kernel) -> (NameId, NameId) {
    let root = kernel.anon();
    let target = kernel.name_str(root, "CircularityFixtureTarget");
    let candidate = kernel.name_str(root, "CircularityFixtureCandidate");
    (target, candidate)
}

/// The adversarial fixture: `target : Prop` (an assumed, otherwise
/// meaningless, axiom — a standalone value of type `Prop`, i.e. `Sort 0`),
/// then `candidate : Prop := target`, literally citing `target` by name.
/// [`support::audit_circularity`] MUST reject this — it is exactly the
/// "candidate closing the goal by citing the target" shape the brief
/// requires be mechanically caught.
#[test]
fn circularity_audit_rejects_direct_self_citation() {
    let mut kernel = Kernel::new();
    let (target, candidate) = names(&mut kernel);
    let prop = kernel.sort_zero();

    kernel
        .add_declaration(Declaration::Axiom {
            name: target,
            uparams: vec![],
            ty: prop,
        })
        .expect("axiom `target : Prop` must admit");

    let cite = kernel.const_(target, vec![]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: candidate,
            uparams: vec![],
            ty: prop,
            value: cite,
        })
        .expect("`candidate : Prop := target` typechecks (target : Prop, so this is well-typed)");

    let audit = support::audit_circularity(&kernel, candidate, target);
    assert!(
        audit.target_dependency,
        "closure of a candidate whose VALUE is literally `Const(target)` must contain target"
    );
    assert!(
        !audit.passes(),
        "a candidate that cites its own target by name must fail the circularity audit: {audit:?}"
    );
}

/// The negative control for the fixture above: a candidate of the exact same
/// shape (`Theorem : Prop`) that does **not** mention `target` at all (its
/// value is an unrelated, independently-declared axiom) must pass. Without
/// this, `target_dependency` firing on every `Theorem`-vs-`Axiom` pair
/// regardless of content would be indistinguishable from firing correctly.
#[test]
fn circularity_audit_accepts_unrelated_candidate() {
    let mut kernel = Kernel::new();
    let (target, candidate) = names(&mut kernel);
    let prop = kernel.sort_zero();

    kernel
        .add_declaration(Declaration::Axiom {
            name: target,
            uparams: vec![],
            ty: prop,
        })
        .expect("axiom `target : Prop` must admit");

    let root = kernel.anon();
    let other = kernel.name_str(root, "UnrelatedAxiom");
    kernel
        .add_declaration(Declaration::Axiom {
            name: other,
            uparams: vec![],
            ty: prop,
        })
        .expect("axiom `other : Prop` must admit");

    let cite_other = kernel.const_(other, vec![]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: candidate,
            uparams: vec![],
            ty: prop,
            value: cite_other,
        })
        .expect("`candidate : Prop := other` typechecks");

    let audit = support::audit_circularity(&kernel, candidate, target);
    assert!(
        !audit.target_dependency,
        "a candidate that never mentions target must not be flagged: {audit:?}"
    );
    // This candidate DOES reach an axiom (`other`), which a real
    // `modeq_family_support` candidate never does (see the end-to-end tests
    // below) — `passes()` is false here for a DIFFERENT, correct reason, and
    // that is exactly what distinguishes the two audit fields.
    assert_eq!(audit.axiom_footprint, 1);
    assert_eq!(audit.theorem_dependencies, 0);
}

/// Build a minimal synthetic stand-in for `Int.ModEq n a b := a % n = b % n`
/// over the real `Eq`/`Eq.rec`/`Iff` this kernel's `LogicPrelude` already
/// provides, so `propose_modeq_family` can be exercised end to end without
/// any Mathlib archive: `ModEq (n a b : Nat) : Prop := Eq Nat a b` (the
/// modulus argument is carried but unused — this schema never inspects what
/// the two sides of the unfolded `Eq` actually compute, only that they are
/// `Eq`-shaped, so a trivial "same carrier, direct equality" stand-in
/// exercises exactly the code path a real `a % n = b % n` unfolding does).
struct ModEqFixture {
    kernel: Kernel,
    nat: axeyum_lean_kernel::ExprId,
    modeq: NameId,
}

fn build_modeq_fixture() -> ModEqFixture {
    use axeyum_lean_kernel::build_nat_prelude;

    let mut kernel = Kernel::new();
    let nat_prelude = build_nat_prelude(&mut kernel).expect("nat prelude must build");
    let logic = nat_prelude.logic;
    let nat = kernel.const_(nat_prelude.nat, vec![]);

    // `ModEq (n a b : Nat) : Prop := @Eq Nat a b`
    let root = kernel.anon();
    let modeq = kernel.name_str(root, "ModEq");
    let n_name = kernel.name_str(root, "n");
    let a_name = kernel.name_str(root, "a");
    let b_name = kernel.name_str(root, "b");
    let prop = kernel.sort_zero();

    let ty_inner = kernel.pi(b_name, nat, prop, BinderInfo::Default);
    let ty_mid = kernel.pi(a_name, nat, ty_inner, BinderInfo::Default);
    let ty = kernel.pi(n_name, nat, ty_mid, BinderInfo::Default);

    let zero_level = kernel.level_zero();
    let one_level = kernel.level_succ(zero_level);
    let a_bvar = kernel.bvar(1);
    let b_bvar = kernel.bvar(0);
    let eq_c = kernel.const_(logic.eq, vec![one_level]);
    let eq_c = kernel.app(eq_c, nat);
    let eq_c = kernel.app(eq_c, a_bvar);
    let body = kernel.app(eq_c, b_bvar);
    let with_b = kernel.lam(b_name, nat, body, BinderInfo::Default);
    let with_a = kernel.lam(a_name, nat, with_b, BinderInfo::Default);
    let value = kernel.lam(n_name, nat, with_a, BinderInfo::Default);

    kernel
        .add_declaration(Declaration::Definition {
            name: modeq,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
        .expect("the fixture's own ModEq definition must typecheck");

    ModEqFixture { kernel, nat, modeq }
}

/// `ModEq n a a` applied to a literal fresh Nat parameter — the `refl` shape.
#[test]
fn end_to_end_refl_closes() {
    let ModEqFixture {
        mut kernel,
        nat,
        modeq,
    } = build_modeq_fixture();
    let root = kernel.anon();
    let n_name = kernel.name_str(root, "n");
    let a_name = kernel.name_str(root, "a");
    let a_bvar0 = kernel.bvar(0);
    let n_bvar1 = kernel.bvar(1);
    let modeq_c = kernel.const_(modeq, vec![]);
    let applied = kernel.app(modeq_c, n_bvar1);
    let applied = kernel.app(applied, a_bvar0);
    let applied = kernel.app(applied, a_bvar0);
    let goal_body = kernel.pi(a_name, nat, applied, BinderInfo::Default);
    let goal = kernel.pi(n_name, nat, goal_body, BinderInfo::Default);

    let candidate = support::propose_modeq_family(&mut kernel, goal)
        .expect("refl-shaped ModEq goal must close");
    assert_eq!(candidate.binders_used, 2, "refl only ever peels n, a");
    let root2 = kernel.anon();
    let candidate_name = kernel.name_str(root2, "ReflCandidate");
    kernel
        .add_declaration(Declaration::Theorem {
            name: candidate_name,
            uparams: vec![],
            ty: goal,
            value: candidate.proof,
        })
        .expect("the produced refl candidate must independently kernel-check");

    // A fresh, unrelated name stands in for "the target" here (this fixture
    // has no separate target declaration at all) — what matters is that the
    // candidate reaches no axiom and no other theorem.
    let unrelated = kernel.name_str(root2, "Unrelated");
    let audit = support::audit_circularity(&kernel, candidate_name, unrelated);
    assert!(
        audit.passes(),
        "a genuine refl derivation must pass the circularity audit: {audit:?}"
    );
}

/// `ModEq n a b -> ModEq n b a` — the `symm` shape.
#[test]
fn end_to_end_symm_closes() {
    let ModEqFixture {
        mut kernel,
        nat,
        modeq,
    } = build_modeq_fixture();
    let root = kernel.anon();
    let n_name = kernel.name_str(root, "n");
    let a_name = kernel.name_str(root, "a");
    let b_name = kernel.name_str(root, "b");
    let hyp_name = kernel.name_str(root, "h");

    // `modeq_nab` is `h`'s own DOMAIN type, evaluated with only `n a b` open
    // (3 binders: b=0, a=1, n=2) — `h` is not yet bound at this point.
    let n_bvar2 = kernel.bvar(2);
    let a_bvar1 = kernel.bvar(1);
    let b_bvar0 = kernel.bvar(0);
    let modeq_nab = {
        let c = kernel.const_(modeq, vec![]);
        let c = kernel.app(c, n_bvar2);
        let c = kernel.app(c, a_bvar1);
        kernel.app(c, b_bvar0)
    };
    // `modeq_nba` is the CONCLUSION, i.e. the body of the `h`-Pi we are about
    // to build — evaluated with `n a b h` all open (4 binders: h=0, b=1,
    // a=2, n=3; `h` itself unused).
    let n_bvar3 = kernel.bvar(3);
    let a_bvar2 = kernel.bvar(2);
    let b_bvar1 = kernel.bvar(1);
    let modeq_nba = {
        let c = kernel.const_(modeq, vec![]);
        let c = kernel.app(c, n_bvar3);
        let c = kernel.app(c, b_bvar1);
        kernel.app(c, a_bvar2)
    };
    let concl = kernel.pi(hyp_name, modeq_nab, modeq_nba, BinderInfo::Default);
    let with_b = kernel.pi(b_name, nat, concl, BinderInfo::Default);
    let with_a = kernel.pi(a_name, nat, with_b, BinderInfo::Default);
    let goal = kernel.pi(n_name, nat, with_a, BinderInfo::Default);

    let candidate = support::propose_modeq_family(&mut kernel, goal)
        .expect("symm-shaped ModEq goal must close");
    assert_eq!(candidate.binders_used, 4, "symm peels n, a, b, h");
    let root2 = kernel.anon();
    let candidate_name = kernel.name_str(root2, "SymmCandidate");
    kernel
        .add_declaration(Declaration::Theorem {
            name: candidate_name,
            uparams: vec![],
            ty: goal,
            value: candidate.proof,
        })
        .expect("the produced symm candidate must independently kernel-check");
    let unrelated = kernel.name_str(root2, "Unrelated");
    let audit = support::audit_circularity(&kernel, candidate_name, unrelated);
    assert!(
        audit.passes(),
        "a genuine symm derivation must pass the circularity audit: {audit:?}"
    );
}
