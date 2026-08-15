//! Gate for `Proj`/`Proj` congruence in definitional equality — the rule that
//! makes `a.i ≡ b.i` follow from `a ≡ b` when neither projection can reduce.
//!
//! WHY THE RULE EXISTS. `Kernel::reduce_projection` fires only when the
//! projected value WHNFs to a constructor application. Lean's compiler emits
//! structural recursion as `brecOn`, and `brecOn` is a projection out of a
//! recursor application, so on a *variable* argument both sides of a `rfl`-proved
//! equation are projections stuck on a neutral term. Without this congruence
//! `Kernel::def_eq_app` sees two bare `Proj` nodes with empty spines and answers
//! `false`, and every `rfl` equation of a structurally recursive Lean function is
//! rejected. Measured on official `lean4export` streams before the rule:
//! `Nat.add_succ`, `Nat.mul_succ`, `Nat.pow_succ`, `List.append_assoc`,
//! `Nat.succ_sub_succ_eq_sub` and the `._f` bodies behind `Nat.zero_add`,
//! `Nat.succ_add` and `Nat.add_assoc` all declined; after it, all admit.
//!
//! WHY IT IS SOUND, AND WHAT THESE TESTS PIN. It is plain congruence for a term
//! former, so it cannot identify terms that are not already equal — *provided*
//! the field index is part of the comparison. That proviso is the whole risk
//! surface, and it is what the negative tests below attack: different field,
//! different projected value, and a projection whose recorded structure name is
//! wrong. Each must still be refused, at `Kernel::add_declaration` and not only
//! at `Kernel::def_eq`, because the declaration gate is the trusted boundary.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, KernelError, NameId, ReducibilityHint,
};

/// A fixture with one two-field structure, two opaque inhabitants, an identity
/// definition that keeps a projected value from being syntactically equal, and a
/// type family indexed by the carrier so that a wrong projection is a *type*
/// error the declaration gate must catch.
struct Fixture {
    /// `Wrap`, a one-constructor structure with two `A`-typed fields.
    wrap: NameId,
    /// `Wrap.mk`.
    wrap_mk: NameId,
    /// `p : Wrap`, opaque.
    p: ExprId,
    /// `q : Wrap`, opaque and distinct from `p`.
    q: ExprId,
    /// `alias : Wrap -> Wrap`, the identity. `alias p` is definitionally `p`
    /// but not syntactically, which is what forces the congruence path.
    alias: ExprId,
    /// `family : A -> Type`, opaque.
    family: NameId,
    /// `witness : family (Proj Wrap 0 p)`, opaque.
    witness: ExprId,
    /// A second structure, used to pin that the recorded structure name is
    /// checked by projection *inference*.
    other: NameId,
}

fn build(kernel: &mut Kernel) -> Fixture {
    let anon = kernel.anon();
    let type_sort = {
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        kernel.sort(one)
    };

    // `A : Type`
    let a_name = kernel.name_str(anon, "A");
    kernel
        .add_declaration(Declaration::Axiom {
            name: a_name,
            uparams: vec![],
            ty: type_sort,
        })
        .expect("carrier type should admit");
    let a = kernel.const_(a_name, vec![]);

    // `structure Wrap where fst : A; snd : A`
    let wrap = kernel.name_str(anon, "Wrap");
    let wrap_mk = kernel.name_str(wrap, "mk");
    let wrap_const = kernel.const_(wrap, vec![]);
    let ctor_ty = {
        let inner = kernel.pi(anon, a, wrap_const, BinderInfo::Default);
        kernel.pi(anon, a, inner, BinderInfo::Default)
    };
    kernel
        .add_inductive(wrap, &[], 0, type_sort, &[(wrap_mk, ctor_ty)])
        .expect("two-field structure should admit");

    // A second, unrelated one-field structure with the same carrier.
    let other = kernel.name_str(anon, "Other");
    let other_mk = kernel.name_str(other, "mk");
    let other_const = kernel.const_(other, vec![]);
    let other_ctor_ty = kernel.pi(anon, a, other_const, BinderInfo::Default);
    kernel
        .add_inductive(other, &[], 0, type_sort, &[(other_mk, other_ctor_ty)])
        .expect("one-field structure should admit");

    // `p q : Wrap`, opaque so that no projection out of them can reduce.
    let p_name = kernel.name_str(anon, "p");
    let q_name = kernel.name_str(anon, "q");
    for name in [p_name, q_name] {
        kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty: wrap_const,
            })
            .expect("opaque inhabitant should admit");
    }
    let p = kernel.const_(p_name, vec![]);
    let q = kernel.const_(q_name, vec![]);

    // `def alias : Wrap -> Wrap := fun x => x`
    let alias_name = kernel.name_str(anon, "alias");
    let alias_ty = kernel.pi(anon, wrap_const, wrap_const, BinderInfo::Default);
    let alias_value = {
        let body = kernel.bvar(0);
        kernel.lam(anon, wrap_const, body, BinderInfo::Default)
    };
    kernel
        .add_declaration(Declaration::Definition {
            name: alias_name,
            uparams: vec![],
            ty: alias_ty,
            value: alias_value,
            hint: ReducibilityHint::Regular(1),
        })
        .expect("identity definition should admit");
    let alias = kernel.const_(alias_name, vec![]);

    // `family : A -> Type`
    let family = kernel.name_str(anon, "family");
    let family_ty = kernel.pi(anon, a, type_sort, BinderInfo::Default);
    kernel
        .add_declaration(Declaration::Axiom {
            name: family,
            uparams: vec![],
            ty: family_ty,
        })
        .expect("type family should admit");

    // `witness : family p.0`
    let witness_name = kernel.name_str(anon, "witness");
    let witness_ty = {
        let projected = kernel.proj(wrap, 0, p);
        let head = kernel.const_(family, vec![]);
        kernel.app(head, projected)
    };
    kernel
        .add_declaration(Declaration::Axiom {
            name: witness_name,
            uparams: vec![],
            ty: witness_ty,
        })
        .expect("witness should admit");
    let witness = kernel.const_(witness_name, vec![]);

    Fixture {
        wrap,
        wrap_mk,
        p,
        q,
        alias,
        family,
        witness,
        other,
    }
}

/// `def <name> : family <projection> := witness`, through the trusted gate.
fn admit_against(
    kernel: &mut Kernel,
    fixture: &Fixture,
    name: &str,
    projection: ExprId,
) -> Result<(), KernelError> {
    let anon = kernel.anon();
    let decl_name = kernel.name_str(anon, name);
    let head = kernel.const_(fixture.family, vec![]);
    let ty = kernel.app(head, projection);
    kernel.add_declaration(Declaration::Definition {
        name: decl_name,
        uparams: vec![],
        ty,
        value: fixture.witness,
        hint: ReducibilityHint::Regular(1),
    })
}

#[test]
fn stuck_projections_of_definitionally_equal_values_are_definitionally_equal() {
    let mut kernel = Kernel::new();
    let fixture = build(&mut kernel);

    let direct = kernel.proj(fixture.wrap, 0, fixture.p);
    let through_alias = {
        let applied = kernel.app(fixture.alias, fixture.p);
        kernel.proj(fixture.wrap, 0, applied)
    };

    // Neither side reduces: `p` is opaque, so no constructor ever appears.
    let reduced = kernel.whnf(through_alias);
    assert!(
        matches!(
            kernel.expr_node(reduced),
            axeyum_lean_kernel::ExprNode::Proj(..)
        ),
        "the fixture must leave the projection stuck, or this test proves nothing"
    );

    assert!(
        kernel.def_eq(direct, through_alias),
        "p.0 and (alias p).0 must be definitionally equal by congruence"
    );
    assert!(
        admit_against(&mut kernel, &fixture, "accepts_congruent", through_alias).is_ok(),
        "the declaration gate must accept a type that differs only by this congruence"
    );
}

#[test]
fn a_different_field_index_is_still_refused() {
    let mut kernel = Kernel::new();
    let fixture = build(&mut kernel);

    let field_zero = kernel.proj(fixture.wrap, 0, fixture.p);
    let field_one = {
        let applied = kernel.app(fixture.alias, fixture.p);
        kernel.proj(fixture.wrap, 1, applied)
    };

    assert!(
        !kernel.def_eq(field_zero, field_one),
        "congruence must not cross field indices: p.0 is not p.1"
    );
    assert!(
        matches!(
            admit_against(&mut kernel, &fixture, "rejects_other_field", field_one),
            Err(KernelError::DeclarationValueMismatch { .. })
        ),
        "the trusted gate must refuse `family p.1 := (witness : family p.0)`"
    );
}

#[test]
fn a_different_projected_value_is_still_refused() {
    let mut kernel = Kernel::new();
    let fixture = build(&mut kernel);

    let from_q = {
        let applied = kernel.app(fixture.alias, fixture.q);
        kernel.proj(fixture.wrap, 0, applied)
    };

    let from_p = kernel.proj(fixture.wrap, 0, fixture.p);
    assert!(
        !kernel.def_eq(from_p, from_q),
        "congruence must not identify projections of distinct opaque values"
    );
    assert!(
        matches!(
            admit_against(&mut kernel, &fixture, "rejects_other_value", from_q),
            Err(KernelError::DeclarationValueMismatch { .. })
        ),
        "the trusted gate must refuse `family q.0 := (witness : family p.0)`"
    );
}

/// `def_eq_proj` deliberately compares only the field index, matching Lean.
/// That is safe because a projection whose recorded structure name does not
/// match the projected value's type never gets past *inference*, so it cannot
/// reach def-eq inside an admitted declaration. This pins that second gate:
/// weaken it and the name really would need comparing in `def_eq_proj`.
#[test]
fn a_projection_naming_the_wrong_structure_is_refused_by_inference() {
    let mut kernel = Kernel::new();
    let fixture = build(&mut kernel);

    let mislabelled = kernel.proj(fixture.other, 0, fixture.p);
    assert!(
        matches!(
            admit_against(
                &mut kernel,
                &fixture,
                "rejects_wrong_structure",
                mislabelled
            ),
            Err(KernelError::ProjectionTypeMismatch { .. })
        ),
        "projection inference must reject `Other.0` applied to a `Wrap`"
    );
}

/// The congruence must not resurrect a *reducible* projection with the wrong
/// answer: when the value really is a constructor application, the fields are
/// selected positionally and remain distinguishable.
#[test]
fn a_reducible_projection_still_selects_the_right_field() {
    let mut kernel = Kernel::new();
    let fixture = build(&mut kernel);
    let anon = kernel.anon();

    let a_name = kernel.name_str(anon, "A");
    let a = kernel.const_(a_name, vec![]);
    let left_name = kernel.name_str(anon, "left");
    let right_name = kernel.name_str(anon, "right");
    for name in [left_name, right_name] {
        kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty: a,
            })
            .expect("carrier inhabitant should admit");
    }
    let left = kernel.const_(left_name, vec![]);
    let right = kernel.const_(right_name, vec![]);

    let pair = {
        let head = kernel.const_(fixture.wrap_mk, vec![]);
        let partial = kernel.app(head, left);
        kernel.app(partial, right)
    };
    let first = kernel.proj(fixture.wrap, 0, pair);
    let second = kernel.proj(fixture.wrap, 1, pair);

    assert!(kernel.def_eq(first, left), "(mk left right).0 is left");
    assert!(kernel.def_eq(second, right), "(mk left right).1 is right");
    assert!(
        !kernel.def_eq(first, right),
        "the two fields must stay distinguishable"
    );
    assert!(
        !kernel.def_eq(second, left),
        "the two fields must stay distinguishable"
    );
}
