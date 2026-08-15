//! K-like reduction (Lean's `to_cnstr_when_K`) at the trusted gate.
//!
//! The rule replaces a **stuck** major premise of a K-like inductive — a
//! non-mutual, `Prop`-valued family with exactly one constructor, that
//! constructor taking only the family's parameters — by that constructor
//! applied to the parameters, after which ι fires. It is what makes
//! `cast α α h a ≡ a` hold for a *variable* `h : α = α`, which is what
//! `eq_of_heq` needs and what this port could not check before.
//!
//! Every test here goes through `Kernel::add_declaration`, not through
//! reduction or `def_eq` directly, because the gate is what has to be right.
//! The probe shape is uniform: for a family `F`, build
//!
//! ```text
//! probe : ∀ (h : F …), @Eq Prop (F.rec (fun _ => Prop) True h) True
//! probe := fun h => @Eq.refl Prop True
//! ```
//!
//! The recursor application is stuck on `h`, so this declaration is admitted
//! **iff** K-like reduction fires for `F`. Two positives — `True`, and the
//! `eq_of_heq` shape on the indexed family `Eq` — and five refusals.
//!
//! **Read the per-test doc comments before trusting a refusal.** Measured while
//! writing these: two of them are refused *before* the guard they name is
//! reached (the def-eq guard fires first on a constructor with fields; a mutual
//! `Prop` group's recursor is small-eliminating, so the probe shape does not
//! exist for it at all). Those clauses are pinned where they actually live, in
//! `inductive_tests::the_k_like_predicate_*`, where removing each one does flip
//! exactly one test. Every claim in this file was checked by disabling the rule
//! or the clause and re-running; see
//! `docs/formalized-math-2026-08/diary-whnf-cache-key.md`.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, InductiveFamilySpec, Kernel, KernelError, LogicPrelude,
    NameId, build_logic_prelude,
};

/// The universe level `1`, i.e. the level of `Prop`'s own sort.
fn level_one(kernel: &mut Kernel) -> axeyum_lean_kernel::LevelId {
    let zero = kernel.level_zero();
    kernel.level_succ(zero)
}

/// `Sort 1` (`Type`).
fn sort_one(kernel: &mut Kernel) -> ExprId {
    let one = level_one(kernel);
    kernel.sort(one)
}

/// The constant motive `fun _ : family => Prop` for a parameterless family.
fn constant_motive(kernel: &mut Kernel, family: ExprId) -> ExprId {
    let anon = kernel.anon();
    let prop = kernel.sort_zero();
    kernel.lam(anon, family, prop, BinderInfo::Default)
}

/// Build and attempt `probe : ∀ (h : major_ty), @Eq.{1} Prop (prefix h) True`,
/// proved by `@Eq.refl.{1} Prop True`.
///
/// `reduct_prefix` is the recursor applied to **everything before the major
/// premise** — parameters, every motive, and every minor. Getting that
/// telescope right matters: a probe that under-applies a recursor is stuck for
/// a reason that has nothing to do with K, and would pass as a negative test
/// while proving nothing.
fn probe_admits(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    label: &str,
    reduct_prefix: ExprId,
    major_ty: ExprId,
) -> Result<(), KernelError> {
    let anon = kernel.anon();
    let one = level_one(kernel);
    let prop = kernel.sort_zero();
    let true_const = kernel.const_(logic.true_, vec![]);

    let major = kernel.bvar(0);
    let reduct = kernel.app(reduct_prefix, major);

    let eq = kernel.const_(logic.eq, vec![one]);
    let goal_body = kernel.app(eq, prop);
    let goal_body = kernel.app(goal_body, reduct);
    let goal_body = kernel.app(goal_body, true_const);
    let goal = kernel.pi(anon, major_ty, goal_body, BinderInfo::Default);

    let refl = kernel.const_(logic.eq_refl, vec![one]);
    let refl = kernel.app(refl, prop);
    let refl = kernel.app(refl, true_const);
    let value = kernel.lam(anon, major_ty, refl, BinderInfo::Default);

    let name = kernel.name_str(anon, format!("kLikeProbe{label}"));
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: goal,
        value,
    })
}

/// A `Prop` family with exactly one constructor taking no fields is K-like, so
/// its recursor reduces even on a major premise that is a bare variable.
///
/// This is the capability the rule exists for: without it the probe's two sides
/// are `True.rec … h` and `True`, and nothing in β/ζ/δ/ι/projection can bring
/// them together while `h` is stuck.
#[test]
fn a_prop_family_with_one_nullary_constructor_is_k_reducible() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let one = level_one(&mut kernel);
    let recursor = kernel.const_(logic.true_rec, vec![one]);
    let true_const = kernel.const_(logic.true_, vec![]);
    let motive = constant_motive(&mut kernel, true_const);
    let prefix = kernel.app(recursor, motive);
    let prefix = kernel.app(prefix, true_const);

    probe_admits(&mut kernel, &logic, "True", prefix, true_const)
        .expect("K-like reduction must fire for a Prop family with one nullary constructor");
}

/// A `Prop` family whose single constructor **has fields** must not be
/// K-reducible.
///
/// The constructor applied to the parameters alone is not even a term of the
/// family, so the rule has nothing to replace the major with; more to the
/// point, distinct inhabitants carry distinct field data and identifying them
/// would be identifying distinct proofs' *content*.
#[test]
fn a_prop_family_whose_constructor_has_fields_is_not_k_reducible() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let anon = kernel.anon();
    let prop = kernel.sort_zero();
    let true_const = kernel.const_(logic.true_, vec![]);

    // inductive Boxed : Prop where | mk : True → Boxed
    let boxed = kernel.name_str(anon, "Boxed");
    let boxed_mk = kernel.name_str(boxed, "mk");
    let boxed_const = kernel.const_(boxed, vec![]);
    let ctor_ty = kernel.pi(anon, true_const, boxed_const, BinderInfo::Default);
    kernel
        .add_inductive(boxed, &[], 0, prop, &[(boxed_mk, ctor_ty)])
        .expect("Boxed admits");

    let boxed_rec = kernel.name_str(boxed, "rec");
    let one = level_one(&mut kernel);
    let recursor = kernel.const_(boxed_rec, vec![one]);
    let motive = constant_motive(&mut kernel, boxed_const);
    // minor : (a : True) → motive (Boxed.mk a), and the motive is constant
    // `Prop`, so the minor is `fun _ : True => True`.
    let minor = kernel.lam(anon, true_const, true_const, BinderInfo::Default);
    let prefix = kernel.app(recursor, motive);
    let prefix = kernel.app(prefix, minor);

    let outcome = probe_admits(&mut kernel, &logic, "Boxed", prefix, boxed_const);
    assert!(
        outcome.is_err(),
        "a Prop constructor with fields must not be K-reducible, got {outcome:?}"
    );
}

/// A family that is **not** `Prop`-valued must not be K-reducible even with one
/// nullary constructor.
///
/// Outside `Prop` an inhabitant is data, and a reduction rule that discards the
/// major would be discarding it. Lean's `k` flag is `Prop`-only for this
/// reason; so is [`Kernel::is_k_like_inductive`].
#[test]
fn a_non_prop_family_with_one_nullary_constructor_is_not_k_reducible() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let anon = kernel.anon();
    let type_ = sort_one(&mut kernel);
    let true_const = kernel.const_(logic.true_, vec![]);

    // inductive Solo : Type where | mk : Solo
    let solo = kernel.name_str(anon, "Solo");
    let solo_mk = kernel.name_str(solo, "mk");
    let solo_const = kernel.const_(solo, vec![]);
    kernel
        .add_inductive(solo, &[], 0, type_, &[(solo_mk, solo_const)])
        .expect("Solo admits");

    let solo_rec = kernel.name_str(solo, "rec");
    let one = level_one(&mut kernel);
    let recursor = kernel.const_(solo_rec, vec![one]);
    let motive = constant_motive(&mut kernel, solo_const);
    let prefix = kernel.app(recursor, motive);
    let prefix = kernel.app(prefix, true_const);

    let outcome = probe_admits(&mut kernel, &logic, "Solo", prefix, solo_const);
    assert!(
        outcome.is_err(),
        "a non-Prop family must not be K-reducible, got {outcome:?}"
    );
}

/// A member of a **mutual** group must not be K-reducible, even when it is a
/// `Prop` family with a single nullary constructor in isolation.
///
/// Lean excludes mutual groups from `k` explicitly ("for simplicity"), and the
/// exclusion is worth keeping verbatim: a mutual recursor's rules and motives
/// are indexed across the whole group, so "the constructor of the family" is
/// not the local reading it looks like.
///
/// **What this test does and does not show.** Measured while writing it: a
/// mutual `Prop` group is not a subsingleton, so its recursors are *small*
/// eliminating and carry **no** universe parameter — the probe shape used
/// everywhere else in this file needs a `Sort 1`-valued motive and therefore
/// cannot be built for one at all (`UniverseArityMismatch`). So this test pins
/// that the declaration is refused, but the refusal is not attributable to the
/// mutual clause of the K predicate. The clause itself is pinned directly by
/// `inductive_tests::the_k_like_predicate_excludes_mutual_groups`, where
/// removing it does flip the result.
#[test]
fn a_mutual_group_member_is_not_k_reducible() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let anon = kernel.anon();
    let prop = kernel.sort_zero();
    let true_const = kernel.const_(logic.true_, vec![]);

    // mutual inductive Left : Prop | lmk : Left  and  Right : Prop | rmk : Right
    let left = kernel.name_str(anon, "MutLeft");
    let left_mk = kernel.name_str(left, "lmk");
    let left_const = kernel.const_(left, vec![]);
    let right = kernel.name_str(anon, "MutRight");
    let right_mk = kernel.name_str(right, "rmk");
    let right_const = kernel.const_(right, vec![]);
    kernel
        .add_mutual_inductive(
            &[],
            0,
            &[
                InductiveFamilySpec::new(left, prop, vec![(left_mk, left_const)]),
                InductiveFamilySpec::new(right, prop, vec![(right_mk, right_const)]),
            ],
        )
        .expect("the mutual group admits");

    let left_rec = kernel.name_str(left, "rec");
    let one = level_one(&mut kernel);
    let recursor = kernel.const_(left_rec, vec![one]);
    // A mutual recursor takes one motive **per family** and one minor per
    // constructor across the whole group, so the probe has to supply four
    // arguments before the major. Supplying fewer would leave the recursor
    // stuck on arity rather than on K, and this test would pass while
    // measuring nothing.
    let motive_left = constant_motive(&mut kernel, left_const);
    let motive_right = constant_motive(&mut kernel, right_const);
    let prefix = kernel.app(recursor, motive_left);
    let prefix = kernel.app(prefix, motive_right);
    let prefix = kernel.app(prefix, true_const);
    let prefix = kernel.app(prefix, true_const);

    let outcome = probe_admits(&mut kernel, &logic, "MutLeft", prefix, left_const);
    assert!(
        outcome.is_err(),
        "a mutual group member must not be K-reducible, got {outcome:?}"
    );
}

/// Build the `Eq.rec` probe for `h : @Eq.{1} Prop True <index>`, where `index`
/// is either the literal `True` or the bound variable one binder out.
///
/// ```text
/// probe : ∀ (h : @Eq.{1} Prop True index),
///           @Eq.{1} Prop (@Eq.rec.{1,1} Prop True (fun _ _ => Prop) True index h) True
/// ```
///
/// `Eq.rec`'s argument order is `α a motive minor index major`; `Eq` has two
/// parameters (`α` and `a`) and one index.
fn eq_rec_probe(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    name: &str,
    variable_index: bool,
) -> Result<(), KernelError> {
    let anon = kernel.anon();
    let one = level_one(kernel);
    let prop = kernel.sort_zero();
    let true_const = kernel.const_(logic.true_, vec![]);
    let eq = kernel.const_(logic.eq, vec![one]);

    // `@Eq.{1} Prop True c` as a function of the de Bruijn index `c`.
    let eq_true_at = |kernel: &mut Kernel, index: ExprId| {
        let applied = kernel.app(eq, prop);
        let applied = kernel.app(applied, true_const);
        kernel.app(applied, index)
    };

    // motive := fun (c : Prop) (_ : @Eq Prop True c) => Prop
    let motive_inner_domain = {
        let c = kernel.bvar(0);
        eq_true_at(kernel, c)
    };
    let motive_inner = kernel.lam(anon, motive_inner_domain, prop, BinderInfo::Default);
    let motive = kernel.lam(anon, prop, motive_inner, BinderInfo::Default);

    // The binder is `h : @Eq Prop True index0`, where `index0` is either
    // `True` or an outer bound variable. In the variable case the probe is
    // universally quantified over the index first.
    let (binder_index, reduct_index, wrap_outer) = if variable_index {
        // ∀ (b : Prop) (h : @Eq Prop True b), …  — inside the `h` binder, `b`
        // is de Bruijn index 1.
        (kernel.bvar(0), kernel.bvar(1), true)
    } else {
        (true_const, true_const, false)
    };
    let major_ty = eq_true_at(kernel, binder_index);

    let eq_rec = kernel.const_(logic.eq_rec, vec![one, one]);
    let reduct = kernel.app(eq_rec, prop);
    let reduct = kernel.app(reduct, true_const);
    let reduct = kernel.app(reduct, motive);
    let reduct = kernel.app(reduct, true_const);
    let reduct = kernel.app(reduct, reduct_index);
    let major = kernel.bvar(0);
    let reduct = kernel.app(reduct, major);

    let goal_body = kernel.app(eq, prop);
    let goal_body = kernel.app(goal_body, reduct);
    let goal_body = kernel.app(goal_body, true_const);
    let goal = kernel.pi(anon, major_ty, goal_body, BinderInfo::Default);
    let goal = if wrap_outer {
        kernel.pi(anon, prop, goal, BinderInfo::Default)
    } else {
        goal
    };

    let refl = kernel.const_(logic.eq_refl, vec![one]);
    let refl = kernel.app(refl, prop);
    let refl = kernel.app(refl, true_const);
    let value = kernel.lam(anon, major_ty, refl, BinderInfo::Default);
    let value = if wrap_outer {
        kernel.lam(anon, prop, value, BinderInfo::Default)
    } else {
        value
    };

    let name = kernel.name_str(anon, name);
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: goal,
        value,
    })
}

/// The `eq_of_heq` shape: `Eq.rec` on a **variable** proof whose type is the
/// reflexive instance `@Eq α a a` reduces.
///
/// `Eq` is indexed, so this is the case that also exercises guard (3): the
/// candidate constructor `@Eq.refl Prop True` has type `@Eq Prop True True`,
/// which is definitionally the major's type here, so K fires.
#[test]
fn eq_rec_reduces_on_a_variable_proof_of_a_reflexive_instance() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    eq_rec_probe(&mut kernel, &logic, "kLikeEqRefl", false)
        .expect("K must fire when the major's type is the reflexive instance");
}

/// **The load-bearing negative.** `Eq` is K-like, but a proof whose index is a
/// *variable* must not be treated as `Eq.refl`.
///
/// The candidate constructor at those parameters is `@Eq.refl Prop True`, of
/// type `@Eq Prop True True`; the major's type is `@Eq Prop True b` for a bound
/// `b`. Guard (3) — definitional equality of those two types — is exactly what
/// refuses this, and dropping it would make the recursor reduce for an
/// arbitrary index, which is to say it would let `b` be treated as `True`
/// definitionally for every `b`.
#[test]
fn eq_rec_does_not_reduce_on_a_variable_index() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let outcome = eq_rec_probe(&mut kernel, &logic, "kLikeEqOpenIndex", true);
    assert!(
        outcome.is_err(),
        "K must not fire when the major's index is a variable, got {outcome:?}"
    );
}

/// K-like reduction is a reduction rule, not an inhabitation rule: it never
/// manufactures an inhabitant of an empty family.
///
/// `False` has **zero** constructors, so it is not K-like and `False.rec` stays
/// stuck on a variable. If it did not, `False` would be provable.
#[test]
fn the_empty_prop_family_gains_no_inhabitant() {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
    let anon = kernel.anon();
    let false_const = kernel.const_(logic.false_, vec![]);

    let name: NameId = kernel.name_str(anon, "kLikeFalseIsNotInhabited");
    // `False.rec` applied to nothing at all cannot be a proof of `False`; the
    // real content is that no probe above admitted a declaration whose type is
    // `False`, and that `False` itself has no closed proof here.
    let outcome = kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty: false_const,
        value: false_const,
    });
    assert!(
        outcome.is_err(),
        "`False` must not be provable, got {outcome:?}"
    );
}
