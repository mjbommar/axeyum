//! Tests for the dependent-pair family (ADR-1613).
//!
//! Three things are checked, and each is checked so that a broken kernel would
//! print something *different* from a working one:
//!
//! 1. **Admission.** Every name is present with the right declaration kind, and
//!    the universe guard's decision is read off the generated recursors: a
//!    large-eliminating recursor carries a fresh motive level *ahead of* the
//!    family's own universe parameters, so `Sigma.rec` has three universe
//!    parameters and `PSigma.rec` has two. That count IS the measurement of
//!    which families the kernel judged possibly-`Prop`.
//! 2. **Computation.** Every `Definition` here is evaluated at concrete, small
//!    arguments, each paired with a negative control that differs in one
//!    component — because a projection that returned the *wrong* field would
//!    still type-check.
//! 3. **Dependency.** `Sigma.snd`'s type genuinely depends on `Sigma.fst`, and
//!    `Subtype.mk`'s proof field genuinely depends on its value field. Both are
//!    demonstrated by a pair of terms differing in one leaf, one of which the
//!    kernel must ACCEPT and the other REFUSE. A test that only built the
//!    accepted one would pass against a kernel with no dependency at all.

use crate::env::Declaration;
use crate::expr::ExprId;
use crate::{BinderInfo, Kernel, LogicPrelude, build_logic_prelude};

fn built() -> (Kernel, LogicPrelude) {
    let mut kernel = Kernel::new();
    let prelude = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    (kernel, prelude)
}

fn apply_all(kernel: &mut Kernel, mut function: ExprId, arguments: &[ExprId]) -> ExprId {
    for &argument in arguments {
        function = kernel.app(function, argument);
    }
    function
}

/// `fun (_ : domain) => body`, with `body` not mentioning the binder.
fn const_lam(kernel: &mut Kernel, domain: ExprId, body: ExprId) -> ExprId {
    let anon = kernel.anon();
    kernel.lam(anon, domain, body, BinderInfo::Default)
}

/// The declaration's type, whatever term-carrying kind it is.
fn declared_type(kernel: &Kernel, name: crate::NameId, label: &str) -> ExprId {
    let decl = kernel
        .environment()
        .get(name)
        .unwrap_or_else(|| panic!("{label} must be declared"));
    match decl {
        Declaration::Theorem { ty, .. }
        | Declaration::Definition { ty, .. }
        | Declaration::Axiom { ty, .. }
        | Declaration::Opaque { ty, .. }
        | Declaration::Inductive { ty, .. }
        | Declaration::Constructor { ty, .. }
        | Declaration::Recursor { ty, .. } => *ty,
        Declaration::Quotient { .. } => panic!("{label} is not a term declaration"),
    }
}

/// `(Bool, fun _ : Bool => Bool)` — the simplest `Sigma.{0,0}` instantiation:
/// `Bool : Type 0 = Sort 1`, so `u = v = 0`.
// `LogicPrelude` is past clippy's by-value size threshold but is `Copy` and
// cheap to move; this is a size-lint override, not a real inefficiency (the
// same override `prelude_tests.rs` carries).
#[allow(clippy::large_types_passed_by_value)]
fn bool_pair_shape(kernel: &mut Kernel, p: LogicPrelude) -> (ExprId, ExprId) {
    let bool_const = kernel.const_(p.bool_, vec![]);
    let beta = const_lam(kernel, bool_const, bool_const);
    (bool_const, beta)
}

#[test]
fn the_dependent_pair_family_is_admitted_with_the_expected_kinds() {
    let (kernel, p) = built();
    let s = p.sigma;

    for (label, name) in [
        ("Sigma", s.sigma),
        ("PSigma", s.psigma),
        ("Subtype", s.subtype),
    ] {
        assert!(
            matches!(
                kernel.environment().get(name),
                Some(Declaration::Inductive { .. })
            ),
            "{label} must be an inductive admitted through add_inductive"
        );
    }
    for (label, name) in [
        ("Sigma.mk", s.sigma_mk),
        ("PSigma.mk", s.psigma_mk),
        ("Subtype.mk", s.subtype_mk),
    ] {
        assert!(
            matches!(
                kernel.environment().get(name),
                Some(Declaration::Constructor { .. })
            ),
            "{label} must be a constructor"
        );
    }
    for (label, name) in [
        ("Sigma.fst", s.sigma_fst),
        ("Sigma.snd", s.sigma_snd),
        ("PSigma.fst", s.psigma_fst),
        ("PSigma.snd", s.psigma_snd),
        ("Subtype.val", s.subtype_val),
    ] {
        assert!(
            matches!(
                kernel.environment().get(name),
                Some(Declaration::Definition { .. })
            ),
            "{label} must be a definition (its codomain is data, not Prop)"
        );
    }
    for (label, name) in [
        ("Sigma.fst_mk", s.sigma_fst_mk),
        ("Sigma.snd_mk", s.sigma_snd_mk),
        ("Sigma.mk_eta", s.sigma_mk_eta),
        ("Subtype.property", s.subtype_property),
        ("Subtype.val_mk", s.subtype_val_mk),
        ("Subtype.mk_eta", s.subtype_mk_eta),
    ] {
        assert!(
            matches!(
                kernel.environment().get(name),
                Some(Declaration::Theorem { .. })
            ),
            "{label} must be a theorem"
        );
    }
}

/// The recursor's universe-parameter count reports the kernel's own verdict on
/// whether a family's result universe is provably non-zero: a large-eliminating
/// recursor carries a fresh motive level AHEAD of the family's own parameters.
///
/// All three families clear that bar, and `PSigma`'s `1` is what buys it. The
/// obvious `Sort (max u v)` does NOT — this kernel admits it and soundly denies
/// it large elimination, while real Lean refuses the declaration outright (see
/// the module doc; `real_lean_shared_prelude_crosscheck` is what measured it).
#[test]
fn the_recursor_universe_counts_report_which_families_may_be_prop() {
    let (kernel, p) = built();
    let s = p.sigma;

    let uparam_count = |name, label: &str| match kernel.environment().get(name) {
        Some(Declaration::Recursor { uparams, .. }) => uparams.len(),
        _ => panic!("{label} must be a generated recursor"),
    };

    // `Sigma.{u,v} : Type (max u v)` — a successor universe, provably non-zero,
    // so `Sigma.rec.{w,u,v}`.
    assert_eq!(
        uparam_count(s.sigma_rec, "Sigma.rec"),
        3,
        "Sigma.rec must carry a fresh motive level ahead of u and v"
    );
    // `Subtype.{u} : Sort (max 1 u)` — a `max` with a literal 1, provably
    // non-zero, so `Subtype.rec.{w,u}`.
    assert_eq!(
        uparam_count(s.subtype_rec, "Subtype.rec"),
        2,
        "Subtype.rec must carry a fresh motive level ahead of u"
    );
    // `PSigma.{u,v} : Sort (max 1 u v)` — the literal `1` is what makes it
    // provably non-zero, so `PSigma.rec.{w,u,v}` and both projections exist.
    assert_eq!(
        uparam_count(s.psigma_rec, "PSigma.rec"),
        3,
        "PSigma.rec must carry a fresh motive level: the 1 in max 1 u v earns it"
    );

    // The claim that the `1` is load-bearing, made falsifiable: a family
    // declared at the bare `Sort (max u v)` must be admitted WITHOUT a motive
    // level, since `max u v` is zero at u = v = 0. Declared into a scratch
    // kernel so the shared prelude is untouched.
    let mut scratch = Kernel::new();
    let _ = build_logic_prelude(&mut scratch).expect("logic prelude must build");
    let anon = scratch.anon();
    let u_name = scratch.name_str(anon, "u");
    let v_name = scratch.name_str(anon, "v");
    let bare = scratch.name_str(anon, "SigmaProbeAtBareMaxUV");
    let bare_mk = scratch.name_str(bare, "mk");
    {
        let u_lvl = scratch.level_param(u_name);
        let v_lvl = scratch.level_param(v_name);
        let sort_u = scratch.sort(u_lvl);
        let sort_v = scratch.sort(v_lvl);
        let result_sort = {
            let max_uv = scratch.level_max(u_lvl, v_lvl);
            scratch.sort(max_uv)
        };
        let bare_const = scratch.const_(bare, vec![u_lvl, v_lvl]);
        let ty = {
            let a0 = scratch.bvar(0);
            let beta_ty = scratch.pi(anon, a0, sort_v, BinderInfo::Default);
            let inner = scratch.pi(anon, beta_ty, result_sort, BinderInfo::Default);
            scratch.pi(anon, sort_u, inner, BinderInfo::Default)
        };
        let mk_ty = {
            let a3 = scratch.bvar(3);
            let b2 = scratch.bvar(2);
            let applied = {
                let e = scratch.app(bare_const, a3);
                scratch.app(e, b2)
            };
            let b1 = scratch.bvar(1);
            let f0 = scratch.bvar(0);
            let beta_fst = scratch.app(b1, f0);
            let inner_snd = scratch.pi(anon, beta_fst, applied, BinderInfo::Default);
            let a1 = scratch.bvar(1);
            let inner_fst = scratch.pi(anon, a1, inner_snd, BinderInfo::Default);
            let a0 = scratch.bvar(0);
            let beta_ty = scratch.pi(anon, a0, sort_v, BinderInfo::Default);
            let inner_beta = scratch.pi(anon, beta_ty, inner_fst, BinderInfo::Default);
            scratch.pi(anon, sort_u, inner_beta, BinderInfo::Default)
        };
        scratch
            .add_inductive(bare, &[u_name, v_name], 2, ty, &[(bare_mk, mk_ty)])
            .expect("this kernel ADMITS Sort (max u v) — it is real Lean that refuses it");
    }
    let bare_rec = scratch.name_str(bare, "rec");
    let bare_uparams = match scratch.environment().get(bare_rec) {
        Some(Declaration::Recursor { uparams, .. }) => uparams.len(),
        _ => panic!("the probe's recursor must be generated"),
    };
    assert_eq!(
        bare_uparams, 2,
        "at the bare Sort (max u v) the kernel must DENY large elimination — that denial is \
         what makes PSigma's literal 1 load-bearing rather than cosmetic"
    );
}

#[test]
fn every_dependent_pair_declaration_is_axiom_free() {
    let (kernel, p) = built();
    let s = p.sigma;

    let names = [
        ("Sigma", s.sigma),
        ("Sigma.mk", s.sigma_mk),
        ("Sigma.rec", s.sigma_rec),
        ("Sigma.fst", s.sigma_fst),
        ("Sigma.snd", s.sigma_snd),
        ("Sigma.fst_mk", s.sigma_fst_mk),
        ("Sigma.snd_mk", s.sigma_snd_mk),
        ("Sigma.mk_eta", s.sigma_mk_eta),
        ("PSigma", s.psigma),
        ("PSigma.mk", s.psigma_mk),
        ("PSigma.rec", s.psigma_rec),
        ("PSigma.fst", s.psigma_fst),
        ("PSigma.snd", s.psigma_snd),
        ("Subtype", s.subtype),
        ("Subtype.mk", s.subtype_mk),
        ("Subtype.rec", s.subtype_rec),
        ("Subtype.val", s.subtype_val),
        ("Subtype.property", s.subtype_property),
        ("Subtype.val_mk", s.subtype_val_mk),
        ("Subtype.mk_eta", s.subtype_mk_eta),
    ];
    for (label, name) in names {
        assert!(
            kernel.environment().get(name).is_some(),
            "{label} must be declared — an empty footprint for a MISSING name proves nothing"
        );
        let footprint = kernel.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{label} must be axiom-free, found {} assumption(s)",
            footprint.len()
        );
    }

    // The control that makes the emptiness above load-bearing: a name that was
    // never declared ALSO has an empty footprint, so `is_empty()` alone is not
    // evidence and the presence assertion is what carries the claim.
    let mut kernel = kernel;
    let anon = kernel.anon();
    let never_declared = kernel.name_str(anon, "Sigma_this_name_was_never_declared");
    assert!(kernel.environment().get(never_declared).is_none());
    assert!(
        kernel.axiom_footprint(never_declared).is_empty(),
        "control: a missing name's footprint is empty too"
    );
}

#[test]
fn sigma_projections_compute_at_concrete_arguments() {
    let (mut kernel, p) = built();
    let s = p.sigma;
    let (bool_const, beta) = bool_pair_shape(&mut kernel, p);
    let zero = kernel.level_zero();

    let bool_true = kernel.const_(p.bool_true, vec![]);
    let bool_false = kernel.const_(p.bool_false, vec![]);

    let mk = kernel.const_(s.sigma_mk, vec![zero, zero]);
    let pair = apply_all(&mut kernel, mk, &[bool_const, beta, bool_true, bool_false]);

    let fst_const = kernel.const_(s.sigma_fst, vec![zero, zero]);
    let fst = apply_all(&mut kernel, fst_const, &[bool_const, beta, pair]);
    let snd_const = kernel.const_(s.sigma_snd, vec![zero, zero]);
    let snd = apply_all(&mut kernel, snd_const, &[bool_const, beta, pair]);

    assert!(
        kernel.def_eq(fst, bool_true),
        "Sigma.fst ⟨true, false⟩ must compute to true"
    );
    assert!(
        !kernel.def_eq(fst, bool_false),
        "negative control: Sigma.fst ⟨true, false⟩ must NOT be false"
    );
    assert!(
        kernel.def_eq(snd, bool_false),
        "Sigma.snd ⟨true, false⟩ must compute to false"
    );
    assert!(
        !kernel.def_eq(snd, bool_true),
        "negative control: Sigma.snd ⟨true, false⟩ must NOT be true"
    );

    // The pair itself, and the eta equation at a literal constructor.
    let rebuilt = apply_all(&mut kernel, mk, &[bool_const, beta, fst, snd]);
    assert!(
        kernel.def_eq(rebuilt, pair),
        "⟨fst p, snd p⟩ must be the pair back at a literal constructor"
    );
    let swapped = apply_all(&mut kernel, mk, &[bool_const, beta, snd, fst]);
    assert!(
        !kernel.def_eq(swapped, pair),
        "negative control: the component-swapped pair differs in one leaf and must NOT be equal"
    );
}

/// `PSigma`'s projections compute too, at `Sort`-level components. `Prop` is a
/// legal first component here (`u = 0`), which is the case `Sigma` cannot take
/// and the reason `PSigma` exists at all.
#[test]
fn psigma_projections_compute_at_concrete_arguments() {
    let (mut kernel, p) = built();
    let s = p.sigma;
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);

    let bool_const = kernel.const_(p.bool_, vec![]);
    let bool_true = kernel.const_(p.bool_true, vec![]);
    let bool_false = kernel.const_(p.bool_false, vec![]);
    let beta = const_lam(&mut kernel, bool_const, bool_const);

    // `Bool : Sort 1`, so this is `PSigma.{1,1}`.
    let mk = kernel.const_(s.psigma_mk, vec![one, one]);
    let pair = apply_all(&mut kernel, mk, &[bool_const, beta, bool_true, bool_false]);

    let fst_const = kernel.const_(s.psigma_fst, vec![one, one]);
    let fst = apply_all(&mut kernel, fst_const, &[bool_const, beta, pair]);
    let snd_const = kernel.const_(s.psigma_snd, vec![one, one]);
    let snd = apply_all(&mut kernel, snd_const, &[bool_const, beta, pair]);

    assert!(
        kernel.def_eq(fst, bool_true),
        "PSigma.fst ⟨true, false⟩ must compute to true"
    );
    assert!(
        !kernel.def_eq(fst, bool_false),
        "negative control: PSigma.fst ⟨true, false⟩ must NOT be false"
    );
    assert!(
        kernel.def_eq(snd, bool_false),
        "PSigma.snd ⟨true, false⟩ must compute to false"
    );
    assert!(
        !kernel.def_eq(snd, bool_true),
        "negative control: PSigma.snd ⟨true, false⟩ must NOT be true"
    );

    // The case that distinguishes `PSigma` from `Sigma`: a `Prop` first
    // component. `Sigma` cannot take one — `Prop` is `Sort 0`, which is not
    // `Type u` for any `u` — so this instantiation is the whole point.
    let true_prop = kernel.const_(p.true_, vec![]);
    let true_intro = kernel.const_(p.true_intro, vec![]);
    // beta : True -> Sort 0, so its VALUE must be a Prop -- `True` itself, not
    // `Prop` (which lives at Sort 1 and would make this PSigma.{0,1}).
    let prop_beta = const_lam(&mut kernel, true_prop, true_prop);
    let prop_mk = kernel.const_(s.psigma_mk, vec![zero, zero]);
    let prop_pair = apply_all(
        &mut kernel,
        prop_mk,
        &[true_prop, prop_beta, true_intro, true_intro],
    );
    assert!(
        kernel.infer(prop_pair).is_ok(),
        "PSigma must accept a Prop first component"
    );
    let sigma_mk_at_prop = kernel.const_(s.sigma_mk, vec![zero, zero]);
    let refused = apply_all(
        &mut kernel,
        sigma_mk_at_prop,
        &[true_prop, prop_beta, true_intro, true_intro],
    );
    assert!(
        kernel.infer(refused).is_err(),
        "negative control: Sigma.{{0,0}} takes Type 0, not Prop, so the same pair is REFUSED"
    );
}

/// `Sigma.snd`'s codomain is `β (Sigma.fst s)`, not a fixed type. The proof is
/// a pair of terms differing in ONE leaf, one accepted and one refused, over a
/// genuinely dependent `β` (`β false = Nat`, `β true = Bool`).
#[test]
fn the_second_component_is_genuinely_dependent() {
    let (mut kernel, p) = built();
    let s = p.sigma;
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let two = kernel.level_succ(one);

    let bool_const = kernel.const_(p.bool_, vec![]);
    let nat_const = kernel.const_(p.nat, vec![]);
    let bool_true = kernel.const_(p.bool_true, vec![]);
    let bool_false = kernel.const_(p.bool_false, vec![]);
    let nat_zero = kernel.const_(p.nat_zero, vec![]);

    // β := fun b : Bool => Bool.rec.{2} (fun _ : Bool => Type 0) Nat Bool b.
    // The motive `fun _ => Sort 1` has type `Bool → Sort 2`, hence `.{2}`.
    // Constructor order is `Bool.false | Bool.true`, so the minors are Nat then
    // Bool: `β false = Nat`, `β true = Bool`.
    let beta = {
        let type0 = kernel.sort(one);
        let motive = const_lam(&mut kernel, bool_const, type0);
        let rec_const = kernel.const_(p.bool_rec, vec![two]);
        let anon = kernel.anon();
        let b = kernel.bvar(0);
        let body = apply_all(&mut kernel, rec_const, &[motive, nat_const, bool_const, b]);
        kernel.lam(anon, bool_const, body, BinderInfo::Default)
    };

    let mk = kernel.const_(s.sigma_mk, vec![zero, zero]);

    // ACCEPTED: the second component of `⟨false, _⟩` must be a `Nat`.
    let good = apply_all(&mut kernel, mk, &[bool_const, beta, bool_false, nat_zero]);
    let good_ty = kernel
        .infer(good)
        .expect("⟨false, Nat.zero⟩ must type-check: β false reduces to Nat");
    let sigma_const = kernel.const_(s.sigma, vec![zero, zero]);
    let expected = apply_all(&mut kernel, sigma_const, &[bool_const, beta]);
    assert!(
        kernel.def_eq(good_ty, expected),
        "the accepted pair must live in Sigma Bool β"
    );

    // REFUSED: one leaf changed — a `Bool` where a `Nat` is required.
    let bad = apply_all(&mut kernel, mk, &[bool_const, beta, bool_false, bool_true]);
    assert!(
        kernel.infer(bad).is_err(),
        "⟨false, Bool.true⟩ must be REFUSED: β false is Nat, not Bool"
    );

    // …and `snd` on the accepted pair computes, at the dependent type.
    let snd_const = kernel.const_(s.sigma_snd, vec![zero, zero]);
    let snd = apply_all(&mut kernel, snd_const, &[bool_const, beta, good]);
    assert!(
        kernel.def_eq(snd, nat_zero),
        "Sigma.snd ⟨false, Nat.zero⟩ must compute to Nat.zero"
    );
    let snd_ty = kernel.infer(snd).expect("snd of a well-typed pair infers");
    assert!(
        kernel.def_eq(snd_ty, nat_const),
        "its inferred type must reduce to Nat, not to a stuck β application"
    );
    assert!(
        !kernel.def_eq(snd_ty, bool_const),
        "negative control: the dependent codomain is NOT Bool at this pair"
    );
}

/// `Subtype`'s proof field genuinely depends on its value field: the same
/// witness that proves `true = true` cannot be paired with `false`.
#[test]
fn subtype_val_computes_and_its_property_field_is_dependent() {
    let (mut kernel, p) = built();
    let s = p.sigma;
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);

    let bool_const = kernel.const_(p.bool_, vec![]);
    let bool_true = kernel.const_(p.bool_true, vec![]);
    let bool_false = kernel.const_(p.bool_false, vec![]);

    // `Bool : Sort 1`, so this is `Subtype.{1}`.
    // predicate := fun b : Bool => Eq.{1} Bool b Bool.true.
    let predicate = {
        let anon = kernel.anon();
        let eq_const = kernel.const_(p.eq, vec![one]);
        let b = kernel.bvar(0);
        let body = apply_all(&mut kernel, eq_const, &[bool_const, b, bool_true]);
        kernel.lam(anon, bool_const, body, BinderInfo::Default)
    };
    let witness = {
        let refl = kernel.const_(p.eq_refl, vec![one]);
        apply_all(&mut kernel, refl, &[bool_const, bool_true])
    };

    let mk = kernel.const_(s.subtype_mk, vec![one]);
    let good = apply_all(
        &mut kernel,
        mk,
        &[bool_const, predicate, bool_true, witness],
    );
    assert!(
        kernel.infer(good).is_ok(),
        "⟨true, rfl⟩ must type-check as a Subtype Bool (· = true)"
    );

    // ONE leaf changed: the same witness against `false`.
    let bad = apply_all(
        &mut kernel,
        mk,
        &[bool_const, predicate, bool_false, witness],
    );
    assert!(
        kernel.infer(bad).is_err(),
        "⟨false, rfl⟩ must be REFUSED: the property field is dependent on the value field"
    );

    let val_const = kernel.const_(s.subtype_val, vec![one]);
    let val = apply_all(&mut kernel, val_const, &[bool_const, predicate, good]);
    assert!(
        kernel.def_eq(val, bool_true),
        "Subtype.val ⟨true, rfl⟩ must compute to true"
    );
    assert!(
        !kernel.def_eq(val, bool_false),
        "negative control: it must NOT compute to false"
    );
}

#[test]
fn the_dependent_pair_family_types_render() {
    let (kernel, p) = built();
    let s = p.sigma;

    for (label, name) in [
        ("Sigma", s.sigma),
        ("Sigma.mk", s.sigma_mk),
        ("Sigma.fst", s.sigma_fst),
        ("Sigma.snd", s.sigma_snd),
        ("Sigma.fst_mk", s.sigma_fst_mk),
        ("Sigma.snd_mk", s.sigma_snd_mk),
        ("Sigma.mk_eta", s.sigma_mk_eta),
        ("PSigma", s.psigma),
        ("PSigma.mk", s.psigma_mk),
        ("PSigma.fst", s.psigma_fst),
        ("PSigma.snd", s.psigma_snd),
        ("Subtype", s.subtype),
        ("Subtype.mk", s.subtype_mk),
        ("Subtype.val", s.subtype_val),
        ("Subtype.property", s.subtype_property),
        ("Subtype.val_mk", s.subtype_val_mk),
        ("Subtype.mk_eta", s.subtype_mk_eta),
    ] {
        let ty = declared_type(&kernel, name, label);
        println!("{label} : {}", kernel.render_lean(ty));
    }

    // Pin the two shapes the three blocked sites actually depend on: the
    // subtype's result universe is a `max`, and `Sigma.snd` is dependent.
    let subtype_ty = declared_type(&kernel, s.subtype, "Subtype");
    let rendered = kernel.render_lean(subtype_ty);
    assert!(
        rendered.contains("max"),
        "Subtype's result universe must be a max, got {rendered}"
    );
    let snd_ty = declared_type(&kernel, s.sigma_snd, "Sigma.snd");
    let rendered_snd = kernel.render_lean(snd_ty);
    assert!(
        rendered_snd.contains("Sigma.fst"),
        "Sigma.snd's codomain must mention Sigma.fst, got {rendered_snd}"
    );
}
