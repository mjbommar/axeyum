//! The standard **logical prelude** (ADR-0036): the foundational logical
//! connectives and equality, declared into a [`Kernel`]'s environment through
//! the trusted `add_inductive`/`add_declaration` gates.
//!
//! This is the foundation layer for **P3.7 (Alethe→Lean reconstruction)**: a
//! reconstructed proof is a Lean term whose type is the goal proposition, built
//! from these connectives. The kernel itself type-checks every declaration here
//! (a malformed prelude is rejected by `add_inductive`/`add_declaration`, so a
//! green build *is* the prelude's well-formedness proof), and — crucially — the
//! same `infer`/`whnf` machinery then checks the **proof terms** built on top of
//! it. The accompanying tests build real proofs (and-introduction, and/or
//! elimination, `Eq` transport, modus ponens, ex-falso, an `And.comm`-style
//! composite) and `infer` them to their expected propositions: the kernel
//! genuinely verifies them.
//!
//! ## What is declared
//!
//! All connectives live in `Prop = Sort 0`; the propositional parameters of
//! `And`/`Or`/`Iff` are themselves `Prop`:
//!
//! - **`True : Prop`** — one nullary constructor `True.intro : True`.
//! - **`False : Prop`** — **no** constructors; its recursor `False.rec` is the
//!   ex-falso eliminator.
//! - **`And (a b : Prop) : Prop`** — `And.intro : a → b → And a b`.
//! - **`Or (a b : Prop) : Prop`** — `Or.inl : a → Or a b`,
//!   `Or.inr : b → Or a b`.
//! - **`Iff (a b : Prop) : Prop`** — `Iff.intro : (a → b) → (b → a) → Iff a b`.
//! - **`Eq.{u} {α : Sort u} (a : α) : α → Prop`** — `Eq.refl : Eq a a`
//!   (the slice-7 indexed inductive).
//! - **`Not (a : Prop) : Prop := a → False`** — a [`Declaration::Definition`],
//!   not an inductive.
//!
//! Every inductive's generated recursor (`True.rec`, `False.rec`, `And.rec`,
//! `Or.rec`, `Iff.rec`, `Eq.rec`) is registered too and is the eliminator used
//! by the proof terms.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::name::NameId;
use crate::{BinderInfo, Kernel};

/// The interned names produced by [`build_logic_prelude`]: every inductive, its
/// constructors, and its (generated) recursor, plus the `Not` definition and the
/// shared `Eq` universe parameter.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels. All fields are public so tests and callers can build `Const` terms
/// (`k.const_(prelude.and, vec![])`, `k.const_(prelude.and_intro, vec![])`, …).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LogicPrelude {
    /// `True : Prop`.
    pub true_: NameId,
    /// `True.intro : True`.
    pub true_intro: NameId,
    /// `True.rec` — the (trivial) `True` eliminator.
    pub true_rec: NameId,

    /// `False : Prop`.
    pub false_: NameId,
    /// `False.rec` — the ex-falso eliminator (zero-constructor recursor).
    pub false_rec: NameId,

    /// `And : Prop → Prop → Prop`.
    pub and: NameId,
    /// `And.intro : ∀ {a b : Prop}, a → b → And a b`.
    pub and_intro: NameId,
    /// `And.rec` — the `And` eliminator.
    pub and_rec: NameId,

    /// `Or : Prop → Prop → Prop`.
    pub or: NameId,
    /// `Or.inl : ∀ {a b : Prop}, a → Or a b`.
    pub or_inl: NameId,
    /// `Or.inr : ∀ {a b : Prop}, b → Or a b`.
    pub or_inr: NameId,
    /// `Or.rec` — the `Or` case-analysis eliminator.
    pub or_rec: NameId,

    /// `Iff : Prop → Prop → Prop`.
    pub iff: NameId,
    /// `Iff.intro : ∀ {a b : Prop}, (a → b) → (b → a) → Iff a b`.
    pub iff_intro: NameId,
    /// `Iff.rec` — the `Iff` eliminator.
    pub iff_rec: NameId,

    /// `Eq.{u} : ∀ {α : Sort u}, α → α → Prop`.
    pub eq: NameId,
    /// `Eq.refl.{u} : ∀ {α : Sort u} (a : α), Eq a a`.
    pub eq_refl: NameId,
    /// `Eq.rec` — the equality eliminator (transport).
    pub eq_rec: NameId,
    /// The universe parameter `u` shared by `Eq`/`Eq.refl`/`Eq.rec`.
    pub eq_uparam: NameId,

    /// `Not : Prop → Prop` (the definition `fun a => a → False`).
    pub not: NameId,
}

impl Kernel {
    /// `Prop`, i.e. `Sort 0`. A local convenience alias for the prelude builders.
    fn prop(&mut self) -> ExprId {
        self.sort_zero()
    }
}

/// Declare the standard logical prelude into `kernel`'s environment, returning
/// the [`LogicPrelude`] of interned names.
///
/// Each declaration is admitted through the **trusted** gates
/// ([`Kernel::add_inductive`] / [`Kernel::add_declaration`]), which type-check
/// it; a malformed declaration would be rejected (and would panic here, since a
/// well-formed prelude is a precondition). On success the environment contains
/// `True`/`False`/`And`/`Or`/`Iff`/`Eq` (with their constructors and recursors)
/// and the `Not` definition.
///
/// # Panics
///
/// Panics if any declaration fails to type-check, which would indicate a kernel
/// regression rather than a caller error — the prelude is fixed and valid.
#[must_use]
#[allow(clippy::too_many_lines)]
pub fn build_logic_prelude(kernel: &mut Kernel) -> LogicPrelude {
    let anon = kernel.anon();

    // --- True : Prop, True.intro : True ----------------------------------
    // A nullary enum in Prop: 0 params, 0 indices, one nullary constructor.
    let true_ = kernel.name_str(anon, "True");
    let true_intro = kernel.name_str(true_, "intro");
    {
        let prop = kernel.prop();
        let true_const = kernel.const_(true_, vec![]);
        // True.intro : True   (its type is just `True`, the bare inductive).
        kernel
            .add_inductive(true_, &[], 0, prop, &[(true_intro, true_const)])
            .expect("True should admit");
    }
    let true_rec = kernel.name_str(true_, "rec");

    // --- False : Prop, no constructors -----------------------------------
    // The empty type in Prop. Its recursor `False.rec` is ex-falso.
    let false_ = kernel.name_str(anon, "False");
    {
        let prop = kernel.prop();
        kernel
            .add_inductive(false_, &[], 0, prop, &[])
            .expect("False (zero-constructor) should admit");
    }
    let false_rec = kernel.name_str(false_, "rec");

    // --- And (a b : Prop) : Prop, And.intro : a → b → And a b ------------
    // 2 Prop parameters, non-recursive structure.
    let and = kernel.name_str(anon, "And");
    let and_intro = kernel.name_str(and, "intro");
    {
        let prop = kernel.prop();
        // ty := Π (a : Prop) (b : Prop), Prop.
        let and_ty = {
            let inner = kernel.pi(anon, prop, prop, BinderInfo::Default);
            kernel.pi(anon, prop, inner, BinderInfo::Default)
        };
        // And.intro : Π (a : Prop) (b : Prop) (_ : a) (_ : b), And a b.
        //   binders outer→inner: a(param), b(param), ha(field), hb(field).
        //   At the result (under all 4): a = BVar 3, b = BVar 2.
        //   `hb : b` is under a, b, ha → b = BVar 1.
        //   `ha : a` is under a, b     → a = BVar 1.
        let and_const = kernel.const_(and, vec![]);
        let intro_ty = {
            let a3 = kernel.bvar(3);
            let b2 = kernel.bvar(2);
            let and_ab = {
                let e = kernel.app(and_const, a3);
                kernel.app(e, b2)
            };
            let b1 = kernel.bvar(1); // hb : b
            let inner_hb = kernel.pi(anon, b1, and_ab, BinderInfo::Default);
            let a1 = kernel.bvar(1); // ha : a
            let inner_ha = kernel.pi(anon, a1, inner_hb, BinderInfo::Default);
            let inner_b = kernel.pi(anon, prop, inner_ha, BinderInfo::Default);
            kernel.pi(anon, prop, inner_b, BinderInfo::Default)
        };
        kernel
            .add_inductive(and, &[], 2, and_ty, &[(and_intro, intro_ty)])
            .expect("And should admit");
    }
    let and_rec = kernel.name_str(and, "rec");

    // --- Or (a b : Prop) : Prop, Or.inl : a → Or a b, Or.inr : b → Or a b -
    let or = kernel.name_str(anon, "Or");
    let or_inl = kernel.name_str(or, "inl");
    let or_inr = kernel.name_str(or, "inr");
    {
        let prop = kernel.prop();
        let or_ty = {
            let inner = kernel.pi(anon, prop, prop, BinderInfo::Default);
            kernel.pi(anon, prop, inner, BinderInfo::Default)
        };
        let or_const = kernel.const_(or, vec![]);
        // Or.inl : Π (a : Prop) (b : Prop) (_ : a), Or a b.
        //   binders a, b, ha; result Or a b: a = BVar 2, b = BVar 1; `ha : a`: a = BVar 1.
        let inl_ty = {
            let a2 = kernel.bvar(2);
            let b1 = kernel.bvar(1);
            let or_ab = {
                let e = kernel.app(or_const, a2);
                kernel.app(e, b1)
            };
            let a1 = kernel.bvar(1); // ha : a
            let inner_ha = kernel.pi(anon, a1, or_ab, BinderInfo::Default);
            let inner_b = kernel.pi(anon, prop, inner_ha, BinderInfo::Default);
            kernel.pi(anon, prop, inner_b, BinderInfo::Default)
        };
        // Or.inr : Π (a : Prop) (b : Prop) (_ : b), Or a b.
        //   `hb : b` is under a, b → b = BVar 0.
        let inr_ty = {
            let a2 = kernel.bvar(2);
            let b1 = kernel.bvar(1);
            let or_ab = {
                let e = kernel.app(or_const, a2);
                kernel.app(e, b1)
            };
            let b0 = kernel.bvar(0); // hb : b
            let inner_hb = kernel.pi(anon, b0, or_ab, BinderInfo::Default);
            let inner_b = kernel.pi(anon, prop, inner_hb, BinderInfo::Default);
            kernel.pi(anon, prop, inner_b, BinderInfo::Default)
        };
        kernel
            .add_inductive(or, &[], 2, or_ty, &[(or_inl, inl_ty), (or_inr, inr_ty)])
            .expect("Or should admit");
    }
    let or_rec = kernel.name_str(or, "rec");

    // --- Iff (a b : Prop) : Prop, Iff.intro : (a → b) → (b → a) → Iff a b -
    let iff = kernel.name_str(anon, "Iff");
    let iff_intro = kernel.name_str(iff, "intro");
    {
        let prop = kernel.prop();
        let iff_ty = {
            let inner = kernel.pi(anon, prop, prop, BinderInfo::Default);
            kernel.pi(anon, prop, inner, BinderInfo::Default)
        };
        let iff_const = kernel.const_(iff, vec![]);
        // Iff.intro : Π (a : Prop) (b : Prop) (_ : a → b) (_ : b → a), Iff a b.
        //   binders a, b, mp(field), mpr(field).
        //   result Iff a b (under all 4): a = BVar 3, b = BVar 2.
        //   `mpr : b → a` under a, b, mp: b = BVar 2, a = BVar 1.
        //   `mp  : a → b` under a, b:     a = BVar 1, b = BVar 0.
        let intro_ty = {
            let a3 = kernel.bvar(3);
            let b2 = kernel.bvar(2);
            let iff_ab = {
                let e = kernel.app(iff_const, a3);
                kernel.app(e, b2)
            };
            // mpr : b → a   (under a, b, mp). The arrow `b → a` is itself a Pi
            // binding the domain, so inside its codomain everything shifts by 1:
            //   domain `b` (under a, b, mp) = BVar 1;
            //   codomain `a` (under a, b, mp, arrow) = BVar 2 + 1 = BVar 3.
            let b1_dom = kernel.bvar(1);
            let a3_cod = kernel.bvar(3);
            let mpr_ty = kernel.pi(anon, b1_dom, a3_cod, BinderInfo::Default);
            let inner_mpr = kernel.pi(anon, mpr_ty, iff_ab, BinderInfo::Default);
            // mp : a → b   (under a, b). domain `a` = BVar 1; codomain `b` under
            // the arrow's own binder = BVar 0 + 1 = BVar 1.
            let a1_dom = kernel.bvar(1);
            let b1_cod = kernel.bvar(1);
            let mp_ty = kernel.pi(anon, a1_dom, b1_cod, BinderInfo::Default);
            let inner_mp = kernel.pi(anon, mp_ty, inner_mpr, BinderInfo::Default);
            let inner_b = kernel.pi(anon, prop, inner_mp, BinderInfo::Default);
            kernel.pi(anon, prop, inner_b, BinderInfo::Default)
        };
        kernel
            .add_inductive(iff, &[], 2, iff_ty, &[(iff_intro, intro_ty)])
            .expect("Iff should admit");
    }
    let iff_rec = kernel.name_str(iff, "rec");

    // --- Eq.{u} {α : Sort u} (a : α) : α → Prop, Eq.refl : Eq a a --------
    // The slice-7 indexed inductive: 2 params (α, a), 1 index, one ctor.
    let eq_uparam = kernel.name_str(anon, "u");
    let eq = kernel.name_str(anon, "Eq");
    let eq_refl = kernel.name_str(eq, "refl");
    {
        let u_lvl = kernel.level_param(eq_uparam);
        let sort_u = kernel.sort(u_lvl);
        let eq_const = kernel.const_(eq, vec![u_lvl]);
        let prop = kernel.prop();
        // ty := Π (α : Sort u) (a : α) (b : α), Prop.
        //   `b : α` under α, a → α = BVar 1; `a : α` under α → α = BVar 0.
        let eq_ty = {
            let a1 = kernel.bvar(1);
            let inner_b = kernel.pi(anon, a1, prop, BinderInfo::Default);
            let a0 = kernel.bvar(0);
            let inner_a = kernel.pi(anon, a0, inner_b, BinderInfo::Default);
            kernel.pi(anon, sort_u, inner_a, BinderInfo::Default)
        };
        // refl : Π (α : Sort u) (a : α), Eq α a a.
        //   result Eq α a a under α, a → α = BVar 1, a = BVar 0.
        let refl_ty = {
            let a1 = kernel.bvar(1);
            let a0 = kernel.bvar(0);
            let eq_app = {
                let e = kernel.app(eq_const, a1);
                let e = kernel.app(e, a0);
                kernel.app(e, a0)
            };
            let inner_a = kernel.pi(anon, a0, eq_app, BinderInfo::Default);
            kernel.pi(anon, sort_u, inner_a, BinderInfo::Default)
        };
        kernel
            .add_inductive(eq, &[eq_uparam], 2, eq_ty, &[(eq_refl, refl_ty)])
            .expect("Eq should admit");
    }
    let eq_rec = kernel.name_str(eq, "rec");

    // --- Not (a : Prop) : Prop := fun a => a → False ---------------------
    // A Definition (not an inductive). Type: Prop → Prop. Value: λ a, a → False.
    let not = kernel.name_str(anon, "Not");
    {
        let prop = kernel.prop();
        // type := Prop → Prop.
        let not_ty = kernel.pi(anon, prop, prop, BinderInfo::Default);
        // value := fun (a : Prop) => a → False  (= Π (_ : a), False).
        let false_const = kernel.const_(false_, vec![]);
        let not_val = {
            let a0 = kernel.bvar(0); // a
            let arrow = kernel.pi(anon, a0, false_const, BinderInfo::Default);
            kernel.lam(anon, prop, arrow, BinderInfo::Default)
        };
        kernel
            .add_declaration(Declaration::Definition {
                name: not,
                uparams: vec![],
                ty: not_ty,
                value: not_val,
                hint: ReducibilityHint::Regular(0),
            })
            .expect("Not should admit");
    }

    LogicPrelude {
        true_,
        true_intro,
        true_rec,
        false_,
        false_rec,
        and,
        and_intro,
        and_rec,
        or,
        or_inl,
        or_inr,
        or_rec,
        iff,
        iff_intro,
        iff_rec,
        eq,
        eq_refl,
        eq_rec,
        eq_uparam,
        not,
    }
}

#[cfg(test)]
mod prelude_tests;
