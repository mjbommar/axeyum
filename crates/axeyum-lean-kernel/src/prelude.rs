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
//! - **`Exists.{u} (α : Sort u) (p : α → Prop) : Prop`** —
//!   `Exists.intro : ∀ (w : α), p w → Exists α p` (the existential, a parametric
//!   non-indexed inductive). Its generated recursor `Exists.rec` is the
//!   eliminator `(∃ x, p x) → (∀ w, p w → C) → C` for any motive `C` — the
//!   foundation for certifying **existential skolemization** (P3.7).
//! - **`Not (a : Prop) : Prop := a → False`** — a [`Declaration::Definition`],
//!   not an inductive.
//!
//! Every inductive's generated recursor (`True.rec`, `False.rec`, `And.rec`,
//! `Or.rec`, `Iff.rec`, `Eq.rec`, `Exists.rec`) is registered too and is the
//! eliminator used by the proof terms.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
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

    /// `Exists.{u} : ∀ (α : Sort u), (α → Prop) → Prop`.
    pub exists_: NameId,
    /// `Exists.intro.{u} : ∀ (α : Sort u) (p : α → Prop) (w : α), p w → Exists α p`.
    pub exists_intro: NameId,
    /// `Exists.rec` — the existential eliminator
    /// (`(∃ x, p x) → (∀ w, p w → C) → C`).
    pub exists_rec: NameId,
    /// The universe parameter `u` shared by `Exists`/`Exists.intro`/`Exists.rec`.
    pub exists_uparam: NameId,

    /// `Not : Prop → Prop` (the definition `fun a => a → False`).
    pub not: NameId,

    /// `Bool : Type` (`Sort 1`) — the **computational** two-element type, a
    /// nullary enum `Bool.true | Bool.false`. This is *not* the `Prop`-valued
    /// `True`/`False`; it is the carrier the datatype **is-tester** recursor
    /// eliminates into (`is_C : D → Bool`), so `is_C (C x)` ι-reduces to a
    /// genuine `Bool` value computable by `def_eq`.
    pub bool_: NameId,
    /// `Bool.true : Bool`.
    pub bool_true: NameId,
    /// `Bool.false : Bool`.
    pub bool_false: NameId,
    /// `Bool.rec` — the `Bool` eliminator (used to build is-testers).
    pub bool_rec: NameId,

    /// `Nat : Type` (`Sort 1`) — the **computational** unary naturals, a
    /// recursive enum `Nat.zero | Nat.succ (n : Nat)`. This is the codomain of
    /// the datatype **size** measure (`size : D → Nat`): a containment cycle
    /// `x = C(… x …)` forces `size x = Nat.succ (size x)`, i.e. `n = Nat.succ n`,
    /// which is `False` by induction on `Nat` (the **acyclicity** route). Like
    /// `Bool`, `Nat` is rendered as a real Lean `inductive` so an external Lean
    /// regenerates `Nat.rec` *with* ι.
    pub nat: NameId,
    /// `Nat.zero : Nat`.
    pub nat_zero: NameId,
    /// `Nat.succ : Nat → Nat` (a direct recursive field).
    pub nat_succ: NameId,
    /// `Nat.rec` — the `Nat` eliminator (used to build the size measure, the
    /// `Nat.zero ≠ Nat.succ _` discriminator, the predecessor selector, and the
    /// `n ≠ Nat.succ n` induction).
    pub nat_rec: NameId,
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

    // --- Exists.{u} (α : Sort u) (p : α → Prop) : Prop -------------------
    // The existential: a parametric, NON-indexed inductive (2 params, 0
    // indices), with one constructor
    //   Exists.intro : Π (α) (p) (w : α) (h : p w), Exists α p.
    // The field `h : p w` mentions the PARAMETER `p` (not the inductive), so
    // it is non-recursive — the slice-7 parametric machinery admits it. The
    // generated `Exists.rec` is the eliminator
    //   Exists.rec : Π (α) (p) {motive : Exists α p → Sort v}
    //                (Π (w : α) (h : p w), motive (Exists.intro α p w h))
    //                (major : Exists α p), motive major,
    // and `Exists.rec` with `motive := fun _ => C` is `Exists.elim`.
    let exists_uparam = kernel.name_str(anon, "u");
    let exists_ = kernel.name_str(anon, "Exists");
    let exists_intro = kernel.name_str(exists_, "intro");
    {
        let u_lvl = kernel.level_param(exists_uparam);
        let sort_u = kernel.sort(u_lvl);
        let exists_const = kernel.const_(exists_, vec![u_lvl]);
        let prop = kernel.prop();
        // ty := Π (α : Sort u) (p : α → Prop), Prop.
        //   `p : α → Prop` under α → its domain `α` = BVar 0 (Π (_ : α), Prop).
        let exists_ty = {
            let a0 = kernel.bvar(0);
            let p_ty = kernel.pi(anon, a0, prop, BinderInfo::Default);
            let inner_p = kernel.pi(anon, p_ty, prop, BinderInfo::Default);
            kernel.pi(anon, sort_u, inner_p, BinderInfo::Default)
        };
        // Exists.intro : Π (α : Sort u) (p : α → Prop) (w : α) (h : p w),
        //                Exists α p.
        //   binders outer→inner: α(param), p(param), w(field), h(field).
        //   result `Exists α p` (under all 4): α = BVar 3, p = BVar 2.
        //   `h : p w`   under α, p, w → p = BVar 1, w = BVar 0 ⇒ App(BVar 1, BVar 0).
        //   `w : α`     under α, p     → α = BVar 1.
        //   `p : α → Prop` under α     → α = BVar 0.
        let intro_ty = {
            let a3 = kernel.bvar(3);
            let p2 = kernel.bvar(2);
            let exists_ap = {
                let e = kernel.app(exists_const, a3);
                kernel.app(e, p2)
            };
            // h : p w   (under α, p, w).
            let p1 = kernel.bvar(1);
            let w0 = kernel.bvar(0);
            let p_w = kernel.app(p1, w0);
            let inner_h = kernel.pi(anon, p_w, exists_ap, BinderInfo::Default);
            // w : α   (under α, p).
            let a1 = kernel.bvar(1);
            let inner_w = kernel.pi(anon, a1, inner_h, BinderInfo::Default);
            // p : α → Prop   (under α).
            let a0 = kernel.bvar(0);
            let p_ty = kernel.pi(anon, a0, prop, BinderInfo::Default);
            let inner_p = kernel.pi(anon, p_ty, inner_w, BinderInfo::Default);
            kernel.pi(anon, sort_u, inner_p, BinderInfo::Default)
        };
        kernel
            .add_inductive(
                exists_,
                &[exists_uparam],
                2,
                exists_ty,
                &[(exists_intro, intro_ty)],
            )
            .expect("Exists should admit");
    }
    let exists_rec = kernel.name_str(exists_, "rec");

    // --- Not (a : Prop) : Prop := fun a => a → False ---------------------
    // --- Bool : Type, Bool.true | Bool.false -----------------------------
    // The computational two-element enum at `Sort 1` (= Type). Its two nullary
    // constructors carry the truth values the is-tester recursor returns; the
    // generated `Bool.rec` is the eliminator that ι-computes `is_C (C x)`.
    let bool_ = kernel.name_str(anon, "Bool");
    let bool_true = kernel.name_str(bool_, "true");
    let bool_false = kernel.name_str(bool_, "false");
    {
        // Bool : Sort 1.
        let z = kernel.level_zero();
        let one = kernel.level_succ(z);
        let bool_ty = kernel.sort(one);
        // Each nullary constructor has type `Bool` (the bare inductive).
        let bool_const = kernel.const_(bool_, vec![]);
        kernel
            .add_inductive(
                bool_,
                &[],
                0,
                bool_ty,
                &[(bool_true, bool_const), (bool_false, bool_const)],
            )
            .expect("Bool should admit");
    }
    let bool_rec = kernel.name_str(bool_, "rec");

    // --- Nat : Type, Nat.zero | Nat.succ (n : Nat) -----------------------
    // The computational unary naturals at `Sort 1` (= Type), a RECURSIVE enum:
    // `Nat.succ : Nat → Nat` is a direct recursive field (admitted by the
    // slice-5 inductive gate). `Nat.rec` ι-computes
    //   Nat.rec C z s Nat.zero      ι→ z,
    //   Nat.rec C z s (Nat.succ k)  ι→ s k (Nat.rec C z s k),
    // and eliminates into an arbitrary `Sort v` (incl. `Prop`) — this kernel
    // imposes no large-elimination restriction. The size measure, the
    // `zero ≠ succ` discriminator, the predecessor selector, and the
    // `n ≠ succ n` induction (acyclicity) all ride on it.
    let nat = kernel.name_str(anon, "Nat");
    let nat_zero = kernel.name_str(nat, "zero");
    let nat_succ = kernel.name_str(nat, "succ");
    {
        let z = kernel.level_zero();
        let one = kernel.level_succ(z);
        let nat_ty = kernel.sort(one);
        let nat_const = kernel.const_(nat, vec![]);
        // Nat.zero : Nat ;  Nat.succ : Nat → Nat (direct recursive field).
        let succ_ty = kernel.pi(anon, nat_const, nat_const, BinderInfo::Default);
        kernel
            .add_inductive(
                nat,
                &[],
                0,
                nat_ty,
                &[(nat_zero, nat_const), (nat_succ, succ_ty)],
            )
            .expect("Nat should admit");
    }
    let nat_rec = kernel.name_str(nat, "rec");

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
        exists_,
        exists_intro,
        exists_rec,
        exists_uparam,
        not,
        bool_,
        bool_true,
        bool_false,
        bool_rec,
        nat,
        nat_zero,
        nat_succ,
        nat_rec,
    }
}

/// The interned names of a **datatype inductive** declared by
/// [`Kernel::add_datatype_inductive`]: a single-constructor, non-recursive,
/// non-indexed inductive `D : Sort u` whose constructor `D.mk` takes `num_fields`
/// fields all of one fixed carrier type, plus the generated recursor `D.rec`.
///
/// This is the kernel foundation for **route-A datatype-elim** (zero-trust
/// datatypes): modeling an SMT datatype constructor as a kernel constructor makes
/// the SMT selector a recursor application, so the read-over-construct projection
/// `select_i(mk(a…)) = a_i` is **ι-reduction** (`Eq.refl`, kernel-computed by
/// `def_eq`) rather than an assumed datatype axiom.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DatatypeInductive {
    /// `D : Sort u` (the carrier-modeling inductive sort).
    pub ind: NameId,
    /// `D.mk : carrier → … → D` (`num_fields` carrier arrows).
    pub ctor: NameId,
    /// `D.rec` — the eliminator, used to define the field selectors.
    pub rec: NameId,
    /// The number of constructor fields (selector index range).
    pub num_fields: usize,
}

impl Kernel {
    /// Declare a **single-constructor datatype inductive** `D : Sort u` whose
    /// constructor `D.mk` takes `num_fields` fields, each of the fixed
    /// `carrier` type (an already-declared `Sort u` expression, e.g. the EUF
    /// reconstruction carrier `α : Type`), and return the interned
    /// [`DatatypeInductive`] names.
    ///
    /// `name` is the (fresh) inductive name; `D.mk` and `D.rec` are derived from
    /// it (`name.mk`, `name.rec`). `carrier_sort` is the universe level `u` of the
    /// carrier (so `D : Sort u` lives at the same level and the eliminator can
    /// produce a `carrier`). The constructor result `D` is closed (no field
    /// reference), so the fields are non-recursive and the slice-7 inductive gate
    /// admits it directly.
    ///
    /// With this declared, the `i`-th selector is the recursor application
    /// `λ (t : D), D.rec.{u} (motive := λ _ => carrier) (λ f₀ … f_{n-1} => f_i) t`
    /// (see [`Kernel::datatype_selector`]); `selector_i (D.mk x₀ … x_{n-1})`
    /// ι-reduces to `x_i`, so the projection equation is `Eq.refl`.
    ///
    /// # Errors
    ///
    /// Returns the [`KernelError`](crate::tc::KernelError) from
    /// [`Kernel::add_inductive`] if the declaration fails to admit (e.g. a name
    /// clash, or a malformed carrier).
    pub fn add_datatype_inductive(
        &mut self,
        name: NameId,
        carrier: ExprId,
        carrier_sort: LevelId,
        num_fields: usize,
    ) -> Result<DatatypeInductive, crate::tc::KernelError> {
        let ctor = self.name_str(name, "mk");
        let anon = self.anon();
        // ty := Sort u (the datatype's own sort, closed — no params, no indices).
        let ind_ty = self.sort(carrier_sort);
        let ind_const = self.const_(name, vec![]);
        // ctor type := Π (_ : carrier)^num_fields, D   (the result `D` is closed).
        let mut ctor_ty = ind_const;
        for _ in 0..num_fields {
            ctor_ty = self.pi(anon, carrier, ctor_ty, BinderInfo::Default);
        }
        self.add_inductive(name, &[], 0, ind_ty, &[(ctor, ctor_ty)])?;
        let rec = self.name_str(name, "rec");
        Ok(DatatypeInductive {
            ind: name,
            ctor,
            rec,
            num_fields,
        })
    }

    /// Build the `index`-th **field selector** of a [`DatatypeInductive`] as a
    /// closed recursor application term
    /// `λ (t : D), D.rec.{u} (motive := λ _ => carrier) (λ f₀ … f_{n-1} => f_index) t`.
    ///
    /// Applying it to a constructor application `D.mk x₀ … x_{n-1}` ι-reduces
    /// (kernel `whnf`/`def_eq`) to `x_index`, so the projection equation
    /// `Eq carrier (selector (D.mk x…)) x_index` is `Eq.refl carrier x_index`.
    ///
    /// `carrier_sort` is the carrier's universe level `u` (the recursor's
    /// elimination universe is instantiated to `u` so the motive can yield
    /// `carrier`). `index` must be `< dt.num_fields`.
    ///
    /// # Panics
    ///
    /// Panics if `index >= dt.num_fields` (a caller bug; selectors are bounded by
    /// the constructor's field count).
    #[must_use]
    pub fn datatype_selector(
        &mut self,
        dt: DatatypeInductive,
        carrier: ExprId,
        carrier_sort: LevelId,
        index: usize,
    ) -> ExprId {
        assert!(index < dt.num_fields, "selector index out of field range");
        let anon = self.anon();
        let ind_const = self.const_(dt.ind, vec![]);
        // motive := λ (_ : D), carrier   (constant motive `λ _ => carrier`).
        let motive = self.lam(anon, ind_const, carrier, BinderInfo::Default);
        // minor := λ (f₀ … f_{n-1} : carrier), f_index.
        // Under the n field binders the `index`-th field (outer-to-inner f₀…f_{n-1})
        // is `BVar (n - 1 - index)`.
        let minor = {
            let mut body = self.bvar(u32::try_from(dt.num_fields - 1 - index).expect("fits u32"));
            for _ in 0..dt.num_fields {
                body = self.lam(anon, carrier, body, BinderInfo::Default);
            }
            body
        };
        // λ (t : D), D.rec.{u} motive minor t.
        let rec_const = self.const_(dt.rec, vec![carrier_sort]);
        let applied = {
            let e = self.app(rec_const, motive);
            let e = self.app(e, minor);
            let t = self.bvar(0);
            self.app(e, t)
        };
        self.lam(anon, ind_const, applied, BinderInfo::Default)
    }
}

/// The interned names of a **multi-constructor datatype family** declared by
/// [`Kernel::add_datatype_family`]: a non-recursive, non-indexed inductive
/// `D : Sort u` carrying *every* constructor of an SMT datatype, each
/// `D.cⱼ : carrier → … → D` taking its own field count of the fixed carrier
/// type, plus the generated recursor `D.rec`.
///
/// This is the foundation for the **is-tester** fold (`is_C (C x) = true`,
/// `is_C (K x) = false` for `K ≠ C`): because the family carries *all*
/// constructors, the recursor can distinguish them, so the is-tester recursor
/// application [`Kernel::datatype_tester`] ι-reduces to a concrete `Bool` value
/// — `is_C (cⱼ x…)` is `Eq.refl Bool` against `Bool.true`/`Bool.false`, with no
/// assumed datatype axiom (route-A, the is-tester twin of the selector route).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DatatypeFamily {
    /// `D : Sort u` (the carrier-modeling inductive sort).
    pub ind: NameId,
    /// The constructors `D.c₀ … D.c_{k-1}`, in declaration order.
    pub ctors: Vec<NameId>,
    /// The field count (carrier-arrow count) of each constructor, by the same
    /// index as `ctors`.
    pub arities: Vec<usize>,
    /// `D.rec` — the eliminator, used to define the is-testers.
    pub rec: NameId,
}

impl Kernel {
    /// Declare a **multi-constructor datatype family** `D : Sort u` whose
    /// constructors are `(name, arity)` pairs — each `D.cⱼ` takes `arityⱼ`
    /// fields, all of the fixed `carrier` type — and return the interned
    /// [`DatatypeFamily`].
    ///
    /// `name` is the (fresh) inductive name; each constructor name and `D.rec`
    /// are derived/registered through the trusted [`Kernel::add_inductive`]
    /// gate. The constructor result `D` is closed (no field reference), so the
    /// fields are non-recursive and the slice-7 inductive gate admits it.
    ///
    /// With this declared, the **is-tester** for the constructor at `tested` is
    /// the recursor application
    /// `λ (t : D), D.rec.{1} (motive := λ _ => Bool) min₀ … min_{k-1} t`
    /// where `min_tested = λ fields => Bool.true` and every other minor yields
    /// `Bool.false` (see [`Kernel::datatype_tester`]); `is_C (cⱼ x…)` ι-reduces
    /// to the corresponding `Bool` value, so the fold equation is `Eq.refl`.
    ///
    /// # Errors
    ///
    /// Returns the [`KernelError`](crate::tc::KernelError) from
    /// [`Kernel::add_inductive`] if the declaration fails to admit (a name
    /// clash or a malformed carrier).
    pub fn add_datatype_family(
        &mut self,
        name: NameId,
        carrier: ExprId,
        carrier_sort: LevelId,
        ctors: &[(NameId, usize)],
    ) -> Result<DatatypeFamily, crate::tc::KernelError> {
        let anon = self.anon();
        // ty := Sort u (closed — no params, no indices).
        let ind_ty = self.sort(carrier_sort);
        let ind_const = self.const_(name, vec![]);
        // Each constructor type := Π (_ : carrier)^arity, D   (result `D` closed).
        let ctor_decls: Vec<(NameId, ExprId)> = ctors
            .iter()
            .map(|&(cn, arity)| {
                let mut ctor_ty = ind_const;
                for _ in 0..arity {
                    ctor_ty = self.pi(anon, carrier, ctor_ty, BinderInfo::Default);
                }
                (cn, ctor_ty)
            })
            .collect();
        self.add_inductive(name, &[], 0, ind_ty, &ctor_decls)?;
        let rec = self.name_str(name, "rec");
        Ok(DatatypeFamily {
            ind: name,
            ctors: ctors.iter().map(|&(cn, _)| cn).collect(),
            arities: ctors.iter().map(|&(_, a)| a).collect(),
            rec,
        })
    }

    /// Build the **is-tester** for the `tested`-th constructor of a
    /// [`DatatypeFamily`] as a closed recursor application
    /// `λ (t : D), D.rec.{1} (motive := λ _ => Bool) min₀ … min_{k-1} t`, where
    /// `min_tested = λ (f₀ … : carrier), Bool.true` and every other minor is
    /// `λ (f₀ … : carrier), Bool.false`.
    ///
    /// Applying it to a constructor application `D.cⱼ x…` ι-reduces (kernel
    /// `whnf`/`def_eq`) to `Bool.true` when `j == tested` and `Bool.false`
    /// otherwise, so the is-tester fold `Eq Bool (is_C (cⱼ x…)) (true/false)`
    /// is `Eq.refl Bool (true/false)` — kernel-computed, axiom-free.
    ///
    /// `bool_`, `bool_true`, `bool_false` are the computational `Bool` names
    /// (from [`LogicPrelude`]); `tested` must be `< family.ctors.len()`.
    ///
    /// # Panics
    ///
    /// Panics if `tested >= family.ctors.len()` (a caller bug; the tested
    /// constructor must belong to the family).
    #[must_use]
    pub fn datatype_tester(
        &mut self,
        family: &DatatypeFamily,
        bool_: NameId,
        bool_true: NameId,
        bool_false: NameId,
        carrier: ExprId,
        tested: usize,
    ) -> ExprId {
        assert!(
            tested < family.ctors.len(),
            "tested constructor out of family range"
        );
        let anon = self.anon();
        let ind_const = self.const_(family.ind, vec![]);
        let bool_const = self.const_(bool_, vec![]);
        // motive := λ (_ : D), Bool   (constant motive `λ _ => Bool`).
        let motive = self.lam(anon, ind_const, bool_const, BinderInfo::Default);
        // The recursor's elimination universe for a `Bool : Sort 1` motive is `1`.
        let z = self.level_zero();
        let one = self.level_succ(z);
        let rec_const = self.const_(family.rec, vec![one]);
        let mut applied = self.app(rec_const, motive);
        // One minor per constructor: `λ (f₀ … f_{a-1} : carrier), value` — the
        // fields are bound and ignored, so the minor is a constant function.
        for (j, &arity) in family.arities.iter().enumerate() {
            let value = if j == tested { bool_true } else { bool_false };
            let mut minor = self.const_(value, vec![]);
            for _ in 0..arity {
                minor = self.lam(anon, carrier, minor, BinderInfo::Default);
            }
            applied = self.app(applied, minor);
        }
        // λ (t : D), D.rec.{1} motive min₀ … min_{k-1} t.
        let t = self.bvar(0);
        let body = self.app(applied, t);
        self.lam(anon, ind_const, body, BinderInfo::Default)
    }

    /// Build the **field selector** for the `tested`-th constructor of a
    /// [`DatatypeFamily`] at field `index`, as a closed recursor application
    /// `λ (t : D), D.rec.{u} (motive := λ _ => carrier) min₀ … min_{k-1} t`, where
    /// `min_tested = λ (f₀ … f_{a-1} : carrier), f_index` projects the requested
    /// field and **every other** minor `min_j = λ (f₀ … : carrier), default`
    /// returns the supplied `default` carrier inhabitant.
    ///
    /// Applying it to a constructor application `D.c_tested x…` ι-reduces (kernel
    /// `whnf`/`def_eq`) to `x_index`, so the selector fold
    /// `Eq carrier (sel (D.c_tested x…)) x_index` is `Eq.refl carrier x_index` —
    /// kernel-computed, axiom-free. (The other-constructor minors are only there to
    /// type the recursor; in the same-constructor injectivity use the selector is
    /// only ever applied to `c_tested`-headed majors, so they never reduce.)
    ///
    /// This is the **family analogue** of [`Kernel::datatype_selector`] (which is
    /// specialised to a single-constructor [`DatatypeInductive`]); both make the
    /// read-over-construct projection an ι-reduction rather than an assumed axiom.
    ///
    /// `carrier_sort` is the carrier's universe level `u` (the recursor's
    /// elimination universe). `tested` must be `< family.ctors.len()`, and `index`
    /// must be `< family.arities[tested]`. `default` must be a closed `carrier`
    /// inhabitant (used only to type the non-`tested` minors).
    ///
    /// # Panics
    ///
    /// Panics if `tested >= family.ctors.len()` or `index >= family.arities[tested]`
    /// (a caller bug; the field must belong to the tested constructor).
    #[must_use]
    pub fn datatype_family_selector(
        &mut self,
        family: &DatatypeFamily,
        carrier: ExprId,
        carrier_sort: LevelId,
        tested: usize,
        index: usize,
        default: ExprId,
    ) -> ExprId {
        assert!(
            tested < family.ctors.len(),
            "tested constructor out of family range"
        );
        assert!(
            index < family.arities[tested],
            "selector index out of the tested constructor's field range"
        );
        let anon = self.anon();
        let ind_const = self.const_(family.ind, vec![]);
        // motive := λ (_ : D), carrier   (constant motive `λ _ => carrier`).
        let motive = self.lam(anon, ind_const, carrier, BinderInfo::Default);
        let rec_const = self.const_(family.rec, vec![carrier_sort]);
        let mut applied = self.app(rec_const, motive);
        for (j, &arity) in family.arities.iter().enumerate() {
            // The `tested` minor projects field `index` (outer-to-inner f₀…f_{a-1},
            // so field `index` is `BVar(arity - 1 - index)`); every other minor is
            // the constant `default` carrier inhabitant (closed, weakening-invariant
            // under the field binders).
            let mut minor = if j == tested {
                self.bvar(u32::try_from(arity - 1 - index).expect("fits u32"))
            } else {
                default
            };
            for _ in 0..arity {
                minor = self.lam(anon, carrier, minor, BinderInfo::Default);
            }
            applied = self.app(applied, minor);
        }
        // λ (t : D), D.rec.{u} motive min₀ … min_{k-1} t.
        let t = self.bvar(0);
        let body = self.app(applied, t);
        self.lam(anon, ind_const, body, BinderInfo::Default)
    }
}

/// Whether a recursive-datatype constructor field is an opaque carrier value
/// (`α`) or a recursive self-reference to the datatype `D` itself. Used by
/// [`Kernel::add_recursive_datatype_family`] so a field like `tail : D` is
/// modeled as the kernel inductive's own sort — making the constructor a genuine
/// **recursive** kernel constructor whose recursor carries an induction
/// hypothesis (the size measure recurses through it).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecField {
    /// A non-recursive field of the opaque carrier sort `α` (e.g. a `head : α`).
    Carrier,
    /// A recursive field whose type is the datatype `D` itself (a direct
    /// recursive field, e.g. a list `tail : D`) — the source of acyclicity's
    /// structural descent.
    Recursive,
}

/// The interned names of a **recursive multi-constructor datatype family**
/// declared by [`Kernel::add_recursive_datatype_family`]: a non-parametric,
/// non-indexed *recursive* inductive `D : Sort u` carrying every constructor,
/// where each constructor field is either the opaque carrier `α`
/// ([`RecField::Carrier`]) or the datatype `D` itself ([`RecField::Recursive`], a
/// direct recursive field), plus the generated recursor `D.rec`.
///
/// This is the **recursive twin** of [`DatatypeFamily`] (whose every field is
/// `α`): it is needed for **acyclicity**, where the cycle `x = C(… x …)` is over
/// a recursive datatype (`cons(head : α, tail : D)`), so the `tail : D` field
/// must be the inductive's own sort for the recursor to recurse and the size
/// measure to add `1` per recursive field.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecursiveDatatypeFamily {
    /// `D : Sort u` (the recursive datatype sort).
    pub ind: NameId,
    /// The constructors `D.c₀ … D.c_{k-1}`, in declaration order.
    pub ctors: Vec<NameId>,
    /// The per-field shapes (carrier vs recursive) of each constructor, by the
    /// same index as `ctors`.
    pub fields: Vec<Vec<RecField>>,
    /// `D.rec` — the eliminator, used to define the size measure.
    pub rec: NameId,
}

impl Kernel {
    /// Declare a **recursive multi-constructor datatype family** `D : Sort u`
    /// whose constructors are `(name, field-shapes)` pairs — each `D.cⱼ` takes a
    /// field per shape, [`RecField::Carrier`] fields typed `carrier` and
    /// [`RecField::Recursive`] fields typed `D` (a direct recursive field) — and
    /// return the interned [`RecursiveDatatypeFamily`].
    ///
    /// The constructor result `D` is closed (no field reference), and recursive
    /// fields are exactly `D` (direct recursion), so the slice-5 inductive gate
    /// admits it and generates `D.rec` with an induction hypothesis per recursive
    /// field — the backbone the size measure ([`Kernel::recursive_datatype_size`])
    /// recurses through.
    ///
    /// `carrier` is the carrier-sort expression (an already-declared `Sort u`,
    /// e.g. the EUF carrier `α : Type`); `carrier_sort` is its level `u`, so
    /// `D : Sort u` lives at the same level and can carry both `α`-typed and
    /// `D`-typed fields.
    ///
    /// # Errors
    ///
    /// Returns the [`KernelError`](crate::tc::KernelError) from
    /// [`Kernel::add_inductive`] if the declaration fails to admit (a name clash,
    /// a malformed carrier, or — defensively — a recursive field the gate
    /// rejects).
    pub fn add_recursive_datatype_family(
        &mut self,
        name: NameId,
        carrier: ExprId,
        carrier_sort: LevelId,
        ctors: &[(NameId, Vec<RecField>)],
    ) -> Result<RecursiveDatatypeFamily, crate::tc::KernelError> {
        let anon = self.anon();
        let ind_ty = self.sort(carrier_sort);
        let ind_const = self.const_(name, vec![]);
        // Each constructor type := Π (fields…), D, with each field typed `carrier`
        // (Carrier) or `D` (Recursive). The result `D` is closed. Build the field
        // Pis right-to-left so the first shape becomes the outermost binder.
        let ctor_decls: Vec<(NameId, ExprId)> = ctors
            .iter()
            .map(|(cn, shapes)| {
                let mut ctor_ty = ind_const;
                for shape in shapes.iter().rev() {
                    let dom = match shape {
                        RecField::Carrier => carrier,
                        RecField::Recursive => ind_const,
                    };
                    ctor_ty = self.pi(anon, dom, ctor_ty, BinderInfo::Default);
                }
                (*cn, ctor_ty)
            })
            .collect();
        self.add_inductive(name, &[], 0, ind_ty, &ctor_decls)?;
        let rec = self.name_str(name, "rec");
        Ok(RecursiveDatatypeFamily {
            ind: name,
            ctors: ctors.iter().map(|&(cn, _)| cn).collect(),
            fields: ctors.iter().map(|(_, s)| s.clone()).collect(),
            rec,
        })
    }

    /// Build the **size measure** `size : D → Nat` for a
    /// [`RecursiveDatatypeFamily`] as a closed recursor application
    /// `λ (t : D), D.rec.{1} (motive := λ _ => Nat) min₀ … min_{k-1} t`, where each
    /// minor returns `Nat.succ` applied to the recursive field's induction
    /// hypothesis (its sub-value size):
    ///
    /// - a **non-recursive** constructor (all [`RecField::Carrier`]) maps to
    ///   `Nat.zero` (its minor ignores all carrier fields);
    /// - a constructor with one recursive field wraps one `Nat.succ` around the
    ///   recursive field's induction-hypothesis size, so e.g.
    ///   `cons(head : α, tail : D)` maps to
    ///   `λ (head : α) (tail : D) (ih_tail : Nat), Nat.succ ih_tail`.
    ///
    /// Applying it to a constructor application ι-reduces: `size nil` ι→
    /// `Nat.zero`, and `size (cons h t)` ι→ `Nat.succ (size t)` (one ι step exposes
    /// `m_cons h t (size t)`, which β-reduces to `Nat.succ (size t)`). So a cycle
    /// `x = cons(h, x)` gives, by congruence on `size`, `size x = Nat.succ
    /// (size x)` — the `n = Nat.succ n` contradiction.
    ///
    /// `nat`/`nat_zero`/`nat_succ` are the computational `Nat` names (from
    /// [`LogicPrelude`]); `carrier` is the family's carrier sort `α` expression.
    /// Constructors are restricted to **at most one** [`RecField::Recursive`]
    /// field here (the SMT datatypes that arise in acyclicity cycles — lists,
    /// trees written as nested pairs — have a single recursive tail per cell;
    /// multi-recursive constructors would chain the `succ`s but are not needed for
    /// this slice). The recursor's elimination universe for a `Nat : Sort 1`
    /// motive is the fixed `1`.
    ///
    /// # Panics
    ///
    /// Panics if any constructor has more than one [`RecField::Recursive`] field
    /// (the single-recursive-tail restriction above) — a caller bug for the
    /// datatypes this slice targets.
    #[must_use]
    pub fn recursive_datatype_size(
        &mut self,
        family: &RecursiveDatatypeFamily,
        carrier: ExprId,
        nat: NameId,
        nat_zero: NameId,
        nat_succ: NameId,
    ) -> ExprId {
        let anon = self.anon();
        let ind_const = self.const_(family.ind, vec![]);
        let nat_const = self.const_(nat, vec![]);
        // motive := λ (_ : D), Nat.
        let motive = self.lam(anon, ind_const, nat_const, BinderInfo::Default);
        // The recursor's elimination universe for a `Nat : Sort 1` motive is `1`.
        let z = self.level_zero();
        let one = self.level_succ(z);
        let rec_const = self.const_(family.rec, vec![one]);
        let mut applied = self.app(rec_const, motive);
        let zero_const = self.const_(nat_zero, vec![]);
        let succ_const = self.const_(nat_succ, vec![]);
        for shapes in &family.fields {
            let rec_count = shapes
                .iter()
                .filter(|s| matches!(s, RecField::Recursive))
                .count();
            assert!(
                rec_count <= 1,
                "recursive_datatype_size supports at most one recursive field per constructor"
            );
            // The minor binds, in order, each field (carrier or D) and then — for
            // each recursive field, appended after the field binders by the
            // recursor — one induction-hypothesis `ih : Nat` (the size of that
            // recursive subterm). De Bruijn layout, outer→inner:
            //   f₀ … f_{a-1}  ih_rec₀ … ih_rec_{r-1}
            // For `rec_count == 1` the lone IH is the innermost binder (BVar 0)
            // inside the minor body; the body is `Nat.succ ih`. With no recursive
            // field the body is `Nat.zero`.
            let body = if rec_count == 0 {
                zero_const
            } else {
                let ih = self.bvar(0); // the single recursive-field IH
                self.app(succ_const, ih)
            };
            // Wrap the IH binders (one `Nat` per recursive field), innermost first.
            let mut minor = body;
            for _ in 0..rec_count {
                minor = self.lam(anon, nat_const, minor, BinderInfo::Default);
            }
            // Wrap the field binders (carrier or D), innermost-to-outermost.
            for shape in shapes.iter().rev() {
                let dom = match shape {
                    RecField::Carrier => carrier,
                    RecField::Recursive => ind_const,
                };
                minor = self.lam(anon, dom, minor, BinderInfo::Default);
            }
            applied = self.app(applied, minor);
        }
        // λ (t : D), D.rec.{1} motive min₀ … min_{k-1} t.
        let t = self.bvar(0);
        let body = self.app(applied, t);
        self.lam(anon, ind_const, body, BinderInfo::Default)
    }
}

#[cfg(test)]
mod prelude_tests;
