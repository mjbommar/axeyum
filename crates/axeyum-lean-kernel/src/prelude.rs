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
//! - **`And (a b : Prop) : Prop`** — `And.intro : a → b → And a b`, plus the
//!   `And.rec`-derived projections **`And.left`**/**`And.right`**.
//! - **`Or (a b : Prop) : Prop`** — `Or.inl : a → Or a b`,
//!   `Or.inr : b → Or a b`, plus **`Or.elim`** and its two corollaries
//!   **`Or.resolve_left`**/**`Or.resolve_right`**.
//! - **`Iff (a b : Prop) : Prop`** — `Iff.intro : (a → b) → (b → a) → Iff a b`,
//!   plus the `Iff.rec`-derived projections **`Iff.mp`**/**`Iff.mpr`**.
//! - **`Eq.{u} {α : Sort u} (a : α) : α → Prop`** — `Eq.refl : Eq a a`
//!   (the slice-7 indexed inductive), plus **`Eq.symm`** and the
//!   non-dependent function-congruence lemma **`` congrFun' ``**.
//! - **`Exists.{u} (α : Sort u) (p : α → Prop) : Prop`** —
//!   `Exists.intro : ∀ (w : α), p w → Exists α p` (the existential, a parametric
//!   non-indexed inductive). Its generated recursor `Exists.rec` is the
//!   eliminator `(∃ x, p x) → (∀ w, p w → C) → C` for any motive `C` — the
//!   foundation for certifying **existential skolemization** (P3.7).
//! - **`Acc.{u} {α : Sort u} (r : α → α → Prop) (a : α) : Prop`** — the
//!   accessibility predicate with its higher-order recursive constructor and
//!   generated `Acc.rec`; **`Acc.inv`** extracts predecessor accessibility;
//!   **`WellFounded r := ∀ a, Acc r a`** packages global accessibility, and
//!   **`WellFounded.fix`** supplies a universe-polymorphic fixpoint with a
//!   checked **`WellFounded.fix_eq`** unfolding theorem.
//! - **`Not (a : Prop) : Prop := a → False`** — a [`Declaration::Definition`],
//!   not an inductive, plus **`absurd`** (universe-polymorphic ex falso) and
//!   **`mt`** (modus tollens).
//!
//! Every inductive's generated recursor (`True.rec`, `False.rec`, `And.rec`,
//! `Or.rec`, `Iff.rec`, `Eq.rec`, `Exists.rec`) is registered too and is the
//! eliminator used by the proof terms. The corollaries listed above
//! (`And.left`/`And.right`, `Or.elim`/`Or.resolve_left`/`Or.resolve_right`,
//! `Iff.mp`/`Iff.mpr`, `` congrFun' ``, `absurd`, `mt`) are all
//! [`Declaration::Theorem`]s built directly from those recursors (or from
//! plain function composition for `mt`) — none needs an axiom, and
//! `Kernel::axiom_footprint` is empty for every one of them (see
//! `prelude_tests`).
//!
//! ## The negation toolkit, De Morgan, and the classical principles
//!
//! This kernel is **intuitionistic**: `Classical.em`, `propext`, and `funext`
//! are not declared anywhere, so every theorem below had to be proved without
//! them, using only the connectives above.
//!
//! - **`not_not_intro`**, **`not_not_not`** (the triple-negation collapse
//!   `¬¬¬a → ¬a`), and **`noncontradiction`** (`¬(a ∧ ¬a)`) round out the
//!   negation toolkit alongside the pre-existing `absurd`/`mt`.
//! - **De Morgan.** Three of the four directions relating `¬`, `∧`, and `∨`
//!   are intuitionistically valid and declared here: **`demorgan_not_or`**
//!   (`¬(a ∨ b) → ¬a ∧ ¬b`), its converse **`demorgan_not_or_converse`**
//!   (`¬a ∧ ¬b → ¬(a ∨ b)`), and **`demorgan_or_not_and`**
//!   (`¬a ∨ ¬b → ¬(a ∧ b)`). The fourth direction — the converse of the last,
//!   `¬(a ∧ b) → ¬a ∨ ¬b` — is **not a theorem of intuitionistic logic**: it
//!   is classically valid but constructively equivalent to a weak form of
//!   excluded middle, so deriving it would require assuming a classical
//!   principle this kernel does not have. It is deliberately not declared,
//!   stated as an axiom, or approximated by anything in this prelude.
//! - **The classical principles are interderivable, and none of them is
//!   assumed.** `Classical.em`'s statement (`∀ P, P ∨ ¬P`), double-negation
//!   elimination's statement (`∀ P, ¬¬P → P`), and Peirce's law's statement
//!   (`∀ A B, ((A → B) → A) → A`) are each *hypotheses* of a theorem here,
//!   never conclusions asserted outright: **`dne_of_em`**, **`em_of_dne`**,
//!   **`peirce_of_em`**, **`em_of_peirce`**. The standalone
//!   **`not_not_em : ¬¬(P ∨ ¬P)`** — excluded middle's double negation, which
//!   *is* an intuitionistic theorem with no hypothesis at all — is what makes
//!   `em_of_dne` work: instantiate double-negation elimination at `P ∨ ¬P`
//!   itself and discharge its `¬¬(P ∨ ¬P)` premise with `not_not_em`.

#![allow(clippy::similar_names, clippy::many_single_char_names)]

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::{BinderInfo, Kernel, KernelError, PreludeKey, PreludeValue};

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
    /// `And.left : Π (a b : Prop), And a b → a` — the first-field projection,
    /// built directly from `And.rec` (motive := the constant `a`, minor :=
    /// `fun ha hb => ha`).
    pub and_left: NameId,
    /// `And.right : Π (a b : Prop), And a b → b` — the second-field
    /// projection, the same construction with motive `b` and minor
    /// `fun ha hb => hb`.
    pub and_right: NameId,

    /// `Or : Prop → Prop → Prop`.
    pub or: NameId,
    /// `Or.inl : ∀ {a b : Prop}, a → Or a b`.
    pub or_inl: NameId,
    /// `Or.inr : ∀ {a b : Prop}, b → Or a b`.
    pub or_inr: NameId,
    /// `Or.rec` — the `Or` case-analysis eliminator.
    pub or_rec: NameId,
    /// `Or.elim : Π (a b c : Prop), Or a b → (a → c) → (b → c) → c` — built
    /// directly from `Or.rec` with a constant motive `c` and the two supplied
    /// arrows reused verbatim as the minor premises.
    pub or_elim: NameId,
    /// `Or.resolve_left : Π (a b : Prop), Or a b → (a → False) → b` — the
    /// left branch discharged by `False.rec` against the supplied refutation
    /// of `a`, the right branch returned as-is.
    pub or_resolve_left: NameId,
    /// `Or.resolve_right : Π (a b : Prop), Or a b → (b → False) → a` — the
    /// mirror image of [`Self::or_resolve_left`].
    pub or_resolve_right: NameId,

    /// `Iff : Prop → Prop → Prop`.
    pub iff: NameId,
    /// `Iff.intro : ∀ {a b : Prop}, (a → b) → (b → a) → Iff a b`.
    pub iff_intro: NameId,
    /// `Iff.rec` — the `Iff` eliminator.
    pub iff_rec: NameId,
    /// `Iff.mp : Π (a b : Prop), Iff a b → a → b` — the forward-direction
    /// projection, built from `Iff.rec` with motive `a → b` and minor
    /// `fun mp mpr => mp`.
    pub iff_mp: NameId,
    /// `Iff.mpr : Π (a b : Prop), Iff a b → b → a` — the backward-direction
    /// projection, the same construction with motive `b → a` and minor
    /// `fun mp mpr => mpr`.
    pub iff_mpr: NameId,

    /// `Eq.{u} : ∀ {α : Sort u}, α → α → Prop`.
    pub eq: NameId,
    /// `Eq.refl.{u} : ∀ {α : Sort u} (a : α), Eq a a`.
    pub eq_refl: NameId,
    /// `Eq.rec` — the equality eliminator (transport).
    pub eq_rec: NameId,
    /// The universe parameter `u` shared by `Eq`/`Eq.refl`/`Eq.rec`.
    pub eq_uparam: NameId,
    /// `Eq.symm.{u} : ∀ {α : Sort u} {a b : α}, Eq a b → Eq b a` — built directly
    /// from `Eq.rec` (the standard `motive x _ := Eq x a` transport at `a`),
    /// universe-polymorphic like `Eq`/`Eq.refl`/`Eq.rec` themselves so it
    /// applies uniformly to equalities between propositions, naturals, or
    /// anything else built on top.
    pub eq_symm: NameId,
    /// `` congrFun' `` `.{u,v} : Π (α : Sort u) (β : Sort v) (f g : α → β),
    /// Eq.{imax u v} (α → β) f g → Π (a : α), Eq.{v} β (f a) (g a)` — the
    /// non-dependent function-congruence lemma, built directly from `Eq.rec`
    /// the same way [`Self::eq_symm`] is: the varying side of the hypothesis
    /// equality (`g'`) is transported into the motive `Eq β (f a) (g' a)`
    /// against the trivial `Eq.refl β (f a)` at `g' := f`.
    pub congr_fun_prime: NameId,

    /// `Exists.{u} : ∀ (α : Sort u), (α → Prop) → Prop`.
    pub exists_: NameId,
    /// `Exists.intro.{u} : ∀ (α : Sort u) (p : α → Prop) (w : α), p w → Exists α p`.
    pub exists_intro: NameId,
    /// `Exists.rec` — the existential eliminator
    /// (`(∃ x, p x) → (∀ w, p w → C) → C`).
    pub exists_rec: NameId,
    /// The universe parameter `u` shared by `Exists`/`Exists.intro`/`Exists.rec`.
    pub exists_uparam: NameId,

    /// `Acc.{u} : {α : Sort u} → (α → α → Prop) → α → Prop`.
    pub acc: NameId,
    /// `Acc.intro.{u} : ∀ {α} r x, (∀ y, r y x → Acc r y) → Acc r x`.
    pub acc_intro: NameId,
    /// `Acc.rec` — accessibility induction, including the recursive hypotheses
    /// generated from `Acc.intro`'s higher-order field.
    pub acc_rec: NameId,
    /// `Acc.inv.{u} : Acc r x → r y x → Acc r y` — predecessor
    /// accessibility extracted by `Acc.rec`.
    pub acc_inv: NameId,
    /// The universe parameter shared by `Acc`, `Acc.intro`, `Acc.rec`, and
    /// `WellFounded`.
    pub acc_uparam: NameId,
    /// `WellFounded.{u} {α : Sort u} (r : α → α → Prop) := ∀ a, Acc r a`.
    pub well_founded: NameId,
    /// `WellFounded.fix.{u,v}` — the generic well-founded fixpoint built from
    /// `Acc.rec`.
    pub well_founded_fix: NameId,
    /// `WellFounded.fix_eq.{u,v}` — the checked unfolding equation for the
    /// generic well-founded fixpoint.
    pub well_founded_fix_eq: NameId,
    /// The result-family universe parameter `v` of `WellFounded.fix`.
    pub well_founded_fix_vparam: NameId,

    /// `Not : Prop → Prop` (the definition `fun a => a → False`).
    pub not: NameId,
    /// `absurd.{v} : Π (a : Prop) (b : Sort v), a → (a → False) → b` — ex
    /// falso from a proposition and its refutation, built directly from
    /// `False.rec`; universe-polymorphic in the target `b` the same way
    /// [`Self::eq_symm`] is polymorphic in its carrier.
    pub absurd: NameId,
    /// The universe parameter `v` of [`Self::absurd`] (the target sort).
    pub absurd_vparam: NameId,
    /// `mt : Π (a b : Prop), (a → b) → (b → False) → (a → False)` — modus
    /// tollens, direct function composition (`fun ha => nb (f ha)`), no
    /// recursor needed.
    pub mt: NameId,

    /// `not_not_intro : Π (a : Prop), a → (a → False) → False` — double
    /// negation introduction (`¬¬a` from `a`), plain function application
    /// (`fun a ha hna => hna ha`).
    pub not_not_intro: NameId,
    /// `noncontradiction : Π (a : Prop), And a (a → False) → False` —
    /// `¬(a ∧ ¬a)`, built from [`Self::and_left`]/[`Self::and_right`].
    pub noncontradiction: NameId,
    /// `not_not_not : Π (a : Prop), (((a → False) → False) → False) → a → False`
    /// — the triple-negation collapse `¬¬¬a → ¬a`. Constructively valid (unlike
    /// its non-existent inverse `¬a → ¬¬¬a`'s converse `¬¬a → a`, which is
    /// exactly [`Self::dne_of_em`]'s non-constructive hypothesis): built from
    /// [`Self::not_not_intro`] composed with the given `¬¬¬a`.
    pub not_not_not: NameId,
    /// `demorgan_not_or : Π (a b : Prop), (Or a b → False) → And (a → False) (b → False)`
    /// — `¬(a ∨ b) → ¬a ∧ ¬b`, one of the three intuitionistically valid De
    /// Morgan directions (see the module doc for the one that is not).
    pub demorgan_not_or: NameId,
    /// `demorgan_not_or_converse : Π (a b : Prop), And (a → False) (b → False) → (Or a b → False)`
    /// — the converse `¬a ∧ ¬b → ¬(a ∨ b)`, built from [`Self::or_elim`].
    pub demorgan_not_or_converse: NameId,
    /// `demorgan_or_not_and : Π (a b : Prop), Or (a → False) (b → False) → (And a b → False)`
    /// — `¬a ∨ ¬b → ¬(a ∧ b)`, built from [`Self::or_elim`] and
    /// [`Self::and_left`]/[`Self::and_right`]. The converse of this one,
    /// `¬(a ∧ b) → ¬a ∨ ¬b`, is the De Morgan direction that is **not**
    /// intuitionistically valid (module doc) and is deliberately not declared.
    pub demorgan_or_not_and: NameId,
    /// `not_not_em : Π (p : Prop), ((Or p (p → False)) → False) → False` —
    /// `¬¬(p ∨ ¬p)`, excluded middle's double negation, provable outright in
    /// intuitionistic logic with no classical hypothesis: refute `¬(p ∨ ¬p)`
    /// by building `¬p` from it (any `p` gives `p ∨ ¬p` via `Or.inl`) and then
    /// closing with `Or.inr` on that very `¬p`. The route [`Self::em_of_dne`]
    /// uses to derive excluded middle from double-negation elimination.
    pub not_not_em: NameId,
    /// `dne_of_em : Π (em : Π (p : Prop), Or p (p → False)), Π (p : Prop), (((p → False) → False) → p)`
    /// — excluded middle implies double-negation elimination: case-split on
    /// `em p` via [`Self::or_elim`], the `p` branch is immediate and the `¬p`
    /// branch is refuted by the given `¬¬p`.
    pub dne_of_em: NameId,
    /// `em_of_dne : Π (dne : Π (p : Prop), (((p → False) → False) → p)), Π (p : Prop), Or p (p → False)`
    /// — double-negation elimination implies excluded middle: apply `dne` to
    /// `Or p (p → False)` itself, discharging its `¬¬(p ∨ ¬p)` hypothesis with
    /// [`Self::not_not_em`]. Together with [`Self::dne_of_em`] this is the
    /// headline result — the classical principle and its converse are
    /// interderivable *theorems* of this intuitionistic kernel; neither
    /// principle itself is declared or assumed.
    pub em_of_dne: NameId,
    /// `peirce_of_em : Π (em : Π (p : Prop), Or p (p → False)), Π (a b : Prop), (((a → b) → a) → a)`
    /// — excluded middle implies Peirce's law: case-split on `em a`, the `a`
    /// branch is immediate and the `¬a` branch builds the needed `a → b` by ex
    /// falso before applying the hypothesis.
    pub peirce_of_em: NameId,
    /// `em_of_peirce : Π (peirce : Π (a b : Prop), (((a → b) → a) → a)), Π (p : Prop), Or p (p → False)`
    /// — Peirce's law implies excluded middle: instantiate `peirce` at
    /// `(Or p (p → False), False)`, discharging the resulting
    /// `(Or p (p → False) → False) → Or p (p → False)` hypothesis with the same
    /// `Or.inr`-from-refuted-`Or.inl` construction as [`Self::not_not_em`].
    pub em_of_peirce: NameId,

    /// `not_not_not_intro : Π (a : Prop), (a → False) → ¬¬¬a` — the other
    /// half of the `¬¬¬a ↔ ¬a` pair ([`Self::not_not_not`] is `¬¬¬a → ¬a`):
    /// [`Self::not_not_intro`] instantiated at `¬a` itself.
    pub not_not_not_intro: NameId,
    /// `not_not_and : Π (a b : Prop), ¬¬a → ¬¬b → ¬¬(And a b)` — the
    /// conjunction case of the Gödel–Gentzen negative translation.
    pub not_not_and: NameId,
    /// `not_not_imp : Π (a b : Prop), (a → b) → ¬¬a → ¬¬b` — functoriality
    /// (equivalently, monotonicity) of double negation.
    pub not_not_imp: NameId,

    /// `Bool.false_ne_true : Eq Bool Bool.false Bool.true → False` — Bool's
    /// disjointness discriminator, built by transporting `True.intro`
    /// through a type-valued `Bool.rec` discriminator along a hypothetical
    /// `false = true`. The prerequisite for [`Self::of_decide_eq_true`]/
    /// [`Self::of_decide_eq_false`] to rule out the impossible branch of a
    /// computed `Bool`.
    pub bool_false_ne_true: NameId,
    /// `Bool.true_ne_false : Eq Bool Bool.true Bool.false → False` — the
    /// mirror image of [`Self::bool_false_ne_true`], via [`Self::eq_symm`].
    pub bool_true_ne_false: NameId,

    /// `Decidable.{0} (p : Prop) : Type` — the `Type`-valued decision.
    /// Unlike `Or` (a two-constructor `Prop` that eliminates only into
    /// `Prop`), `Decidable` lives at `Sort 1` and its recursor eliminates
    /// into an arbitrary `Sort v` ([`Self::decidable_by_cases`]).
    pub decidable: NameId,
    /// `Decidable.isFalse : Π (p : Prop) (h : p → False), Decidable p`.
    pub decidable_is_false: NameId,
    /// `Decidable.isTrue : Π (p : Prop) (h : p), Decidable p`.
    pub decidable_is_true: NameId,
    /// `Decidable.rec` — the `Decidable` eliminator; unlike `Or.rec`, this
    /// one carries a genuine elimination-level parameter.
    pub decidable_rec: NameId,
    /// `Decidable.decide : Π (p : Prop), Decidable p → Bool` — a
    /// [`Declaration::Definition`] (its codomain `Bool` is not `Prop`, the
    /// same reason [`Self::absurd`] is a `Definition`). The missing
    /// abstraction under `Nat.ble`/`Rat.ble`/`Char.beq`/`Str.beq`'s four
    /// independent hand-rolled decision procedures.
    pub decide: NameId,
    /// `Decidable.of_decide_eq_true : Π (p : Prop) (d : Decidable p), Eq Bool
    /// (decide p d) Bool.true → p` — one spec direction tying `decide` to
    /// `p`: a `Decidable` witness that computed `true` proves `p`.
    pub of_decide_eq_true: NameId,
    /// `Decidable.of_decide_eq_false : Π (p : Prop) (d : Decidable p), Eq
    /// Bool (decide p d) Bool.false → (p → False)` — the other spec
    /// direction: a witness that computed `false` refutes `p`.
    pub of_decide_eq_false: NameId,
    /// `Decidable.em : Π (p : Prop), Decidable p → Or p (p → False)` —
    /// excluded middle exactly where a decision procedure exists, and
    /// nowhere else: the point of the whole `Decidable` design.
    pub decidable_em: NameId,
    /// `Decidable.byCases.{v} : Π (p : Prop) (C : Sort v) (d : Decidable p),
    /// (p → C) → ((p → False) → C) → C` — a [`Declaration::Definition`]
    /// (codomain an arbitrary `Sort v`, not `Prop`, like [`Self::decide`]).
    /// Case-split with a `Type`-valued result, exactly what `Or.rec`
    /// structurally cannot offer.
    pub decidable_by_cases: NameId,
    /// The universe parameter `v` of [`Self::decidable_by_cases`].
    pub decidable_by_cases_vparam: NameId,
    /// `DecidablePred.{u} : Π (α : Sort u) (p : α → Prop), Sort (max u 1)` —
    /// Mathlib's `DecidablePred`, `fun α p => Π (a : α), Decidable (p a)`,
    /// with `α` explicit because this kernel has no instance implicits. A
    /// [`Declaration::Definition`] like [`Self::decide`]. This is the
    /// vocabulary a Mathlib statement quantifying over a decidable predicate
    /// needs before it can be STATED here at all; `Nat.findGreatest`
    /// (`nat_prelude/find_greatest.rs`) is its first consumer.
    pub decidable_pred: NameId,
    /// The universe parameter `u` of [`Self::decidable_pred`].
    pub decidable_pred_uparam: NameId,
    /// `Decidable.ofBool : Π (p : Prop) (b : Bool), (Eq Bool b Bool.true → p) →
    /// (Eq Bool b Bool.false → (p → False)) → Decidable p` — the bridge from a
    /// computed `Bool` plus its two spec directions to a `Decidable` witness:
    /// the leverage that turns each of `Nat.ble`/`Rat.ble`/`Char.beq`/
    /// `Str.beq`'s independent hand-rolled decision procedures into a
    /// one-line instance. A [`Declaration::Definition`] like [`Self::decide`]
    /// (codomain `Decidable p : Sort 1`, not `Prop`), built by `Bool.rec.{1}`
    /// on `b` — each branch is closed by instantiating its own live
    /// hypothesis at `Eq.refl`, not by ruling out an impossible one (unlike
    /// [`Self::of_decide_eq_true`]/[`Self::of_decide_eq_false`], which case
    /// on a *fixed* `decide` result and must discharge the impossible branch
    /// with [`Self::bool_false_ne_true`]/[`Self::bool_true_ne_false`]).
    pub decidable_of_bool: NameId,
    /// `Decidable.and : Π (p q : Prop), Decidable p → Decidable q →
    /// Decidable (And p q)` — closes `Decidable` under conjunction, built by
    /// nested `Decidable.rec.{1}` case-splits on `dp` then `dq`.
    pub decidable_and: NameId,
    /// `Decidable.or : Π (p q : Prop), Decidable p → Decidable q →
    /// Decidable (Or p q)` — closes `Decidable` under disjunction, the same
    /// nested-case-split shape as [`Self::decidable_and`], refuting the
    /// `¬p ∧ ¬q` branch via [`Self::or_elim`].
    pub decidable_or: NameId,
    /// `Decidable.not : Π (p : Prop), Decidable p → Decidable (p → False)` —
    /// closes `Decidable` under negation by swapping the two `Decidable.rec`
    /// branches.
    pub decidable_not: NameId,
    /// `Decidable.decide_eq_true_iff : Π (p : Prop) (d : Decidable p),
    /// Iff (Eq Bool (decide p d) Bool.true) p` — packages
    /// [`Self::of_decide_eq_true`] (the `Iff.mp` direction) together with a
    /// `Decidable.rec` case-split proving the converse (`Iff.mpr`): the
    /// `isTrue` branch is `Eq.refl` after `decide` ι-reduces, the `isFalse`
    /// branch is ex falso from the given `h : p` against the constructor's
    /// own refutation.
    pub decidable_decide_eq_true_iff: NameId,

    /// `Bool : Type` (`Sort 1`) — the **computational** two-element type, a
    /// nullary enum `Bool.false | Bool.true`, in official Lean order. This is
    /// *not* the `Prop`-valued
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

fn apply_all(kernel: &mut Kernel, mut function: ExprId, arguments: &[ExprId]) -> ExprId {
    for &argument in arguments {
        function = kernel.app(function, argument);
    }
    function
}

/// `Eq.{u_lvl} alpha x y`, i.e. `x = y` at the carrier `alpha : Sort u_lvl`.
fn eq_app(
    kernel: &mut Kernel,
    eq: NameId,
    u_lvl: LevelId,
    alpha: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let e = kernel.const_(eq, vec![u_lvl]);
    apply_all(kernel, e, &[alpha, x, y])
}

fn lam_fvar(kernel: &mut Kernel, fvar: u64, ty: ExprId, body: ExprId, info: BinderInfo) -> ExprId {
    let body = kernel.abstract_fvars(body, &[fvar]);
    let anon = kernel.anon();
    kernel.lam(anon, ty, body, info)
}

fn pi_fvar(kernel: &mut Kernel, fvar: u64, ty: ExprId, body: ExprId, info: BinderInfo) -> ExprId {
    let body = kernel.abstract_fvars(body, &[fvar]);
    let anon = kernel.anon();
    kernel.pi(anon, ty, body, info)
}

/// Declare the standard logical prelude into `kernel`'s environment, returning
/// the [`LogicPrelude`] of interned names.
///
/// Each declaration is admitted through the **trusted** gates
/// ([`Kernel::add_inductive`] / [`Kernel::add_declaration`]), which type-check
/// it. On success the environment contains
/// `True`/`False`/`And`/`Or`/`Iff`/`Eq` (with their constructors and recursors)
/// and the `Not` definition.
///
/// Repeated construction validates and returns the exact registered package.
/// Any trusted-gate rejection is returned as [`KernelError`] and rolls back all
/// declarations admitted by this invocation.
///
/// # Errors
///
/// Returns the trusted gate's rejection or an exact-package conflict. A failed
/// first build leaves the environment unchanged.
pub fn build_logic_prelude(kernel: &mut Kernel) -> Result<LogicPrelude, KernelError> {
    if let Some(PreludeValue::Logic(prelude)) =
        crate::prelude_cache::try_restore(kernel, PreludeKey::Logic)
    {
        return Ok(prelude);
    }
    build_logic_prelude_uncached(kernel)
}

/// [`build_logic_prelude`] without the process-wide template fast path.
///
/// This is the route that actually runs the trusted gate, and the one the
/// template itself is built through (ADR-0464).
#[allow(clippy::too_many_lines)]
pub(crate) fn build_logic_prelude_uncached(
    kernel: &mut Kernel,
) -> Result<LogicPrelude, KernelError> {
    if let Some(PreludeValue::Logic(prelude)) = kernel.cached_prelude(PreludeKey::Logic)? {
        return Ok(prelude);
    }
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<LogicPrelude, KernelError> {
        let anon = kernel.anon();

        // --- True : Prop, True.intro : True ----------------------------------
        // A nullary enum in Prop: 0 params, 0 indices, one nullary constructor.
        let true_ = kernel.name_str(anon, "True");
        let true_intro = kernel.name_str(true_, "intro");
        {
            let prop = kernel.prop();
            let true_const = kernel.const_(true_, vec![]);
            // True.intro : True   (its type is just `True`, the bare inductive).
            kernel.add_inductive(true_, &[], 0, prop, &[(true_intro, true_const)])?;
        }
        let true_rec = kernel.name_str(true_, "rec");

        // --- False : Prop, no constructors -----------------------------------
        // The empty type in Prop. Its recursor `False.rec` is ex-falso.
        let false_ = kernel.name_str(anon, "False");
        {
            let prop = kernel.prop();
            kernel.add_inductive(false_, &[], 0, prop, &[])?;
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
            kernel.add_inductive(and, &[], 2, and_ty, &[(and_intro, intro_ty)])?;
        }
        let and_rec = kernel.name_str(and, "rec");

        // --- And.left / And.right : Π (a b : Prop), And a b → a / b ---------
        // Direct `And.rec` field projections: motive := the constant field
        // (`a` or `b`), minor := the matching argument of `And.intro`. The
        // same construction `int_prelude`'s private `and_left`/`and_right`
        // helpers already use, promoted here to a genuine, reusable,
        // axiom-free kernel theorem so it does not need re-deriving per
        // prelude.
        let and_left = kernel.name_str(and, "left");
        {
            let prop = kernel.prop();
            let a_fvar = 23_000;
            let b_fvar = 23_001;
            let h_fvar = 23_002;
            let pair_fvar = 23_003;
            let ha_fvar = 23_004;
            let hb_fvar = 23_005;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let and_const = kernel.const_(and, vec![]);
            let and_ab = apply_all(kernel, and_const, &[a, b]);

            // type: Π (a b : Prop), And a b → a.
            let with_h = kernel.pi(anon, and_ab, a, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, with_h, BinderInfo::Default);
            let and_left_ty = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b h => And.rec.{0} a b (fun _ => a) (fun ha hb => ha) h.
            let motive = lam_fvar(kernel, pair_fvar, and_ab, a, BinderInfo::Default);
            let minor = {
                let ha = kernel.fvar(ha_fvar);
                let inner = lam_fvar(kernel, hb_fvar, b, ha, BinderInfo::Default);
                lam_fvar(kernel, ha_fvar, a, inner, BinderInfo::Default)
            };
            let zero = kernel.level_zero();
            let and_rec_const = kernel.const_(and_rec, vec![zero]);
            let h = kernel.fvar(h_fvar);
            let applied = apply_all(kernel, and_rec_const, &[a, b, motive, minor, h]);

            let with_h_v = lam_fvar(kernel, h_fvar, and_ab, applied, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_h_v, BinderInfo::Default);
            let and_left_value = lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: and_left,
                uparams: vec![],
                ty: and_left_ty,
                value: and_left_value,
            })?;
        }
        let and_right = kernel.name_str(and, "right");
        {
            let prop = kernel.prop();
            let a_fvar = 23_100;
            let b_fvar = 23_101;
            let h_fvar = 23_102;
            let pair_fvar = 23_103;
            let ha_fvar = 23_104;
            let hb_fvar = 23_105;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let and_const = kernel.const_(and, vec![]);
            let and_ab = apply_all(kernel, and_const, &[a, b]);

            // type: Π (a b : Prop), And a b → b.
            let with_h = kernel.pi(anon, and_ab, b, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, with_h, BinderInfo::Default);
            let and_right_ty = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b h => And.rec.{0} a b (fun _ => b) (fun ha hb => hb) h.
            let motive = lam_fvar(kernel, pair_fvar, and_ab, b, BinderInfo::Default);
            let minor = {
                let hb = kernel.fvar(hb_fvar);
                let inner = lam_fvar(kernel, hb_fvar, b, hb, BinderInfo::Default);
                lam_fvar(kernel, ha_fvar, a, inner, BinderInfo::Default)
            };
            let zero = kernel.level_zero();
            let and_rec_const = kernel.const_(and_rec, vec![zero]);
            let h = kernel.fvar(h_fvar);
            let applied = apply_all(kernel, and_rec_const, &[a, b, motive, minor, h]);

            let with_h_v = lam_fvar(kernel, h_fvar, and_ab, applied, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_h_v, BinderInfo::Default);
            let and_right_value = lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: and_right,
                uparams: vec![],
                ty: and_right_ty,
                value: and_right_value,
            })?;
        }

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
            kernel.add_inductive(or, &[], 2, or_ty, &[(or_inl, inl_ty), (or_inr, inr_ty)])?;
        }
        let or_rec = kernel.name_str(or, "rec");

        // --- Or.elim : Π (a b c : Prop), Or a b → (a → c) → (b → c) → c -----
        // `Or.rec` with a constant motive `c`; since the motive is constant,
        // the minor premises are exactly the two supplied arrows themselves
        // (no wrapping needed). `Or.rec` has no elimination-universe
        // parameter (a two-constructor `Prop` eliminates only into `Prop`,
        // confirmed by `or_case_analysis_checks` in the prelude tests).
        let or_elim = kernel.name_str(or, "elim");
        {
            let prop = kernel.prop();
            let a_fvar = 23_200;
            let b_fvar = 23_201;
            let c_fvar = 23_202;
            let h_fvar = 23_203;
            let ha_fvar = 23_204;
            let hb_fvar = 23_205;
            let dummy_fvar = 23_206;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let c = kernel.fvar(c_fvar);
            let or_const = kernel.const_(or, vec![]);
            let or_ab = apply_all(kernel, or_const, &[a, b]);
            let ac = kernel.pi(anon, a, c, BinderInfo::Default); // a → c
            let bc = kernel.pi(anon, b, c, BinderInfo::Default); // b → c

            // type: Π (a b c : Prop), Or a b → (a → c) → (b → c) → c.
            let t_inner = kernel.pi(anon, bc, c, BinderInfo::Default);
            let t_mid = kernel.pi(anon, ac, t_inner, BinderInfo::Default);
            let t_outer = kernel.pi(anon, or_ab, t_mid, BinderInfo::Default);
            let with_c = pi_fvar(kernel, c_fvar, prop, t_outer, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, with_c, BinderInfo::Default);
            let or_elim_ty = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b c h ha hb => Or.rec a b (fun _ => c) ha hb h.
            let motive = lam_fvar(kernel, dummy_fvar, or_ab, c, BinderInfo::Default);
            let or_rec_const = kernel.const_(or_rec, vec![]);
            let ha = kernel.fvar(ha_fvar);
            let hb = kernel.fvar(hb_fvar);
            let h = kernel.fvar(h_fvar);
            let applied = apply_all(kernel, or_rec_const, &[a, b, motive, ha, hb, h]);

            let with_hb_v = lam_fvar(kernel, hb_fvar, bc, applied, BinderInfo::Default);
            let with_ha_v = lam_fvar(kernel, ha_fvar, ac, with_hb_v, BinderInfo::Default);
            let with_h_v = lam_fvar(kernel, h_fvar, or_ab, with_ha_v, BinderInfo::Default);
            let with_c_v = lam_fvar(kernel, c_fvar, prop, with_h_v, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_c_v, BinderInfo::Default);
            let or_elim_value = lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: or_elim,
                uparams: vec![],
                ty: or_elim_ty,
                value: or_elim_value,
            })?;
        }

        // --- Or.resolve_left / Or.resolve_right ------------------------------
        // `Or.resolve_left : Π (a b : Prop), Or a b → (a → False) → b` and its
        // mirror `Or.resolve_right`. The hypothesis is written as the plain
        // arrow `a → False` rather than `Not a` applied (matching how
        // `nat_prelude::order_extra` states its own `Not`-shaped lemmas): the
        // two are definitionally equal since `Not` unfolds to exactly this
        // arrow, and writing it directly avoids relying on delta-unfolding an
        // applied `Not` during the recursor's minor-premise type check.
        let or_resolve_left = kernel.name_str(or, "resolve_left");
        {
            let prop = kernel.prop();
            let a_fvar = 23_300;
            let b_fvar = 23_301;
            let h_fvar = 23_302;
            let na_fvar = 23_303;
            let ha_fvar = 23_304;
            let hb_fvar = 23_305;
            let dummy_fvar = 23_306;
            let false_dummy_fvar = 23_307;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let or_const = kernel.const_(or, vec![]);
            let or_ab = apply_all(kernel, or_const, &[a, b]);
            let false_const = kernel.const_(false_, vec![]);
            let na_ty = kernel.pi(anon, a, false_const, BinderInfo::Default); // a → False

            // type: Π (a b : Prop), Or a b → (a → False) → b.
            let t_inner = kernel.pi(anon, na_ty, b, BinderInfo::Default);
            let t_outer = kernel.pi(anon, or_ab, t_inner, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, t_outer, BinderInfo::Default);
            let or_resolve_left_ty = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b h na =>
            //   Or.rec a b (fun _ => b)
            //     (fun ha => False.rec.{0} (fun _ => b) (na ha))
            //     (fun hb => hb)
            //     h.
            let motive = lam_fvar(kernel, dummy_fvar, or_ab, b, BinderInfo::Default);
            let na = kernel.fvar(na_fvar);
            let minor_inl = {
                let ha = kernel.fvar(ha_fvar);
                let na_ha = kernel.app(na, ha);
                let false_motive = lam_fvar(
                    kernel,
                    false_dummy_fvar,
                    false_const,
                    b,
                    BinderInfo::Default,
                );
                let zero = kernel.level_zero();
                let false_rec_const = kernel.const_(false_rec, vec![zero]);
                let absurd_proof = apply_all(kernel, false_rec_const, &[false_motive, na_ha]);
                lam_fvar(kernel, ha_fvar, a, absurd_proof, BinderInfo::Default)
            };
            let minor_inr = {
                let hb = kernel.fvar(hb_fvar);
                lam_fvar(kernel, hb_fvar, b, hb, BinderInfo::Default)
            };
            let or_rec_const = kernel.const_(or_rec, vec![]);
            let h = kernel.fvar(h_fvar);
            let applied = apply_all(
                kernel,
                or_rec_const,
                &[a, b, motive, minor_inl, minor_inr, h],
            );

            let with_na_v = lam_fvar(kernel, na_fvar, na_ty, applied, BinderInfo::Default);
            let with_h_v = lam_fvar(kernel, h_fvar, or_ab, with_na_v, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_h_v, BinderInfo::Default);
            let or_resolve_left_value =
                lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: or_resolve_left,
                uparams: vec![],
                ty: or_resolve_left_ty,
                value: or_resolve_left_value,
            })?;
        }
        let or_resolve_right = kernel.name_str(or, "resolve_right");
        {
            let prop = kernel.prop();
            let a_fvar = 23_400;
            let b_fvar = 23_401;
            let h_fvar = 23_402;
            let nb_fvar = 23_403;
            let ha_fvar = 23_404;
            let hb_fvar = 23_405;
            let dummy_fvar = 23_406;
            let false_dummy_fvar = 23_407;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let or_const = kernel.const_(or, vec![]);
            let or_ab = apply_all(kernel, or_const, &[a, b]);
            let false_const = kernel.const_(false_, vec![]);
            let nb_ty = kernel.pi(anon, b, false_const, BinderInfo::Default); // b → False

            // type: Π (a b : Prop), Or a b → (b → False) → a.
            let t_inner = kernel.pi(anon, nb_ty, a, BinderInfo::Default);
            let t_outer = kernel.pi(anon, or_ab, t_inner, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, t_outer, BinderInfo::Default);
            let or_resolve_right_ty = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b h nb =>
            //   Or.rec a b (fun _ => a)
            //     (fun ha => ha)
            //     (fun hb => False.rec.{0} (fun _ => a) (nb hb))
            //     h.
            let motive = lam_fvar(kernel, dummy_fvar, or_ab, a, BinderInfo::Default);
            let nb = kernel.fvar(nb_fvar);
            let minor_inl = {
                let ha = kernel.fvar(ha_fvar);
                lam_fvar(kernel, ha_fvar, a, ha, BinderInfo::Default)
            };
            let minor_inr = {
                let hb = kernel.fvar(hb_fvar);
                let nb_hb = kernel.app(nb, hb);
                let false_motive = lam_fvar(
                    kernel,
                    false_dummy_fvar,
                    false_const,
                    a,
                    BinderInfo::Default,
                );
                let zero = kernel.level_zero();
                let false_rec_const = kernel.const_(false_rec, vec![zero]);
                let absurd_proof = apply_all(kernel, false_rec_const, &[false_motive, nb_hb]);
                lam_fvar(kernel, hb_fvar, b, absurd_proof, BinderInfo::Default)
            };
            let or_rec_const = kernel.const_(or_rec, vec![]);
            let h = kernel.fvar(h_fvar);
            let applied = apply_all(
                kernel,
                or_rec_const,
                &[a, b, motive, minor_inl, minor_inr, h],
            );

            let with_nb_v = lam_fvar(kernel, nb_fvar, nb_ty, applied, BinderInfo::Default);
            let with_h_v = lam_fvar(kernel, h_fvar, or_ab, with_nb_v, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_h_v, BinderInfo::Default);
            let or_resolve_right_value =
                lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: or_resolve_right,
                uparams: vec![],
                ty: or_resolve_right_ty,
                value: or_resolve_right_value,
            })?;
        }

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
            kernel.add_inductive(iff, &[], 2, iff_ty, &[(iff_intro, intro_ty)])?;
        }
        let iff_rec = kernel.name_str(iff, "rec");

        // --- Iff.mp / Iff.mpr : Π (a b : Prop), Iff a b → a → b / b → a -----
        // `Iff` is a single-constructor `Prop` (like `And`), so `Iff.rec`
        // admits the same constant-motive projection trick as
        // `And.left`/`And.right`: motive := the arrow itself, minor := the
        // matching field of `Iff.intro`. The result of applying `Iff.rec`
        // already has the arrow type, so — exactly as with `And.left` — no
        // extra binder for the hypothesis of type `a` (resp. `b`) is needed.
        let iff_mp = kernel.name_str(iff, "mp");
        {
            let prop = kernel.prop();
            let a_fvar = 23_500;
            let b_fvar = 23_501;
            let h_fvar = 23_502;
            let pair_fvar = 23_503;
            let mp_fvar = 23_504;
            let mpr_fvar = 23_505;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let iff_const = kernel.const_(iff, vec![]);
            let iff_ab = apply_all(kernel, iff_const, &[a, b]);
            let ab_arrow = kernel.pi(anon, a, b, BinderInfo::Default); // a → b
            let ba_arrow = kernel.pi(anon, b, a, BinderInfo::Default); // b → a

            // type: Π (a b : Prop), Iff a b → a → b.
            let with_h = kernel.pi(anon, iff_ab, ab_arrow, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, with_h, BinderInfo::Default);
            let iff_mp_ty = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b h => Iff.rec.{0} a b (fun _ => a → b) (fun mp mpr => mp) h.
            let motive = lam_fvar(kernel, pair_fvar, iff_ab, ab_arrow, BinderInfo::Default);
            let minor = {
                let mp = kernel.fvar(mp_fvar);
                let inner = lam_fvar(kernel, mpr_fvar, ba_arrow, mp, BinderInfo::Default);
                lam_fvar(kernel, mp_fvar, ab_arrow, inner, BinderInfo::Default)
            };
            let zero = kernel.level_zero();
            let iff_rec_const = kernel.const_(iff_rec, vec![zero]);
            let h = kernel.fvar(h_fvar);
            let applied = apply_all(kernel, iff_rec_const, &[a, b, motive, minor, h]);

            let with_h_v = lam_fvar(kernel, h_fvar, iff_ab, applied, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_h_v, BinderInfo::Default);
            let iff_mp_value = lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: iff_mp,
                uparams: vec![],
                ty: iff_mp_ty,
                value: iff_mp_value,
            })?;
        }
        let iff_mpr = kernel.name_str(iff, "mpr");
        {
            let prop = kernel.prop();
            let a_fvar = 23_510;
            let b_fvar = 23_511;
            let h_fvar = 23_512;
            let pair_fvar = 23_513;
            let mp_fvar = 23_514;
            let mpr_fvar = 23_515;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let iff_const = kernel.const_(iff, vec![]);
            let iff_ab = apply_all(kernel, iff_const, &[a, b]);
            let ab_arrow = kernel.pi(anon, a, b, BinderInfo::Default); // a → b
            let ba_arrow = kernel.pi(anon, b, a, BinderInfo::Default); // b → a

            // type: Π (a b : Prop), Iff a b → b → a.
            let with_h = kernel.pi(anon, iff_ab, ba_arrow, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, with_h, BinderInfo::Default);
            let iff_mpr_ty = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b h => Iff.rec.{0} a b (fun _ => b → a) (fun mp mpr => mpr) h.
            let motive = lam_fvar(kernel, pair_fvar, iff_ab, ba_arrow, BinderInfo::Default);
            let minor = {
                let mpr = kernel.fvar(mpr_fvar);
                let inner = lam_fvar(kernel, mpr_fvar, ba_arrow, mpr, BinderInfo::Default);
                lam_fvar(kernel, mp_fvar, ab_arrow, inner, BinderInfo::Default)
            };
            let zero = kernel.level_zero();
            let iff_rec_const = kernel.const_(iff_rec, vec![zero]);
            let h = kernel.fvar(h_fvar);
            let applied = apply_all(kernel, iff_rec_const, &[a, b, motive, minor, h]);

            let with_h_v = lam_fvar(kernel, h_fvar, iff_ab, applied, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_h_v, BinderInfo::Default);
            let iff_mpr_value = lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: iff_mpr,
                uparams: vec![],
                ty: iff_mpr_ty,
                value: iff_mpr_value,
            })?;
        }

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
            kernel.add_inductive(eq, &[eq_uparam], 2, eq_ty, &[(eq_refl, refl_ty)])?;
        }
        let eq_rec = kernel.name_str(eq, "rec");

        // --- Eq.symm.{u} : Π (α : Sort u) (a b : α), Eq α a b → Eq α b a -----
        // `motive := fun (x : α) (_ : Eq α a x) => Eq α x a`; `Eq.rec` at the
        // refl case `Eq.refl α a : Eq α a a` transported along `h : Eq α a b`
        // gives `Eq α b a`. The standard symmetry proof, universe-polymorphic.
        let eq_symm = kernel.name_str(eq, "symm");
        {
            let u_lvl = kernel.level_param(eq_uparam);
            let sort_u = kernel.sort(u_lvl);
            let zero_lvl = kernel.level_zero();

            let alpha_fvar = 22_000;
            let a_fvar = 22_001;
            let b_fvar = 22_002;
            let h_fvar = 22_003;
            let x_fvar = 22_004;
            let alpha = kernel.fvar(alpha_fvar);
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let x = kernel.fvar(x_fvar);

            let ab_eq = eq_app(kernel, eq, u_lvl, alpha, a, b);
            let ba_eq = eq_app(kernel, eq, u_lvl, alpha, b, a);

            // --- type: Π (α : Sort u) (a b : α), Eq α a b → Eq α b a --------
            let with_h = kernel.pi(anon, ab_eq, ba_eq, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, alpha, with_h, BinderInfo::Default);
            let with_a = pi_fvar(kernel, a_fvar, alpha, with_b, BinderInfo::Default);
            let symm_ty = pi_fvar(kernel, alpha_fvar, sort_u, with_a, BinderInfo::Implicit);

            // --- value --------------------------------------------------------
            // motive := fun (x : α) (_ : Eq α a x) => Eq α x a   [a, x free here]
            let a_x_eq = eq_app(kernel, eq, u_lvl, alpha, a, x);
            let x_a_eq = eq_app(kernel, eq, u_lvl, alpha, x, a);
            let motive_inner = kernel.lam(anon, a_x_eq, x_a_eq, BinderInfo::Default);
            let motive = lam_fvar(kernel, x_fvar, alpha, motive_inner, BinderInfo::Default);

            let eq_refl_const = kernel.const_(eq_refl, vec![u_lvl]);
            let refl_case = apply_all(kernel, eq_refl_const, &[alpha, a]);

            let eq_rec_const = kernel.const_(eq_rec, vec![zero_lvl, u_lvl]);
            let h = kernel.fvar(h_fvar);
            let applied = apply_all(kernel, eq_rec_const, &[alpha, a, motive, refl_case, b, h]);

            let with_h = lam_fvar(kernel, h_fvar, ab_eq, applied, BinderInfo::Default);
            let with_b = lam_fvar(kernel, b_fvar, alpha, with_h, BinderInfo::Default);
            let with_a = lam_fvar(kernel, a_fvar, alpha, with_b, BinderInfo::Default);
            let symm_value = lam_fvar(kernel, alpha_fvar, sort_u, with_a, BinderInfo::Implicit);

            kernel.add_declaration(Declaration::Theorem {
                name: eq_symm,
                uparams: vec![eq_uparam],
                ty: symm_ty,
                value: symm_value,
            })?;
        }

        // --- congrFun'.{u,v} : Π (α : Sort u) (β : Sort v) (f g : α → β), --
        //     Eq.{imax u v} (α → β) f g → Π (a : α), Eq.{v} β (f a) (g a) ----
        // The non-dependent function-congruence lemma, built the same way
        // `Eq.symm` above is: `Eq.rec` transports the trivial
        // `Eq.refl β (f a) : Eq β (f a) (f a)` along `h : Eq (α → β) f g`
        // into `Eq β (f a) (g a)`, via the motive
        // `fun (g' : α → β) (_ : Eq (α → β) f g') => Eq β (f a) (g' a)`.
        // `α → β`'s own sort is `imax u v` (the kernel's Pi-formation rule,
        // `tc.rs::infer_pi`), matching Lean's own convention; `Eq` itself is
        // always `Prop`-valued regardless of the carrier's universe, so the
        // elimination (motive) level is always `0`, exactly as in `Eq.symm`.
        let congr_fun_prime = kernel.name_str(anon, "congrFun'");
        {
            let u_name = kernel.name_str(anon, "u");
            let v_name = kernel.name_str(anon, "v");
            let u_lvl = kernel.level_param(u_name);
            let v_lvl = kernel.level_param(v_name);
            let sort_u = kernel.sort(u_lvl);
            let sort_v = kernel.sort(v_lvl);
            let imax_uv = kernel.level_imax(u_lvl, v_lvl);
            let zero = kernel.level_zero();

            let alpha_fvar = 23_600;
            let beta_fvar = 23_601;
            let f_fvar = 23_602;
            let g_fvar = 23_603;
            let h_fvar = 23_604;
            let a_pt_fvar = 23_605;
            let gprime_fvar = 23_606;
            let heq_dummy_fvar = 23_607;

            let alpha = kernel.fvar(alpha_fvar);
            let beta = kernel.fvar(beta_fvar);
            let arrow_ab = kernel.pi(anon, alpha, beta, BinderInfo::Default); // α → β
            let f = kernel.fvar(f_fvar);
            let g = kernel.fvar(g_fvar);
            let eq_const_imax = kernel.const_(eq, vec![imax_uv]);
            let hyp_ty = apply_all(kernel, eq_const_imax, &[arrow_ab, f, g]); // Eq (α→β) f g

            let a_pt = kernel.fvar(a_pt_fvar);
            let f_a = kernel.app(f, a_pt);
            let g_a = kernel.app(g, a_pt);
            let eq_const_v = kernel.const_(eq, vec![v_lvl]);
            let concl = apply_all(kernel, eq_const_v, &[beta, f_a, g_a]); // Eq β (f a) (g a)

            // type: Π (α β) (f g : α→β) (h : hyp_ty) (a : α), concl.
            let with_a = pi_fvar(kernel, a_pt_fvar, alpha, concl, BinderInfo::Default);
            let with_h = kernel.pi(anon, hyp_ty, with_a, BinderInfo::Default);
            let with_g = pi_fvar(kernel, g_fvar, arrow_ab, with_h, BinderInfo::Default);
            let with_f = pi_fvar(kernel, f_fvar, arrow_ab, with_g, BinderInfo::Default);
            let with_beta = pi_fvar(kernel, beta_fvar, sort_v, with_f, BinderInfo::Default);
            let congr_fun_ty = pi_fvar(kernel, alpha_fvar, sort_u, with_beta, BinderInfo::Implicit);

            // value: fun α β f g h a =>
            //   Eq.rec.{0,imax u v} (α→β) f
            //     (fun g' (_ : Eq (α→β) f g') => Eq β (f a) (g' a))
            //     (Eq.refl β (f a))
            //     g h.
            let eq_refl_const_v = kernel.const_(eq_refl, vec![v_lvl]);
            let refl_case = apply_all(kernel, eq_refl_const_v, &[beta, f_a]);

            let gprime = kernel.fvar(gprime_fvar);
            let gprime_a = kernel.app(gprime, a_pt);
            let eq_const_v2 = kernel.const_(eq, vec![v_lvl]);
            let motive_body = apply_all(kernel, eq_const_v2, &[beta, f_a, gprime_a]);
            let eq_const_imax2 = kernel.const_(eq, vec![imax_uv]);
            let hyp_ty_g = apply_all(kernel, eq_const_imax2, &[arrow_ab, f, gprime]);
            let motive_inner = lam_fvar(
                kernel,
                heq_dummy_fvar,
                hyp_ty_g,
                motive_body,
                BinderInfo::Default,
            );
            let motive = lam_fvar(
                kernel,
                gprime_fvar,
                arrow_ab,
                motive_inner,
                BinderInfo::Default,
            );

            let eq_rec_const = kernel.const_(eq_rec, vec![zero, imax_uv]);
            let h = kernel.fvar(h_fvar);
            let applied = apply_all(
                kernel,
                eq_rec_const,
                &[arrow_ab, f, motive, refl_case, g, h],
            );

            let with_a_v = lam_fvar(kernel, a_pt_fvar, alpha, applied, BinderInfo::Default);
            let with_h_v = lam_fvar(kernel, h_fvar, hyp_ty, with_a_v, BinderInfo::Default);
            let with_g_v = lam_fvar(kernel, g_fvar, arrow_ab, with_h_v, BinderInfo::Default);
            let with_f_v = lam_fvar(kernel, f_fvar, arrow_ab, with_g_v, BinderInfo::Default);
            let with_beta_v = lam_fvar(kernel, beta_fvar, sort_v, with_f_v, BinderInfo::Default);
            let congr_fun_value = lam_fvar(
                kernel,
                alpha_fvar,
                sort_u,
                with_beta_v,
                BinderInfo::Implicit,
            );

            kernel.add_declaration(Declaration::Theorem {
                name: congr_fun_prime,
                uparams: vec![u_name, v_name],
                ty: congr_fun_ty,
                value: congr_fun_value,
            })?;
        }

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
            kernel.add_inductive(
                exists_,
                &[exists_uparam],
                2,
                exists_ty,
                &[(exists_intro, intro_ty)],
            )?;
        }
        let exists_rec = kernel.name_str(exists_, "rec");

        // --- Acc.{u} {α} (r : α → α → Prop) : α → Prop ---------------------
        // Two parameters (`α`, `r`), one index, and one constructor whose
        // higher-order recursive field exercises ADR-0353's general rule.
        let acc_uparam = kernel.name_str(anon, "u");
        let acc = kernel.name_str(anon, "Acc");
        let acc_intro = kernel.name_str(acc, "intro");
        {
            let u_lvl = kernel.level_param(acc_uparam);
            let sort_u = kernel.sort(u_lvl);
            let prop = kernel.prop();
            let acc_const = kernel.const_(acc, vec![u_lvl]);

            // Under `α`, the relation type is `α → α → Prop`.
            let relation_ty = {
                let alpha0 = kernel.bvar(0);
                let alpha1 = kernel.bvar(1);
                let inner = kernel.pi(anon, alpha1, prop, BinderInfo::Default);
                kernel.pi(anon, alpha0, inner, BinderInfo::Default)
            };
            let acc_ty = {
                // Under `α, r`, the index has type `α` = BVar 1.
                let alpha1 = kernel.bvar(1);
                let indexed = kernel.pi(anon, alpha1, prop, BinderInfo::Default);
                let with_relation = kernel.pi(anon, relation_ty, indexed, BinderInfo::Default);
                kernel.pi(anon, sort_u, with_relation, BinderInfo::Implicit)
            };

            // intro : ∀ {α} r x, (∀ y, r y x → Acc r y) → Acc r x.
            let intro_ty = {
                // Field `h`, under `α, r, x`.
                let recursive_field = {
                    let alpha2 = kernel.bvar(2);
                    // Under `α, r, x, y`: r=BVar 2, x=BVar 1, y=BVar 0.
                    let relation2 = kernel.bvar(2);
                    let y0 = kernel.bvar(0);
                    let x1 = kernel.bvar(1);
                    let ry = kernel.app(relation2, y0);
                    let ryx = kernel.app(ry, x1);
                    // Under the relation proof: α=BVar 4, r=BVar 3, y=BVar 1.
                    let alpha4 = kernel.bvar(4);
                    let relation3 = kernel.bvar(3);
                    let y1 = kernel.bvar(1);
                    let recursive_result = {
                        let expression = kernel.app(acc_const, alpha4);
                        let expression = kernel.app(expression, relation3);
                        kernel.app(expression, y1)
                    };
                    let with_relation_proof =
                        kernel.pi(anon, ryx, recursive_result, BinderInfo::Default);
                    kernel.pi(anon, alpha2, with_relation_proof, BinderInfo::Default)
                };
                // Result under `α, r, x, h`: Acc α r x.
                let result = {
                    let alpha3 = kernel.bvar(3);
                    let relation2 = kernel.bvar(2);
                    let x1 = kernel.bvar(1);
                    let expression = kernel.app(acc_const, alpha3);
                    let expression = kernel.app(expression, relation2);
                    kernel.app(expression, x1)
                };
                let with_recursive = kernel.pi(anon, recursive_field, result, BinderInfo::Default);
                // Under `α, r`, x : α = BVar 1.
                let alpha1 = kernel.bvar(1);
                let with_index = kernel.pi(anon, alpha1, with_recursive, BinderInfo::Default);
                let with_relation = kernel.pi(anon, relation_ty, with_index, BinderInfo::Default);
                kernel.pi(anon, sort_u, with_relation, BinderInfo::Implicit)
            };
            kernel.add_inductive(acc, &[acc_uparam], 2, acc_ty, &[(acc_intro, intro_ty)])?;
        }
        let acc_rec = kernel.name_str(acc, "rec");
        let acc_inv = kernel.name_str(acc, "inv");
        {
            let u_lvl = kernel.level_param(acc_uparam);
            let zero_lvl = kernel.level_zero();
            let sort_u = kernel.sort(u_lvl);
            let prop = kernel.prop();
            let acc_const = kernel.const_(acc, vec![u_lvl]);

            let alpha_fvar = 19_000;
            let relation_fvar = 19_001;
            let source_fvar = 19_002;
            let predecessor_fvar = 19_003;
            let accessible_fvar = 19_004;
            let related_fvar = 19_005;
            let alpha = kernel.fvar(alpha_fvar);
            let relation = kernel.fvar(relation_fvar);
            let source = kernel.fvar(source_fvar);
            let predecessor = kernel.fvar(predecessor_fvar);
            let accessible = kernel.fvar(accessible_fvar);
            let related = kernel.fvar(related_fvar);

            let relation_left_fvar = 19_006;
            let relation_right_fvar = 19_007;
            let relation_ty = {
                let right = pi_fvar(
                    kernel,
                    relation_right_fvar,
                    alpha,
                    prop,
                    BinderInfo::Default,
                );
                pi_fvar(
                    kernel,
                    relation_left_fvar,
                    alpha,
                    right,
                    BinderInfo::Default,
                )
            };
            let accessible_source = apply_all(kernel, acc_const, &[alpha, relation, source]);
            let predecessor_relation = apply_all(kernel, relation, &[predecessor, source]);
            let accessible_predecessor =
                apply_all(kernel, acc_const, &[alpha, relation, predecessor]);
            let theorem_ty = {
                let with_related = pi_fvar(
                    kernel,
                    related_fvar,
                    predecessor_relation,
                    accessible_predecessor,
                    BinderInfo::Default,
                );
                let with_accessible = pi_fvar(
                    kernel,
                    accessible_fvar,
                    accessible_source,
                    with_related,
                    BinderInfo::Default,
                );
                let with_predecessor = pi_fvar(
                    kernel,
                    predecessor_fvar,
                    alpha,
                    with_accessible,
                    BinderInfo::Implicit,
                );
                let with_source = pi_fvar(
                    kernel,
                    source_fvar,
                    alpha,
                    with_predecessor,
                    BinderInfo::Implicit,
                );
                let with_relation = pi_fvar(
                    kernel,
                    relation_fvar,
                    relation_ty,
                    with_source,
                    BinderInfo::Implicit,
                );
                pi_fvar(
                    kernel,
                    alpha_fvar,
                    sort_u,
                    with_relation,
                    BinderInfo::Implicit,
                )
            };

            // motive := fun x (_ : Acc r x) => forall y, r y x -> Acc r y.
            let motive_source_fvar = 19_008;
            let motive_accessible_fvar = 19_009;
            let motive_predecessor_fvar = 19_010;
            let motive_related_fvar = 19_011;
            let motive_source = kernel.fvar(motive_source_fvar);
            let motive_predecessor = kernel.fvar(motive_predecessor_fvar);
            let motive_accessible_ty =
                apply_all(kernel, acc_const, &[alpha, relation, motive_source]);
            let motive_relation = apply_all(kernel, relation, &[motive_predecessor, motive_source]);
            let motive_result =
                apply_all(kernel, acc_const, &[alpha, relation, motive_predecessor]);
            let motive_with_related = pi_fvar(
                kernel,
                motive_related_fvar,
                motive_relation,
                motive_result,
                BinderInfo::Default,
            );
            let motive_with_predecessor = pi_fvar(
                kernel,
                motive_predecessor_fvar,
                alpha,
                motive_with_related,
                BinderInfo::Default,
            );
            let motive_with_accessible = lam_fvar(
                kernel,
                motive_accessible_fvar,
                motive_accessible_ty,
                motive_with_predecessor,
                BinderInfo::Default,
            );
            let motive = lam_fvar(
                kernel,
                motive_source_fvar,
                alpha,
                motive_with_accessible,
                BinderInfo::Default,
            );

            // minor := fun _ field _ y h => field y h.
            let minor_source_fvar = 19_012;
            let minor_field_fvar = 19_013;
            let minor_ih_fvar = 19_014;
            let minor_predecessor_fvar = 19_015;
            let minor_related_fvar = 19_016;
            let minor_source = kernel.fvar(minor_source_fvar);
            let minor_predecessor = kernel.fvar(minor_predecessor_fvar);
            let minor_related = kernel.fvar(minor_related_fvar);
            let minor_relation = apply_all(kernel, relation, &[minor_predecessor, minor_source]);
            let minor_field_ty = {
                let field_predecessor_fvar = 19_017;
                let field_related_fvar = 19_018;
                let field_predecessor = kernel.fvar(field_predecessor_fvar);
                let field_relation =
                    apply_all(kernel, relation, &[field_predecessor, minor_source]);
                let field_result =
                    apply_all(kernel, acc_const, &[alpha, relation, field_predecessor]);
                let with_related = pi_fvar(
                    kernel,
                    field_related_fvar,
                    field_relation,
                    field_result,
                    BinderInfo::Default,
                );
                pi_fvar(
                    kernel,
                    field_predecessor_fvar,
                    alpha,
                    with_related,
                    BinderInfo::Default,
                )
            };
            let minor_field = kernel.fvar(minor_field_fvar);
            let ih_ty = {
                let ih_predecessor_fvar = 19_019;
                let ih_related_fvar = 19_020;
                let ih_predecessor = kernel.fvar(ih_predecessor_fvar);
                let ih_related = kernel.fvar(ih_related_fvar);
                let field_accessible =
                    apply_all(kernel, minor_field, &[ih_predecessor, ih_related]);
                let ih_result = apply_all(kernel, motive, &[ih_predecessor, field_accessible]);
                let ih_relation = apply_all(kernel, relation, &[ih_predecessor, minor_source]);
                let with_related = pi_fvar(
                    kernel,
                    ih_related_fvar,
                    ih_relation,
                    ih_result,
                    BinderInfo::Default,
                );
                pi_fvar(
                    kernel,
                    ih_predecessor_fvar,
                    alpha,
                    with_related,
                    BinderInfo::Default,
                )
            };
            let selected = apply_all(kernel, minor_field, &[minor_predecessor, minor_related]);
            let minor_with_related = lam_fvar(
                kernel,
                minor_related_fvar,
                minor_relation,
                selected,
                BinderInfo::Default,
            );
            let minor_with_predecessor = lam_fvar(
                kernel,
                minor_predecessor_fvar,
                alpha,
                minor_with_related,
                BinderInfo::Default,
            );
            let minor_with_ih = lam_fvar(
                kernel,
                minor_ih_fvar,
                ih_ty,
                minor_with_predecessor,
                BinderInfo::Default,
            );
            let minor_with_field = lam_fvar(
                kernel,
                minor_field_fvar,
                minor_field_ty,
                minor_with_ih,
                BinderInfo::Default,
            );
            let minor = lam_fvar(
                kernel,
                minor_source_fvar,
                alpha,
                minor_with_field,
                BinderInfo::Default,
            );

            let rec = kernel.const_(acc_rec, vec![zero_lvl, u_lvl]);
            let eliminated = apply_all(
                kernel,
                rec,
                &[alpha, relation, motive, minor, source, accessible],
            );
            let body = apply_all(kernel, eliminated, &[predecessor, related]);
            let theorem_value = {
                let with_related = lam_fvar(
                    kernel,
                    related_fvar,
                    predecessor_relation,
                    body,
                    BinderInfo::Default,
                );
                let with_accessible = lam_fvar(
                    kernel,
                    accessible_fvar,
                    accessible_source,
                    with_related,
                    BinderInfo::Default,
                );
                let with_predecessor = lam_fvar(
                    kernel,
                    predecessor_fvar,
                    alpha,
                    with_accessible,
                    BinderInfo::Implicit,
                );
                let with_source = lam_fvar(
                    kernel,
                    source_fvar,
                    alpha,
                    with_predecessor,
                    BinderInfo::Implicit,
                );
                let with_relation = lam_fvar(
                    kernel,
                    relation_fvar,
                    relation_ty,
                    with_source,
                    BinderInfo::Implicit,
                );
                lam_fvar(
                    kernel,
                    alpha_fvar,
                    sort_u,
                    with_relation,
                    BinderInfo::Implicit,
                )
            };
            kernel.add_declaration(Declaration::Theorem {
                name: acc_inv,
                uparams: vec![acc_uparam],
                ty: theorem_ty,
                value: theorem_value,
            })?;
        }

        // WellFounded.{u} {α} r := ∀ a, Acc r a.
        let well_founded = kernel.name_str(anon, "WellFounded");
        {
            let u_lvl = kernel.level_param(acc_uparam);
            let sort_u = kernel.sort(u_lvl);
            let prop = kernel.prop();
            let acc_const = kernel.const_(acc, vec![u_lvl]);
            let relation_ty = {
                let alpha0 = kernel.bvar(0);
                let alpha1 = kernel.bvar(1);
                let inner = kernel.pi(anon, alpha1, prop, BinderInfo::Default);
                kernel.pi(anon, alpha0, inner, BinderInfo::Default)
            };
            let well_founded_ty = {
                let with_relation = kernel.pi(anon, relation_ty, prop, BinderInfo::Default);
                kernel.pi(anon, sort_u, with_relation, BinderInfo::Implicit)
            };
            let well_founded_value = {
                // Under `α, r, a`: Acc α r a.
                let alpha2 = kernel.bvar(2);
                let relation1 = kernel.bvar(1);
                let a0 = kernel.bvar(0);
                let body = {
                    let expression = kernel.app(acc_const, alpha2);
                    let expression = kernel.app(expression, relation1);
                    kernel.app(expression, a0)
                };
                // Under `α, r`, a : α = BVar 1.
                let alpha1 = kernel.bvar(1);
                let all_accessible = kernel.pi(anon, alpha1, body, BinderInfo::Default);
                let value_with_relation =
                    kernel.lam(anon, relation_ty, all_accessible, BinderInfo::Default);
                kernel.lam(anon, sort_u, value_with_relation, BinderInfo::Implicit)
            };
            kernel.add_declaration(Declaration::Definition {
                name: well_founded,
                uparams: vec![acc_uparam],
                ty: well_founded_ty,
                value: well_founded_value,
                hint: ReducibilityHint::Regular(3),
            })?;
        }

        // WellFounded.fix.{u,v} :
        //   ∀ {α} {r} {C}, WellFounded r →
        //     (∀ x, (∀ y, r y x → C y) → C x) → ∀ x, C x.
        // Its value is the corresponding `Acc.rec` application. Source-level
        // termination elaboration remains outside this core definition.
        let well_founded_fix = kernel.name_str(well_founded, "fix");
        let well_founded_fix_eq = kernel.name_str(well_founded, "fix_eq");
        let well_founded_fix_vparam = kernel.name_str(anon, "v");
        {
            let u_lvl = kernel.level_param(acc_uparam);
            let v_lvl = kernel.level_param(well_founded_fix_vparam);
            let sort_u = kernel.sort(u_lvl);
            let sort_v = kernel.sort(v_lvl);
            let prop = kernel.prop();
            let acc_const = kernel.const_(acc, vec![u_lvl]);
            let well_founded_const = kernel.const_(well_founded, vec![u_lvl]);

            let alpha_fvar = 20_000;
            let relation_fvar = 20_001;
            let family_fvar = 20_002;
            let well_founded_proof_fvar = 20_003;
            let step_fvar = 20_004;
            let value_fvar = 20_005;
            let alpha = kernel.fvar(alpha_fvar);
            let relation = kernel.fvar(relation_fvar);
            let family = kernel.fvar(family_fvar);
            let well_founded_proof = kernel.fvar(well_founded_proof_fvar);
            let step = kernel.fvar(step_fvar);
            let value = kernel.fvar(value_fvar);

            let relation_left_fvar = 20_006;
            let relation_right_fvar = 20_007;
            let relation_ty = {
                let right = pi_fvar(
                    kernel,
                    relation_right_fvar,
                    alpha,
                    prop,
                    BinderInfo::Default,
                );
                pi_fvar(
                    kernel,
                    relation_left_fvar,
                    alpha,
                    right,
                    BinderInfo::Default,
                )
            };
            let family_argument_fvar = 20_008;
            let family_ty = pi_fvar(
                kernel,
                family_argument_fvar,
                alpha,
                sort_v,
                BinderInfo::Default,
            );
            let well_founded_ty = apply_all(kernel, well_founded_const, &[alpha, relation]);

            let step_value_fvar = 20_009;
            let step_predecessor_fvar = 20_010;
            let step_relation_proof_fvar = 20_011;
            let step_recursive_fvar = 20_012;
            let step_value = kernel.fvar(step_value_fvar);
            let step_predecessor = kernel.fvar(step_predecessor_fvar);
            let step_relation = apply_all(kernel, relation, &[step_predecessor, step_value]);
            let step_predecessor_result = kernel.app(family, step_predecessor);
            let recursive_at_relation = pi_fvar(
                kernel,
                step_relation_proof_fvar,
                step_relation,
                step_predecessor_result,
                BinderInfo::Default,
            );
            let recursive_values = pi_fvar(
                kernel,
                step_predecessor_fvar,
                alpha,
                recursive_at_relation,
                BinderInfo::Default,
            );
            let step_result = kernel.app(family, step_value);
            let step_with_recursive = pi_fvar(
                kernel,
                step_recursive_fvar,
                recursive_values,
                step_result,
                BinderInfo::Default,
            );
            let step_ty = pi_fvar(
                kernel,
                step_value_fvar,
                alpha,
                step_with_recursive,
                BinderInfo::Default,
            );
            let result_ty = kernel.app(family, value);

            let fix_ty = {
                let with_value = pi_fvar(kernel, value_fvar, alpha, result_ty, BinderInfo::Default);
                let with_step =
                    pi_fvar(kernel, step_fvar, step_ty, with_value, BinderInfo::Default);
                let with_well_founded = pi_fvar(
                    kernel,
                    well_founded_proof_fvar,
                    well_founded_ty,
                    with_step,
                    BinderInfo::Default,
                );
                let with_family = pi_fvar(
                    kernel,
                    family_fvar,
                    family_ty,
                    with_well_founded,
                    BinderInfo::Implicit,
                );
                let with_relation = pi_fvar(
                    kernel,
                    relation_fvar,
                    relation_ty,
                    with_family,
                    BinderInfo::Implicit,
                );
                pi_fvar(
                    kernel,
                    alpha_fvar,
                    sort_u,
                    with_relation,
                    BinderInfo::Implicit,
                )
            };

            // motive := fun x (_ : Acc r x) => C x.
            let motive_value_fvar = 20_013;
            let motive_accessible_fvar = 20_014;
            let motive_value = kernel.fvar(motive_value_fvar);
            let motive_accessible_ty = {
                let expression = kernel.app(acc_const, alpha);
                let expression = kernel.app(expression, relation);
                kernel.app(expression, motive_value)
            };
            let motive_result = kernel.app(family, motive_value);
            let motive_with_accessible = lam_fvar(
                kernel,
                motive_accessible_fvar,
                motive_accessible_ty,
                motive_result,
                BinderInfo::Default,
            );
            let motive = lam_fvar(
                kernel,
                motive_value_fvar,
                alpha,
                motive_with_accessible,
                BinderInfo::Default,
            );

            // minor := fun x (_h : predecessors accessible) ih => F x ih.
            let minor_value_fvar = 20_015;
            let minor_field_fvar = 20_016;
            let minor_ih_fvar = 20_017;
            let minor_predecessor_fvar = 20_018;
            let minor_relation_proof_fvar = 20_019;
            let minor_value = kernel.fvar(minor_value_fvar);
            let minor_predecessor = kernel.fvar(minor_predecessor_fvar);
            let minor_relation_ty = apply_all(kernel, relation, &[minor_predecessor, minor_value]);
            let minor_accessible_result = {
                let expression = kernel.app(acc_const, alpha);
                let expression = kernel.app(expression, relation);
                kernel.app(expression, minor_predecessor)
            };
            let minor_field_at_relation = pi_fvar(
                kernel,
                minor_relation_proof_fvar,
                minor_relation_ty,
                minor_accessible_result,
                BinderInfo::Default,
            );
            let minor_field_ty = pi_fvar(
                kernel,
                minor_predecessor_fvar,
                alpha,
                minor_field_at_relation,
                BinderInfo::Default,
            );

            let ih_predecessor_fvar = 20_020;
            let ih_relation_proof_fvar = 20_021;
            let ih_predecessor = kernel.fvar(ih_predecessor_fvar);
            let ih_relation_ty = apply_all(kernel, relation, &[ih_predecessor, minor_value]);
            let ih_result = kernel.app(family, ih_predecessor);
            let ih_at_relation = pi_fvar(
                kernel,
                ih_relation_proof_fvar,
                ih_relation_ty,
                ih_result,
                BinderInfo::Default,
            );
            let ih_ty = pi_fvar(
                kernel,
                ih_predecessor_fvar,
                alpha,
                ih_at_relation,
                BinderInfo::Default,
            );
            let ih = kernel.fvar(minor_ih_fvar);
            let step_at_value = kernel.app(step, minor_value);
            let minor_body = kernel.app(step_at_value, ih);
            let minor_with_ih = lam_fvar(
                kernel,
                minor_ih_fvar,
                ih_ty,
                minor_body,
                BinderInfo::Default,
            );
            let minor_with_field = lam_fvar(
                kernel,
                minor_field_fvar,
                minor_field_ty,
                minor_with_ih,
                BinderInfo::Default,
            );
            let minor = lam_fvar(
                kernel,
                minor_value_fvar,
                alpha,
                minor_with_field,
                BinderInfo::Default,
            );

            let accessible_value = kernel.app(well_founded_proof, value);
            // Generated recursors order the motive universe before the
            // inductive family's declared universe parameters.
            let acc_rec = kernel.const_(acc_rec, vec![v_lvl, u_lvl]);
            let body = apply_all(
                kernel,
                acc_rec,
                &[alpha, relation, motive, minor, value, accessible_value],
            );
            let fix_value = {
                let with_value = lam_fvar(kernel, value_fvar, alpha, body, BinderInfo::Default);
                let with_step =
                    lam_fvar(kernel, step_fvar, step_ty, with_value, BinderInfo::Default);
                let with_well_founded = lam_fvar(
                    kernel,
                    well_founded_proof_fvar,
                    well_founded_ty,
                    with_step,
                    BinderInfo::Default,
                );
                let with_family = lam_fvar(
                    kernel,
                    family_fvar,
                    family_ty,
                    with_well_founded,
                    BinderInfo::Implicit,
                );
                let with_relation = lam_fvar(
                    kernel,
                    relation_fvar,
                    relation_ty,
                    with_family,
                    BinderInfo::Implicit,
                );
                lam_fvar(
                    kernel,
                    alpha_fvar,
                    sort_u,
                    with_relation,
                    BinderInfo::Implicit,
                )
            };
            kernel.add_declaration(Declaration::Definition {
                name: well_founded_fix,
                uparams: vec![acc_uparam, well_founded_fix_vparam],
                ty: fix_ty,
                value: fix_value,
                hint: ReducibilityHint::Regular(8),
            })?;
        }

        // WellFounded.fix_eq.{u,v} :
        //   ∀ {α} {r} {C} (wf : WellFounded r) (F) x,
        //     fix wf F x = F x (fun y _ => fix wf F y).
        // Accessibility induction makes the equation reflexive in the single
        // constructor case: proof irrelevance identifies the accessibility
        // proof selected by `wf` with the constructor field used by `Acc.rec`.
        {
            let u_lvl = kernel.level_param(acc_uparam);
            let v_lvl = kernel.level_param(well_founded_fix_vparam);
            let zero_lvl = kernel.level_zero();
            let sort_u = kernel.sort(u_lvl);
            let sort_v = kernel.sort(v_lvl);
            let prop = kernel.prop();
            let acc_const = kernel.const_(acc, vec![u_lvl]);
            let well_founded_const = kernel.const_(well_founded, vec![u_lvl]);
            let fix_const = kernel.const_(well_founded_fix, vec![u_lvl, v_lvl]);
            let eq_const = kernel.const_(eq, vec![v_lvl]);

            let alpha_fvar = 21_000;
            let relation_fvar = 21_001;
            let family_fvar = 21_002;
            let well_founded_proof_fvar = 21_003;
            let step_fvar = 21_004;
            let value_fvar = 21_005;
            let alpha = kernel.fvar(alpha_fvar);
            let relation = kernel.fvar(relation_fvar);
            let family = kernel.fvar(family_fvar);
            let well_founded_proof = kernel.fvar(well_founded_proof_fvar);
            let step = kernel.fvar(step_fvar);
            let value = kernel.fvar(value_fvar);

            let relation_left_fvar = 21_006;
            let relation_right_fvar = 21_007;
            let relation_ty = {
                let right = pi_fvar(
                    kernel,
                    relation_right_fvar,
                    alpha,
                    prop,
                    BinderInfo::Default,
                );
                pi_fvar(
                    kernel,
                    relation_left_fvar,
                    alpha,
                    right,
                    BinderInfo::Default,
                )
            };
            let family_argument_fvar = 21_008;
            let family_ty = pi_fvar(
                kernel,
                family_argument_fvar,
                alpha,
                sort_v,
                BinderInfo::Default,
            );
            let well_founded_ty = apply_all(kernel, well_founded_const, &[alpha, relation]);

            let step_value_fvar = 21_009;
            let step_predecessor_fvar = 21_010;
            let step_relation_proof_fvar = 21_011;
            let step_recursive_fvar = 21_012;
            let step_value = kernel.fvar(step_value_fvar);
            let step_predecessor = kernel.fvar(step_predecessor_fvar);
            let step_relation = apply_all(kernel, relation, &[step_predecessor, step_value]);
            let step_predecessor_result = kernel.app(family, step_predecessor);
            let recursive_at_relation = pi_fvar(
                kernel,
                step_relation_proof_fvar,
                step_relation,
                step_predecessor_result,
                BinderInfo::Default,
            );
            let recursive_values = pi_fvar(
                kernel,
                step_predecessor_fvar,
                alpha,
                recursive_at_relation,
                BinderInfo::Default,
            );
            let step_result = kernel.app(family, step_value);
            let step_with_recursive = pi_fvar(
                kernel,
                step_recursive_fvar,
                recursive_values,
                step_result,
                BinderInfo::Default,
            );
            let step_ty = pi_fvar(
                kernel,
                step_value_fvar,
                alpha,
                step_with_recursive,
                BinderInfo::Default,
            );

            let fix_at = |kernel: &mut Kernel, point: ExprId| {
                apply_all(
                    kernel,
                    fix_const,
                    &[alpha, relation, family, well_founded_proof, step, point],
                )
            };
            let fix_body_at = |kernel: &mut Kernel, point: ExprId, accessible: ExprId| {
                let motive_point_fvar = 21_100;
                let motive_accessible_fvar = 21_101;
                let motive_point = kernel.fvar(motive_point_fvar);
                let motive_accessible_ty =
                    apply_all(kernel, acc_const, &[alpha, relation, motive_point]);
                let motive_result = kernel.app(family, motive_point);
                let motive_with_accessible = lam_fvar(
                    kernel,
                    motive_accessible_fvar,
                    motive_accessible_ty,
                    motive_result,
                    BinderInfo::Default,
                );
                let result_motive = lam_fvar(
                    kernel,
                    motive_point_fvar,
                    alpha,
                    motive_with_accessible,
                    BinderInfo::Default,
                );

                let minor_point_fvar = 21_102;
                let minor_field_fvar = 21_103;
                let minor_ih_fvar = 21_104;
                let minor_predecessor_fvar = 21_105;
                let minor_relation_proof_fvar = 21_106;
                let minor_point = kernel.fvar(minor_point_fvar);
                let minor_predecessor = kernel.fvar(minor_predecessor_fvar);
                let minor_relation_ty =
                    apply_all(kernel, relation, &[minor_predecessor, minor_point]);
                let minor_accessible_result =
                    apply_all(kernel, acc_const, &[alpha, relation, minor_predecessor]);
                let minor_field_at_relation = pi_fvar(
                    kernel,
                    minor_relation_proof_fvar,
                    minor_relation_ty,
                    minor_accessible_result,
                    BinderInfo::Default,
                );
                let minor_field_ty = pi_fvar(
                    kernel,
                    minor_predecessor_fvar,
                    alpha,
                    minor_field_at_relation,
                    BinderInfo::Default,
                );

                let ih_predecessor_fvar = 21_107;
                let ih_relation_proof_fvar = 21_108;
                let ih_predecessor = kernel.fvar(ih_predecessor_fvar);
                let ih_relation_ty = apply_all(kernel, relation, &[ih_predecessor, minor_point]);
                let ih_result = kernel.app(family, ih_predecessor);
                let ih_at_relation = pi_fvar(
                    kernel,
                    ih_relation_proof_fvar,
                    ih_relation_ty,
                    ih_result,
                    BinderInfo::Default,
                );
                let ih_ty = pi_fvar(
                    kernel,
                    ih_predecessor_fvar,
                    alpha,
                    ih_at_relation,
                    BinderInfo::Default,
                );
                let ih = kernel.fvar(minor_ih_fvar);
                let minor_body = apply_all(kernel, step, &[minor_point, ih]);
                let minor_with_ih = lam_fvar(
                    kernel,
                    minor_ih_fvar,
                    ih_ty,
                    minor_body,
                    BinderInfo::Default,
                );
                let minor_with_field = lam_fvar(
                    kernel,
                    minor_field_fvar,
                    minor_field_ty,
                    minor_with_ih,
                    BinderInfo::Default,
                );
                let result_minor = lam_fvar(
                    kernel,
                    minor_point_fvar,
                    alpha,
                    minor_with_field,
                    BinderInfo::Default,
                );
                let result_rec = kernel.const_(acc_rec, vec![v_lvl, u_lvl]);
                apply_all(
                    kernel,
                    result_rec,
                    &[
                        alpha,
                        relation,
                        result_motive,
                        result_minor,
                        point,
                        accessible,
                    ],
                )
            };
            let recursive_at = |kernel: &mut Kernel, point: ExprId| {
                let predecessor_fvar = 21_013;
                let relation_proof_fvar = 21_014;
                let predecessor = kernel.fvar(predecessor_fvar);
                let relation_proof_ty = apply_all(kernel, relation, &[predecessor, point]);
                let recursive = fix_at(kernel, predecessor);
                let with_proof = lam_fvar(
                    kernel,
                    relation_proof_fvar,
                    relation_proof_ty,
                    recursive,
                    BinderInfo::Default,
                );
                lam_fvar(
                    kernel,
                    predecessor_fvar,
                    alpha,
                    with_proof,
                    BinderInfo::Default,
                )
            };
            let equation_at = |kernel: &mut Kernel, point: ExprId| {
                let carrier = kernel.app(family, point);
                let lhs = fix_at(kernel, point);
                let recursive = recursive_at(kernel, point);
                let rhs = apply_all(kernel, step, &[point, recursive]);
                apply_all(kernel, eq_const, &[carrier, lhs, rhs])
            };

            let equation = equation_at(kernel, value);
            let theorem_ty = {
                let with_value = pi_fvar(kernel, value_fvar, alpha, equation, BinderInfo::Default);
                let with_step =
                    pi_fvar(kernel, step_fvar, step_ty, with_value, BinderInfo::Default);
                let with_well_founded = pi_fvar(
                    kernel,
                    well_founded_proof_fvar,
                    well_founded_ty,
                    with_step,
                    BinderInfo::Default,
                );
                let with_family = pi_fvar(
                    kernel,
                    family_fvar,
                    family_ty,
                    with_well_founded,
                    BinderInfo::Implicit,
                );
                let with_relation = pi_fvar(
                    kernel,
                    relation_fvar,
                    relation_ty,
                    with_family,
                    BinderInfo::Implicit,
                );
                pi_fvar(
                    kernel,
                    alpha_fvar,
                    sort_u,
                    with_relation,
                    BinderInfo::Implicit,
                )
            };

            // motive := fun x (_ : Acc r x) => fix wf F x = F x (... fix ...).
            let motive_value_fvar = 21_015;
            let motive_accessible_fvar = 21_016;
            let motive_value = kernel.fvar(motive_value_fvar);
            let motive_accessible_ty =
                apply_all(kernel, acc_const, &[alpha, relation, motive_value]);
            let motive_equation = equation_at(kernel, motive_value);
            let motive_with_accessible = lam_fvar(
                kernel,
                motive_accessible_fvar,
                motive_accessible_ty,
                motive_equation,
                BinderInfo::Default,
            );
            let motive = lam_fvar(
                kernel,
                motive_value_fvar,
                alpha,
                motive_with_accessible,
                BinderInfo::Default,
            );

            let minor_value_fvar = 21_017;
            let minor_field_fvar = 21_018;
            let minor_ih_fvar = 21_019;
            let minor_predecessor_fvar = 21_020;
            let minor_relation_proof_fvar = 21_021;
            let minor_value = kernel.fvar(minor_value_fvar);
            let minor_predecessor = kernel.fvar(minor_predecessor_fvar);
            let minor_relation_ty = apply_all(kernel, relation, &[minor_predecessor, minor_value]);
            let minor_accessible_result =
                apply_all(kernel, acc_const, &[alpha, relation, minor_predecessor]);
            let minor_field_at_relation = pi_fvar(
                kernel,
                minor_relation_proof_fvar,
                minor_relation_ty,
                minor_accessible_result,
                BinderInfo::Default,
            );
            let minor_field_ty = pi_fvar(
                kernel,
                minor_predecessor_fvar,
                alpha,
                minor_field_at_relation,
                BinderInfo::Default,
            );

            let ih_predecessor_fvar = 21_022;
            let ih_relation_proof_fvar = 21_023;
            let ih_predecessor = kernel.fvar(ih_predecessor_fvar);
            let ih_relation_ty = apply_all(kernel, relation, &[ih_predecessor, minor_value]);
            let ih_accessible = {
                let field = kernel.fvar(minor_field_fvar);
                let relation_proof = kernel.fvar(ih_relation_proof_fvar);
                apply_all(kernel, field, &[ih_predecessor, relation_proof])
            };
            let ih_result = apply_all(kernel, motive, &[ih_predecessor, ih_accessible]);
            let ih_at_relation = pi_fvar(
                kernel,
                ih_relation_proof_fvar,
                ih_relation_ty,
                ih_result,
                BinderInfo::Default,
            );
            let ih_ty = pi_fvar(
                kernel,
                ih_predecessor_fvar,
                alpha,
                ih_at_relation,
                BinderInfo::Default,
            );

            let minor_recursive = recursive_at(kernel, minor_value);
            let minor_rhs = apply_all(kernel, step, &[minor_value, minor_recursive]);
            let minor_carrier = kernel.app(family, minor_value);
            let minor_field = kernel.fvar(minor_field_fvar);
            let constructor = kernel.const_(acc_intro, vec![u_lvl]);
            let constructor_proof = apply_all(
                kernel,
                constructor,
                &[alpha, relation, minor_value, minor_field],
            );
            let selected_proof = kernel.app(well_founded_proof, minor_value);
            let proof_carrier = apply_all(kernel, acc_const, &[alpha, relation, minor_value]);

            // First reduce the fixpoint at the explicit constructor proof, then
            // transport along equality of accessibility proofs. The equality
            // itself is reflexive modulo proof irrelevance.
            let case_refl = kernel.const_(eq_refl, vec![v_lvl]);
            let case_proof = apply_all(kernel, case_refl, &[minor_carrier, minor_rhs]);
            let transport_proof_fvar = 21_109;
            let transport_equality_fvar = 21_110;
            let transport_proof = kernel.fvar(transport_proof_fvar);
            let transported_lhs = fix_body_at(kernel, minor_value, transport_proof);
            let transported_equation = apply_all(
                kernel,
                eq_const,
                &[minor_carrier, transported_lhs, minor_rhs],
            );
            let equality_ty = {
                let proof_eq = kernel.const_(eq, vec![zero_lvl]);
                apply_all(
                    kernel,
                    proof_eq,
                    &[proof_carrier, constructor_proof, transport_proof],
                )
            };
            let transport_with_equality = lam_fvar(
                kernel,
                transport_equality_fvar,
                equality_ty,
                transported_equation,
                BinderInfo::Default,
            );
            let transport_motive = lam_fvar(
                kernel,
                transport_proof_fvar,
                proof_carrier,
                transport_with_equality,
                BinderInfo::Default,
            );
            let proof_refl = kernel.const_(eq_refl, vec![zero_lvl]);
            let proof_equality = apply_all(kernel, proof_refl, &[proof_carrier, constructor_proof]);
            let eq_rec = kernel.const_(eq_rec, vec![zero_lvl, zero_lvl]);
            let minor_body = apply_all(
                kernel,
                eq_rec,
                &[
                    proof_carrier,
                    constructor_proof,
                    transport_motive,
                    case_proof,
                    selected_proof,
                    proof_equality,
                ],
            );
            let minor_with_ih = lam_fvar(
                kernel,
                minor_ih_fvar,
                ih_ty,
                minor_body,
                BinderInfo::Default,
            );
            let minor_with_field = lam_fvar(
                kernel,
                minor_field_fvar,
                minor_field_ty,
                minor_with_ih,
                BinderInfo::Default,
            );
            let minor = lam_fvar(
                kernel,
                minor_value_fvar,
                alpha,
                minor_with_field,
                BinderInfo::Default,
            );

            let accessible_value = kernel.app(well_founded_proof, value);
            let acc_rec = kernel.const_(acc_rec, vec![zero_lvl, u_lvl]);
            let proof = apply_all(
                kernel,
                acc_rec,
                &[alpha, relation, motive, minor, value, accessible_value],
            );
            let theorem_value = {
                let with_value = lam_fvar(kernel, value_fvar, alpha, proof, BinderInfo::Default);
                let with_step =
                    lam_fvar(kernel, step_fvar, step_ty, with_value, BinderInfo::Default);
                let with_well_founded = lam_fvar(
                    kernel,
                    well_founded_proof_fvar,
                    well_founded_ty,
                    with_step,
                    BinderInfo::Default,
                );
                let with_family = lam_fvar(
                    kernel,
                    family_fvar,
                    family_ty,
                    with_well_founded,
                    BinderInfo::Implicit,
                );
                let with_relation = lam_fvar(
                    kernel,
                    relation_fvar,
                    relation_ty,
                    with_family,
                    BinderInfo::Implicit,
                );
                lam_fvar(
                    kernel,
                    alpha_fvar,
                    sort_u,
                    with_relation,
                    BinderInfo::Implicit,
                )
            };
            kernel.add_declaration(Declaration::Theorem {
                name: well_founded_fix_eq,
                uparams: vec![acc_uparam, well_founded_fix_vparam],
                ty: theorem_ty,
                value: theorem_value,
            })?;
        }

        // --- Not (a : Prop) : Prop := fun a => a → False ---------------------
        // --- Bool : Type, Bool.false | Bool.true (official Lean order) -------
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
            kernel.add_inductive(
                bool_,
                &[],
                0,
                bool_ty,
                &[(bool_false, bool_const), (bool_true, bool_const)],
            )?;
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
            kernel.add_inductive(
                nat,
                &[],
                0,
                nat_ty,
                &[(nat_zero, nat_const), (nat_succ, succ_ty)],
            )?;
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
            kernel.add_declaration(Declaration::Definition {
                name: not,
                uparams: vec![],
                ty: not_ty,
                value: not_val,
                hint: ReducibilityHint::Regular(0),
            })?;
        }

        // --- absurd.{v} : Π (a : Prop) (b : Sort v), a → (a → False) → b ----
        // Ex falso from a proposition and its refutation, built directly from
        // `False.rec` (universe-polymorphic in the target `b`, same technique
        // as the `False.rec.{level}` calls throughout `int_prelude`/
        // `nat_prelude`'s private `absurd` helpers). The refutation is again
        // the plain arrow `a → False` rather than `Not a` applied.
        let absurd_vparam = kernel.name_str(anon, "v");
        let absurd = kernel.name_str(anon, "absurd");
        {
            let prop = kernel.prop();
            let v_lvl = kernel.level_param(absurd_vparam);
            let sort_v = kernel.sort(v_lvl);

            let a_fvar = 23_700;
            let b_fvar = 23_701;
            let h1_fvar = 23_702;
            let h2_fvar = 23_703;
            let dummy_fvar = 23_704;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let h2_ty = kernel.pi(anon, a, false_const, BinderInfo::Default); // a → False

            // type: Π (a : Prop) (b : Sort v), a → (a → False) → b.
            let t_inner = kernel.pi(anon, h2_ty, b, BinderInfo::Default);
            let t_outer = kernel.pi(anon, a, t_inner, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, sort_v, t_outer, BinderInfo::Default);
            let absurd_ty = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b h1 h2 => False.rec.{v} (fun _ => b) (h2 h1).
            let h1 = kernel.fvar(h1_fvar);
            let h2 = kernel.fvar(h2_fvar);
            let h2_h1 = kernel.app(h2, h1);
            let false_motive = lam_fvar(kernel, dummy_fvar, false_const, b, BinderInfo::Default);
            let false_rec_const = kernel.const_(false_rec, vec![v_lvl]);
            let absurd_body = apply_all(kernel, false_rec_const, &[false_motive, h2_h1]);

            let with_h2 = lam_fvar(kernel, h2_fvar, h2_ty, absurd_body, BinderInfo::Default);
            let with_h1 = lam_fvar(kernel, h1_fvar, a, with_h2, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, sort_v, with_h1, BinderInfo::Default);
            let absurd_value = lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            // A DEFINITION, not a Theorem, and the difference is not cosmetic.
            // `absurd`'s type lands in `Sort v` for an arbitrary universe, not in
            // `Prop`, and a theorem's type must be a proposition. Lean itself
            // declares it `@[macro_inline] def absurd {a : Prop} {b : Sort v}`
            // for exactly this reason.
            //
            // It was declared as a `Theorem` when the logic prelude was extended
            // on 2026-08-22. Our kernel accepted it; the REAL Lean kernel refuses
            // it — "type of theorem 'absurd' is not a proposition" — and
            // `tests/real_lean_wire_differential.rs::
            // our_kernel_admits_nothing_the_real_lean_kernel_refuses` caught the
            // divergence. That test exists for precisely this, and it is the only
            // check in the tree that compares our admission against the real
            // kernel's.
            kernel.add_declaration(Declaration::Definition {
                name: absurd,
                uparams: vec![absurd_vparam],
                ty: absurd_ty,
                value: absurd_value,
                hint: ReducibilityHint::Regular(1),
            })?;
        }

        // --- mt : Π (a b : Prop), (a → b) → (b → False) → (a → False) ------
        // Modus tollens: plain function composition, `fun ha => nb (f ha)`,
        // no recursor needed.
        let mt = kernel.name_str(anon, "mt");
        {
            let prop = kernel.prop();
            let a_fvar = 23_710;
            let b_fvar = 23_711;
            let f_fvar = 23_712;
            let nb_fvar = 23_713;
            let ha_fvar = 23_714;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let f_ty = kernel.pi(anon, a, b, BinderInfo::Default); // a → b
            let nb_ty = kernel.pi(anon, b, false_const, BinderInfo::Default); // b → False
            let result_ty = kernel.pi(anon, a, false_const, BinderInfo::Default); // a → False

            // type: Π (a b : Prop), (a → b) → (b → False) → (a → False).
            let t_inner = kernel.pi(anon, nb_ty, result_ty, BinderInfo::Default);
            let t_outer = kernel.pi(anon, f_ty, t_inner, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, t_outer, BinderInfo::Default);
            let mt_ty = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b f nb ha => nb (f ha).
            let f = kernel.fvar(f_fvar);
            let nb = kernel.fvar(nb_fvar);
            let ha = kernel.fvar(ha_fvar);
            let f_ha = kernel.app(f, ha);
            let nb_f_ha = kernel.app(nb, f_ha);

            let with_ha = lam_fvar(kernel, ha_fvar, a, nb_f_ha, BinderInfo::Default);
            let with_nb = lam_fvar(kernel, nb_fvar, nb_ty, with_ha, BinderInfo::Default);
            let with_f = lam_fvar(kernel, f_fvar, f_ty, with_nb, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_f, BinderInfo::Default);
            let mt_value = lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: mt,
                uparams: vec![],
                ty: mt_ty,
                value: mt_value,
            })?;
        }

        // =====================================================================
        // The classical principles, made interderivable -- proved
        // intuitionistically, with none of them assumed (ADR-0036 follow-on).
        // =====================================================================

        // --- not_not_intro : Π (a : Prop), a → (a → False) → False ----------
        let not_not_intro = kernel.name_str(anon, "not_not_intro");
        {
            let prop = kernel.prop();
            let a_fvar = 23_720;
            let ha_fvar = 23_721;
            let hna_fvar = 23_722;
            let a = kernel.fvar(a_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let na_ty = kernel.pi(anon, a, false_const, BinderInfo::Default); // a → False

            // type: Π (a : Prop), a → (a → False) → False.
            let t_inner = kernel.pi(anon, na_ty, false_const, BinderInfo::Default);
            let t_outer = kernel.pi(anon, a, t_inner, BinderInfo::Default);
            let not_not_intro_ty = pi_fvar(kernel, a_fvar, prop, t_outer, BinderInfo::Default);

            // value: fun a ha hna => hna ha.
            let ha = kernel.fvar(ha_fvar);
            let hna = kernel.fvar(hna_fvar);
            let hna_ha = kernel.app(hna, ha);

            let with_hna = lam_fvar(kernel, hna_fvar, na_ty, hna_ha, BinderInfo::Default);
            let with_ha = lam_fvar(kernel, ha_fvar, a, with_hna, BinderInfo::Default);
            let not_not_intro_value = lam_fvar(kernel, a_fvar, prop, with_ha, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: not_not_intro,
                uparams: vec![],
                ty: not_not_intro_ty,
                value: not_not_intro_value,
            })?;
        }

        // --- noncontradiction : Π (a : Prop), And a (a → False) → False -----
        let noncontradiction = kernel.name_str(anon, "noncontradiction");
        {
            let prop = kernel.prop();
            let a_fvar = 23_730;
            let hp_fvar = 23_731;
            let a = kernel.fvar(a_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let na_ty = kernel.pi(anon, a, false_const, BinderInfo::Default); // a → False
            let and_const = kernel.const_(and, vec![]);
            let and_a_na = apply_all(kernel, and_const, &[a, na_ty]);

            // type: Π (a : Prop), And a (a → False) → False.
            let t_outer = kernel.pi(anon, and_a_na, false_const, BinderInfo::Default);
            let noncontradiction_ty = pi_fvar(kernel, a_fvar, prop, t_outer, BinderInfo::Default);

            // value: fun a hp => And.right a (a → False) hp (And.left a (a → False) hp).
            let hp = kernel.fvar(hp_fvar);
            let and_left_const = kernel.const_(and_left, vec![]);
            let left = apply_all(kernel, and_left_const, &[a, na_ty, hp]);
            let and_right_const = kernel.const_(and_right, vec![]);
            let right = apply_all(kernel, and_right_const, &[a, na_ty, hp]);
            let applied = kernel.app(right, left);

            let with_hp = lam_fvar(kernel, hp_fvar, and_a_na, applied, BinderInfo::Default);
            let noncontradiction_value =
                lam_fvar(kernel, a_fvar, prop, with_hp, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: noncontradiction,
                uparams: vec![],
                ty: noncontradiction_ty,
                value: noncontradiction_value,
            })?;
        }

        // --- not_not_not : Π (a : Prop), ¬¬¬a → a → False --------------------
        // The triple-negation collapse: ¬¬¬a → ¬a. Built directly from
        // `not_not_intro` rather than a fresh recursor derivation.
        let not_not_not = kernel.name_str(anon, "not_not_not");
        {
            let prop = kernel.prop();
            let a_fvar = 23_740;
            let h3_fvar = 23_741;
            let ha_fvar = 23_742;
            let a = kernel.fvar(a_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let na_ty = kernel.pi(anon, a, false_const, BinderInfo::Default); // a → False
            let nna_ty = kernel.pi(anon, na_ty, false_const, BinderInfo::Default); // ¬¬a
            let nnna_ty = kernel.pi(anon, nna_ty, false_const, BinderInfo::Default); // ¬¬¬a

            // type: Π (a : Prop), ¬¬¬a → a → False.
            let t_outer = kernel.pi(anon, nnna_ty, na_ty, BinderInfo::Default);
            let not_not_not_ty = pi_fvar(kernel, a_fvar, prop, t_outer, BinderInfo::Default);

            // value: fun a h3 ha => h3 (not_not_intro a ha).
            let h3 = kernel.fvar(h3_fvar);
            let ha = kernel.fvar(ha_fvar);
            let not_not_intro_const = kernel.const_(not_not_intro, vec![]);
            let nn_a = apply_all(kernel, not_not_intro_const, &[a, ha]);
            let h3_nn_a = kernel.app(h3, nn_a);

            let with_ha = lam_fvar(kernel, ha_fvar, a, h3_nn_a, BinderInfo::Default);
            let with_h3 = lam_fvar(kernel, h3_fvar, nnna_ty, with_ha, BinderInfo::Default);
            let not_not_not_value = lam_fvar(kernel, a_fvar, prop, with_h3, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: not_not_not,
                uparams: vec![],
                ty: not_not_not_ty,
                value: not_not_not_value,
            })?;
        }

        // --- demorgan_not_or : ¬(a ∨ b) → ¬a ∧ ¬b -----------------------------
        let demorgan_not_or = kernel.name_str(anon, "demorgan_not_or");
        {
            let prop = kernel.prop();
            let a_fvar = 23_750;
            let b_fvar = 23_751;
            let h_fvar = 23_752;
            let ha_fvar = 23_753;
            let hb_fvar = 23_754;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let or_const = kernel.const_(or, vec![]);
            let or_ab = apply_all(kernel, or_const, &[a, b]);
            let na_ty = kernel.pi(anon, a, false_const, BinderInfo::Default); // a → False
            let nb_ty = kernel.pi(anon, b, false_const, BinderInfo::Default); // b → False
            let and_const = kernel.const_(and, vec![]);
            let and_na_nb = apply_all(kernel, and_const, &[na_ty, nb_ty]);
            let or_to_false = kernel.pi(anon, or_ab, false_const, BinderInfo::Default);

            // type: Π (a b : Prop), (Or a b → False) → And (a → False) (b → False).
            let t_outer = kernel.pi(anon, or_to_false, and_na_nb, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, t_outer, BinderInfo::Default);
            let demorgan_not_or_ty = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b h =>
            //   And.intro (a → False) (b → False)
            //     (fun ha => h (Or.inl a b ha)) (fun hb => h (Or.inr a b hb)).
            let h = kernel.fvar(h_fvar);
            let or_inl_const = kernel.const_(or_inl, vec![]);
            let or_inr_const = kernel.const_(or_inr, vec![]);
            let left_fn = {
                let ha = kernel.fvar(ha_fvar);
                let inl_applied = apply_all(kernel, or_inl_const, &[a, b, ha]);
                let h_inl = kernel.app(h, inl_applied);
                lam_fvar(kernel, ha_fvar, a, h_inl, BinderInfo::Default)
            };
            let right_fn = {
                let hb = kernel.fvar(hb_fvar);
                let inr_applied = apply_all(kernel, or_inr_const, &[a, b, hb]);
                let h_inr = kernel.app(h, inr_applied);
                lam_fvar(kernel, hb_fvar, b, h_inr, BinderInfo::Default)
            };
            let and_intro_const = kernel.const_(and_intro, vec![]);
            let applied = apply_all(kernel, and_intro_const, &[na_ty, nb_ty, left_fn, right_fn]);

            let with_h = lam_fvar(kernel, h_fvar, or_to_false, applied, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_h, BinderInfo::Default);
            let demorgan_not_or_value =
                lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: demorgan_not_or,
                uparams: vec![],
                ty: demorgan_not_or_ty,
                value: demorgan_not_or_value,
            })?;
        }

        // --- demorgan_not_or_converse : ¬a ∧ ¬b → ¬(a ∨ b) -------------------
        let demorgan_not_or_converse = kernel.name_str(anon, "demorgan_not_or_converse");
        {
            let prop = kernel.prop();
            let a_fvar = 23_760;
            let b_fvar = 23_761;
            let hp_fvar = 23_762;
            let hor_fvar = 23_763;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let or_const = kernel.const_(or, vec![]);
            let or_ab = apply_all(kernel, or_const, &[a, b]);
            let na_ty = kernel.pi(anon, a, false_const, BinderInfo::Default); // a → False
            let nb_ty = kernel.pi(anon, b, false_const, BinderInfo::Default); // b → False
            let and_const = kernel.const_(and, vec![]);
            let and_na_nb = apply_all(kernel, and_const, &[na_ty, nb_ty]);
            let or_to_false = kernel.pi(anon, or_ab, false_const, BinderInfo::Default);

            // type: Π (a b : Prop), And (a → False) (b → False) → (Or a b → False).
            let t_outer = kernel.pi(anon, and_na_nb, or_to_false, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, t_outer, BinderInfo::Default);
            let demorgan_not_or_converse_ty =
                pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b hp hor =>
            //   Or.elim a b False hor (And.left (a → False) (b → False) hp)
            //     (And.right (a → False) (b → False) hp).
            let hp = kernel.fvar(hp_fvar);
            let hor = kernel.fvar(hor_fvar);
            let and_left_const = kernel.const_(and_left, vec![]);
            let and_right_const = kernel.const_(and_right, vec![]);
            let left_proof = apply_all(kernel, and_left_const, &[na_ty, nb_ty, hp]);
            let right_proof = apply_all(kernel, and_right_const, &[na_ty, nb_ty, hp]);
            let or_elim_const = kernel.const_(or_elim, vec![]);
            let applied = apply_all(
                kernel,
                or_elim_const,
                &[a, b, false_const, hor, left_proof, right_proof],
            );

            let inner = lam_fvar(kernel, hor_fvar, or_ab, applied, BinderInfo::Default);
            let with_hp = lam_fvar(kernel, hp_fvar, and_na_nb, inner, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_hp, BinderInfo::Default);
            let demorgan_not_or_converse_value =
                lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: demorgan_not_or_converse,
                uparams: vec![],
                ty: demorgan_not_or_converse_ty,
                value: demorgan_not_or_converse_value,
            })?;
        }

        // --- demorgan_or_not_and : ¬a ∨ ¬b → ¬(a ∧ b) ------------------------
        // The converse of THIS one -- ¬(a ∧ b) → ¬a ∨ ¬b -- is the De Morgan
        // direction that is NOT a theorem of intuitionistic logic (see the
        // module doc); it is not declared here or anywhere in this prelude.
        let demorgan_or_not_and = kernel.name_str(anon, "demorgan_or_not_and");
        {
            let prop = kernel.prop();
            let a_fvar = 23_770;
            let b_fvar = 23_771;
            let hor_fvar = 23_772;
            let na_fvar = 23_773;
            let hab1_fvar = 23_774;
            let nb_fvar = 23_775;
            let hab2_fvar = 23_776;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let and_const = kernel.const_(and, vec![]);
            let and_ab = apply_all(kernel, and_const, &[a, b]);
            let na_ty = kernel.pi(anon, a, false_const, BinderInfo::Default); // a → False
            let nb_ty = kernel.pi(anon, b, false_const, BinderInfo::Default); // b → False
            let or_const = kernel.const_(or, vec![]);
            let or_na_nb = apply_all(kernel, or_const, &[na_ty, nb_ty]);
            let and_to_false = kernel.pi(anon, and_ab, false_const, BinderInfo::Default);

            // type: Π (a b : Prop), Or (a → False) (b → False) → (And a b → False).
            let t_outer = kernel.pi(anon, or_na_nb, and_to_false, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, t_outer, BinderInfo::Default);
            let demorgan_or_not_and_ty = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b hor =>
            //   Or.elim (a → False) (b → False) (And a b → False) hor
            //     (fun na hab => na (And.left a b hab))
            //     (fun nb hab => nb (And.right a b hab)).
            let and_left_const = kernel.const_(and_left, vec![]);
            let and_right_const = kernel.const_(and_right, vec![]);
            let branch1 = {
                let na = kernel.fvar(na_fvar);
                let hab = kernel.fvar(hab1_fvar);
                let al = apply_all(kernel, and_left_const, &[a, b, hab]);
                let na_al = kernel.app(na, al);
                let inner = lam_fvar(kernel, hab1_fvar, and_ab, na_al, BinderInfo::Default);
                lam_fvar(kernel, na_fvar, na_ty, inner, BinderInfo::Default)
            };
            let branch2 = {
                let nb = kernel.fvar(nb_fvar);
                let hab = kernel.fvar(hab2_fvar);
                let ar = apply_all(kernel, and_right_const, &[a, b, hab]);
                let nb_ar = kernel.app(nb, ar);
                let inner = lam_fvar(kernel, hab2_fvar, and_ab, nb_ar, BinderInfo::Default);
                lam_fvar(kernel, nb_fvar, nb_ty, inner, BinderInfo::Default)
            };
            let hor = kernel.fvar(hor_fvar);
            let or_elim_const = kernel.const_(or_elim, vec![]);
            let applied = apply_all(
                kernel,
                or_elim_const,
                &[na_ty, nb_ty, and_to_false, hor, branch1, branch2],
            );

            let with_hor = lam_fvar(kernel, hor_fvar, or_na_nb, applied, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_hor, BinderInfo::Default);
            let demorgan_or_not_and_value =
                lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: demorgan_or_not_and,
                uparams: vec![],
                ty: demorgan_or_not_and_ty,
                value: demorgan_or_not_and_value,
            })?;
        }

        // --- not_not_em : Π (p : Prop), ¬¬(Or p (p → False)) ------------------
        // Excluded middle's double negation, provable outright: build ¬p from
        // ¬(p ∨ ¬p) (a hp : p would give p ∨ ¬p via Or.inl, contradicting the
        // hypothesis), then close with Or.inr on that very ¬p.
        let not_not_em = kernel.name_str(anon, "not_not_em");
        {
            let prop = kernel.prop();
            let p_fvar = 23_780;
            let h_fvar = 23_781;
            let hp_fvar = 23_782;
            let p = kernel.fvar(p_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let np_ty = kernel.pi(anon, p, false_const, BinderInfo::Default); // p → False
            let or_const = kernel.const_(or, vec![]);
            let or_p_np = apply_all(kernel, or_const, &[p, np_ty]);
            let or_to_false = kernel.pi(anon, or_p_np, false_const, BinderInfo::Default);

            // type: Π (p : Prop), ((Or p (p → False)) → False) → False.
            let t_outer = kernel.pi(anon, or_to_false, false_const, BinderInfo::Default);
            let not_not_em_ty = pi_fvar(kernel, p_fvar, prop, t_outer, BinderInfo::Default);

            // value: fun p h => h (Or.inr p (p → False) (fun hp => h (Or.inl p (p → False) hp))).
            let h = kernel.fvar(h_fvar);
            let or_inl_const = kernel.const_(or_inl, vec![]);
            let or_inr_const = kernel.const_(or_inr, vec![]);
            let np_proof = {
                let hp = kernel.fvar(hp_fvar);
                let inl_applied = apply_all(kernel, or_inl_const, &[p, np_ty, hp]);
                let h_inl = kernel.app(h, inl_applied);
                lam_fvar(kernel, hp_fvar, p, h_inl, BinderInfo::Default)
            };
            let inr_applied = apply_all(kernel, or_inr_const, &[p, np_ty, np_proof]);
            let h_inr = kernel.app(h, inr_applied);

            let with_h = lam_fvar(kernel, h_fvar, or_to_false, h_inr, BinderInfo::Default);
            let not_not_em_value = lam_fvar(kernel, p_fvar, prop, with_h, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: not_not_em,
                uparams: vec![],
                ty: not_not_em_ty,
                value: not_not_em_value,
            })?;
        }

        // --- dne_of_em : excluded middle → double-negation elimination -------
        let dne_of_em = kernel.name_str(anon, "dne_of_em");
        {
            let prop = kernel.prop();
            let em_fvar = 23_790;
            let p_fvar = 23_791;
            let hnn_fvar = 23_792;
            let hp_fvar = 23_793;
            let hnp_fvar = 23_794;
            let em_p_fvar = 23_795;
            let dummy_fvar = 23_796;
            let false_const = kernel.const_(false_, vec![]);
            let or_const = kernel.const_(or, vec![]);

            // em_ty : Π (p : Prop), Or p (p → False).
            let em_ty = {
                let p_for_ty = kernel.fvar(em_p_fvar);
                let np_for_ty = kernel.pi(anon, p_for_ty, false_const, BinderInfo::Default);
                let or_p_np_for_ty = apply_all(kernel, or_const, &[p_for_ty, np_for_ty]);
                pi_fvar(kernel, em_p_fvar, prop, or_p_np_for_ty, BinderInfo::Default)
            };

            let p = kernel.fvar(p_fvar);
            let np_ty = kernel.pi(anon, p, false_const, BinderInfo::Default); // p → False
            let nnp_ty = kernel.pi(anon, np_ty, false_const, BinderInfo::Default); // ¬¬p

            // type: Π (em : em_ty), Π (p : Prop), ¬¬p → p.
            let t_inner = kernel.pi(anon, nnp_ty, p, BinderInfo::Default);
            let with_p = pi_fvar(kernel, p_fvar, prop, t_inner, BinderInfo::Default);
            let dne_of_em_ty = pi_fvar(kernel, em_fvar, em_ty, with_p, BinderInfo::Default);

            // value: fun em p hnn =>
            //   Or.elim p (p → False) p (em p) (fun hp => hp)
            //     (fun hnp => False.rec.{0} (fun _ => p) (hnn hnp)).
            let em = kernel.fvar(em_fvar);
            let em_applied = kernel.app(em, p);
            let branch1 = {
                let hp = kernel.fvar(hp_fvar);
                lam_fvar(kernel, hp_fvar, p, hp, BinderInfo::Default)
            };
            let branch2 = {
                let hnn = kernel.fvar(hnn_fvar);
                let hnp = kernel.fvar(hnp_fvar);
                let hnn_hnp = kernel.app(hnn, hnp);
                let false_motive =
                    lam_fvar(kernel, dummy_fvar, false_const, p, BinderInfo::Default);
                let zero = kernel.level_zero();
                let false_rec_const = kernel.const_(false_rec, vec![zero]);
                let ex_falso = apply_all(kernel, false_rec_const, &[false_motive, hnn_hnp]);
                lam_fvar(kernel, hnp_fvar, np_ty, ex_falso, BinderInfo::Default)
            };
            let or_elim_const = kernel.const_(or_elim, vec![]);
            let applied = apply_all(
                kernel,
                or_elim_const,
                &[p, np_ty, p, em_applied, branch1, branch2],
            );

            let with_hnn = lam_fvar(kernel, hnn_fvar, nnp_ty, applied, BinderInfo::Default);
            let with_p_v = lam_fvar(kernel, p_fvar, prop, with_hnn, BinderInfo::Default);
            let dne_of_em_value = lam_fvar(kernel, em_fvar, em_ty, with_p_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: dne_of_em,
                uparams: vec![],
                ty: dne_of_em_ty,
                value: dne_of_em_value,
            })?;
        }

        // --- em_of_dne : double-negation elimination → excluded middle -------
        // The interesting direction: instantiate `dne` at `Or p ¬p` itself and
        // discharge its `¬¬(Or p ¬p)` hypothesis with `not_not_em`.
        let em_of_dne = kernel.name_str(anon, "em_of_dne");
        {
            let prop = kernel.prop();
            let dne_fvar = 23_800;
            let p_fvar = 23_801;
            let dne_p_fvar = 23_802;
            let false_const = kernel.const_(false_, vec![]);
            let or_const = kernel.const_(or, vec![]);

            // dne_ty : Π (p : Prop), (((p → False) → False) → p).
            let dne_ty = {
                let p_for_ty = kernel.fvar(dne_p_fvar);
                let np_for_ty = kernel.pi(anon, p_for_ty, false_const, BinderInfo::Default);
                let nnp_for_ty = kernel.pi(anon, np_for_ty, false_const, BinderInfo::Default);
                let inner_for_ty = kernel.pi(anon, nnp_for_ty, p_for_ty, BinderInfo::Default);
                pi_fvar(kernel, dne_p_fvar, prop, inner_for_ty, BinderInfo::Default)
            };

            let p = kernel.fvar(p_fvar);
            let np_ty = kernel.pi(anon, p, false_const, BinderInfo::Default);
            let or_p_np = apply_all(kernel, or_const, &[p, np_ty]);

            // type: Π (dne : dne_ty), Π (p : Prop), Or p (p → False).
            let with_p = pi_fvar(kernel, p_fvar, prop, or_p_np, BinderInfo::Default);
            let em_of_dne_ty = pi_fvar(kernel, dne_fvar, dne_ty, with_p, BinderInfo::Default);

            // value: fun dne p => dne (Or p (p → False)) (not_not_em p).
            let dne = kernel.fvar(dne_fvar);
            let dne_applied1 = kernel.app(dne, or_p_np);
            let not_not_em_const = kernel.const_(not_not_em, vec![]);
            let nnem_p = kernel.app(not_not_em_const, p);
            let applied = kernel.app(dne_applied1, nnem_p);

            let with_p_v = lam_fvar(kernel, p_fvar, prop, applied, BinderInfo::Default);
            let em_of_dne_value = lam_fvar(kernel, dne_fvar, dne_ty, with_p_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: em_of_dne,
                uparams: vec![],
                ty: em_of_dne_ty,
                value: em_of_dne_value,
            })?;
        }

        // --- peirce_of_em : excluded middle → Peirce's law -------------------
        let peirce_of_em = kernel.name_str(anon, "peirce_of_em");
        {
            let prop = kernel.prop();
            let em_fvar = 23_810;
            let a_fvar = 23_811;
            let b_fvar = 23_812;
            let h_fvar = 23_813;
            let hp_fvar = 23_814;
            let hna_fvar = 23_815;
            let ha_fvar = 23_816;
            let em_p_fvar = 23_817;
            let dummy_fvar = 23_818;
            let false_const = kernel.const_(false_, vec![]);
            let or_const = kernel.const_(or, vec![]);

            // em_ty : Π (p : Prop), Or p (p → False).
            let em_ty = {
                let p_for_ty = kernel.fvar(em_p_fvar);
                let np_for_ty = kernel.pi(anon, p_for_ty, false_const, BinderInfo::Default);
                let or_p_np_for_ty = apply_all(kernel, or_const, &[p_for_ty, np_for_ty]);
                pi_fvar(kernel, em_p_fvar, prop, or_p_np_for_ty, BinderInfo::Default)
            };

            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let ab_arrow = kernel.pi(anon, a, b, BinderInfo::Default); // a → b
            let h_ty = kernel.pi(anon, ab_arrow, a, BinderInfo::Default); // (a → b) → a

            // type: Π (em : em_ty), Π (a b : Prop), ((a → b) → a) → a.
            let t_inner = kernel.pi(anon, h_ty, a, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, t_inner, BinderInfo::Default);
            let with_a = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);
            let peirce_of_em_ty = pi_fvar(kernel, em_fvar, em_ty, with_a, BinderInfo::Default);

            // value: fun em a b h =>
            //   Or.elim a (a → False) a (em a) (fun hp => hp)
            //     (fun hna => h (fun ha => False.rec.{0} (fun _ => b) (hna ha))).
            let na_ty = kernel.pi(anon, a, false_const, BinderInfo::Default); // a → False
            let em = kernel.fvar(em_fvar);
            let em_applied = kernel.app(em, a);
            let branch1 = {
                let hp = kernel.fvar(hp_fvar);
                lam_fvar(kernel, hp_fvar, a, hp, BinderInfo::Default)
            };
            let branch2 = {
                let hna = kernel.fvar(hna_fvar);
                let ha = kernel.fvar(ha_fvar);
                let hna_ha = kernel.app(hna, ha);
                let false_motive =
                    lam_fvar(kernel, dummy_fvar, false_const, b, BinderInfo::Default);
                let zero = kernel.level_zero();
                let false_rec_const = kernel.const_(false_rec, vec![zero]);
                let ex_falso_b = apply_all(kernel, false_rec_const, &[false_motive, hna_ha]);
                let ab_proof = lam_fvar(kernel, ha_fvar, a, ex_falso_b, BinderInfo::Default);
                let h = kernel.fvar(h_fvar);
                let h_applied = kernel.app(h, ab_proof);
                lam_fvar(kernel, hna_fvar, na_ty, h_applied, BinderInfo::Default)
            };
            let or_elim_const = kernel.const_(or_elim, vec![]);
            let applied = apply_all(
                kernel,
                or_elim_const,
                &[a, na_ty, a, em_applied, branch1, branch2],
            );

            let with_h = lam_fvar(kernel, h_fvar, h_ty, applied, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_h, BinderInfo::Default);
            let with_a_v = lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);
            let peirce_of_em_value =
                lam_fvar(kernel, em_fvar, em_ty, with_a_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: peirce_of_em,
                uparams: vec![],
                ty: peirce_of_em_ty,
                value: peirce_of_em_value,
            })?;
        }

        // --- em_of_peirce : Peirce's law → excluded middle -------------------
        // Instantiate `peirce` at `(Or p ¬p, False)`: the same
        // Or.inr-from-refuted-Or.inl construction as `not_not_em` discharges
        // its `(Or p ¬p → False) → Or p ¬p` hypothesis directly.
        let em_of_peirce = kernel.name_str(anon, "em_of_peirce");
        {
            let prop = kernel.prop();
            let peirce_fvar = 23_820;
            let p_fvar = 23_821;
            let h_fvar = 23_822;
            let hp_fvar = 23_823;
            let pa_fvar = 23_824;
            let pb_fvar = 23_825;
            let false_const = kernel.const_(false_, vec![]);
            let or_const = kernel.const_(or, vec![]);

            // peirce_ty : Π (a b : Prop), ((a → b) → a) → a.
            let peirce_ty = {
                let pa = kernel.fvar(pa_fvar);
                let pb = kernel.fvar(pb_fvar);
                let pab_arrow = kernel.pi(anon, pa, pb, BinderInfo::Default);
                let ph_ty = kernel.pi(anon, pab_arrow, pa, BinderInfo::Default);
                let p_inner = kernel.pi(anon, ph_ty, pa, BinderInfo::Default);
                let with_pb = pi_fvar(kernel, pb_fvar, prop, p_inner, BinderInfo::Default);
                pi_fvar(kernel, pa_fvar, prop, with_pb, BinderInfo::Default)
            };

            let p = kernel.fvar(p_fvar);
            let np_ty = kernel.pi(anon, p, false_const, BinderInfo::Default); // p → False
            let or_p_np = apply_all(kernel, or_const, &[p, np_ty]);

            // type: Π (peirce : peirce_ty), Π (p : Prop), Or p (p → False).
            let with_p = pi_fvar(kernel, p_fvar, prop, or_p_np, BinderInfo::Default);
            let em_of_peirce_ty =
                pi_fvar(kernel, peirce_fvar, peirce_ty, with_p, BinderInfo::Default);

            // value: fun peirce p =>
            //   peirce (Or p (p → False)) False
            //     (fun h => Or.inr p (p → False) (fun hp => h (Or.inl p (p → False) hp))).
            let peirce = kernel.fvar(peirce_fvar);
            let peirce_applied1 = apply_all(kernel, peirce, &[or_p_np, false_const]);
            let h_dom_ty = kernel.pi(anon, or_p_np, false_const, BinderInfo::Default); // A → False
            let or_inl_const = kernel.const_(or_inl, vec![]);
            let or_inr_const = kernel.const_(or_inr, vec![]);
            let inner_proof = {
                let h = kernel.fvar(h_fvar);
                let np_proof = {
                    let hp = kernel.fvar(hp_fvar);
                    let inl_applied = apply_all(kernel, or_inl_const, &[p, np_ty, hp]);
                    let h_inl = kernel.app(h, inl_applied);
                    lam_fvar(kernel, hp_fvar, p, h_inl, BinderInfo::Default)
                };
                let inr_applied = apply_all(kernel, or_inr_const, &[p, np_ty, np_proof]);
                lam_fvar(kernel, h_fvar, h_dom_ty, inr_applied, BinderInfo::Default)
            };
            let applied_final = kernel.app(peirce_applied1, inner_proof);

            let with_p_v = lam_fvar(kernel, p_fvar, prop, applied_final, BinderInfo::Default);
            let em_of_peirce_value = lam_fvar(
                kernel,
                peirce_fvar,
                peirce_ty,
                with_p_v,
                BinderInfo::Default,
            );

            kernel.add_declaration(Declaration::Theorem {
                name: em_of_peirce,
                uparams: vec![],
                ty: em_of_peirce_ty,
                value: em_of_peirce_value,
            })?;
        }

        // --- not_not_not_intro : Π (a : Prop), ¬a → ¬¬¬a ---------------------
        // The other half of the ¬¬¬a ↔ ¬a pair (`not_not_not` above is
        // ¬¬¬a → ¬a): `not_not_intro` instantiated at `¬a` itself.
        let not_not_not_intro = kernel.name_str(anon, "not_not_not_intro");
        {
            let prop = kernel.prop();
            let a_fvar = 24_000;
            let na_fvar = 24_001;
            let a = kernel.fvar(a_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let na_ty = kernel.pi(anon, a, false_const, BinderInfo::Default); // ¬a
            let nna_ty = kernel.pi(anon, na_ty, false_const, BinderInfo::Default); // ¬¬a
            let nnna_ty = kernel.pi(anon, nna_ty, false_const, BinderInfo::Default); // ¬¬¬a

            // type: Π (a : Prop), ¬a → ¬¬¬a.
            let with_na = kernel.pi(anon, na_ty, nnna_ty, BinderInfo::Default);
            let not_not_not_intro_ty = pi_fvar(kernel, a_fvar, prop, with_na, BinderInfo::Default);

            // value: fun a na => not_not_intro (a → False) na.
            let not_not_intro_const = kernel.const_(not_not_intro, vec![]);
            let na = kernel.fvar(na_fvar);
            let applied = apply_all(kernel, not_not_intro_const, &[na_ty, na]);
            let with_na_v = lam_fvar(kernel, na_fvar, na_ty, applied, BinderInfo::Default);
            let not_not_not_intro_value =
                lam_fvar(kernel, a_fvar, prop, with_na_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: not_not_not_intro,
                uparams: vec![],
                ty: not_not_not_intro_ty,
                value: not_not_not_intro_value,
            })?;
        }

        // --- not_not_and : Π (a b : Prop), ¬¬a → ¬¬b → ¬¬(And a b) ----------
        // The conjunction case of the Gödel–Gentzen negative translation:
        // `fun ha => nnb (fun hb => hnab (And.intro a b ha hb))` refutes
        // `¬a` using `nnb`/`hnab`, closing `nna`'s own `¬¬a` obligation.
        let not_not_and = kernel.name_str(anon, "not_not_and");
        {
            let prop = kernel.prop();
            let a_fvar = 24_010;
            let b_fvar = 24_011;
            let nna_fvar = 24_012;
            let nnb_fvar = 24_013;
            let hnab_fvar = 24_014;
            let ha_fvar = 24_015;
            let hb_fvar = 24_016;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let na_ty = kernel.pi(anon, a, false_const, BinderInfo::Default); // ¬a
            let nna_ty = kernel.pi(anon, na_ty, false_const, BinderInfo::Default); // ¬¬a
            let nb_ty = kernel.pi(anon, b, false_const, BinderInfo::Default); // ¬b
            let nnb_ty = kernel.pi(anon, nb_ty, false_const, BinderInfo::Default); // ¬¬b
            let and_const = kernel.const_(and, vec![]);
            let and_ab = apply_all(kernel, and_const, &[a, b]);
            let nab_ty = kernel.pi(anon, and_ab, false_const, BinderInfo::Default); // ¬(a∧b)
            let nnab_ty = kernel.pi(anon, nab_ty, false_const, BinderInfo::Default); // ¬¬(a∧b)

            // type: Π (a b : Prop), ¬¬a → ¬¬b → ¬¬(And a b).
            let t3 = kernel.pi(anon, nnb_ty, nnab_ty, BinderInfo::Default);
            let t2 = kernel.pi(anon, nna_ty, t3, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, t2, BinderInfo::Default);
            let not_not_and_ty = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b nna nnb hnab =>
            //   nna (fun ha => nnb (fun hb => hnab (And.intro a b ha hb))).
            let and_intro_const = kernel.const_(and_intro, vec![]);
            let hnab = kernel.fvar(hnab_fvar);
            let nnb = kernel.fvar(nnb_fvar);
            let nna = kernel.fvar(nna_fvar);
            let inner_body = {
                let ha = kernel.fvar(ha_fvar);
                let hb = kernel.fvar(hb_fvar);
                let intro = apply_all(kernel, and_intro_const, &[a, b, ha, hb]);
                let hnab_applied = kernel.app(hnab, intro);
                let f_hb = lam_fvar(kernel, hb_fvar, b, hnab_applied, BinderInfo::Default);
                let nnb_applied = kernel.app(nnb, f_hb);
                lam_fvar(kernel, ha_fvar, a, nnb_applied, BinderInfo::Default)
            };
            let nna_applied = kernel.app(nna, inner_body);

            let with_hnab = lam_fvar(kernel, hnab_fvar, nab_ty, nna_applied, BinderInfo::Default);
            let with_nnb = lam_fvar(kernel, nnb_fvar, nnb_ty, with_hnab, BinderInfo::Default);
            let with_nna = lam_fvar(kernel, nna_fvar, nna_ty, with_nnb, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_nna, BinderInfo::Default);
            let not_not_and_value = lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: not_not_and,
                uparams: vec![],
                ty: not_not_and_ty,
                value: not_not_and_value,
            })?;
        }

        // --- not_not_imp : Π (a b : Prop), (a → b) → ¬¬a → ¬¬b ---------------
        // Functoriality of double negation: `fun ha => hnb (f ha)` refutes `a`
        // from a refutation of `b`, closing `nna`'s `¬¬a` obligation. This is
        // also the monotonicity form (`a → b` monotone gives `¬¬a → ¬¬b`
        // monotone), so no separate `not_not_mono` is declared.
        let not_not_imp = kernel.name_str(anon, "not_not_imp");
        {
            let prop = kernel.prop();
            let a_fvar = 24_020;
            let b_fvar = 24_021;
            let f_fvar = 24_022;
            let nna_fvar = 24_023;
            let hnb_fvar = 24_024;
            let ha_fvar = 24_025;
            let a = kernel.fvar(a_fvar);
            let b = kernel.fvar(b_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let ab_ty = kernel.pi(anon, a, b, BinderInfo::Default); // a → b
            let na_ty = kernel.pi(anon, a, false_const, BinderInfo::Default); // ¬a
            let nna_ty = kernel.pi(anon, na_ty, false_const, BinderInfo::Default); // ¬¬a
            let nb_ty = kernel.pi(anon, b, false_const, BinderInfo::Default); // ¬b
            let nnb_ty = kernel.pi(anon, nb_ty, false_const, BinderInfo::Default); // ¬¬b

            // type: Π (a b : Prop), (a → b) → ¬¬a → ¬¬b.
            let t3 = kernel.pi(anon, nna_ty, nnb_ty, BinderInfo::Default);
            let t2 = kernel.pi(anon, ab_ty, t3, BinderInfo::Default);
            let with_b = pi_fvar(kernel, b_fvar, prop, t2, BinderInfo::Default);
            let not_not_imp_ty = pi_fvar(kernel, a_fvar, prop, with_b, BinderInfo::Default);

            // value: fun a b f nna hnb => nna (fun ha => hnb (f ha)).
            let f = kernel.fvar(f_fvar);
            let nna = kernel.fvar(nna_fvar);
            let hnb = kernel.fvar(hnb_fvar);
            let inner = {
                let ha = kernel.fvar(ha_fvar);
                let f_ha = kernel.app(f, ha);
                let hnb_f_ha = kernel.app(hnb, f_ha);
                lam_fvar(kernel, ha_fvar, a, hnb_f_ha, BinderInfo::Default)
            };
            let nna_applied = kernel.app(nna, inner);
            let with_hnb = lam_fvar(kernel, hnb_fvar, nb_ty, nna_applied, BinderInfo::Default);
            let with_nna = lam_fvar(kernel, nna_fvar, nna_ty, with_hnb, BinderInfo::Default);
            let with_f = lam_fvar(kernel, f_fvar, ab_ty, with_nna, BinderInfo::Default);
            let with_b_v = lam_fvar(kernel, b_fvar, prop, with_f, BinderInfo::Default);
            let not_not_imp_value = lam_fvar(kernel, a_fvar, prop, with_b_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: not_not_imp,
                uparams: vec![],
                ty: not_not_imp_ty,
                value: not_not_imp_value,
            })?;
        }

        // --- Bool.false_ne_true : Eq Bool Bool.false Bool.true → False -------
        // Bool's disjointness discriminator (Lean's `Bool.noConfusion`,
        // specialised to `False`): transport the trivial `True.intro : D
        // Bool.false` along a hypothetical `false = true` through the
        // type-VALUED discriminator `D := fun b => Bool.rec.{1}
        // (motive := fun _ => Prop) True False b` (`D Bool.false ≡ True`,
        // `D Bool.true ≡ False` by ι), landing on `D Bool.true ≡ False`. This
        // is what makes the `Decidable.of_decide_eq_*` spec lemmas below
        // possible: ruling out the impossible branch of a computed `Bool`
        // needs Bool's two values to be provably distinct, and nothing in the
        // prelude supplied that before this declaration.
        let bool_false_ne_true = kernel.name_str(bool_, "false_ne_true");
        {
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            let h_fvar = 24_030;
            let x_fvar = 24_031;
            let dummy_fvar = 24_032;

            let bool_const = kernel.const_(bool_, vec![]);
            let bool_false_v = kernel.const_(bool_false, vec![]);
            let bool_true_v = kernel.const_(bool_true, vec![]);
            let false_const = kernel.const_(false_, vec![]);
            let true_const = kernel.const_(true_, vec![]);
            let prop = kernel.prop();

            // type: Eq Bool Bool.false Bool.true → False.
            let heq_ty = eq_app(kernel, eq, one, bool_const, bool_false_v, bool_true_v);
            let bool_false_ne_true_ty = kernel.pi(anon, heq_ty, false_const, BinderInfo::Default);

            // D := fun (_ : Bool) => Prop, via Bool.rec.{1};
            // D Bool.false ≡ True, D Bool.true ≡ False.
            let d_motive = lam_fvar(kernel, dummy_fvar, bool_const, prop, BinderInfo::Default);
            let bool_rec_one = kernel.const_(bool_rec, vec![one]);

            // motive for the transport: fun (x:Bool) (_:Eq Bool false x) => D x.
            let x = kernel.fvar(x_fvar);
            let eq_false_x_ty = eq_app(kernel, eq, one, bool_const, bool_false_v, x);
            let d_x = apply_all(
                kernel,
                bool_rec_one,
                &[d_motive, true_const, false_const, x],
            );
            let eq_motive_inner = kernel.lam(anon, eq_false_x_ty, d_x, BinderInfo::Default);
            let eq_motive = lam_fvar(
                kernel,
                x_fvar,
                bool_const,
                eq_motive_inner,
                BinderInfo::Default,
            );

            // refl case: True.intro : D Bool.false ≡ True.
            let true_intro_const = kernel.const_(true_intro, vec![]);

            // value: fun h => Eq.rec.{0,1} Bool Bool.false eq_motive True.intro Bool.true h.
            let eq_rec_const = kernel.const_(eq_rec, vec![zero, one]);
            let h = kernel.fvar(h_fvar);
            let applied = apply_all(
                kernel,
                eq_rec_const,
                &[
                    bool_const,
                    bool_false_v,
                    eq_motive,
                    true_intro_const,
                    bool_true_v,
                    h,
                ],
            );
            let bool_false_ne_true_value =
                lam_fvar(kernel, h_fvar, heq_ty, applied, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: bool_false_ne_true,
                uparams: vec![],
                ty: bool_false_ne_true_ty,
                value: bool_false_ne_true_value,
            })?;
        }

        // --- Bool.true_ne_false : Eq Bool Bool.true Bool.false → False -------
        let bool_true_ne_false = kernel.name_str(bool_, "true_ne_false");
        {
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            let h_fvar = 24_040;

            let bool_const = kernel.const_(bool_, vec![]);
            let bool_false_v = kernel.const_(bool_false, vec![]);
            let bool_true_v = kernel.const_(bool_true, vec![]);
            let false_const = kernel.const_(false_, vec![]);

            let heq_ty = eq_app(kernel, eq, one, bool_const, bool_true_v, bool_false_v);
            let bool_true_ne_false_ty = kernel.pi(anon, heq_ty, false_const, BinderInfo::Default);

            // value: fun h => Bool.false_ne_true (Eq.symm Bool Bool.true Bool.false h).
            let eq_symm_const = kernel.const_(eq_symm, vec![one]);
            let h = kernel.fvar(h_fvar);
            let symm_h = apply_all(
                kernel,
                eq_symm_const,
                &[bool_const, bool_true_v, bool_false_v, h],
            );
            let bool_false_ne_true_const = kernel.const_(bool_false_ne_true, vec![]);
            let applied = kernel.app(bool_false_ne_true_const, symm_h);
            let bool_true_ne_false_value =
                lam_fvar(kernel, h_fvar, heq_ty, applied, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: bool_true_ne_false,
                uparams: vec![],
                ty: bool_true_ne_false_ty,
                value: bool_true_ne_false_value,
            })?;
        }

        // --- Decidable (p : Prop) : Type, Decidable.isFalse | isTrue --------
        // The `Type`-valued decision: unlike `Or` (a two-constructor `Prop`
        // that eliminates only into `Prop` — see the module doc), `Decidable`
        // lives at `Sort 1` and so its generated recursor gets a genuine
        // elimination-level parameter and eliminates into an arbitrary
        // `Sort v` (`Decidable.byCases` below). Constructor order follows the
        // `isFalse`-before-`isTrue` convention already used for
        // `Bool.false`/`Bool.true`.
        let decidable = kernel.name_str(anon, "Decidable");
        let decidable_is_false = kernel.name_str(decidable, "isFalse");
        let decidable_is_true = kernel.name_str(decidable, "isTrue");
        {
            let prop = kernel.prop();
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            let sort1 = kernel.sort(one);
            // ty := Π (p : Prop), Sort 1.
            let decidable_ty = kernel.pi(anon, prop, sort1, BinderInfo::Default);

            let decidable_const = kernel.const_(decidable, vec![]);
            let false_const = kernel.const_(false_, vec![]);

            // isFalse : Π (p : Prop) (h : p → False), Decidable p.
            let is_false_ty = {
                let p1 = kernel.bvar(1); // p, under [p, h]
                let dec_p = kernel.app(decidable_const, p1);
                let p0 = kernel.bvar(0); // p, under [p] (h's own domain)
                let h_ty = kernel.pi(anon, p0, false_const, BinderInfo::Default);
                let inner = kernel.pi(anon, h_ty, dec_p, BinderInfo::Default);
                kernel.pi(anon, prop, inner, BinderInfo::Default)
            };
            // isTrue : Π (p : Prop) (h : p), Decidable p.
            let is_true_ty = {
                let p1 = kernel.bvar(1);
                let dec_p = kernel.app(decidable_const, p1);
                let p0 = kernel.bvar(0);
                let inner = kernel.pi(anon, p0, dec_p, BinderInfo::Default);
                kernel.pi(anon, prop, inner, BinderInfo::Default)
            };
            kernel.add_inductive(
                decidable,
                &[],
                1,
                decidable_ty,
                &[
                    (decidable_is_false, is_false_ty),
                    (decidable_is_true, is_true_ty),
                ],
            )?;
        }
        let decidable_rec = kernel.name_str(decidable, "rec");

        // --- Decidable.decide : Π (p : Prop), Decidable p → Bool -------------
        // A `Definition`, not a `Theorem`: its codomain `Bool` is not `Prop`
        // (the same reason `absurd` above is a `Definition`, and the same
        // real-Lean-kernel divergence that comment documents).
        let decide = kernel.name_str(decidable, "decide");
        {
            let prop = kernel.prop();
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            let p_fvar = 24_050;
            let d_fvar = 24_051;
            let dummy_fvar = 24_052;
            let hf_fvar = 24_053;
            let ht_fvar = 24_054;

            let p = kernel.fvar(p_fvar);
            let decidable_const = kernel.const_(decidable, vec![]);
            let dec_p = kernel.app(decidable_const, p);
            let false_const = kernel.const_(false_, vec![]);
            let hf_ty = kernel.pi(anon, p, false_const, BinderInfo::Default); // p → False
            let bool_const = kernel.const_(bool_, vec![]);

            // type: Π (p : Prop) (d : Decidable p), Bool.
            let t_outer = kernel.pi(anon, dec_p, bool_const, BinderInfo::Default);
            let decide_ty = pi_fvar(kernel, p_fvar, prop, t_outer, BinderInfo::Default);

            // value: fun p d => Decidable.rec.{1} p (motive := fun _ => Bool)
            //   (fun _ => Bool.false) (fun _ => Bool.true) d.
            let motive = lam_fvar(kernel, dummy_fvar, dec_p, bool_const, BinderInfo::Default);
            let bool_false_v = kernel.const_(bool_false, vec![]);
            let bool_true_v = kernel.const_(bool_true, vec![]);
            let minor_is_false =
                lam_fvar(kernel, hf_fvar, hf_ty, bool_false_v, BinderInfo::Default);
            let minor_is_true = lam_fvar(kernel, ht_fvar, p, bool_true_v, BinderInfo::Default);
            let decidable_rec_const = kernel.const_(decidable_rec, vec![one]);
            let d = kernel.fvar(d_fvar);
            let applied = apply_all(
                kernel,
                decidable_rec_const,
                &[p, motive, minor_is_false, minor_is_true, d],
            );

            let with_d = lam_fvar(kernel, d_fvar, dec_p, applied, BinderInfo::Default);
            let decide_value = lam_fvar(kernel, p_fvar, prop, with_d, BinderInfo::Default);

            kernel.add_declaration(Declaration::Definition {
                name: decide,
                uparams: vec![],
                ty: decide_ty,
                value: decide_value,
                hint: ReducibilityHint::Regular(0),
            })?;
        }

        // --- Decidable.of_decide_eq_true : Π (p : Prop) (d : Decidable p), ---
        //     Eq Bool (decide p d) Bool.true → p --------------------------
        let of_decide_eq_true = kernel.name_str(decidable, "of_decide_eq_true");
        {
            let prop = kernel.prop();
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            let p_fvar = 24_060;
            let d_fvar = 24_061;
            let dvar_fvar = 24_062;
            let hf_fvar = 24_063;
            let ht_fvar = 24_064;
            let heq_fvar = 24_065;

            let p = kernel.fvar(p_fvar);
            let decidable_const = kernel.const_(decidable, vec![]);
            let dec_p = kernel.app(decidable_const, p);
            let false_const = kernel.const_(false_, vec![]);
            let hf_ty = kernel.pi(anon, p, false_const, BinderInfo::Default); // p → False
            let bool_const = kernel.const_(bool_, vec![]);
            let bool_true_v = kernel.const_(bool_true, vec![]);
            let bool_false_v = kernel.const_(bool_false, vec![]);
            let decide_const = kernel.const_(decide, vec![]);

            let d = kernel.fvar(d_fvar);
            let decide_p_d = apply_all(kernel, decide_const, &[p, d]);
            let eq_true_d_ty = eq_app(kernel, eq, one, bool_const, decide_p_d, bool_true_v);

            // type: Π (p : Prop) (d : Decidable p), Eq Bool (decide p d) Bool.true → p.
            let t_outer = kernel.pi(anon, eq_true_d_ty, p, BinderInfo::Default);
            let with_d = pi_fvar(kernel, d_fvar, dec_p, t_outer, BinderInfo::Default);
            let of_decide_eq_true_ty = pi_fvar(kernel, p_fvar, prop, with_d, BinderInfo::Default);

            // value: fun p d => Decidable.rec.{0} p
            //   (motive := fun dvar => Eq Bool (decide p dvar) Bool.true → p)
            //   (fun h heq => False.rec p (Bool.false_ne_true heq))
            //   (fun h _ => h)
            //   d.
            let decide_const2 = kernel.const_(decide, vec![]);
            let dvar = kernel.fvar(dvar_fvar);
            let decide_p_dvar = apply_all(kernel, decide_const2, &[p, dvar]);
            let eq_true_dvar_ty = eq_app(kernel, eq, one, bool_const, decide_p_dvar, bool_true_v);
            let motive_inner = kernel.pi(anon, eq_true_dvar_ty, p, BinderInfo::Default);
            let motive = lam_fvar(kernel, dvar_fvar, dec_p, motive_inner, BinderInfo::Default);

            // minor_isFalse, built at the reduced type
            // (decide p (isFalse p h) ≡ Bool.false).
            let minor_is_false = {
                let heq_ty = eq_app(kernel, eq, one, bool_const, bool_false_v, bool_true_v);
                let bool_false_ne_true_const = kernel.const_(bool_false_ne_true, vec![]);
                let heq = kernel.fvar(heq_fvar);
                let contradiction = kernel.app(bool_false_ne_true_const, heq);
                let false_rec_const = kernel.const_(false_rec, vec![zero]);
                let false_motive = {
                    let dummy_fvar = 24_066;
                    lam_fvar(kernel, dummy_fvar, false_const, p, BinderInfo::Default)
                };
                let body = apply_all(kernel, false_rec_const, &[false_motive, contradiction]);
                let with_heq = lam_fvar(kernel, heq_fvar, heq_ty, body, BinderInfo::Default);
                lam_fvar(kernel, hf_fvar, hf_ty, with_heq, BinderInfo::Default)
            };

            // minor_isTrue, trivial: decide p (isTrue p h) ≡ Bool.true, so the
            // (now-refl) equality is simply discarded.
            let minor_is_true = {
                let ht = kernel.fvar(ht_fvar);
                let eq_refl_ty = eq_app(kernel, eq, one, bool_const, bool_true_v, bool_true_v);
                let discard_fvar = 24_067;
                let inner = lam_fvar(kernel, discard_fvar, eq_refl_ty, ht, BinderInfo::Default);
                lam_fvar(kernel, ht_fvar, p, inner, BinderInfo::Default)
            };

            let decidable_rec_const = kernel.const_(decidable_rec, vec![zero]);
            let applied = apply_all(
                kernel,
                decidable_rec_const,
                &[p, motive, minor_is_false, minor_is_true, d],
            );

            let with_d_v = lam_fvar(kernel, d_fvar, dec_p, applied, BinderInfo::Default);
            let of_decide_eq_true_value =
                lam_fvar(kernel, p_fvar, prop, with_d_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: of_decide_eq_true,
                uparams: vec![],
                ty: of_decide_eq_true_ty,
                value: of_decide_eq_true_value,
            })?;
        }

        // --- Decidable.of_decide_eq_false : Π (p : Prop) (d : Decidable p), --
        //     Eq Bool (decide p d) Bool.false → (p → False) -----------------
        let of_decide_eq_false = kernel.name_str(decidable, "of_decide_eq_false");
        {
            let prop = kernel.prop();
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            let p_fvar = 24_070;
            let d_fvar = 24_071;
            let dvar_fvar = 24_072;
            let hf_fvar = 24_073;
            let ht_fvar = 24_074;
            let heq_fvar = 24_075;

            let p = kernel.fvar(p_fvar);
            let decidable_const = kernel.const_(decidable, vec![]);
            let dec_p = kernel.app(decidable_const, p);
            let false_const = kernel.const_(false_, vec![]);
            let hf_ty = kernel.pi(anon, p, false_const, BinderInfo::Default); // p → False
            let bool_const = kernel.const_(bool_, vec![]);
            let bool_true_v = kernel.const_(bool_true, vec![]);
            let bool_false_v = kernel.const_(bool_false, vec![]);
            let decide_const = kernel.const_(decide, vec![]);

            let d = kernel.fvar(d_fvar);
            let decide_p_d = apply_all(kernel, decide_const, &[p, d]);
            let eq_false_d_ty = eq_app(kernel, eq, one, bool_const, decide_p_d, bool_false_v);

            // type: Π (p : Prop) (d : Decidable p),
            //   Eq Bool (decide p d) Bool.false → (p → False).
            let t_outer = kernel.pi(anon, eq_false_d_ty, hf_ty, BinderInfo::Default);
            let with_d = pi_fvar(kernel, d_fvar, dec_p, t_outer, BinderInfo::Default);
            let of_decide_eq_false_ty = pi_fvar(kernel, p_fvar, prop, with_d, BinderInfo::Default);

            // value: fun p d => Decidable.rec.{0} p
            //   (motive := fun dvar => Eq Bool (decide p dvar) Bool.false → (p → False))
            //   (fun h _ => h)
            //   (fun h heq => False.rec (p → False) (Bool.true_ne_false heq))
            //   d.
            let decide_const2 = kernel.const_(decide, vec![]);
            let dvar = kernel.fvar(dvar_fvar);
            let decide_p_dvar = apply_all(kernel, decide_const2, &[p, dvar]);
            let eq_false_dvar_ty = eq_app(kernel, eq, one, bool_const, decide_p_dvar, bool_false_v);
            let motive_inner = kernel.pi(anon, eq_false_dvar_ty, hf_ty, BinderInfo::Default);
            let motive = lam_fvar(kernel, dvar_fvar, dec_p, motive_inner, BinderInfo::Default);

            // minor_isFalse, trivial: decide p (isFalse p h) ≡ Bool.false, so
            // the (now-refl) equality is simply discarded.
            let minor_is_false = {
                let hf = kernel.fvar(hf_fvar);
                let eq_refl_ty = eq_app(kernel, eq, one, bool_const, bool_false_v, bool_false_v);
                let discard_fvar = 24_076;
                let inner = lam_fvar(kernel, discard_fvar, eq_refl_ty, hf, BinderInfo::Default);
                lam_fvar(kernel, hf_fvar, hf_ty, inner, BinderInfo::Default)
            };

            // minor_isTrue, built at the reduced type
            // (decide p (isTrue p h) ≡ Bool.true).
            let minor_is_true = {
                let heq_ty = eq_app(kernel, eq, one, bool_const, bool_true_v, bool_false_v);
                let bool_true_ne_false_const = kernel.const_(bool_true_ne_false, vec![]);
                let heq = kernel.fvar(heq_fvar);
                let contradiction = kernel.app(bool_true_ne_false_const, heq);
                let false_rec_const = kernel.const_(false_rec, vec![zero]);
                let false_motive = {
                    let dummy_fvar = 24_077;
                    lam_fvar(kernel, dummy_fvar, false_const, hf_ty, BinderInfo::Default)
                };
                let body = apply_all(kernel, false_rec_const, &[false_motive, contradiction]);
                let with_heq = lam_fvar(kernel, heq_fvar, heq_ty, body, BinderInfo::Default);
                lam_fvar(kernel, ht_fvar, p, with_heq, BinderInfo::Default)
            };

            let decidable_rec_const = kernel.const_(decidable_rec, vec![zero]);
            let applied = apply_all(
                kernel,
                decidable_rec_const,
                &[p, motive, minor_is_false, minor_is_true, d],
            );

            let with_d_v = lam_fvar(kernel, d_fvar, dec_p, applied, BinderInfo::Default);
            let of_decide_eq_false_value =
                lam_fvar(kernel, p_fvar, prop, with_d_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: of_decide_eq_false,
                uparams: vec![],
                ty: of_decide_eq_false_ty,
                value: of_decide_eq_false_value,
            })?;
        }

        // --- Decidable.em : Π (p : Prop), Decidable p → Or p (p → False) -----
        // Excluded middle, exactly where a `Decidable` witness exists: case
        // split on `d` (into `Prop`, so `Or.rec`'s restriction to `Prop`
        // never bites) and re-pack with `Or.inl`/`Or.inr`.
        let decidable_em = kernel.name_str(decidable, "em");
        {
            let prop = kernel.prop();
            let zero = kernel.level_zero();
            let p_fvar = 24_080;
            let d_fvar = 24_081;
            let dummy_fvar = 24_082;
            let hf_fvar = 24_083;
            let ht_fvar = 24_084;

            let p = kernel.fvar(p_fvar);
            let decidable_const = kernel.const_(decidable, vec![]);
            let dec_p = kernel.app(decidable_const, p);
            let false_const = kernel.const_(false_, vec![]);
            let hf_ty = kernel.pi(anon, p, false_const, BinderInfo::Default); // p → False
            let or_const = kernel.const_(or, vec![]);
            let or_p_np = apply_all(kernel, or_const, &[p, hf_ty]);

            // type: Π (p : Prop) (d : Decidable p), Or p (p → False).
            let t_outer = kernel.pi(anon, dec_p, or_p_np, BinderInfo::Default);
            let decidable_em_ty = pi_fvar(kernel, p_fvar, prop, t_outer, BinderInfo::Default);

            // value: fun p d => Decidable.rec.{0} p (motive := fun _ => Or p (p→False))
            //   (fun h => Or.inr p (p→False) h) (fun h => Or.inl p (p→False) h) d.
            let motive = lam_fvar(kernel, dummy_fvar, dec_p, or_p_np, BinderInfo::Default);
            let or_inl_const = kernel.const_(or_inl, vec![]);
            let or_inr_const = kernel.const_(or_inr, vec![]);
            let minor_is_false = {
                let hf = kernel.fvar(hf_fvar);
                let body = apply_all(kernel, or_inr_const, &[p, hf_ty, hf]);
                lam_fvar(kernel, hf_fvar, hf_ty, body, BinderInfo::Default)
            };
            let minor_is_true = {
                let ht = kernel.fvar(ht_fvar);
                let body = apply_all(kernel, or_inl_const, &[p, hf_ty, ht]);
                lam_fvar(kernel, ht_fvar, p, body, BinderInfo::Default)
            };
            let decidable_rec_const = kernel.const_(decidable_rec, vec![zero]);
            let d = kernel.fvar(d_fvar);
            let applied = apply_all(
                kernel,
                decidable_rec_const,
                &[p, motive, minor_is_false, minor_is_true, d],
            );

            let with_d = lam_fvar(kernel, d_fvar, dec_p, applied, BinderInfo::Default);
            let decidable_em_value = lam_fvar(kernel, p_fvar, prop, with_d, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: decidable_em,
                uparams: vec![],
                ty: decidable_em_ty,
                value: decidable_em_value,
            })?;
        }

        // --- Decidable.byCases.{v} : Π (p : Prop) (C : Sort v) ---------------
        //     (d : Decidable p), (p → C) → ((p → False) → C) → C ------------
        // Case-split with an ARBITRARY-sort result: unlike `Decidable.em`
        // (whose conclusion is the `Prop` `Or p (p → False)`), this lands in
        // any `Sort v` -- exactly what `Or.rec` structurally cannot offer
        // (module doc), and exactly the wall named in the assignment: a
        // `Decidable` hypothesis lets a construction SELECT data, not just
        // prove a proposition. A `Definition`, not a `Theorem`, for the same
        // reason `decide` above is (its codomain is an arbitrary `Sort v`,
        // not `Prop`).
        let decidable_by_cases_vparam = kernel.name_str(anon, "v");
        let decidable_by_cases = kernel.name_str(decidable, "byCases");
        {
            let prop = kernel.prop();
            let v_lvl = kernel.level_param(decidable_by_cases_vparam);
            let sort_v = kernel.sort(v_lvl);

            let p_fvar = 24_090;
            let c_fvar = 24_091;
            let d_fvar = 24_092;
            let dummy_fvar = 24_093;
            let hpos_fvar = 24_094;
            let hneg_fvar = 24_095;

            let p = kernel.fvar(p_fvar);
            let c = kernel.fvar(c_fvar);
            let decidable_const = kernel.const_(decidable, vec![]);
            let dec_p = kernel.app(decidable_const, p);
            let false_const = kernel.const_(false_, vec![]);
            let hf_ty = kernel.pi(anon, p, false_const, BinderInfo::Default); // p → False
            let pc_ty = kernel.pi(anon, p, c, BinderInfo::Default); // p → C
            let nc_ty = kernel.pi(anon, hf_ty, c, BinderInfo::Default); // (p → False) → C

            // type: Π (p : Prop) (C : Sort v) (d : Decidable p),
            //   (p → C) → ((p → False) → C) → C.
            let t_inner = kernel.pi(anon, nc_ty, c, BinderInfo::Default);
            let t_mid = kernel.pi(anon, pc_ty, t_inner, BinderInfo::Default);
            let t_outer = kernel.pi(anon, dec_p, t_mid, BinderInfo::Default);
            let with_c = pi_fvar(kernel, c_fvar, sort_v, t_outer, BinderInfo::Default);
            let decidable_by_cases_ty = pi_fvar(kernel, p_fvar, prop, with_c, BinderInfo::Default);

            // value: fun p C d hpos hneg => Decidable.rec.{v} p
            //   (motive := fun _ => C) hneg hpos d.
            let motive = lam_fvar(kernel, dummy_fvar, dec_p, c, BinderInfo::Default);
            let decidable_rec_const = kernel.const_(decidable_rec, vec![v_lvl]);
            let d = kernel.fvar(d_fvar);
            let hpos = kernel.fvar(hpos_fvar);
            let hneg = kernel.fvar(hneg_fvar);
            let applied = apply_all(kernel, decidable_rec_const, &[p, motive, hneg, hpos, d]);

            let with_hneg = lam_fvar(kernel, hneg_fvar, nc_ty, applied, BinderInfo::Default);
            let with_hpos = lam_fvar(kernel, hpos_fvar, pc_ty, with_hneg, BinderInfo::Default);
            let with_d = lam_fvar(kernel, d_fvar, dec_p, with_hpos, BinderInfo::Default);
            let with_c_v = lam_fvar(kernel, c_fvar, sort_v, with_d, BinderInfo::Default);
            let decidable_by_cases_value =
                lam_fvar(kernel, p_fvar, prop, with_c_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Definition {
                name: decidable_by_cases,
                uparams: vec![decidable_by_cases_vparam],
                ty: decidable_by_cases_ty,
                value: decidable_by_cases_value,
                hint: ReducibilityHint::Regular(0),
            })?;
        }

        // --- DecidablePred.{u} : Π (α : Sort u) (p : α → Prop), -------------
        //     Sort (max u 1) := fun α p => Π (a : α), Decidable (p a) --------
        // Mathlib's own definition, verbatim (`Init.Core`:
        // `abbrev DecidablePred {α : Sort u} (p : α → Prop) := ∀ a, Decidable
        // (p a)`), with `α` explicit because this kernel has no instance
        // implicits. A `Definition`, not a `Theorem`: its codomain is a
        // `Sort`, like `decide` and `byCases` above.
        //
        // Declared here rather than in `nat_prelude` even though `Nat.
        // findGreatest` is its only consumer today, for two reasons. It is a
        // root-namespace LOGIC notion about `Decidable`, which lives here; and
        // `nat_prelude`'s `every_nat_declaration_is_checked_and_axiom_free`
        // filters the environment on the `Nat.` prefix, so a root-level name
        // declared from there would be invisible to the one assertion that
        // reads coverage from the environment rather than from a list.
        //
        // The declared codomain is `Sort (max u 1)` and the value's actual
        // type is `Sort (imax u 1)`; those are the same level here because
        // `IMax` is `Zero` only when its RIGHT argument is, and `1` is not.
        let decidable_pred_uparam = kernel.name_str(anon, "u");
        let decidable_pred = kernel.name_str(anon, "DecidablePred");
        {
            let prop = kernel.prop();
            let u_lvl = kernel.level_param(decidable_pred_uparam);
            let sort_u = kernel.sort(u_lvl);
            let level_zero = kernel.level_zero();
            let level_one = kernel.level_succ(level_zero);
            let max_u_one = kernel.level_max(u_lvl, level_one);
            let sort_max_u_one = kernel.sort(max_u_one);

            let alpha_fvar = 24_120;
            let pred_fvar = 24_121;
            let arg_fvar = 24_122;

            let alpha = kernel.fvar(alpha_fvar);
            // α → Prop
            let pred_ty = kernel.pi(anon, alpha, prop, BinderInfo::Default);
            let pred = kernel.fvar(pred_fvar);
            let arg = kernel.fvar(arg_fvar);
            let pred_at_arg = kernel.app(pred, arg);
            let decidable_const = kernel.const_(decidable, vec![]);
            let decidable_pred_at_arg = kernel.app(decidable_const, pred_at_arg);

            // value: fun α p => Π (a : α), Decidable (p a).
            let body = pi_fvar(
                kernel,
                arg_fvar,
                alpha,
                decidable_pred_at_arg,
                BinderInfo::Default,
            );
            let with_pred = lam_fvar(kernel, pred_fvar, pred_ty, body, BinderInfo::Default);
            let decidable_pred_value =
                lam_fvar(kernel, alpha_fvar, sort_u, with_pred, BinderInfo::Default);

            // type: Π (α : Sort u) (p : α → Prop), Sort (max u 1).
            let ty_inner = pi_fvar(
                kernel,
                pred_fvar,
                pred_ty,
                sort_max_u_one,
                BinderInfo::Default,
            );
            let decidable_pred_ty =
                pi_fvar(kernel, alpha_fvar, sort_u, ty_inner, BinderInfo::Default);

            kernel.add_declaration(Declaration::Definition {
                name: decidable_pred,
                uparams: vec![decidable_pred_uparam],
                ty: decidable_pred_ty,
                value: decidable_pred_value,
                // Unfolds as readily as `byCases`: every consumer has to see
                // through it to a `Pi` before it can apply the witness.
                hint: ReducibilityHint::Regular(0),
            })?;
        }

        // --- Decidable.ofBool : Π (p : Prop) (b : Bool), --------------------
        //     (Eq Bool b Bool.true → p) → (Eq Bool b Bool.false → (p → False))
        //     → Decidable p --------------------------------------------------
        // The leverage lemma: case-split on `b` via `Bool.rec.{1}` (the motive
        // selects the remaining two-hypothesis Pi type, so this needs the
        // type-valued `Bool` recursor, the same shape as the
        // `bool_false_ne_true` discriminator above). Each branch is closed by
        // applying its OWN live hypothesis at `Eq.refl` -- unlike
        // `of_decide_eq_true`/`of_decide_eq_false`, no impossible branch ever
        // needs `Bool.false_ne_true`/`Bool.true_ne_false` here, because both
        // branches of `b` are live and each carries exactly the hypothesis
        // that discharges it.
        let decidable_of_bool = kernel.name_str(decidable, "ofBool");
        {
            let prop = kernel.prop();
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            let p_fvar = 24_100;
            let b_fvar = 24_101;
            let h1_fvar = 24_102;
            let h2_fvar = 24_103;
            let bval_fvar = 24_104;
            let h1c_fvar = 24_105;
            let h2c_fvar = 24_106;
            let h1d_fvar = 24_107;
            let h2d_fvar = 24_108;

            let p = kernel.fvar(p_fvar);
            let b = kernel.fvar(b_fvar);
            let bool_const = kernel.const_(bool_, vec![]);
            let bool_true_v = kernel.const_(bool_true, vec![]);
            let bool_false_v = kernel.const_(bool_false, vec![]);
            let false_const = kernel.const_(false_, vec![]);
            let decidable_const = kernel.const_(decidable, vec![]);
            let dec_p = kernel.app(decidable_const, p);
            let hf_ty = kernel.pi(anon, p, false_const, BinderInfo::Default); // p → False

            // h1_ty := Eq Bool b Bool.true → p ; h2_ty := Eq Bool b Bool.false → hf_ty.
            let eq_b_true_ty = eq_app(kernel, eq, one, bool_const, b, bool_true_v);
            let h1_ty = kernel.pi(anon, eq_b_true_ty, p, BinderInfo::Default);
            let eq_b_false_ty = eq_app(kernel, eq, one, bool_const, b, bool_false_v);
            let h2_ty = kernel.pi(anon, eq_b_false_ty, hf_ty, BinderInfo::Default);

            // type: Π (p : Prop) (b : Bool), h1_ty → h2_ty → Decidable p.
            let t_inner = kernel.pi(anon, h2_ty, dec_p, BinderInfo::Default);
            let t_mid = kernel.pi(anon, h1_ty, t_inner, BinderInfo::Default);
            let with_b_ty = pi_fvar(kernel, b_fvar, bool_const, t_mid, BinderInfo::Default);
            let decidable_of_bool_ty =
                pi_fvar(kernel, p_fvar, prop, with_b_ty, BinderInfo::Default);

            // motive(bval) := (Eq Bool bval Bool.true → p) →
            //   (Eq Bool bval Bool.false → hf_ty) → Decidable p.
            let bval = kernel.fvar(bval_fvar);
            let eq_bval_true_ty = eq_app(kernel, eq, one, bool_const, bval, bool_true_v);
            let h1_ty_bval = kernel.pi(anon, eq_bval_true_ty, p, BinderInfo::Default);
            let eq_bval_false_ty = eq_app(kernel, eq, one, bool_const, bval, bool_false_v);
            let h2_ty_bval = kernel.pi(anon, eq_bval_false_ty, hf_ty, BinderInfo::Default);
            let motive_inner = kernel.pi(anon, h2_ty_bval, dec_p, BinderInfo::Default);
            let motive_body = kernel.pi(anon, h1_ty_bval, motive_inner, BinderInfo::Default);
            let motive = lam_fvar(
                kernel,
                bval_fvar,
                bool_const,
                motive_body,
                BinderInfo::Default,
            );

            let decidable_is_false_const = kernel.const_(decidable_is_false, vec![]);
            let decidable_is_true_const = kernel.const_(decidable_is_true, vec![]);
            let eq_refl_const = kernel.const_(eq_refl, vec![one]);

            // case Bool.false: fun _h1 h2 => Decidable.isFalse p (h2 (Eq.refl Bool Bool.false)).
            let case_false = {
                let h1_ty_false = {
                    let e = eq_app(kernel, eq, one, bool_const, bool_false_v, bool_true_v);
                    kernel.pi(anon, e, p, BinderInfo::Default)
                };
                let h2_ty_false = {
                    let e = eq_app(kernel, eq, one, bool_const, bool_false_v, bool_false_v);
                    kernel.pi(anon, e, hf_ty, BinderInfo::Default)
                };
                let refl_false = apply_all(kernel, eq_refl_const, &[bool_const, bool_false_v]);
                let h2c = kernel.fvar(h2c_fvar);
                let hf_from_h2 = kernel.app(h2c, refl_false);
                let is_false_applied =
                    apply_all(kernel, decidable_is_false_const, &[p, hf_from_h2]);
                let with_h2 = lam_fvar(
                    kernel,
                    h2c_fvar,
                    h2_ty_false,
                    is_false_applied,
                    BinderInfo::Default,
                );
                lam_fvar(kernel, h1c_fvar, h1_ty_false, with_h2, BinderInfo::Default)
            };

            // case Bool.true: fun h1 _h2 => Decidable.isTrue p (h1 (Eq.refl Bool Bool.true)).
            let case_true = {
                let h1_ty_true = {
                    let e = eq_app(kernel, eq, one, bool_const, bool_true_v, bool_true_v);
                    kernel.pi(anon, e, p, BinderInfo::Default)
                };
                let h2_ty_true = {
                    let e = eq_app(kernel, eq, one, bool_const, bool_true_v, bool_false_v);
                    kernel.pi(anon, e, hf_ty, BinderInfo::Default)
                };
                let refl_true = apply_all(kernel, eq_refl_const, &[bool_const, bool_true_v]);
                let h1d = kernel.fvar(h1d_fvar);
                let p_from_h1 = kernel.app(h1d, refl_true);
                let is_true_applied = apply_all(kernel, decidable_is_true_const, &[p, p_from_h1]);
                let with_h2 = lam_fvar(
                    kernel,
                    h2d_fvar,
                    h2_ty_true,
                    is_true_applied,
                    BinderInfo::Default,
                );
                lam_fvar(kernel, h1d_fvar, h1_ty_true, with_h2, BinderInfo::Default)
            };

            let bool_rec_one = kernel.const_(bool_rec, vec![one]);
            let cased = apply_all(kernel, bool_rec_one, &[motive, case_false, case_true, b]);
            let h1 = kernel.fvar(h1_fvar);
            let h2 = kernel.fvar(h2_fvar);
            let applied = apply_all(kernel, cased, &[h1, h2]);

            let with_h2v = lam_fvar(kernel, h2_fvar, h2_ty, applied, BinderInfo::Default);
            let with_h1v = lam_fvar(kernel, h1_fvar, h1_ty, with_h2v, BinderInfo::Default);
            let with_bv = lam_fvar(kernel, b_fvar, bool_const, with_h1v, BinderInfo::Default);
            let decidable_of_bool_value =
                lam_fvar(kernel, p_fvar, prop, with_bv, BinderInfo::Default);

            kernel.add_declaration(Declaration::Definition {
                name: decidable_of_bool,
                uparams: vec![],
                ty: decidable_of_bool_ty,
                value: decidable_of_bool_value,
                hint: ReducibilityHint::Regular(0),
            })?;
        }

        // --- Decidable.and : Π (p q : Prop), Decidable p → Decidable q → ----
        //     Decidable (And p q) -------------------------------------------
        let decidable_and = kernel.name_str(decidable, "and");
        {
            let prop = kernel.prop();
            let zero = kernel.level_zero();
            let p_fvar = 24_110;
            let q_fvar = 24_111;
            let dp_fvar = 24_112;
            let dq_fvar = 24_113;
            let dummy_p_fvar = 24_114;
            let dummy_q_fvar = 24_115;
            let hnp_fvar = 24_116;
            let hp_fvar = 24_117;
            let hnq_fvar = 24_118;
            let hq_fvar = 24_119;
            let hpq_fvar = 24_120;

            let p = kernel.fvar(p_fvar);
            let q = kernel.fvar(q_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let decidable_const = kernel.const_(decidable, vec![]);
            let dec_p = kernel.app(decidable_const, p);
            let dec_q = kernel.app(decidable_const, q);
            let and_const = kernel.const_(and, vec![]);
            let and_pq = apply_all(kernel, and_const, &[p, q]);
            let dec_and_pq = kernel.app(decidable_const, and_pq);
            let hnp_ty = kernel.pi(anon, p, false_const, BinderInfo::Default); // p → False
            let hnq_ty = kernel.pi(anon, q, false_const, BinderInfo::Default); // q → False

            // type: Π (p q : Prop), Decidable p → Decidable q → Decidable (And p q).
            let t_inner = kernel.pi(anon, dec_q, dec_and_pq, BinderInfo::Default);
            let t_mid = kernel.pi(anon, dec_p, t_inner, BinderInfo::Default);
            let with_q = pi_fvar(kernel, q_fvar, prop, t_mid, BinderInfo::Default);
            let decidable_and_ty = pi_fvar(kernel, p_fvar, prop, with_q, BinderInfo::Default);

            let decidable_is_false_const = kernel.const_(decidable_is_false, vec![]);
            let decidable_is_true_const = kernel.const_(decidable_is_true, vec![]);
            let one = kernel.level_succ(zero);
            let decidable_rec_one = kernel.const_(decidable_rec, vec![one]);
            let and_left_const = kernel.const_(and_left, vec![]);
            let and_right_const = kernel.const_(and_right, vec![]);
            let and_intro_const = kernel.const_(and_intro, vec![]);

            // isFalse p hnp => Decidable.isFalse (And p q) (fun hpq => hnp (And.left p q hpq)).
            let case_false_p = {
                let hnp = kernel.fvar(hnp_fvar);
                let hpq = kernel.fvar(hpq_fvar);
                let left_pq = apply_all(kernel, and_left_const, &[p, q, hpq]);
                let refuted = kernel.app(hnp, left_pq);
                let body = lam_fvar(kernel, hpq_fvar, and_pq, refuted, BinderInfo::Default);
                let applied = apply_all(kernel, decidable_is_false_const, &[and_pq, body]);
                lam_fvar(kernel, hnp_fvar, hnp_ty, applied, BinderInfo::Default)
            };
            // isTrue p hp => <inner case-split on dq, using hp>.
            let case_true_p = {
                let hp = kernel.fvar(hp_fvar);
                let dummy_q =
                    lam_fvar(kernel, dummy_q_fvar, dec_q, dec_and_pq, BinderInfo::Default);
                // isFalse q hnq => Decidable.isFalse (And p q) (fun hpq => hnq (And.right p q hpq)).
                let case_false_q = {
                    let hnq = kernel.fvar(hnq_fvar);
                    let hpq = kernel.fvar(hpq_fvar);
                    let right_pq = apply_all(kernel, and_right_const, &[p, q, hpq]);
                    let refuted = kernel.app(hnq, right_pq);
                    let body = lam_fvar(kernel, hpq_fvar, and_pq, refuted, BinderInfo::Default);
                    let applied = apply_all(kernel, decidable_is_false_const, &[and_pq, body]);
                    lam_fvar(kernel, hnq_fvar, hnq_ty, applied, BinderInfo::Default)
                };
                // isTrue q hq => Decidable.isTrue (And p q) (And.intro p q hp hq).
                let case_true_q = {
                    let hq = kernel.fvar(hq_fvar);
                    let intro = apply_all(kernel, and_intro_const, &[p, q, hp, hq]);
                    let applied = apply_all(kernel, decidable_is_true_const, &[and_pq, intro]);
                    lam_fvar(kernel, hq_fvar, q, applied, BinderInfo::Default)
                };
                let dq = kernel.fvar(dq_fvar);
                let split = apply_all(
                    kernel,
                    decidable_rec_one,
                    &[q, dummy_q, case_false_q, case_true_q, dq],
                );
                lam_fvar(kernel, hp_fvar, p, split, BinderInfo::Default)
            };

            let dummy_p = lam_fvar(kernel, dummy_p_fvar, dec_p, dec_and_pq, BinderInfo::Default);
            let dp = kernel.fvar(dp_fvar);
            let outer = apply_all(
                kernel,
                decidable_rec_one,
                &[p, dummy_p, case_false_p, case_true_p, dp],
            );

            let with_dq = lam_fvar(kernel, dq_fvar, dec_q, outer, BinderInfo::Default);
            let with_dp = lam_fvar(kernel, dp_fvar, dec_p, with_dq, BinderInfo::Default);
            let with_qv = lam_fvar(kernel, q_fvar, prop, with_dp, BinderInfo::Default);
            let decidable_and_value = lam_fvar(kernel, p_fvar, prop, with_qv, BinderInfo::Default);

            kernel.add_declaration(Declaration::Definition {
                name: decidable_and,
                uparams: vec![],
                ty: decidable_and_ty,
                value: decidable_and_value,
                hint: ReducibilityHint::Regular(0),
            })?;
        }

        // --- Decidable.or : Π (p q : Prop), Decidable p → Decidable q → -----
        //     Decidable (Or p q) ------------------------------------------
        let decidable_or = kernel.name_str(decidable, "or");
        {
            let prop = kernel.prop();
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            let p_fvar = 24_130;
            let q_fvar = 24_131;
            let dp_fvar = 24_132;
            let dq_fvar = 24_133;
            let dummy_p_fvar = 24_134;
            let dummy_q_fvar = 24_135;
            let hnp_fvar = 24_136;
            let hp_fvar = 24_137;
            let hnq_fvar = 24_138;
            let hq_fvar = 24_139;

            let p = kernel.fvar(p_fvar);
            let q = kernel.fvar(q_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let decidable_const = kernel.const_(decidable, vec![]);
            let dec_p = kernel.app(decidable_const, p);
            let dec_q = kernel.app(decidable_const, q);
            let or_const = kernel.const_(or, vec![]);
            let or_pq = apply_all(kernel, or_const, &[p, q]);
            let dec_or_pq = kernel.app(decidable_const, or_pq);
            let hnp_ty = kernel.pi(anon, p, false_const, BinderInfo::Default); // p → False
            let hnq_ty = kernel.pi(anon, q, false_const, BinderInfo::Default); // q → False

            // type: Π (p q : Prop), Decidable p → Decidable q → Decidable (Or p q).
            let t_inner = kernel.pi(anon, dec_q, dec_or_pq, BinderInfo::Default);
            let t_mid = kernel.pi(anon, dec_p, t_inner, BinderInfo::Default);
            let with_q = pi_fvar(kernel, q_fvar, prop, t_mid, BinderInfo::Default);
            let decidable_or_ty = pi_fvar(kernel, p_fvar, prop, with_q, BinderInfo::Default);

            let decidable_is_false_const = kernel.const_(decidable_is_false, vec![]);
            let decidable_is_true_const = kernel.const_(decidable_is_true, vec![]);
            let decidable_rec_one = kernel.const_(decidable_rec, vec![one]);
            let or_inl_const = kernel.const_(or_inl, vec![]);
            let or_inr_const = kernel.const_(or_inr, vec![]);
            let or_elim_const = kernel.const_(or_elim, vec![]);

            // isTrue p hp => Decidable.isTrue (Or p q) (Or.inl p q hp).
            let case_true_p = {
                let hp = kernel.fvar(hp_fvar);
                let inl = apply_all(kernel, or_inl_const, &[p, q, hp]);
                let applied = apply_all(kernel, decidable_is_true_const, &[or_pq, inl]);
                lam_fvar(kernel, hp_fvar, p, applied, BinderInfo::Default)
            };
            // isFalse p hnp => <inner case-split on dq, using hnp>.
            let case_false_p = {
                let hnp = kernel.fvar(hnp_fvar);
                let dummy_q = lam_fvar(kernel, dummy_q_fvar, dec_q, dec_or_pq, BinderInfo::Default);
                // isTrue q hq => Decidable.isTrue (Or p q) (Or.inr p q hq).
                let case_true_q = {
                    let hq = kernel.fvar(hq_fvar);
                    let inr = apply_all(kernel, or_inr_const, &[p, q, hq]);
                    let applied = apply_all(kernel, decidable_is_true_const, &[or_pq, inr]);
                    lam_fvar(kernel, hq_fvar, q, applied, BinderInfo::Default)
                };
                // isFalse q hnq => Decidable.isFalse (Or p q)
                //   (fun hpq => Or.elim p q False hpq hnp hnq).
                let case_false_q = {
                    let hnq = kernel.fvar(hnq_fvar);
                    let hpq_fvar = 24_140;
                    let hpq = kernel.fvar(hpq_fvar);
                    let refuted =
                        apply_all(kernel, or_elim_const, &[p, q, false_const, hpq, hnp, hnq]);
                    let body = lam_fvar(kernel, hpq_fvar, or_pq, refuted, BinderInfo::Default);
                    let applied = apply_all(kernel, decidable_is_false_const, &[or_pq, body]);
                    lam_fvar(kernel, hnq_fvar, hnq_ty, applied, BinderInfo::Default)
                };
                let dq = kernel.fvar(dq_fvar);
                let split = apply_all(
                    kernel,
                    decidable_rec_one,
                    &[q, dummy_q, case_false_q, case_true_q, dq],
                );
                lam_fvar(kernel, hnp_fvar, hnp_ty, split, BinderInfo::Default)
            };

            let dummy_p = lam_fvar(kernel, dummy_p_fvar, dec_p, dec_or_pq, BinderInfo::Default);
            let dp = kernel.fvar(dp_fvar);
            let outer = apply_all(
                kernel,
                decidable_rec_one,
                &[p, dummy_p, case_false_p, case_true_p, dp],
            );

            let with_dq = lam_fvar(kernel, dq_fvar, dec_q, outer, BinderInfo::Default);
            let with_dp = lam_fvar(kernel, dp_fvar, dec_p, with_dq, BinderInfo::Default);
            let with_qv = lam_fvar(kernel, q_fvar, prop, with_dp, BinderInfo::Default);
            let decidable_or_value = lam_fvar(kernel, p_fvar, prop, with_qv, BinderInfo::Default);

            kernel.add_declaration(Declaration::Definition {
                name: decidable_or,
                uparams: vec![],
                ty: decidable_or_ty,
                value: decidable_or_value,
                hint: ReducibilityHint::Regular(0),
            })?;
        }

        // --- Decidable.not : Π (p : Prop), Decidable p → -------------------
        //     Decidable (p → False) --------------------------------------
        let decidable_not = kernel.name_str(decidable, "not");
        {
            let prop = kernel.prop();
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            let p_fvar = 24_150;
            let dp_fvar = 24_151;
            let dummy_fvar = 24_152;
            let hnp_fvar = 24_153;
            let hp_fvar = 24_154;
            let hnp2_fvar = 24_155;

            let p = kernel.fvar(p_fvar);
            let false_const = kernel.const_(false_, vec![]);
            let decidable_const = kernel.const_(decidable, vec![]);
            let dec_p = kernel.app(decidable_const, p);
            let hnp_ty = kernel.pi(anon, p, false_const, BinderInfo::Default); // p → False
            let dec_not_p = kernel.app(decidable_const, hnp_ty);

            // type: Π (p : Prop), Decidable p → Decidable (p → False).
            let with_dp = kernel.pi(anon, dec_p, dec_not_p, BinderInfo::Default);
            let decidable_not_ty = pi_fvar(kernel, p_fvar, prop, with_dp, BinderInfo::Default);

            let decidable_is_false_const = kernel.const_(decidable_is_false, vec![]);
            let decidable_is_true_const = kernel.const_(decidable_is_true, vec![]);
            let decidable_rec_one = kernel.const_(decidable_rec, vec![one]);

            // isFalse p hnp => Decidable.isTrue (p → False) hnp.
            let case_false_p = {
                let hnp = kernel.fvar(hnp_fvar);
                let applied = apply_all(kernel, decidable_is_true_const, &[hnp_ty, hnp]);
                lam_fvar(kernel, hnp_fvar, hnp_ty, applied, BinderInfo::Default)
            };
            // isTrue p hp => Decidable.isFalse (p → False) (fun hnp => hnp hp).
            let case_true_p = {
                let hp = kernel.fvar(hp_fvar);
                let hnp2 = kernel.fvar(hnp2_fvar);
                let refuted = kernel.app(hnp2, hp);
                let body = lam_fvar(kernel, hnp2_fvar, hnp_ty, refuted, BinderInfo::Default);
                let applied = apply_all(kernel, decidable_is_false_const, &[hnp_ty, body]);
                lam_fvar(kernel, hp_fvar, p, applied, BinderInfo::Default)
            };

            let dummy = lam_fvar(kernel, dummy_fvar, dec_p, dec_not_p, BinderInfo::Default);
            let dp = kernel.fvar(dp_fvar);
            let cased = apply_all(
                kernel,
                decidable_rec_one,
                &[p, dummy, case_false_p, case_true_p, dp],
            );

            let with_dp_v = lam_fvar(kernel, dp_fvar, dec_p, cased, BinderInfo::Default);
            let decidable_not_value =
                lam_fvar(kernel, p_fvar, prop, with_dp_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Definition {
                name: decidable_not,
                uparams: vec![],
                ty: decidable_not_ty,
                value: decidable_not_value,
                hint: ReducibilityHint::Regular(0),
            })?;
        }

        // --- Decidable.decide_eq_true_iff : Π (p : Prop) (d : Decidable p), -
        //     Iff (Eq Bool (decide p d) Bool.true) p --------------------------
        // `Iff.intro` of `of_decide_eq_true` (the `mp` direction) with a
        // `Decidable.rec` case-split proving the converse `mpr`: the `isTrue`
        // branch is `Eq.refl` once `decide` ι-reduces, the `isFalse` branch is
        // ex falso from the supplied `hp : p` against the constructor's own
        // refutation.
        let decidable_decide_eq_true_iff = kernel.name_str(decidable, "decide_eq_true_iff");
        {
            let prop = kernel.prop();
            let zero = kernel.level_zero();
            let one = kernel.level_succ(zero);
            let p_fvar = 24_160;
            let d_fvar = 24_161;
            let dvar_fvar = 24_162;
            let h_fvar = 24_163;
            let hp_fvar = 24_164;
            let hp2_fvar = 24_165;

            let p = kernel.fvar(p_fvar);
            let decidable_const = kernel.const_(decidable, vec![]);
            let dec_p = kernel.app(decidable_const, p);
            let bool_const = kernel.const_(bool_, vec![]);
            let bool_true_v = kernel.const_(bool_true, vec![]);
            let false_const = kernel.const_(false_, vec![]);
            let hf_ty = kernel.pi(anon, p, false_const, BinderInfo::Default); // p → False
            let decide_const = kernel.const_(decide, vec![]);

            let d = kernel.fvar(d_fvar);
            let decide_p_d = apply_all(kernel, decide_const, &[p, d]);
            let eq_true_d_ty = eq_app(kernel, eq, one, bool_const, decide_p_d, bool_true_v);
            let iff_const = kernel.const_(iff, vec![]);
            let iff_ty = apply_all(kernel, iff_const, &[eq_true_d_ty, p]);

            // type: Π (p : Prop) (d : Decidable p), Iff (Eq Bool (decide p d) Bool.true) p.
            let with_d = pi_fvar(kernel, d_fvar, dec_p, iff_ty, BinderInfo::Default);
            let decidable_decide_eq_true_iff_ty =
                pi_fvar(kernel, p_fvar, prop, with_d, BinderInfo::Default);

            // mp := of_decide_eq_true p d : Eq Bool (decide p d) Bool.true → p.
            let of_decide_eq_true_const = kernel.const_(of_decide_eq_true, vec![]);
            let mp_term = apply_all(kernel, of_decide_eq_true_const, &[p, d]);

            // mpr := Decidable.rec.{0} p (motive := fun dvar => p → Eq Bool (decide p dvar) Bool.true)
            //   (fun h hp => False.rec (Eq Bool Bool.false Bool.true) (h hp))
            //   (fun h _hp => Eq.refl Bool Bool.true)
            //   d.
            let dvar = kernel.fvar(dvar_fvar);
            let decide_p_dvar = apply_all(kernel, decide_const, &[p, dvar]);
            let eq_true_dvar_ty = eq_app(kernel, eq, one, bool_const, decide_p_dvar, bool_true_v);
            let motive_inner = kernel.pi(anon, p, eq_true_dvar_ty, BinderInfo::Default);
            let motive = lam_fvar(kernel, dvar_fvar, dec_p, motive_inner, BinderInfo::Default);

            let bool_false_v = kernel.const_(bool_false, vec![]);
            let false_rec_const = kernel.const_(false_rec, vec![zero]);
            let minor_is_false = {
                let h = kernel.fvar(h_fvar);
                let hp = kernel.fvar(hp_fvar);
                let refuted = kernel.app(h, hp); // False
                let target_ty = eq_app(kernel, eq, one, bool_const, bool_false_v, bool_true_v);
                let false_motive = {
                    let dummy_fvar = 24_167;
                    lam_fvar(
                        kernel,
                        dummy_fvar,
                        false_const,
                        target_ty,
                        BinderInfo::Default,
                    )
                };
                let body = apply_all(kernel, false_rec_const, &[false_motive, refuted]);
                let with_hp = lam_fvar(kernel, hp_fvar, p, body, BinderInfo::Default);
                lam_fvar(kernel, h_fvar, hf_ty, with_hp, BinderInfo::Default)
            };
            let eq_refl_const = kernel.const_(eq_refl, vec![one]);
            let minor_is_true = {
                let h2_fvar = 24_166;
                let refl_true = apply_all(kernel, eq_refl_const, &[bool_const, bool_true_v]);
                let with_hp2 = lam_fvar(kernel, hp2_fvar, p, refl_true, BinderInfo::Default);
                lam_fvar(kernel, h2_fvar, p, with_hp2, BinderInfo::Default)
            };

            let decidable_rec_zero = kernel.const_(decidable_rec, vec![zero]);
            let mpr_term = apply_all(
                kernel,
                decidable_rec_zero,
                &[p, motive, minor_is_false, minor_is_true, d],
            );

            let iff_intro_const = kernel.const_(iff_intro, vec![]);
            let decidable_decide_eq_true_iff_value_body = apply_all(
                kernel,
                iff_intro_const,
                &[eq_true_d_ty, p, mp_term, mpr_term],
            );

            let with_d_v = lam_fvar(
                kernel,
                d_fvar,
                dec_p,
                decidable_decide_eq_true_iff_value_body,
                BinderInfo::Default,
            );
            let decidable_decide_eq_true_iff_value =
                lam_fvar(kernel, p_fvar, prop, with_d_v, BinderInfo::Default);

            kernel.add_declaration(Declaration::Theorem {
                name: decidable_decide_eq_true_iff,
                uparams: vec![],
                ty: decidable_decide_eq_true_iff_ty,
                value: decidable_decide_eq_true_iff_value,
            })?;
        }

        Ok(LogicPrelude {
            true_,
            true_intro,
            true_rec,
            false_,
            false_rec,
            and,
            and_intro,
            and_rec,
            and_left,
            and_right,
            or,
            or_inl,
            or_inr,
            or_rec,
            or_elim,
            or_resolve_left,
            or_resolve_right,
            iff,
            iff_intro,
            iff_rec,
            iff_mp,
            iff_mpr,
            eq,
            eq_refl,
            eq_rec,
            eq_uparam,
            eq_symm,
            congr_fun_prime,
            exists_,
            exists_intro,
            exists_rec,
            exists_uparam,
            acc,
            acc_intro,
            acc_rec,
            acc_inv,
            acc_uparam,
            well_founded,
            well_founded_fix,
            well_founded_fix_eq,
            well_founded_fix_vparam,
            not,
            absurd,
            absurd_vparam,
            mt,
            not_not_intro,
            noncontradiction,
            not_not_not,
            demorgan_not_or,
            demorgan_not_or_converse,
            demorgan_or_not_and,
            not_not_em,
            dne_of_em,
            em_of_dne,
            peirce_of_em,
            em_of_peirce,
            not_not_not_intro,
            not_not_and,
            not_not_imp,
            bool_false_ne_true,
            bool_true_ne_false,
            decidable,
            decidable_is_false,
            decidable_is_true,
            decidable_rec,
            decide,
            of_decide_eq_true,
            of_decide_eq_false,
            decidable_em,
            decidable_by_cases,
            decidable_by_cases_vparam,
            decidable_pred,
            decidable_pred_uparam,
            decidable_of_bool,
            decidable_and,
            decidable_or,
            decidable_not,
            decidable_decide_eq_true_iff,
            bool_,
            bool_true,
            bool_false,
            bool_rec,
            nat,
            nat_zero,
            nat_succ,
            nat_rec,
        })
    })();
    match built {
        Ok(prelude) => {
            kernel.register_prelude(PreludeKey::Logic, PreludeValue::Logic(prelude), checkpoint);
            Ok(prelude)
        }
        Err(error) => {
            kernel.rollback_prelude(checkpoint);
            Err(error)
        }
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
    /// Returns the [`KernelError`] from
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
    /// Returns the [`KernelError`] from
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
    /// Returns the [`KernelError`] from
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
