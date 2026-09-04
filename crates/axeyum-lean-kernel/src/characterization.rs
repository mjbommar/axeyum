//! **Characterization theorems**: machine-checked evidence that the `Nat` and
//! `Int` this kernel constructs are *the* natural numbers and *the* integers,
//! rather than two bespoke inductive types that happen to carry familiar law
//! names.
//!
//! ## The gap this closes
//!
//! `nat_axiom_inventory` reports `nat: axiom=0` and `integer: axiom=0`, and the
//! `Int` prelude proves the full ordered-ring law set. None of that says the
//! objects are the standard ones. A theorem about an inductive type named `Int`
//! is only as meaningful as that type being what everyone means by `ℤ`: if
//! `Int.lt` were subtly wrong every module would still typecheck, still report
//! an empty axiom footprint, and still be worthless. Rendered Lean modules make
//! the gap concrete — they run in `prelude` mode and **re-declare** their own
//! `Nat`, `Int`, `Eq` and `False`, so official Lean accepting one certifies
//! "this proof typechecks against *these* definitions", not that they are the
//! standard ones.
//!
//! The remedy is not inspection but **proof**: state the properties that
//! determine the object up to isomorphism, and have the kernel check them.
//!
//! ## What is proved
//!
//! ### `Nat` — pinned up to unique isomorphism
//!
//! [`NatCharacterization`] declares the three Peano axioms
//! (`zero_ne_succ`, `succ_injective`, `induction`), the universal property of
//! `Nat` as the initial iteration algebra (`iter`, `iter_zero`, `iter_succ`,
//! `iter_unique`), and — the payload — `categorical`:
//!
//! ```text
//! ∀ (N : Sort u) (z : N) (s : N → N),
//!   (∀ n, z ≠ s n) → (∀ m n, s m = s n → m = n) →
//!   (∀ (P : N → Prop), P z → (∀ n, P n → P (s n)) → ∀ n, P n) →
//!   ((iter N z s 0 = z ∧ ∀ k, iter N z s (k+1) = s (iter N z s k))
//!    ∧ ((∀ k m, iter N z s k = iter N z s m → k = m)
//!       ∧ (∀ y, ∃ k, iter N z s k = y)))
//! ```
//!
//! That is second-order categoricity, stated *inside* the kernel: **any**
//! structure satisfying the Peano axioms is in structure-preserving bijection
//! with our `Nat`, and `iter_unique` says the bijection is the only such map.
//! It is universe-polymorphic, so it is not a statement about one chosen
//! universe. This is strictly stronger than a bridge lemma to a specific other
//! definition of `ℕ`: it quantifies over every possible one.
//!
//! ### `Int` — pinned by no-junk, generation, discreteness and order
//!
//! Ordered-ring laws do **not** pin `ℤ` (`ℚ` satisfies all of them; so does
//! lexicographic `ℤ[x]`, which is even discretely ordered).
//! [`IntCharacterization`] adds the properties that do the separating: `cases`
//! and `of_nat_or_neg` (no junk — every element is `±` a natural), `induction`
//! (generation by `0` under `±1`, which `ℤ[x]` fails), `discrete` (nothing
//! strictly between `0` and `1`, which `ℚ` fails), `discrete_everywhere` (the
//! same at every `a`), `le_total`, `zero_lt_one`, `zero_ne_one`, and
//! `rec_unique` (the uniqueness half of the universal property: two maps out of
//! `Int` agreeing at `0` with the same `±1` recurrences are equal).
//!
//! ### `Int` — pinned up to bijection, and up to a constructed isomorphism
//!
//! [`IntCategoricity`] closes the half [`IntCharacterization`] leaves open. A
//! **`ℤ`-structure** is a carrier with a point and two mutually inverse
//! endomorphisms (`down ∘ up = id`, `up ∘ down = id`) — a pointed set with an
//! automorphism. `Int.Characterization.iter` is the map **into** such a
//! structure, built from its own data; `iter_zero` / `iter_succ` / `iter_pred`
//! are its structure-preservation equations, and together with `rec_unique`
//! they say `Int` is the **initial** `ℤ`-structure. Adding generation (`ℤ ⊔ ℤ`
//! fails it) and aperiodicity at the point (`ℤ/n` fails it),
//! `Int.Characterization.categorical` proves the comparison map is a
//! structure-preserving bijection:
//!
//! ```text
//! ∀ (R : Sort u) (e : R) (up down : R → R),
//!   (∀ x, down (up x) = x) → (∀ x, up (down x) = x) →
//!   (∀ (P : R → Prop), P e → (∀ x, P x → P (up x)) → (∀ x, P x → P (down x)) → ∀ x, P x) →
//!   (∀ n, e ≠ Nat.Peano.iter R e up (n+1)) →
//!   ((iter 0 = e ∧ ((∀ t, iter (t+1) = up (iter t)) ∧ (∀ t, iter (t−1) = down (iter t))))
//!    ∧ ((∀ s t, iter s = iter t → s = t) ∧ (∀ y, ∃ t, iter t = y)))
//! ```
//!
//! `Int.Characterization.categorical_at_int` instantiates it at
//! `(Int, 0, (·+1), (·−1))` with every hypothesis discharged by a real theorem,
//! so the premise list is inhabited and the theorem is not vacuously
//! axiom-free. It is a declaration of the package, checked on every build.
//!
//! ### What is **not** proved — read this before quoting the above
//!
//! * **Neither** categoricity theorem extracts an inverse *function*. Both
//!   prove their comparison map injective and surjective, and in both cases
//!   surjectivity is a `Prop`-level `∃`: the hypothesis that makes the target
//!   generated is a `Prop`-valued induction principle, which can prove
//!   `∀ y, ∃ t, iter t = y` and cannot define a map `R → Int`. "Isomorphism"
//!   here means bijection, not a constructed pair of maps.
//! * `Int.Characterization.iso` **is** the constructed form — it proves
//!   `iter ∘ psi = id_R` and `psi ∘ iter = id_Int` as two equations between
//!   maps — but it takes the back-map `psi` as a hypothesis. So: any
//!   structure-preserving map back is automatically a two-sided inverse and is
//!   unique; that one exists is not proved and does not follow from these
//!   premises.
//! * Aperiodicity is stated over *our* `Nat` (`e ≠ up^(n+1) e`). That is not
//!   circular — `Nat.Peano.categorical` pins that `Nat` — but it is a
//!   composition of the two results rather than a statement in `R` alone.
//! * The categoricity theorem is about `ℤ`-structures (point + automorphism),
//!   **not** about discretely ordered rings. "Every discretely ordered ring
//!   generated by `1` is isomorphic to `Int`" would need the order axioms as
//!   hypotheses and a derivation of the automorphism from them; what is proved
//!   is that the order properties hold of `Int` ([`IntCharacterization`]) and
//!   that the `ℤ`-structure properties determine it ([`IntCategoricity`]).
//! * `Nat`'s `categorical` hypothesises a `Prop`-valued induction principle on
//!   the other structure. That is the second-order Peano axiom, and it is what
//!   makes categoricity true at all — first-order `PA` is *not* categorical.
//!   Surjectivity is proved from it; injectivity from the other two axioms.
//!
//! ## Discipline
//!
//! Every statement in this module is **built here** and handed to
//! [`Kernel::add_declaration`](crate::Kernel::add_declaration) together with
//! its proof, exactly as [`build_int_model_of_arith`](crate::build_int_model_of_arith)
//! computes its obligations from the axioms as they stand in the environment.
//! Three consequences: a prelude theorem whose statement drifts makes the
//! matching restatement here **fail** rather than silently weaken; a proof that
//! stops working is a rejection, not a skipped row; and [`Weakening`] injects
//! deliberate defects into the same code path so the negative-control tests
//! prove each hypothesis is load-bearing.

mod int;
mod int_categoricity;
mod nat;
mod ops;
mod universal_property;

pub use int::IntCharacterization;
pub use int_categoricity::IntCategoricity;
pub use nat::NatCharacterization;
pub use universal_property::{IntUniversalProperty, NatUniversalProperty};

use crate::int_prelude::{IntPrelude, build_int_prelude};
use crate::name::NameId;
use crate::{Kernel, KernelError};

use ops::CharDev;

/// A deliberate defect injected into one characterization statement.
///
/// Every variant other than [`Weakening::None`] must make
/// [`build_characterization_with`] **fail**: that is what makes the
/// corresponding hypothesis provably load-bearing rather than decorative. The
/// variants run through the same builder as the real package, so they test the
/// shipped code path and not a reimplementation of it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Weakening {
    /// Build the real package.
    #[default]
    None,
    /// State Peano 1 as `succ n ≠ zero` while keeping the oriented transport.
    ZeroNeSuccReversed,
    /// Demand the induction base case at `succ zero` instead of `zero`.
    InductionBaseAtOne,
    /// Replace `iter_unique`'s `h zero = a` hypothesis with `True`.
    IterUniqueDropZeroHypothesis,
    /// Replace `injective`'s `z ≠ s n` hypothesis with `True`.
    InjectiveDropZeroNeSucc,
    /// Replace `injective`'s successor-injectivity hypothesis with `True`.
    InjectiveDropSuccInjective,
    /// Replace `surjective`'s induction hypothesis with `True`.
    SurjectiveDropInduction,
    /// Replace the `Int` induction principle's `+1` step with `True`.
    IntInductionDropSuccStep,
    /// Replace the `Int` induction principle's `−1` step with `True`.
    IntInductionDropPredStep,
    /// Replace `rec_unique`'s `g`-side `−1` recurrence with `True`.
    IntRecUniqueDropPredRecurrence,
    /// Replace `iter_succ`'s `up ∘ down = id` hypothesis with `True`.
    IntIterSuccDropInverse,
    /// Replace `iter_pred`'s `down ∘ up = id` hypothesis with `True`.
    IntIterPredDropInverse,
    /// Replace `iter_up_injective`'s `down ∘ up = id` hypothesis with `True`.
    IntIterUpInjectiveDropInverse,
    /// Replace `iter_up_injective`'s aperiodicity hypothesis with `True`.
    IntIterUpInjectiveDropAperiodicity,
    /// Replace `shift`'s `up ∘ down = id` hypothesis with `True`.
    IntShiftDropInverse,
    /// Replace `cross`'s `up ∘ down = id` hypothesis with `True`.
    IntCrossDropInverse,
    /// Replace `cross`'s aperiodicity hypothesis with `True`.
    IntCrossDropAperiodicity,
    /// Replace `iter_down_injective`'s aperiodicity hypothesis with `True`.
    IntDownInjectiveDropAperiodicity,
    /// Replace `Int`-side `injective`'s `down ∘ up = id` hypothesis with `True`.
    IntInjectiveDropRetraction,
    /// Replace `Int`-side `injective`'s aperiodicity hypothesis with `True` —
    /// the defect `ℤ/n` is the counter-model to.
    IntInjectiveDropAperiodicity,
    /// Replace `Int`-side `surjective`'s generation hypothesis with `True` —
    /// the defect `ℤ ⊔ ℤ` is the counter-model to.
    IntSurjectiveDropGeneration,
    /// Replace `iso`'s generation hypothesis with `True`.
    IntIsoDropGeneration,
    /// Replace `iso`'s `psi e = 0` hypothesis with `True`.
    IntIsoDropBasePoint,
    /// Replace `Nat.Peano.initial`'s packaged uniqueness clause's `h 0 = z`
    /// hypothesis with `True`.
    NatInitialDropUniqueZero,
    /// Replace `Int.Characterization.initial`'s packaged uniqueness clause's
    /// `g 0 = e` hypothesis with `True`.
    IntInitialDropUniqueZero,
}

impl Weakening {
    /// The declaration this defect must make the kernel **refuse**, as a dotted
    /// name.
    ///
    /// Asserting only "the build failed" would pass if the defect broke some
    /// earlier, unrelated declaration; the negative controls check that the
    /// build got as far as this declaration and died *there*.
    #[must_use]
    pub fn refused_declaration(self) -> Option<&'static str> {
        match self {
            Weakening::None => None,
            Weakening::ZeroNeSuccReversed => Some("Nat.Peano.zero_ne_succ"),
            Weakening::InductionBaseAtOne => Some("Nat.Peano.induction"),
            Weakening::IterUniqueDropZeroHypothesis => Some("Nat.Peano.iter_unique"),
            Weakening::InjectiveDropZeroNeSucc | Weakening::InjectiveDropSuccInjective => {
                Some("Nat.Peano.injective")
            }
            Weakening::SurjectiveDropInduction => Some("Nat.Peano.surjective"),
            Weakening::IntInductionDropSuccStep | Weakening::IntInductionDropPredStep => {
                Some("Int.Characterization.induction")
            }
            Weakening::IntRecUniqueDropPredRecurrence => Some("Int.Characterization.rec_unique"),
            Weakening::IntIterSuccDropInverse => Some("Int.Characterization.iter_succ"),
            Weakening::IntIterPredDropInverse => Some("Int.Characterization.iter_pred"),
            Weakening::IntIterUpInjectiveDropInverse
            | Weakening::IntIterUpInjectiveDropAperiodicity => {
                Some("Int.Characterization.iter_up_injective")
            }
            Weakening::IntShiftDropInverse => Some("Int.Characterization.shift"),
            Weakening::IntCrossDropInverse | Weakening::IntCrossDropAperiodicity => {
                Some("Int.Characterization.cross")
            }
            Weakening::IntDownInjectiveDropAperiodicity => {
                Some("Int.Characterization.iter_down_injective")
            }
            Weakening::IntInjectiveDropRetraction | Weakening::IntInjectiveDropAperiodicity => {
                Some("Int.Characterization.injective")
            }
            Weakening::IntSurjectiveDropGeneration => Some("Int.Characterization.surjective"),
            Weakening::IntIsoDropGeneration | Weakening::IntIsoDropBasePoint => {
                Some("Int.Characterization.iso")
            }
            Weakening::NatInitialDropUniqueZero => Some("Nat.Peano.initial"),
            Weakening::IntInitialDropUniqueZero => Some("Int.Characterization.initial"),
        }
    }

    /// A declaration the build must **still** have admitted when this defect
    /// stops it.
    ///
    /// `refused_declaration` alone only says the aimed-at declaration is
    /// absent, which an early unrelated failure also achieves. This names the
    /// declaration immediately before it in build order, so the two together
    /// bracket the failure: everything up to here was admitted, and the next
    /// thing was refused.
    #[must_use]
    pub fn reached_declaration(self) -> Option<&'static str> {
        match self {
            // The first declaration of the package: nothing precedes it.
            Weakening::None | Weakening::ZeroNeSuccReversed => None,
            Weakening::InductionBaseAtOne => Some("Nat.Peano.succ_injective"),
            Weakening::IterUniqueDropZeroHypothesis => Some("Nat.Peano.iter_succ"),
            Weakening::InjectiveDropZeroNeSucc | Weakening::InjectiveDropSuccInjective => {
                Some("Nat.Peano.surjective")
            }
            Weakening::SurjectiveDropInduction => Some("Nat.Peano.iter_unique"),
            Weakening::IntInductionDropSuccStep | Weakening::IntInductionDropPredStep => {
                Some("Int.Characterization.of_nat_or_neg")
            }
            Weakening::IntRecUniqueDropPredRecurrence => Some("Int.Characterization.induction"),
            Weakening::IntIterSuccDropInverse => Some("Int.Characterization.iter_zero"),
            Weakening::IntIterPredDropInverse => Some("Int.Characterization.iter_succ"),
            Weakening::IntIterUpInjectiveDropInverse
            | Weakening::IntIterUpInjectiveDropAperiodicity => {
                Some("Int.Characterization.up_injective")
            }
            Weakening::IntShiftDropInverse => Some("Int.Characterization.iter_up_injective"),
            Weakening::IntCrossDropInverse | Weakening::IntCrossDropAperiodicity => {
                Some("Int.Characterization.shift")
            }
            Weakening::IntDownInjectiveDropAperiodicity => Some("Int.Characterization.cross"),
            Weakening::IntInjectiveDropRetraction | Weakening::IntInjectiveDropAperiodicity => {
                Some("Int.Characterization.iter_down_injective")
            }
            Weakening::IntSurjectiveDropGeneration => Some("Int.Characterization.injective"),
            Weakening::IntIsoDropGeneration | Weakening::IntIsoDropBasePoint => {
                Some("Int.Characterization.categorical")
            }
            Weakening::NatInitialDropUniqueZero => Some("Int.Characterization.categorical_at_int"),
            Weakening::IntInitialDropUniqueZero => Some("Nat.Peano.initial"),
        }
    }

    /// Every injected defect, for the negative-control sweep.
    #[must_use]
    pub fn defects() -> &'static [Weakening] {
        &[
            Weakening::ZeroNeSuccReversed,
            Weakening::InductionBaseAtOne,
            Weakening::IterUniqueDropZeroHypothesis,
            Weakening::InjectiveDropZeroNeSucc,
            Weakening::InjectiveDropSuccInjective,
            Weakening::SurjectiveDropInduction,
            Weakening::IntInductionDropSuccStep,
            Weakening::IntInductionDropPredStep,
            Weakening::IntRecUniqueDropPredRecurrence,
            Weakening::IntIterSuccDropInverse,
            Weakening::IntIterPredDropInverse,
            Weakening::IntIterUpInjectiveDropInverse,
            Weakening::IntIterUpInjectiveDropAperiodicity,
            Weakening::IntShiftDropInverse,
            Weakening::IntCrossDropInverse,
            Weakening::IntCrossDropAperiodicity,
            Weakening::IntDownInjectiveDropAperiodicity,
            Weakening::IntInjectiveDropRetraction,
            Weakening::IntInjectiveDropAperiodicity,
            Weakening::IntSurjectiveDropGeneration,
            Weakening::IntIsoDropGeneration,
            Weakening::IntIsoDropBasePoint,
            Weakening::NatInitialDropUniqueZero,
            Weakening::IntInitialDropUniqueZero,
        ]
    }
}

/// What a characterization theorem contributes to pinning its object.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CharacterizationKind {
    /// One of the three Peano axioms for `Nat`.
    PeanoAxiom,
    /// Part of the universal property (initiality) of `Nat`.
    NatUniversalProperty,
    /// Part of the categoricity theorem for `Nat`.
    NatCategoricity,
    /// `Int` has no elements beyond its constructors.
    IntNoJunk,
    /// `Int` is generated by `0` under `±1`.
    IntGeneration,
    /// Part of `Int`'s universal property: the uniqueness half (`rec_unique`)
    /// or one of the comparison map's structure-preservation equations.
    IntUniversalProperty,
    /// Part of the categoricity theorem for `Int`.
    IntCategoricity,
    /// `Int` is discretely ordered, totally ordered, and non-trivial.
    IntOrder,
}

impl CharacterizationKind {
    /// A short stable label for reports.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            CharacterizationKind::PeanoAxiom => "peano-axiom",
            CharacterizationKind::NatUniversalProperty => "nat-universal-property",
            CharacterizationKind::NatCategoricity => "nat-categoricity",
            CharacterizationKind::IntNoJunk => "int-no-junk",
            CharacterizationKind::IntGeneration => "int-generation",
            CharacterizationKind::IntUniversalProperty => "int-universal-property",
            CharacterizationKind::IntCategoricity => "int-categoricity",
            CharacterizationKind::IntOrder => "int-order",
        }
    }
}

/// One admitted characterization declaration and what it establishes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CharacterizationEntry {
    /// The admitted declaration.
    pub name: NameId,
    /// What it contributes.
    pub kind: CharacterizationKind,
}

/// The result of [`build_characterization`]: the underlying `Int` development
/// and both characterization packages.
#[derive(Debug, Clone)]
pub struct Characterization {
    /// The constructed integer prelude everything rests on.
    pub int_prelude: IntPrelude,
    /// The `Nat.Peano` package.
    pub nat: NatCharacterization,
    /// The `Int.Characterization` package.
    pub int: IntCharacterization,
    /// The `Int` categoricity package (same namespace).
    pub int_categoricity: IntCategoricity,
    /// `Nat` named as the initial pointed unary algebra.
    pub nat_universal_property: NatUniversalProperty,
    /// `Int` named as the initial `ℤ`-structure.
    pub int_universal_property: IntUniversalProperty,
    /// Every admitted theorem, in declaration order, with its role.
    pub entries: Vec<CharacterizationEntry>,
}

/// Build the `Int` development and admit every characterization theorem.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` here means the kernel
/// **refused** a characterization proof — the claim is not established.
pub fn build_characterization(kernel: &mut Kernel) -> Result<Characterization, KernelError> {
    build_characterization_with(kernel, Weakening::None)
}

/// [`build_characterization`] with a deliberate defect injected.
///
/// # Errors
///
/// Returns the trusted gate's rejection. For every
/// [`Weakening`] other than [`Weakening::None`] an `Err` is the **expected**
/// outcome and an `Ok` is a test failure: it would mean the weakened hypothesis
/// was never load-bearing.
#[allow(clippy::too_many_lines)]
pub fn build_characterization_with(
    kernel: &mut Kernel,
    weakening: Weakening,
) -> Result<Characterization, KernelError> {
    let int_prelude = build_int_prelude(kernel)?;
    let mut dev = CharDev::new(kernel, int_prelude);
    let nat = nat::declare(&mut dev, weakening)?;
    let int = int::declare(&mut dev, weakening)?;
    let int_categoricity = int_categoricity::declare(&mut dev, nat, int, weakening)?;
    let (nat_universal_property, int_universal_property) =
        universal_property::declare(&mut dev, nat, int, int_categoricity, weakening)?;
    let entries = vec![
        CharacterizationEntry {
            name: nat.zero_ne_succ,
            kind: CharacterizationKind::PeanoAxiom,
        },
        CharacterizationEntry {
            name: nat.succ_injective,
            kind: CharacterizationKind::PeanoAxiom,
        },
        CharacterizationEntry {
            name: nat.induction,
            kind: CharacterizationKind::PeanoAxiom,
        },
        CharacterizationEntry {
            name: nat.iter_zero,
            kind: CharacterizationKind::NatUniversalProperty,
        },
        CharacterizationEntry {
            name: nat.iter_succ,
            kind: CharacterizationKind::NatUniversalProperty,
        },
        CharacterizationEntry {
            name: nat.iter_unique,
            kind: CharacterizationKind::NatUniversalProperty,
        },
        CharacterizationEntry {
            name: nat.injective,
            kind: CharacterizationKind::NatCategoricity,
        },
        CharacterizationEntry {
            name: nat.surjective,
            kind: CharacterizationKind::NatCategoricity,
        },
        CharacterizationEntry {
            name: nat.categorical,
            kind: CharacterizationKind::NatCategoricity,
        },
        CharacterizationEntry {
            name: int.cases,
            kind: CharacterizationKind::IntNoJunk,
        },
        CharacterizationEntry {
            name: int.of_nat_or_neg,
            kind: CharacterizationKind::IntNoJunk,
        },
        CharacterizationEntry {
            name: int.induction,
            kind: CharacterizationKind::IntGeneration,
        },
        CharacterizationEntry {
            name: int.rec_unique,
            kind: CharacterizationKind::IntUniversalProperty,
        },
        CharacterizationEntry {
            name: int.discrete,
            kind: CharacterizationKind::IntOrder,
        },
        CharacterizationEntry {
            name: int.discrete_everywhere,
            kind: CharacterizationKind::IntOrder,
        },
        CharacterizationEntry {
            name: int.le_total,
            kind: CharacterizationKind::IntOrder,
        },
        CharacterizationEntry {
            name: int.zero_lt_one,
            kind: CharacterizationKind::IntOrder,
        },
        CharacterizationEntry {
            name: int.zero_ne_one,
            kind: CharacterizationKind::IntOrder,
        },
        CharacterizationEntry {
            name: int_categoricity.iter_zero,
            kind: CharacterizationKind::IntUniversalProperty,
        },
        CharacterizationEntry {
            name: int_categoricity.iter_succ,
            kind: CharacterizationKind::IntUniversalProperty,
        },
        CharacterizationEntry {
            name: int_categoricity.iter_pred,
            kind: CharacterizationKind::IntUniversalProperty,
        },
        CharacterizationEntry {
            name: int_categoricity.up_injective,
            kind: CharacterizationKind::IntCategoricity,
        },
        CharacterizationEntry {
            name: int_categoricity.iter_up_injective,
            kind: CharacterizationKind::IntCategoricity,
        },
        CharacterizationEntry {
            name: int_categoricity.shift,
            kind: CharacterizationKind::IntCategoricity,
        },
        CharacterizationEntry {
            name: int_categoricity.cross,
            kind: CharacterizationKind::IntCategoricity,
        },
        CharacterizationEntry {
            name: int_categoricity.iter_down_injective,
            kind: CharacterizationKind::IntCategoricity,
        },
        CharacterizationEntry {
            name: int_categoricity.injective,
            kind: CharacterizationKind::IntCategoricity,
        },
        CharacterizationEntry {
            name: int_categoricity.surjective,
            kind: CharacterizationKind::IntCategoricity,
        },
        CharacterizationEntry {
            name: int_categoricity.categorical,
            kind: CharacterizationKind::IntCategoricity,
        },
        CharacterizationEntry {
            name: int_categoricity.iso,
            kind: CharacterizationKind::IntCategoricity,
        },
        CharacterizationEntry {
            name: int_categoricity.iter_at_int,
            kind: CharacterizationKind::IntCategoricity,
        },
        CharacterizationEntry {
            name: int_categoricity.categorical_at_int,
            kind: CharacterizationKind::IntCategoricity,
        },
        CharacterizationEntry {
            name: nat_universal_property.initial,
            kind: CharacterizationKind::NatUniversalProperty,
        },
        CharacterizationEntry {
            name: int_universal_property.initial,
            kind: CharacterizationKind::IntUniversalProperty,
        },
    ];
    Ok(Characterization {
        int_prelude,
        nat,
        int,
        int_categoricity,
        nat_universal_property,
        int_universal_property,
        entries,
    })
}

#[cfg(test)]
mod characterization_tests;
