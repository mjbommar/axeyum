//! The **natural-number prelude**: arithmetic over the logic prelude's
//! *inductive* `Nat`, together with the `Eq`-combinator and induction machinery
//! a development needs to use it.
//!
//! Unlike [`build_arith_prelude`](crate::build_arith_prelude) (an axiomatized
//! linear ordered field, for Farkas/LRA reconstruction) and
//! [`build_int_prelude`](crate::build_int_prelude) (an axiomatized discretely
//! ordered ring, for integer-cut reconstruction), **this prelude declares no
//! axioms at all**. [`build_logic_prelude`] admits `Nat` as a real inductive
//! with a real, ι-computing `Nat.rec`, so `add`/`mul`/`pow` are *definitions* by
//! structural recursion and every algebraic law below is a *theorem* the kernel
//! type-checks at admission through
//! [`Kernel::add_declaration`](crate::Kernel::add_declaration).
//! `nat_prelude_tests::the_nat_prelude_declares_no_axioms` enforces that claim
//! mechanically by walking the resulting environment.
//!
//! ## What is declared (all under the `Nat` namespace)
//!
//! **Recursive arithmetic definitions** — each by `Nat.rec` on its **second**
//! argument, so the defining equations hold *definitionally* (β/δ/ι) and need
//! no equation lemmas:
//!
//! | name      | zero case            | successor case                       |
//! |-----------|----------------------|--------------------------------------|
//! | `Nat.add` | `add x zero ≡ x`     | `add x (succ j) ≡ succ (add x j)`    |
//! | `Nat.mul` | `mul x zero ≡ zero`  | `mul x (succ j) ≡ add (mul x j) x`   |
//! | `Nat.pow` | `pow x zero ≡ 1`     | `pow x (succ j) ≡ mul (pow x j) x`   |
//!
//! **Truncated subtraction**: `Nat.pred` computes predecessor with
//! `pred zero ≡ zero`; `Nat.sub` recurses on its second argument. Checked
//! theorems include successor cancellation, self-subtraction, and restoration
//! under explicit order evidence.
//!
//! **Finite ranges**: `Nat.sumRange f n` recursively sums `f 0` through
//! `f (n-1)`. Its empty and successor equations are checked theorems backed by
//! definitional reduction.
//!
//! **Defining-equation theorems** (`add_zero`, `add_succ`, `mul_zero`,
//! `mul_succ`, `pow_zero`, `pow_succ`, `pred_zero`, `pred_succ`, `sub_zero`,
//! `sub_succ`) — each proved by `Eq.refl`; they exist so callers can rewrite by
//! name without knowing the recursion scheme.
//!
//! **Computational equality**: `Nat.beq` structurally compares two naturals and
//! ι-reduces to `Bool.true` exactly when they are equal. Its soundness,
//! completeness, and `Iff` specification are checked theorems, giving later
//! algorithms a constructive branch condition without classical choice.
//!
//! **Additive theorems**: `zero_add`, `succ_add`, `add_comm`, `add_assoc`,
//! `add_right_comm`, successor injectivity, and left/right cancellation.
//!
//! **Multiplicative theorems**: `zero_mul`, `succ_mul`, `mul_comm`,
//! `left_distrib`, `right_distrib`, `mul_assoc`, `one_mul`, `mul_one`.
//!
//! **Order** (`Nat.le`): an *indexed* `Prop`-valued inductive relation with the
//! same shape as Lean's own `Nat.le` — `Nat.le.refl : Le n n` and
//! `Nat.le.step : Le n m → Le n (succ m)` — admitted through the same trusted
//! inductive gate, so its recursor `Nat.le.rec` (induction on the *derivation*)
//! is kernel-generated. `Nat.lt n m := Nat.le (Nat.succ n) m`. Theorems:
//! `zero_le`, `le_succ_succ`, `le_of_succ_le_succ`, `le_trans`, `le_total`, and
//! `le_add_right`, addition/multiplication monotonicity, order-conditioned
//! `sub_add_cancel`, and bounded `mul_sub_left_distrib`. The reducible checked
//! definition `lt_well_founded` lets generic `WellFounded.fix` programs perform
//! strong recursion over this order.
//!
//! **Divisibility**: `Nat.dvd a n := Exists (fun q => n = a * q)`, together
//! with checked reflexivity, zero, transitivity, multiplication, addition, and
//! all-Nat additive-cancellation laws. `dvd_mod_iff` connects those laws to the
//! executable remainder for every positive divisor without requiring the
//! common divisor itself to be positive.
//!
//! **Division and congruence**: `Nat.divMod` carries quotient and remainder
//! witnesses and proves existence, uniqueness, and floor-order laws. One shared
//! structurally recursive state computes total `Nat.div` and `Nat.mod`; its
//! projections use Lean's dividend-first argument order and zero-divisor values.
//! `div_mod_exec` proves those projections satisfy the relational specification
//! for every positive divisor, so its uniqueness, floor, congruence, and
//! divisibility laws apply to computation.
//! `Nat.gcd` then follows Lean's first-argument Euclidean recursion through the
//! generic checked `WellFounded.fix`; its recursive remainder is justified by
//! the checked `mod_lt` theorem, and `gcd_zero_left` / `gcd_succ` expose its
//! unfolding equations. `gcd_dvd`, `dvd_gcd`, and `dvd_gcd_iff` prove its full
//! common-divisor characterization over all naturals.
//! `Nat.bezout m n g := ∃ mp mn np nn, g + m*mn + n*nn = m*mp + n*np`
//! encodes signed coefficients as balanced natural parts. `gcd_bezout` proves
//! that relation for the executable gcd by the same checked Euclidean descent,
//! without importing the separate assumption-bearing integer prelude.
//! `Nat.modEq d a b := ∃ u v, a + d*u = b + d*v` avoids signed subtraction;
//! reflexivity, symmetry, transitivity, and pairwise additive and multiplicative
//! closure are checked theorems.
//!
//! ## What is **not** here
//!
//! No `min` or decidability of order, no multiplicative divisibility
//! cancellation, Gauss lemma, or `n ≠ succ n`-style
//! discrimination.
//! Adding those is ordinary work on top of this prelude, not a kernel question:
//! the order fragment is deliberately minimal (see [`NatPrelude::le`]).
//!
//! ## Building proofs on top
//!
//! [`NatOps`] is the reusable proof-construction layer: `Eq` combinators
//! (`symm`, `trans`, `congr`, `chain`, `transport`, `eq_motive`), a `Nat.rec`
//! [`induct`](NatOps::induct) helper for `Prop`-valued motives, and the
//! [`define_binary`](NatOps::define_binary) /
//! [`theorem`](NatOps::theorem) declaration plumbing. Implement its two required
//! methods on your own development struct (so your own operators stay ordinary
//! methods and every closure keeps taking `&mut YourDev`), or use the ready-made
//! [`NatDev`] over a borrowed kernel.

// Proof scripts are long, straight-line term constructions with short
// mathematical names; splitting them would obscure the derivation they mirror.
// `type_complexity`: the higher-order declaration helpers take
// `&dyn Fn(&mut Self, …) -> …` builders; a type alias mentioning `Self` is not
// expressible, and naming them per-implementor would hide the signature.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::type_complexity
)]

use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::PreludeKey;
use crate::PreludeValue;
use crate::build_logic_prelude;
use crate::name::NameId;

mod algebra;
mod bezout;
mod defs;
mod divisibility;
mod division;
mod gcd;
mod helpers;
mod modular;
mod ops;
mod order;

pub use ops::{NatDev, NatOps, NatState};

use algebra::{
    declare_additive_theorems, declare_finite_sum_theorems, declare_multiplicative_theorems,
    declare_subtraction_theorems,
};
use bezout::declare_gcd_bezout;
use defs::{
    declare_arithmetic, declare_boolean_equality, declare_defining_equations,
    declare_executable_division, declare_finite_ranges, declare_subtraction,
};
use divisibility::declare_divisibility;
use division::declare_euclidean_division;
use gcd::{declare_executable_gcd, declare_gcd_semantics};
use modular::declare_modular_congruence;
use order::declare_order;

/// The interned names produced by [`build_nat_prelude`]: the inductive `Nat`
/// and its constructors/recursor (re-exported from the [`LogicPrelude`] for
/// convenience), the arithmetic definitions, and every theorem name.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels. All fields are public so callers can build `Const` terms
/// (`k.const_(nat.add, vec![])`) directly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NatPrelude {
    /// The embedded logical prelude (`False`, `Not`, `Eq`, `Exists`, `Nat`, …).
    pub logic: LogicPrelude,

    // --- the inductive Nat (from the logic prelude) --------------------------
    /// `Nat : Type` — the inductive unary naturals.
    pub nat: NameId,
    /// `Nat.zero : Nat`.
    pub zero: NameId,
    /// `Nat.succ : Nat → Nat`.
    pub succ: NameId,
    /// `Nat.rec` — the generated, ι-computing recursor.
    pub rec: NameId,

    // --- definitions ---------------------------------------------------------
    /// `Nat.add : Nat → Nat → Nat`, by recursion on the second argument.
    pub add: NameId,
    /// `Nat.mul : Nat → Nat → Nat`, by recursion on the second argument.
    pub mul: NameId,
    /// `Nat.pow : Nat → Nat → Nat`, by recursion on the exponent.
    pub pow: NameId,
    /// Computational equality `Nat.beq : Nat → Nat → Bool`.
    pub beq: NameId,
    /// `Nat.beq_refl : ∀ n, Nat.beq n n = Bool.true`.
    pub beq_refl: NameId,
    /// `Nat.eq_of_beq_eq_true : ∀ a b, Nat.beq a b = true → a = b`.
    pub eq_of_beq_eq_true: NameId,
    /// `Nat.beq_eq_true_of_eq : ∀ a b, a = b → Nat.beq a b = true`.
    pub beq_eq_true_of_eq: NameId,
    /// `Nat.beq_eq_true_iff : ∀ a b, Nat.beq a b = true ↔ a = b`.
    pub beq_eq_true_iff: NameId,
    /// Shared executable division state `divModState d n : Bool → Nat`;
    /// `true` selects the quotient and `false` the remainder.
    pub div_mod_state: NameId,
    /// Total executable quotient `Nat.div dividend divisor`.
    pub div: NameId,
    /// Total executable remainder `Nat.mod dividend divisor`.
    pub mod_: NameId,
    /// Executable Euclidean greatest-common-divisor algorithm, recursing on its
    /// first argument through checked well-founded recursion.
    pub gcd: NameId,
    /// `Nat.sumRange : (Nat → Nat) → Nat → Nat`.
    pub sum_range: NameId,
    /// `Nat.pred : Nat → Nat`, with `pred zero = zero`.
    pub pred: NameId,
    /// `Nat.sub : Nat → Nat → Nat`, truncated at zero and recursive in the
    /// second argument.
    pub sub: NameId,

    // --- executable division equations -------------------------------------
    /// `div_zero : ∀ n, div n zero = zero`.
    pub div_zero: NameId,
    /// `mod_zero : ∀ n, mod n zero = n`.
    pub mod_zero: NameId,
    /// `zero_div : ∀ d, div zero d = zero`.
    pub zero_div: NameId,
    /// `zero_mod : ∀ d, mod zero d = zero`.
    pub zero_mod: NameId,
    /// Successor equation for executable quotient.
    pub div_succ: NameId,
    /// Successor equation for executable remainder.
    pub mod_succ: NameId,

    // --- defining equations (each proved by `Eq.refl`) -----------------------
    /// `add_zero : ∀ (n : Nat), Eq Nat (add n zero) n`.
    pub add_zero: NameId,
    /// `add_succ : ∀ (n m : Nat), Eq Nat (add n (succ m)) (succ (add n m))`.
    pub add_succ: NameId,
    /// `mul_zero : ∀ (n : Nat), Eq Nat (mul n zero) zero`.
    pub mul_zero: NameId,
    /// `mul_succ : ∀ (n m : Nat), Eq Nat (mul n (succ m)) (add (mul n m) n)`.
    pub mul_succ: NameId,
    /// `pow_zero : ∀ (n : Nat), Eq Nat (pow n zero) (succ zero)`.
    pub pow_zero: NameId,
    /// `pow_add : ∀ (a m n : Nat), Eq Nat (pow a (add m n)) (mul (pow a m) (pow a n))`.
    ///
    /// The exponent law. Closes fact `F:nat-pow-add`, whose `depends_on`
    /// (`F:nat-mul-assoc`, `F:nat-mul-comm`) were already settled — the ledger
    /// picked this goal, which is the self-extension loop working as designed.
    pub pow_add: NameId,
    /// `pow_succ : ∀ (n m : Nat), Eq Nat (pow n (succ m)) (mul (pow n m) n)`.
    pub pow_succ: NameId,
    /// `pred_zero : pred zero = zero`.
    pub pred_zero: NameId,
    /// `pred_succ : ∀ n, pred (succ n) = n`.
    pub pred_succ: NameId,
    /// `sub_zero : ∀ n, sub n zero = n`.
    pub sub_zero: NameId,
    /// `sub_succ : ∀ n m, sub n (succ m) = pred (sub n m)`.
    pub sub_succ: NameId,
    /// `succ_sub_succ : ∀ n m, sub (succ n) (succ m) = sub n m`.
    pub succ_sub_succ: NameId,
    /// `sub_self : ∀ n, sub n n = zero`.
    pub sub_self: NameId,
    /// `add_sub_cancel_left : ∀ m n, sub (add m n) m = n`.
    pub add_sub_cancel_left: NameId,
    /// `sumRange_zero : ∀ f, sumRange f zero = zero`.
    pub sum_range_zero: NameId,
    /// `sumRange_succ : ∀ f n, sumRange f (succ n) = sumRange f n + f n`.
    pub sum_range_succ: NameId,
    /// `sumRange_congr : (∀ i, f i = g i) → sumRange f n = sumRange g n`.
    pub sum_range_congr: NameId,
    /// `mul_sumRange : ∀ a f n, a * sumRange f n = sumRange (fun i => a * f i) n`.
    pub mul_sum_range: NameId,
    /// `mul_sumRange_pow : ∀ a n, a * sumRange (a^·) n = sumRange (a^(·+1)) n`.
    pub mul_sum_range_pow: NameId,

    // --- additive theorems ---------------------------------------------------
    /// `zero_add : ∀ (n : Nat), Eq Nat (add zero n) n`.
    pub zero_add: NameId,
    /// `succ_add : ∀ (n m : Nat), Eq Nat (add (succ n) m) (succ (add n m))`.
    pub succ_add: NameId,
    /// `add_comm : ∀ (n m : Nat), Eq Nat (add n m) (add m n)`.
    pub add_comm: NameId,
    /// `add_assoc : ∀ (a b c : Nat), Eq Nat (add (add a b) c) (add a (add b c))`.
    pub add_assoc: NameId,
    /// `add_right_comm : ∀ (a b c : Nat), Eq Nat (add (add a b) c) (add (add a c) b)`.
    pub add_right_comm: NameId,
    /// `succ_injective : ∀ n m, succ n = succ m → n = m`.
    pub succ_injective: NameId,
    /// `add_right_cancel : ∀ n m k, n + k = m + k → n = m`.
    pub add_right_cancel: NameId,
    /// `add_left_cancel : ∀ a b c, a + b = a + c → b = c`.
    pub add_left_cancel: NameId,

    // --- multiplicative theorems --------------------------------------------
    /// `zero_mul : ∀ (n : Nat), Eq Nat (mul zero n) zero`.
    pub zero_mul: NameId,
    /// `succ_mul : ∀ (n m : Nat), Eq Nat (mul (succ n) m) (add (mul n m) m)`.
    pub succ_mul: NameId,
    /// `mul_comm : ∀ (n m : Nat), Eq Nat (mul n m) (mul m n)`.
    pub mul_comm: NameId,
    /// `left_distrib : ∀ (a b c : Nat), Eq Nat (mul a (add b c)) (add (mul a b) (mul a c))`.
    pub left_distrib: NameId,
    /// `right_distrib : ∀ (a b c : Nat), Eq Nat (mul (add a b) c) (add (mul a c) (mul b c))`.
    pub right_distrib: NameId,
    /// `mul_assoc : ∀ (a b c : Nat), Eq Nat (mul (mul a b) c) (mul a (mul b c))`.
    pub mul_assoc: NameId,
    /// `one_mul : ∀ (a : Nat), Eq Nat (mul (succ zero) a) a`.
    pub one_mul: NameId,
    /// `mul_one : ∀ (a : Nat), Eq Nat (mul a (succ zero)) a`.
    pub mul_one: NameId,

    // --- the order relation --------------------------------------------------
    /// `Nat.le : Nat → Nat → Prop` — an indexed inductive relation with the
    /// shape of Lean's own `Nat.le` (the first argument is a *parameter*, the
    /// second an *index*).
    ///
    /// This fragment is deliberately minimal: it carries reflexivity/step
    /// (the constructors), `zero_le`, successor monotonicity/inversion,
    /// transitivity, and `le_add_right` — enough to *state and derive* bounds,
    /// but **not** a complete order library. There is no antisymmetry, `min`,
    /// or decidability. The constructor shape matches Lean's,
    /// so those are extensions rather than redesigns.
    pub le: NameId,
    /// `Nat.lt n m := Nat.le (Nat.succ n) m`.
    pub lt: NameId,
    /// `Nat.inClosedInterval lower upper value := Le lower value ∧ Le value upper`.
    pub in_closed_interval: NameId,
    /// `Nat.le.refl : ∀ (n : Nat), Le n n`.
    pub le_refl: NameId,
    /// `Nat.le.step : ∀ (n m : Nat), Le n m → Le n (succ m)`.
    pub le_step: NameId,
    /// `Nat.le.rec` — the generated recursor (induction on the derivation).
    pub le_rec: NameId,
    /// `zero_le : ∀ (n : Nat), Le zero n`.
    pub zero_le: NameId,
    /// `le_succ_succ : ∀ (n m : Nat), Le n m → Le (succ n) (succ m)`.
    pub le_succ_succ: NameId,
    /// `le_of_succ_le_succ : ∀ (n m : Nat), Le (succ n) (succ m) → Le n m`.
    pub le_of_succ_le_succ: NameId,
    /// `le_trans : ∀ (a b c : Nat), Le a b → Le b c → Le a c`.
    pub le_trans: NameId,
    /// `lt_or_eq_of_le : ∀ a b, Le a b → Or (Lt a b) (Eq Nat a b)`.
    pub lt_or_eq_of_le: NameId,
    /// `lt_of_lt_of_le : ∀ a b c, Lt a b → Le b c → Lt a c`.
    pub lt_of_lt_of_le: NameId,
    /// `lt_of_le_of_lt : ∀ a b c, Le a b → Lt b c → Lt a c`.
    pub lt_of_le_of_lt: NameId,
    /// `lt_irrefl : ∀ a, Not (Lt a a)`.
    pub lt_irrefl: NameId,
    /// Reducible `lt_well_founded : WellFounded Nat.lt`.
    pub lt_well_founded: NameId,
    /// `le_total : ∀ a b, Or (Le a b) (Le b a)`.
    pub le_total: NameId,
    /// `not_succ_le_zero : ∀ n, Not (Le (succ n) zero)`.
    pub not_succ_le_zero: NameId,
    /// `le_antisymm : ∀ a b, Le a b → Le b a → Eq a b`.
    pub le_antisymm: NameId,
    /// `le_intro : ∀ a b k, a+k=b → Le a b`.
    pub le_intro: NameId,
    /// `le_dest : ∀ a b, Le a b → Exists (fun k => a+k=b)`.
    pub le_dest: NameId,
    /// `le_add_right : ∀ (n k : Nat), Le n (add n k)`.
    pub le_add_right: NameId,
    /// `add_le_add_left : ∀ c a b, Le a b → Le (c+a) (c+b)`.
    pub add_le_add_left: NameId,
    /// `add_lt_add_left : ∀ c a b, Lt a b → Lt (c+a) (c+b)`.
    pub add_lt_add_left: NameId,
    /// `add_le_add_right : ∀ c a b, Le a b → Le (a+c) (b+c)`.
    pub add_le_add_right: NameId,
    /// `le_of_add_le_add_left : ∀ c a b, Le (c+a) (c+b) → Le a b`.
    pub le_of_add_le_add_left: NameId,
    /// `le_of_add_le_add_right : ∀ c a b, Le (a+c) (b+c) → Le a b`.
    pub le_of_add_le_add_right: NameId,
    /// `mul_le_mul_left : ∀ c a b, Le a b → Le (c*a) (c*b)`.
    pub mul_le_mul_left: NameId,
    /// `le_of_mul_le_mul_left_succ : ∀ c a b, Le ((succ c)*a) ((succ c)*b) → Le a b`.
    pub le_of_mul_le_mul_left_succ: NameId,
    /// `le_of_mul_le_mul_left : ∀ c a b, Le one c → Le (c*a) (c*b) → Le a b`.
    pub le_of_mul_le_mul_left: NameId,
    /// `mul_left_cancel_of_pos : ∀ c a b, Le one c → Eq (c*a) (c*b) → Eq a b`.
    pub mul_left_cancel_of_pos: NameId,
    /// `sub_add_cancel : ∀ m n, Le m n → add (sub n m) m = n`.
    pub sub_add_cancel: NameId,
    /// `sub_eq_zero_of_le : ∀ a b, Le a b → sub a b = zero`.
    pub sub_eq_zero_of_le: NameId,
    /// `sub_le_iff_le_add : ∀ x y z, Iff (Le (sub x y) z) (Le x (add z y))`.
    pub sub_le_iff_le_add: NameId,
    /// `mul_sub_left_distrib : ∀ b q a, Le a q → b*(q-a) = b*q-b*a`.
    pub mul_sub_left_distrib: NameId,
    /// Unconditional truncated distributivity `b*(q-a) = b*q-b*a`.
    pub mul_sub_left_distrib_total: NameId,

    // --- Euclidean division -------------------------------------------------
    /// `Nat.divMod d n q r := n = d*q+r ∧ r<d`.
    pub div_mod: NameId,
    /// `Nat.div_mod_exists : ∀ d n, Le one d → ∃ q r, divMod d n q r`.
    pub div_mod_exists: NameId,
    /// `Nat.div_mod_unique : divMod d n q₁ r₁ → divMod d n q₂ r₂ → q₁=q₂ ∧ r₁=r₂`.
    pub div_mod_unique: NameId,
    /// `Nat.div_mod_bounds : divMod d n q r → d*q ≤ n ∧ n < d*(succ q)`.
    pub div_mod_bounds: NameId,
    /// `Nat.div_mod_mul_le_iff : divMod d n q r → (d*s ≤ n ↔ s ≤ q)`.
    pub div_mod_mul_le_iff: NameId,
    /// `Nat.div_mod_lt_mul_iff : divMod d n q r → (n < d*s ↔ q < s)`.
    pub div_mod_lt_mul_iff: NameId,
    /// `Nat.div_mod_add_multiple :
    ///   divMod d n q r → divMod d (n+d*k) (q+k) r`.
    pub div_mod_add_multiple: NameId,

    // --- divisibility -------------------------------------------------------
    /// `Nat.dvd : Nat → Nat → Prop`, where `dvd a n := ∃ q, n = a * q`.
    pub dvd: NameId,
    /// `Nat.div_mod_remainder_eq_zero_iff_dvd : divMod d n q r → (r=0 ↔ dvd d n)`.
    pub div_mod_remainder_eq_zero_iff_dvd: NameId,
    /// `Nat.div_mod_exact_exists : Le one d → dvd d n → ∃ q, divMod d n q zero`.
    pub div_mod_exact_exists: NameId,
    /// Executable quotient and remainder satisfy `divMod` at every successor divisor.
    pub div_mod_exec: NameId,
    /// `Nat.mod_lt : ∀ k n, mod n (succ k) < succ k`.
    pub mod_lt: NameId,
    /// `Nat.gcd_zero_left : ∀ n, gcd zero n = n`.
    pub gcd_zero_left: NameId,
    /// `Nat.gcd_succ : ∀ k n, gcd (succ k) n = gcd (mod n (succ k)) (succ k)`.
    pub gcd_succ: NameId,
    /// `Nat.gcd_dvd : ∀ m n, gcd m n | m ∧ gcd m n | n`.
    pub gcd_dvd: NameId,
    /// `Nat.gcd_dvd_left : ∀ m n, gcd m n | m`.
    pub gcd_dvd_left: NameId,
    /// `Nat.gcd_dvd_right : ∀ m n, gcd m n | n`.
    pub gcd_dvd_right: NameId,
    /// `Nat.dvd_gcd : k | m → k | n → k | gcd m n`.
    pub dvd_gcd: NameId,
    /// `Nat.dvd_gcd_iff : k | gcd m n ↔ k | m ∧ k | n`.
    pub dvd_gcd_iff: NameId,
    /// Balanced natural Bézout certificates:
    /// `bezout m n g := ∃ mp mn np nn, g + m*mn + n*nn = m*mp + n*np`.
    pub bezout: NameId,
    /// `Nat.gcd_bezout : ∀ m n, bezout m n (gcd m n)`.
    pub gcd_bezout: NameId,
    /// `Nat.modEq d a b := ∃ u v, a + d*u = b + d*v`.
    pub mod_eq: NameId,
    /// `Nat.mod_eq_refl : ∀ d a, modEq d a a`.
    pub mod_eq_refl: NameId,
    /// `Nat.mod_eq_symm : ∀ d a b, modEq d a b → modEq d b a`.
    pub mod_eq_symm: NameId,
    /// `Nat.mod_eq_trans : ∀ d a b c, modEq d a b → modEq d b c → modEq d a c`.
    pub mod_eq_trans: NameId,
    /// `Nat.mod_eq_add_left : ∀ d a b c, modEq d a b → modEq d (c+a) (c+b)`.
    pub mod_eq_add_left: NameId,
    /// `Nat.mod_eq_add_right : ∀ d a b c, modEq d a b → modEq d (a+c) (b+c)`.
    pub mod_eq_add_right: NameId,
    /// `Nat.mod_eq_add : modEq d a b → modEq d c e → modEq d (a+c) (b+e)`.
    pub mod_eq_add: NameId,
    /// `Nat.mod_eq_mul_left : ∀ d a b c, modEq d a b → modEq d (c*a) (c*b)`.
    pub mod_eq_mul_left: NameId,
    /// `Nat.mod_eq_mul_right : ∀ d a b c, modEq d a b → modEq d (a*c) (b*c)`.
    pub mod_eq_mul_right: NameId,
    /// `Nat.mod_eq_mul : modEq d a b → modEq d c e → modEq d (a*c) (b*e)`.
    pub mod_eq_mul: NameId,
    /// `Nat.div_mod_same_remainder_mod_eq :
    ///   divMod d a qa r → divMod d b qb r → modEq d a b`.
    pub div_mod_same_remainder_mod_eq: NameId,
    /// `Nat.div_mod_remainder_eq_of_mod_eq :
    ///   modEq d a b → divMod d a qa ra → divMod d b qb rb → ra = rb`.
    pub div_mod_remainder_eq_of_mod_eq: NameId,
    /// `Nat.mod_eq_iff_div_mod_remainder_eq :
    ///   divMod d a qa ra → divMod d b qb rb → (modEq d a b ↔ ra = rb)`.
    pub mod_eq_iff_div_mod_remainder_eq: NameId,
    /// `Nat.mod_eq_zero_of_dvd : dvd d n → modEq d n zero`.
    pub mod_eq_zero_of_dvd: NameId,
    /// `Nat.dvd_of_mod_eq_zero_of_pos :
    ///   Le one d → modEq d n zero → dvd d n`.
    pub dvd_of_mod_eq_zero_of_pos: NameId,
    /// `Nat.mod_eq_zero_iff_dvd : modEq d n zero ↔ dvd d n`.
    pub mod_eq_zero_iff_dvd: NameId,
    /// `Nat.valuationAt a n e := dvd (a^e) n ∧ Not (dvd (a^(e+1)) n)`.
    pub valuation_at: NameId,
    /// `Nat.dvd_mul : ∀ a q, dvd a (a * q)`.
    pub dvd_mul: NameId,
    /// `Nat.dvd_refl : ∀ a, dvd a a`.
    pub dvd_refl: NameId,
    /// `Nat.dvd_zero : ∀ a, dvd a zero`.
    pub dvd_zero: NameId,
    /// `Nat.dvd_trans : ∀ a b c, dvd a b → dvd b c → dvd a c`.
    pub dvd_trans: NameId,
    /// `Nat.dvd_mul_right_of_dvd : dvd a b → dvd a (b*c)`.
    pub dvd_mul_right_of_dvd: NameId,
    /// `Nat.dvd_add_iff_right : dvd k m → (dvd k n ↔ dvd k (m+n))`.
    pub dvd_add_iff_right: NameId,
    /// Positive-divisor executable remainder preserves divisibility.
    pub dvd_mod_iff: NameId,
    /// `Nat.dvd_add : ∀ a m n, dvd a m → dvd a n → dvd a (m + n)`.
    pub dvd_add: NameId,
    /// `Nat.dvd_add_right_cancel_of_pos : ∀ a m n, Le one a → dvd a m → dvd a (m+n) → dvd a n`.
    pub dvd_add_right_cancel_of_pos: NameId,
    /// `Nat.not_dvd_one_of_two_le : ∀ a, Le two a → Not (dvd a one)`.
    pub not_dvd_one_of_two_le: NameId,
    /// `Nat.eq_one_of_dvd_one : ∀ d, dvd d one → Eq d one` — the closing step
    /// for coprimality after dividing by a gcd.
    pub eq_one_of_dvd_one: NameId,
    /// `Nat.coprime_of_bezout_one : ∀ a b, bezout a b 1 → Eq (gcd a b) 1` — a
    /// Bézout identity with coefficient `1` *is* coprimality.
    pub coprime_of_bezout_one: NameId,
    /// `Nat.bezout_of_scaled : ∀ g a b, 1 ≤ g → bezout (g*a) (g*b) g →
    /// bezout a b 1` — divide a Bézout identity through by its coefficient.
    pub bezout_of_scaled: NameId,
    /// `Nat.gcd_cofactors_coprime : ∀ g a b, 1 ≤ g → gcd (g*a) (g*b) = g →
    /// gcd a b = 1` — the cofactors of a gcd are coprime.
    pub gcd_cofactors_coprime: NameId,
    /// `Nat.div_mul_cancel_of_dvd : ∀ g n, 1 ≤ g → dvd g n → g * (n / g) = n` —
    /// exact division recovers its dividend.
    pub div_mul_cancel_of_dvd: NameId,
    /// `Nat.one_le_right_of_mul : ∀ g q, 1 ≤ g * q → 1 ≤ q`.
    pub one_le_right_of_mul: NameId,
    /// `Nat.one_le_left_of_mul : ∀ g q, 1 ≤ g * q → 1 ≤ g`.
    pub one_le_left_of_mul: NameId,
    /// `Nat.one_le_of_dvd_pos : ∀ g n, 1 ≤ n → dvd g n → 1 ≤ g` — a divisor of a
    /// positive number is positive.
    pub one_le_of_dvd_pos: NameId,
    /// `Nat.one_le_mul : ∀ a b, 1 ≤ a → 1 ≤ b → 1 ≤ a * b`.
    pub one_le_mul: NameId,
    /// `Nat.not_dvd_one_add_mul_of_two_le : ∀ a t, Le two a → Not (dvd a (one+a*t))`.
    pub not_dvd_one_add_mul_of_two_le: NameId,
    /// `Nat.valuation_at_two_mul_sq : ∀ a u, Le two a → Not (dvd a u) → valuationAt a ((a*a)*u) two`.
    pub valuation_at_two_mul_sq: NameId,
}

/// Declare the natural-number prelude into `kernel`'s environment, returning the
/// [`NatPrelude`] of interned names.
///
/// The shared logical prelude is built or exact-validated first (as
/// [`build_int_prelude`](crate::build_int_prelude) does).
/// Every definition and theorem is admitted through the **trusted**
/// [`Kernel::add_declaration`](crate::Kernel::add_declaration) gate and `Nat.le`
/// through [`Kernel::add_inductive`](crate::Kernel::add_inductive) — the kernel
/// re-checks each proof term against its stated proposition, so a green build of
/// this function *is* a machine-checked proof of every theorem it declares.
///
/// Repeated construction validates and returns the exact registered package.
/// Any trusted-gate rejection is returned as [`KernelError`] and rolls back all
/// Nat declarations admitted by this invocation.
///
/// # Errors
///
/// Returns the trusted gate's rejection or an exact-package conflict. A failed
/// Nat build leaves the pre-call environment unchanged.
pub fn build_nat_prelude(kernel: &mut Kernel) -> Result<NatPrelude, KernelError> {
    if let Some(PreludeValue::Nat(prelude)) =
        crate::prelude_cache::try_restore(kernel, PreludeKey::Nat)
    {
        return Ok(*prelude);
    }
    build_nat_prelude_uncached(kernel)
}

/// [`build_nat_prelude`] without the process-wide template fast path.
///
/// This is the route that actually runs the trusted gate, and the one the
/// template itself is built through (ADR-0464).
pub(crate) fn build_nat_prelude_uncached(kernel: &mut Kernel) -> Result<NatPrelude, KernelError> {
    let logic = build_logic_prelude(kernel)?;
    if let Some(PreludeValue::Nat(prelude)) = kernel.cached_prelude(PreludeKey::Nat)? {
        return Ok(*prelude);
    }
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<NatPrelude, KernelError> {
        let nat = logic.nat;

        // Intern every name up front so the `NatPrelude` (which the proof scripts
        // below consult for lemma handles) exists before anything is declared.
        let le = kernel.name_str(nat, "le");
        let p = NatPrelude {
            logic,
            nat,
            zero: logic.nat_zero,
            succ: logic.nat_succ,
            rec: logic.nat_rec,
            add: kernel.name_str(nat, "add"),
            mul: kernel.name_str(nat, "mul"),
            pow: kernel.name_str(nat, "pow"),
            beq: kernel.name_str(nat, "beq"),
            beq_refl: kernel.name_str(nat, "beq_refl"),
            eq_of_beq_eq_true: kernel.name_str(nat, "eq_of_beq_eq_true"),
            beq_eq_true_of_eq: kernel.name_str(nat, "beq_eq_true_of_eq"),
            beq_eq_true_iff: kernel.name_str(nat, "beq_eq_true_iff"),
            div_mod_state: kernel.name_str(nat, "divModState"),
            div: kernel.name_str(nat, "div"),
            mod_: kernel.name_str(nat, "mod"),
            gcd: kernel.name_str(nat, "gcd"),
            sum_range: kernel.name_str(nat, "sumRange"),
            pred: kernel.name_str(nat, "pred"),
            sub: kernel.name_str(nat, "sub"),
            div_zero: kernel.name_str(nat, "div_zero"),
            mod_zero: kernel.name_str(nat, "mod_zero"),
            zero_div: kernel.name_str(nat, "zero_div"),
            zero_mod: kernel.name_str(nat, "zero_mod"),
            div_succ: kernel.name_str(nat, "div_succ"),
            mod_succ: kernel.name_str(nat, "mod_succ"),
            add_zero: kernel.name_str(nat, "add_zero"),
            add_succ: kernel.name_str(nat, "add_succ"),
            mul_zero: kernel.name_str(nat, "mul_zero"),
            mul_succ: kernel.name_str(nat, "mul_succ"),
            pow_zero: kernel.name_str(nat, "pow_zero"),
            pow_add: kernel.name_str(nat, "pow_add"),
            pow_succ: kernel.name_str(nat, "pow_succ"),
            pred_zero: kernel.name_str(nat, "pred_zero"),
            pred_succ: kernel.name_str(nat, "pred_succ"),
            sub_zero: kernel.name_str(nat, "sub_zero"),
            sub_succ: kernel.name_str(nat, "sub_succ"),
            succ_sub_succ: kernel.name_str(nat, "succ_sub_succ"),
            sub_self: kernel.name_str(nat, "sub_self"),
            add_sub_cancel_left: kernel.name_str(nat, "add_sub_cancel_left"),
            sum_range_zero: kernel.name_str(nat, "sumRange_zero"),
            sum_range_succ: kernel.name_str(nat, "sumRange_succ"),
            sum_range_congr: kernel.name_str(nat, "sumRange_congr"),
            mul_sum_range: kernel.name_str(nat, "mul_sumRange"),
            mul_sum_range_pow: kernel.name_str(nat, "mul_sumRange_pow"),
            zero_add: kernel.name_str(nat, "zero_add"),
            succ_add: kernel.name_str(nat, "succ_add"),
            add_comm: kernel.name_str(nat, "add_comm"),
            add_assoc: kernel.name_str(nat, "add_assoc"),
            add_right_comm: kernel.name_str(nat, "add_right_comm"),
            succ_injective: kernel.name_str(nat, "succ_injective"),
            add_right_cancel: kernel.name_str(nat, "add_right_cancel"),
            add_left_cancel: kernel.name_str(nat, "add_left_cancel"),
            zero_mul: kernel.name_str(nat, "zero_mul"),
            succ_mul: kernel.name_str(nat, "succ_mul"),
            mul_comm: kernel.name_str(nat, "mul_comm"),
            left_distrib: kernel.name_str(nat, "left_distrib"),
            right_distrib: kernel.name_str(nat, "right_distrib"),
            mul_assoc: kernel.name_str(nat, "mul_assoc"),
            one_mul: kernel.name_str(nat, "one_mul"),
            mul_one: kernel.name_str(nat, "mul_one"),
            le,
            lt: kernel.name_str(nat, "lt"),
            in_closed_interval: kernel.name_str(nat, "inClosedInterval"),
            le_refl: kernel.name_str(le, "refl"),
            le_step: kernel.name_str(le, "step"),
            le_rec: kernel.name_str(le, "rec"),
            zero_le: kernel.name_str(nat, "zero_le"),
            le_succ_succ: kernel.name_str(nat, "le_succ_succ"),
            le_of_succ_le_succ: kernel.name_str(nat, "le_of_succ_le_succ"),
            le_trans: kernel.name_str(nat, "le_trans"),
            lt_or_eq_of_le: kernel.name_str(nat, "lt_or_eq_of_le"),
            lt_of_lt_of_le: kernel.name_str(nat, "lt_of_lt_of_le"),
            lt_of_le_of_lt: kernel.name_str(nat, "lt_of_le_of_lt"),
            lt_irrefl: kernel.name_str(nat, "lt_irrefl"),
            lt_well_founded: kernel.name_str(nat, "lt_well_founded"),
            le_total: kernel.name_str(nat, "le_total"),
            not_succ_le_zero: kernel.name_str(nat, "not_succ_le_zero"),
            le_antisymm: kernel.name_str(nat, "le_antisymm"),
            le_intro: kernel.name_str(nat, "le_intro"),
            le_dest: kernel.name_str(nat, "le_dest"),
            le_add_right: kernel.name_str(nat, "le_add_right"),
            add_le_add_left: kernel.name_str(nat, "add_le_add_left"),
            add_lt_add_left: kernel.name_str(nat, "add_lt_add_left"),
            add_le_add_right: kernel.name_str(nat, "add_le_add_right"),
            le_of_add_le_add_left: kernel.name_str(nat, "le_of_add_le_add_left"),
            le_of_add_le_add_right: kernel.name_str(nat, "le_of_add_le_add_right"),
            mul_le_mul_left: kernel.name_str(nat, "mul_le_mul_left"),
            le_of_mul_le_mul_left_succ: kernel.name_str(nat, "le_of_mul_le_mul_left_succ"),
            le_of_mul_le_mul_left: kernel.name_str(nat, "le_of_mul_le_mul_left"),
            mul_left_cancel_of_pos: kernel.name_str(nat, "mul_left_cancel_of_pos"),
            sub_add_cancel: kernel.name_str(nat, "sub_add_cancel"),
            sub_eq_zero_of_le: kernel.name_str(nat, "sub_eq_zero_of_le"),
            sub_le_iff_le_add: kernel.name_str(nat, "sub_le_iff_le_add"),
            mul_sub_left_distrib: kernel.name_str(nat, "mul_sub_left_distrib"),
            mul_sub_left_distrib_total: kernel.name_str(nat, "mul_sub_left_distrib_total"),
            div_mod: kernel.name_str(nat, "divMod"),
            div_mod_exists: kernel.name_str(nat, "div_mod_exists"),
            div_mod_unique: kernel.name_str(nat, "div_mod_unique"),
            div_mod_bounds: kernel.name_str(nat, "div_mod_bounds"),
            div_mod_mul_le_iff: kernel.name_str(nat, "div_mod_mul_le_iff"),
            div_mod_lt_mul_iff: kernel.name_str(nat, "div_mod_lt_mul_iff"),
            div_mod_add_multiple: kernel.name_str(nat, "div_mod_add_multiple"),
            dvd: kernel.name_str(nat, "dvd"),
            div_mod_remainder_eq_zero_iff_dvd: kernel
                .name_str(nat, "div_mod_remainder_eq_zero_iff_dvd"),
            div_mod_exact_exists: kernel.name_str(nat, "div_mod_exact_exists"),
            div_mod_exec: kernel.name_str(nat, "div_mod_exec"),
            mod_lt: kernel.name_str(nat, "mod_lt"),
            gcd_zero_left: kernel.name_str(nat, "gcd_zero_left"),
            gcd_succ: kernel.name_str(nat, "gcd_succ"),
            gcd_dvd: kernel.name_str(nat, "gcd_dvd"),
            gcd_dvd_left: kernel.name_str(nat, "gcd_dvd_left"),
            gcd_dvd_right: kernel.name_str(nat, "gcd_dvd_right"),
            dvd_gcd: kernel.name_str(nat, "dvd_gcd"),
            dvd_gcd_iff: kernel.name_str(nat, "dvd_gcd_iff"),
            bezout: kernel.name_str(nat, "bezout"),
            gcd_bezout: kernel.name_str(nat, "gcd_bezout"),
            mod_eq: kernel.name_str(nat, "modEq"),
            mod_eq_refl: kernel.name_str(nat, "mod_eq_refl"),
            mod_eq_symm: kernel.name_str(nat, "mod_eq_symm"),
            mod_eq_trans: kernel.name_str(nat, "mod_eq_trans"),
            mod_eq_add_left: kernel.name_str(nat, "mod_eq_add_left"),
            mod_eq_add_right: kernel.name_str(nat, "mod_eq_add_right"),
            mod_eq_add: kernel.name_str(nat, "mod_eq_add"),
            mod_eq_mul_left: kernel.name_str(nat, "mod_eq_mul_left"),
            mod_eq_mul_right: kernel.name_str(nat, "mod_eq_mul_right"),
            mod_eq_mul: kernel.name_str(nat, "mod_eq_mul"),
            div_mod_same_remainder_mod_eq: kernel.name_str(nat, "div_mod_same_remainder_mod_eq"),
            div_mod_remainder_eq_of_mod_eq: kernel.name_str(nat, "div_mod_remainder_eq_of_mod_eq"),
            mod_eq_iff_div_mod_remainder_eq: kernel
                .name_str(nat, "mod_eq_iff_div_mod_remainder_eq"),
            mod_eq_zero_of_dvd: kernel.name_str(nat, "mod_eq_zero_of_dvd"),
            dvd_of_mod_eq_zero_of_pos: kernel.name_str(nat, "dvd_of_mod_eq_zero_of_pos"),
            mod_eq_zero_iff_dvd: kernel.name_str(nat, "mod_eq_zero_iff_dvd"),
            valuation_at: kernel.name_str(nat, "valuationAt"),
            dvd_mul: kernel.name_str(nat, "dvd_mul"),
            dvd_refl: kernel.name_str(nat, "dvd_refl"),
            dvd_zero: kernel.name_str(nat, "dvd_zero"),
            dvd_trans: kernel.name_str(nat, "dvd_trans"),
            dvd_mul_right_of_dvd: kernel.name_str(nat, "dvd_mul_right_of_dvd"),
            dvd_add_iff_right: kernel.name_str(nat, "dvd_add_iff_right"),
            dvd_mod_iff: kernel.name_str(nat, "dvd_mod_iff"),
            dvd_add: kernel.name_str(nat, "dvd_add"),
            dvd_add_right_cancel_of_pos: kernel.name_str(nat, "dvd_add_right_cancel_of_pos"),
            not_dvd_one_of_two_le: kernel.name_str(nat, "not_dvd_one_of_two_le"),
            eq_one_of_dvd_one: kernel.name_str(nat, "eq_one_of_dvd_one"),
            coprime_of_bezout_one: kernel.name_str(nat, "coprime_of_bezout_one"),
            bezout_of_scaled: kernel.name_str(nat, "bezout_of_scaled"),
            gcd_cofactors_coprime: kernel.name_str(nat, "gcd_cofactors_coprime"),
            div_mul_cancel_of_dvd: kernel.name_str(nat, "div_mul_cancel_of_dvd"),
            one_le_right_of_mul: kernel.name_str(nat, "one_le_right_of_mul"),
            one_le_left_of_mul: kernel.name_str(nat, "one_le_left_of_mul"),
            one_le_of_dvd_pos: kernel.name_str(nat, "one_le_of_dvd_pos"),
            one_le_mul: kernel.name_str(nat, "one_le_mul"),
            not_dvd_one_add_mul_of_two_le: kernel.name_str(nat, "not_dvd_one_add_mul_of_two_le"),
            valuation_at_two_mul_sq: kernel.name_str(nat, "valuation_at_two_mul_sq"),
        };

        let mut d = NatDev::new(kernel, p);
        declare_arithmetic(&mut d, &p)?;
        declare_boolean_equality(&mut d, &p)?;
        declare_executable_division(&mut d, &p)?;
        declare_subtraction(&mut d, &p)?;
        declare_finite_ranges(&mut d, &p)?;
        declare_defining_equations(&mut d, &p)?;
        declare_subtraction_theorems(&mut d, &p)?;
        declare_additive_theorems(&mut d, &p)?;
        declare_multiplicative_theorems(&mut d, &p)?;
        declare_finite_sum_theorems(&mut d, &p)?;
        declare_order(&mut d, &p)?;
        declare_euclidean_division(&mut d, &p)?;
        declare_divisibility(&mut d, &p)?;
        declare_executable_gcd(&mut d, &p)?;
        declare_gcd_semantics(&mut d, &p)?;
        declare_gcd_bezout(&mut d, &p)?;
        declare_modular_congruence(&mut d, &p)?;
        Ok(p)
    })();
    match built {
        Ok(prelude) => {
            kernel.register_prelude(
                PreludeKey::Nat,
                PreludeValue::Nat(Box::new(prelude)),
                checkpoint,
            );
            Ok(prelude)
        }
        Err(error) => {
            kernel.rollback_prelude(checkpoint);
            Err(error)
        }
    }
}

#[cfg(test)]
mod nat_prelude_tests;
