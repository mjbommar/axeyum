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

use crate::BinderInfo;
use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::PreludeKey;
use crate::PreludeValue;
use crate::build_logic_prelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;

mod defs;
mod helpers;
mod ops;

pub use ops::{NatDev, NatOps, NatState};

use defs::{
    declare_arithmetic, declare_boolean_equality, declare_defining_equations,
    declare_executable_division, declare_finite_ranges, declare_subtraction,
};
use helpers::{
    and_left, and_right, apply_nat_function_equality, iff_forward, iff_reverse, transport_dvd_left,
    transport_dvd_right,
};

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

/// Balanced-witness congruence over naturals. This representation needs
/// neither signed subtraction nor an executable remainder function.
fn declare_modular_congruence(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();
    let one = d.level_one();

    // modEq d a b := ∃ u v, a + d*u = b + d*v
    {
        let modulus_fv = d.fresh_fvar();
        let modulus = d.kernel().fvar(modulus_fv);
        let left_fv = d.fresh_fvar();
        let left = d.kernel().fvar(left_fv);
        let right_fv = d.fresh_fvar();
        let right = d.kernel().fvar(right_fv);
        let body = d.mod_eq_witnesses(modulus, left, right);
        let value = {
            let with_right = d.lam_fv(right_fv, nat, body);
            let with_left = d.lam_fv(left_fv, nat, with_right);
            d.lam_fv(modulus_fv, nat, with_left)
        };
        let ty = {
            let with_right = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            let with_left = d.kernel().pi(anon, nat, with_right, BinderInfo::Default);
            d.kernel().pi(anon, nat, with_left, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.mod_eq,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    // mod_eq_refl : ∀ d a, modEq d a a
    d.theorem(p.mod_eq_refl, 2, &|d, v| {
        let (modulus, value) = (v[0], v[1]);
        let zero = d.zero();
        let outer_predicate = d.mod_eq_outer_predicate(modulus, value, value);
        let inner_predicate = d.mod_eq_inner_predicate(modulus, value, value, zero);
        let equation = d.refl(value);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let inner = d.apply(intro, &[nat, inner_predicate, zero, equation]);
        let proof = d.apply(intro, &[nat, outer_predicate, zero, inner]);
        (d.mod_eq(modulus, value, value), proof)
    })?;

    // mod_eq_symm : ∀ d a b, modEq d a b → modEq d b a
    d.theorem(p.mod_eq_symm, 3, &|d, v| {
        let (modulus, left, right) = (v[0], v[1], v[2]);
        let source = d.mod_eq(modulus, left, right);
        let target = d.mod_eq(modulus, right, left);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let outer_predicate = d.mod_eq_outer_predicate(modulus, left, right);
        let outer_motive = d.kernel().lam(anon, source, target, BinderInfo::Default);
        let outer_minor = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_source = d.mod_eq_inner_exists(modulus, left, right, u);
            let inner_source_fv = d.fresh_fvar();
            let inner_source_proof = d.kernel().fvar(inner_source_fv);
            let inner_predicate = d.mod_eq_inner_predicate(modulus, left, right, u);
            let inner_motive = d
                .kernel()
                .lam(anon, inner_source, target, BinderInfo::Default);
            let inner_minor = {
                let w_fv = d.fresh_fvar();
                let w = d.kernel().fvar(w_fv);
                let left_sum = d.mod_eq_sum(modulus, left, u);
                let right_sum = d.mod_eq_sum(modulus, right, w);
                let equation_ty = d.eq(left_sum, right_sum);
                let equation_fv = d.fresh_fvar();
                let equation = d.kernel().fvar(equation_fv);
                let reversed = d.symm(left_sum, right_sum, equation);
                let target_outer = d.mod_eq_outer_predicate(modulus, right, left);
                let target_inner = d.mod_eq_inner_predicate(modulus, right, left, w);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let inner_proof = d.apply(intro, &[nat, target_inner, u, reversed]);
                let body = d.apply(intro, &[nat, target_outer, w, inner_proof]);
                let with_equation = d.lam_fv(equation_fv, equation_ty, body);
                d.lam_fv(w_fv, nat, with_equation)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(
                rec,
                &[
                    nat,
                    inner_predicate,
                    inner_motive,
                    inner_minor,
                    inner_source_proof,
                ],
            );
            let with_inner = d.lam_fv(inner_source_fv, inner_source, body);
            d.lam_fv(u_fv, nat, with_inner)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            rec,
            &[
                nat,
                outer_predicate,
                outer_motive,
                outer_minor,
                source_proof,
            ],
        );
        let stmt = d.arrow(source, target);
        let proof = d.lam_fv(source_fv, source, body);
        (stmt, proof)
    })?;

    declare_mod_eq_trans(d, &p, nat, anon, one)?;
    declare_mod_eq_add_left(d, &p, nat, anon, one)?;
    declare_mod_eq_additive_compatibility(d, &p)?;
    declare_mod_eq_mul_left(d, &p, nat, anon, one)?;
    declare_mod_eq_multiplicative_compatibility(d, &p)?;
    declare_div_mod_same_remainder_mod_eq(d, &p, nat, anon, one)?;
    declare_div_mod_remainder_eq_of_mod_eq(d, &p, nat, anon, one)?;
    declare_mod_eq_iff_div_mod_remainder_eq(d, &p)?;
    declare_mod_eq_zero_of_dvd(d, &p, nat, anon, one)?;
    declare_dvd_of_mod_eq_zero_of_pos(d, &p, nat, anon, one)?;
    declare_mod_eq_zero_iff_dvd(d, &p, nat, anon, one)?;
    Ok(())
}

fn declare_div_mod_same_remainder_mod_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;

    // div_mod_same_remainder_mod_eq :
    //   divMod d a qa r → divMod d b qb r → modEq d a b
    // The balanced congruence witnesses are the opposite quotients:
    // a + d*qb = (d*qa+r)+d*qb = (d*qb+r)+d*qa = b + d*qa.
    d.theorem(p.div_mod_same_remainder_mod_eq, 6, &|d, values| {
        let (modulus, left, right, left_quotient, right_quotient, remainder) = (
            values[0], values[1], values[2], values[3], values[4], values[5],
        );
        let left_relation_ty = d.div_mod(modulus, left, left_quotient, remainder);
        let right_relation_ty = d.div_mod(modulus, right, right_quotient, remainder);
        let target = d.mod_eq(modulus, left, right);
        let left_relation_fv = d.fresh_fvar();
        let left_relation = d.kernel().fvar(left_relation_fv);
        let right_relation_fv = d.fresh_fvar();
        let right_relation = d.kernel().fvar(right_relation_fv);

        let left_product = d.mul(modulus, left_quotient);
        let right_product = d.mul(modulus, right_quotient);
        let left_reconstructed = d.add(left_product, remainder);
        let right_reconstructed = d.add(right_product, remainder);
        let left_equation_ty = d.eq(left, left_reconstructed);
        let right_equation_ty = d.eq(right, right_reconstructed);
        let bound_ty = d.lt(remainder, modulus);

        let right_to_target = d.arrow(right_relation_ty, target);
        let left_motive =
            d.kernel()
                .lam(anon, left_relation_ty, right_to_target, BinderInfo::Default);
        let left_minor = {
            let left_equation_fv = d.fresh_fvar();
            let left_equation = d.kernel().fvar(left_equation_fv);
            let left_bound_fv = d.fresh_fvar();

            let right_motive = d
                .kernel()
                .lam(anon, right_relation_ty, target, BinderInfo::Default);
            let right_minor = {
                let right_equation_fv = d.fresh_fvar();
                let right_equation = d.kernel().fvar(right_equation_fv);
                let right_bound_fv = d.fresh_fvar();

                let start = d.add(left, right_product);
                let left_expanded = d.add(left_reconstructed, right_product);
                let left_then_right = d.add(left_product, right_product);
                let products_left_first = d.add(left_then_right, remainder);
                let right_then_left = d.add(right_product, left_product);
                let products_right_first = d.add(right_then_left, remainder);
                let right_expanded = d.add(right_reconstructed, left_product);
                let finish = d.add(right, left_product);

                let expand_left = d.congr(left, left_reconstructed, left_equation, &|d, value| {
                    d.add(value, right_product)
                });
                let regroup_left =
                    d.lemma(p.add_right_comm, &[left_product, remainder, right_product]);
                let commute_products = d.lemma(p.add_comm, &[left_product, right_product]);
                let commute_under_remainder = d.congr(
                    left_then_right,
                    right_then_left,
                    commute_products,
                    &|d, value| d.add(value, remainder),
                );
                let regroup_right_forward =
                    d.lemma(p.add_right_comm, &[right_product, remainder, left_product]);
                let regroup_right =
                    d.symm(right_expanded, products_right_first, regroup_right_forward);
                let right_equation_rev = d.symm(right, right_reconstructed, right_equation);
                let collapse_right = d.congr(
                    right_reconstructed,
                    right,
                    right_equation_rev,
                    &|d, value| d.add(value, left_product),
                );
                let (_, equation) = d.chain(
                    start,
                    &[
                        (left_expanded, expand_left),
                        (products_left_first, regroup_left),
                        (products_right_first, commute_under_remainder),
                        (right_expanded, regroup_right),
                        (finish, collapse_right),
                    ],
                );

                let target_outer = d.mod_eq_outer_predicate(modulus, left, right);
                let target_inner = d.mod_eq_inner_predicate(modulus, left, right, right_quotient);
                let exists_intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let inner = d.apply(exists_intro, &[nat, target_inner, left_quotient, equation]);
                let body = d.apply(exists_intro, &[nat, target_outer, right_quotient, inner]);
                let with_bound = d.lam_fv(right_bound_fv, bound_ty, body);
                d.lam_fv(right_equation_fv, right_equation_ty, with_bound)
            };
            let level_zero = d.kernel().level_zero();
            let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
            let body = d.apply(
                and_rec,
                &[
                    right_equation_ty,
                    bound_ty,
                    right_motive,
                    right_minor,
                    right_relation,
                ],
            );
            let with_right_relation = d.lam_fv(right_relation_fv, right_relation_ty, body);
            let with_bound = d.lam_fv(left_bound_fv, bound_ty, with_right_relation);
            d.lam_fv(left_equation_fv, left_equation_ty, with_bound)
        };
        let level_zero = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
        let body = d.apply(
            and_rec,
            &[
                left_equation_ty,
                bound_ty,
                left_motive,
                left_minor,
                left_relation,
            ],
        );
        let stmt = d.arrow(left_relation_ty, right_to_target);
        let proof = d.lam_fv(left_relation_fv, left_relation_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_div_mod_remainder_eq_of_mod_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;

    // div_mod_remainder_eq_of_mod_eq :
    //   modEq d a b → divMod d a qa ra → divMod d b qb rb → ra = rb
    // A balanced witness shifts both divisions to the same dividend; relational
    // uniqueness then compares their remainders.
    d.theorem(p.div_mod_remainder_eq_of_mod_eq, 7, &|d, values| {
        let (modulus, left, right, left_quotient, left_remainder, right_quotient, right_remainder) = (
            values[0], values[1], values[2], values[3], values[4], values[5], values[6],
        );
        let congruence_ty = d.mod_eq(modulus, left, right);
        let left_relation_ty =
            d.div_mod(modulus, left, left_quotient, left_remainder);
        let right_relation_ty =
            d.div_mod(modulus, right, right_quotient, right_remainder);
        let target = d.eq(left_remainder, right_remainder);
        let congruence_fv = d.fresh_fvar();
        let congruence = d.kernel().fvar(congruence_fv);
        let left_relation_fv = d.fresh_fvar();
        let left_relation = d.kernel().fvar(left_relation_fv);
        let right_relation_fv = d.fresh_fvar();
        let right_relation = d.kernel().fvar(right_relation_fv);

        let outer_predicate = d.mod_eq_outer_predicate(modulus, left, right);
        let outer_motive = d
            .kernel()
            .lam(anon, congruence_ty, target, BinderInfo::Default);
        let outer_minor = {
            let left_shift_fv = d.fresh_fvar();
            let left_shift = d.kernel().fvar(left_shift_fv);
            let inner_exists =
                d.mod_eq_inner_exists(modulus, left, right, left_shift);
            let inner_exists_fv = d.fresh_fvar();
            let inner_exists_proof = d.kernel().fvar(inner_exists_fv);
            let inner_predicate =
                d.mod_eq_inner_predicate(modulus, left, right, left_shift);
            let inner_motive = d
                .kernel()
                .lam(anon, inner_exists, target, BinderInfo::Default);
            let inner_minor = {
                let right_shift_fv = d.fresh_fvar();
                let right_shift = d.kernel().fvar(right_shift_fv);
                let shifted_left = d.mod_eq_sum(modulus, left, left_shift);
                let shifted_right = d.mod_eq_sum(modulus, right, right_shift);
                let witness_equation_ty = d.eq(shifted_left, shifted_right);
                let witness_equation_fv = d.fresh_fvar();
                let witness_equation = d.kernel().fvar(witness_equation_fv);

                let shifted_left_quotient = d.add(left_quotient, left_shift);
                let shifted_right_quotient = d.add(right_quotient, right_shift);
                let left_division = d.lemma(
                    p.div_mod_add_multiple,
                    &[
                        modulus,
                        left,
                        left_quotient,
                        left_remainder,
                        left_shift,
                        left_relation,
                    ],
                );
                let right_division = d.lemma(
                    p.div_mod_add_multiple,
                    &[
                        modulus,
                        right,
                        right_quotient,
                        right_remainder,
                        right_shift,
                        right_relation,
                    ],
                );
                let witness_equation_rev =
                    d.symm(shifted_left, shifted_right, witness_equation);
                let right_motive_at_shifted_right =
                    d.eq_motive(shifted_right, &|d, dividend| {
                        d.div_mod(
                            modulus,
                            dividend,
                            shifted_right_quotient,
                            right_remainder,
                        )
                    });
                let right_division_at_left = d.transport(
                    shifted_right,
                    right_motive_at_shifted_right,
                    right_division,
                    shifted_left,
                    witness_equation_rev,
                );
                let unique = d.lemma(
                    p.div_mod_unique,
                    &[
                        modulus,
                        shifted_left,
                        shifted_left_quotient,
                        left_remainder,
                        shifted_right_quotient,
                        right_remainder,
                        left_division,
                        right_division_at_left,
                    ],
                );
                let quotient_eq_ty =
                    d.eq(shifted_left_quotient, shifted_right_quotient);
                let unique_ty = d.const_app(p.logic.and, &[quotient_eq_ty, target]);
                let unique_motive = d
                    .kernel()
                    .lam(anon, unique_ty, target, BinderInfo::Default);
                let unique_minor = {
                    let quotient_eq_fv = d.fresh_fvar();
                    let remainder_eq_fv = d.fresh_fvar();
                    let remainder_eq = d.kernel().fvar(remainder_eq_fv);
                    let with_remainder =
                        d.lam_fv(remainder_eq_fv, target, remainder_eq);
                    d.lam_fv(quotient_eq_fv, quotient_eq_ty, with_remainder)
                };
                let level_zero = d.kernel().level_zero();
                let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
                let body = d.apply(
                    and_rec,
                    &[quotient_eq_ty, target, unique_motive, unique_minor, unique],
                );
                let with_equation =
                    d.lam_fv(witness_equation_fv, witness_equation_ty, body);
                d.lam_fv(right_shift_fv, nat, with_equation)
            };
            let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(
                exists_rec,
                &[
                    nat,
                    inner_predicate,
                    inner_motive,
                    inner_minor,
                    inner_exists_proof,
                ],
            );
            let with_inner = d.lam_fv(inner_exists_fv, inner_exists, body);
            d.lam_fv(left_shift_fv, nat, with_inner)
        };
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            exists_rec,
            &[
                nat,
                outer_predicate,
                outer_motive,
                outer_minor,
                congruence,
            ],
        );
        let right_to_target = d.arrow(right_relation_ty, target);
        let left_to_target = d.arrow(left_relation_ty, right_to_target);
        let stmt = d.arrow(congruence_ty, left_to_target);
        let with_right = d.lam_fv(right_relation_fv, right_relation_ty, body);
        let with_left = d.lam_fv(left_relation_fv, left_relation_ty, with_right);
        let proof = d.lam_fv(congruence_fv, congruence_ty, with_left);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_mod_eq_iff_div_mod_remainder_eq(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // mod_eq_iff_div_mod_remainder_eq :
    //   divMod d a qa ra → divMod d b qb rb → (modEq d a b ↔ ra = rb)
    d.theorem(p.mod_eq_iff_div_mod_remainder_eq, 7, &|d, values| {
        let (modulus, left, right, left_quotient, left_remainder, right_quotient, right_remainder) = (
            values[0], values[1], values[2], values[3], values[4], values[5], values[6],
        );
        let left_relation_ty =
            d.div_mod(modulus, left, left_quotient, left_remainder);
        let right_relation_ty =
            d.div_mod(modulus, right, right_quotient, right_remainder);
        let congruence_ty = d.mod_eq(modulus, left, right);
        let remainder_eq_ty = d.eq(left_remainder, right_remainder);
        let target = d.const_app(p.logic.iff, &[congruence_ty, remainder_eq_ty]);
        let left_relation_fv = d.fresh_fvar();
        let left_relation = d.kernel().fvar(left_relation_fv);
        let right_relation_fv = d.fresh_fvar();
        let right_relation = d.kernel().fvar(right_relation_fv);

        let forward = {
            let congruence_fv = d.fresh_fvar();
            let congruence = d.kernel().fvar(congruence_fv);
            let body = d.lemma(
                p.div_mod_remainder_eq_of_mod_eq,
                &[
                    modulus,
                    left,
                    right,
                    left_quotient,
                    left_remainder,
                    right_quotient,
                    right_remainder,
                    congruence,
                    left_relation,
                    right_relation,
                ],
            );
            d.lam_fv(congruence_fv, congruence_ty, body)
        };
        let reverse = {
            let remainder_eq_fv = d.fresh_fvar();
            let remainder_eq = d.kernel().fvar(remainder_eq_fv);
            let left_remainder_motive = d.eq_motive(left_remainder, &|d, remainder| {
                d.div_mod(modulus, left, left_quotient, remainder)
            });
            let left_relation_at_right_remainder = d.transport(
                left_remainder,
                left_remainder_motive,
                left_relation,
                right_remainder,
                remainder_eq,
            );
            let body = d.lemma(
                p.div_mod_same_remainder_mod_eq,
                &[
                    modulus,
                    left,
                    right,
                    left_quotient,
                    right_quotient,
                    right_remainder,
                    left_relation_at_right_remainder,
                    right_relation,
                ],
            );
            d.lam_fv(remainder_eq_fv, remainder_eq_ty, body)
        };
        let body = d.const_app(
            p.logic.iff_intro,
            &[congruence_ty, remainder_eq_ty, forward, reverse],
        );
        let right_to_target = d.arrow(right_relation_ty, target);
        let stmt = d.arrow(left_relation_ty, right_to_target);
        let with_right = d.lam_fv(right_relation_fv, right_relation_ty, body);
        let proof = d.lam_fv(left_relation_fv, left_relation_ty, with_right);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_mod_eq_zero_of_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;

    // mod_eq_zero_of_dvd : dvd d n → modEq d n zero
    // A divisibility witness q becomes balanced congruence witnesses 0 and q.
    d.theorem(p.mod_eq_zero_of_dvd, 2, &|d, values| {
        let (modulus, value) = (values[0], values[1]);
        let zero = d.zero();
        let source = d.dvd(modulus, value);
        let target = d.mod_eq(modulus, value, zero);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let predicate = d.dvd_predicate(modulus, value);
        let motive = d.kernel().lam(anon, source, target, BinderInfo::Default);
        let minor = {
            let quotient_fv = d.fresh_fvar();
            let quotient = d.kernel().fvar(quotient_fv);
            let product = d.mul(modulus, quotient);
            let equation_ty = d.eq(value, product);
            let equation_fv = d.fresh_fvar();
            let equation = d.kernel().fvar(equation_fv);

            let zero_product = d.mul(modulus, zero);
            let start = d.add(value, zero_product);
            let value_plus_zero = d.add(value, zero);
            let zero_plus_product = d.add(zero, product);
            let remove_zero_product = d.lemma(p.mul_zero, &[modulus]);
            let step1 = d.congr(zero_product, zero, remove_zero_product, &|d, x| {
                d.add(value, x)
            });
            let step2 = d.lemma(p.add_zero, &[value]);
            let step3 = equation;
            let zero_add_product = d.lemma(p.zero_add, &[product]);
            let step4 = d.symm(zero_plus_product, product, zero_add_product);
            let (_, balanced_equation) = d.chain(
                start,
                &[
                    (value_plus_zero, step1),
                    (value, step2),
                    (product, step3),
                    (zero_plus_product, step4),
                ],
            );

            let target_outer = d.mod_eq_outer_predicate(modulus, value, zero);
            let target_inner = d.mod_eq_inner_predicate(modulus, value, zero, zero);
            let exists_intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            let inner = d.apply(
                exists_intro,
                &[nat, target_inner, quotient, balanced_equation],
            );
            let body = d.apply(exists_intro, &[nat, target_outer, zero, inner]);
            let with_equation = d.lam_fv(equation_fv, equation_ty, body);
            d.lam_fv(quotient_fv, nat, with_equation)
        };
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(exists_rec, &[nat, predicate, motive, minor, source_proof]);
        let stmt = d.arrow(source, target);
        let proof = d.lam_fv(source_fv, source, body);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_dvd_of_mod_eq_zero_of_pos(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;

    // dvd_of_mod_eq_zero_of_pos : Le one d → modEq d n zero → dvd d n
    // A balanced witness says n+d*u=d*v. Both the sum and d*u are divisible
    // by d, so positive-divisor cancellation yields d ∣ n.
    d.theorem(p.dvd_of_mod_eq_zero_of_pos, 2, &|d, values| {
        let (modulus, value) = (values[0], values[1]);
        let zero = d.zero();
        let one_value = d.num(1);
        let positive_ty = d.le(one_value, modulus);
        let congruence_ty = d.mod_eq(modulus, value, zero);
        let target = d.dvd(modulus, value);
        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let congruence_fv = d.fresh_fvar();
        let congruence = d.kernel().fvar(congruence_fv);

        let outer_predicate = d.mod_eq_outer_predicate(modulus, value, zero);
        let outer_motive = d
            .kernel()
            .lam(anon, congruence_ty, target, BinderInfo::Default);
        let outer_minor = {
            let left_witness_fv = d.fresh_fvar();
            let left_witness = d.kernel().fvar(left_witness_fv);
            let inner_exists = d.mod_eq_inner_exists(modulus, value, zero, left_witness);
            let inner_exists_fv = d.fresh_fvar();
            let inner_exists_proof = d.kernel().fvar(inner_exists_fv);
            let inner_predicate = d.mod_eq_inner_predicate(modulus, value, zero, left_witness);
            let inner_motive = d
                .kernel()
                .lam(anon, inner_exists, target, BinderInfo::Default);
            let inner_minor = {
                let right_witness_fv = d.fresh_fvar();
                let right_witness = d.kernel().fvar(right_witness_fv);
                let left_multiple = d.mul(modulus, left_witness);
                let right_multiple = d.mul(modulus, right_witness);
                let value_plus_multiple = d.add(value, left_multiple);
                let zero_plus_right_multiple = d.add(zero, right_multiple);
                let equation_ty = d.eq(value_plus_multiple, zero_plus_right_multiple);
                let equation_fv = d.fresh_fvar();
                let equation = d.kernel().fvar(equation_fv);

                let remove_zero = d.lemma(p.zero_add, &[right_multiple]);
                let (_, sum_equation) = d.chain(
                    value_plus_multiple,
                    &[
                        (zero_plus_right_multiple, equation),
                        (right_multiple, remove_zero),
                    ],
                );
                let sum_predicate = d.dvd_predicate(modulus, value_plus_multiple);
                let exists_intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let divides_sum = d.apply(
                    exists_intro,
                    &[nat, sum_predicate, right_witness, sum_equation],
                );
                let divides_multiple = d.lemma(p.dvd_mul, &[modulus, left_witness]);
                let multiple_plus_value = d.add(left_multiple, value);
                let commute = d.lemma(p.add_comm, &[value, left_multiple]);
                let sum_motive = d.eq_motive(value_plus_multiple, &|d, sum| d.dvd(modulus, sum));
                let divides_commuted_sum = d.transport(
                    value_plus_multiple,
                    sum_motive,
                    divides_sum,
                    multiple_plus_value,
                    commute,
                );
                let body = d.lemma(
                    p.dvd_add_right_cancel_of_pos,
                    &[
                        modulus,
                        left_multiple,
                        value,
                        positive,
                        divides_multiple,
                        divides_commuted_sum,
                    ],
                );
                let with_equation = d.lam_fv(equation_fv, equation_ty, body);
                d.lam_fv(right_witness_fv, nat, with_equation)
            };
            let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(
                exists_rec,
                &[
                    nat,
                    inner_predicate,
                    inner_motive,
                    inner_minor,
                    inner_exists_proof,
                ],
            );
            let with_inner = d.lam_fv(inner_exists_fv, inner_exists, body);
            d.lam_fv(left_witness_fv, nat, with_inner)
        };
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            exists_rec,
            &[nat, outer_predicate, outer_motive, outer_minor, congruence],
        );
        let congruence_to_target = d.arrow(congruence_ty, target);
        let stmt = d.arrow(positive_ty, congruence_to_target);
        let with_congruence = d.lam_fv(congruence_fv, congruence_ty, body);
        let proof = d.lam_fv(positive_fv, positive_ty, with_congruence);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_mod_eq_zero_iff_dvd(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;

    // mod_eq_zero_iff_dvd : modEq d n zero ↔ dvd d n
    // Induction on d keeps the degenerate zero modulus explicit. At zero the
    // balanced equation itself supplies a zero-factor witness; at a successor
    // the positive cancellation theorem applies.
    d.theorem(p.mod_eq_zero_iff_dvd, 2, &|d, values| {
        let (modulus, value) = (values[0], values[1]);
        let zero = d.zero();
        let congruence_ty = d.mod_eq(modulus, value, zero);
        let divides_ty = d.dvd(modulus, value);

        let forward_motive = |d: &mut NatDev<'_>, candidate: ExprId| {
            let congruence = d.mod_eq(candidate, value, zero);
            let divides = d.dvd(candidate, value);
            d.arrow(congruence, divides)
        };
        let forward = d.induct(
            &forward_motive,
            &|d| {
                let congruence_ty = d.mod_eq(zero, value, zero);
                let target = d.dvd(zero, value);
                let congruence_fv = d.fresh_fvar();
                let congruence = d.kernel().fvar(congruence_fv);
                let outer_predicate = d.mod_eq_outer_predicate(zero, value, zero);
                let outer_motive = d
                    .kernel()
                    .lam(anon, congruence_ty, target, BinderInfo::Default);
                let outer_minor = {
                    let left_witness_fv = d.fresh_fvar();
                    let left_witness = d.kernel().fvar(left_witness_fv);
                    let inner_exists = d.mod_eq_inner_exists(zero, value, zero, left_witness);
                    let inner_exists_fv = d.fresh_fvar();
                    let inner_exists_proof = d.kernel().fvar(inner_exists_fv);
                    let inner_predicate = d.mod_eq_inner_predicate(zero, value, zero, left_witness);
                    let inner_motive =
                        d.kernel()
                            .lam(anon, inner_exists, target, BinderInfo::Default);
                    let inner_minor = {
                        let right_witness_fv = d.fresh_fvar();
                        let right_witness = d.kernel().fvar(right_witness_fv);
                        let left_multiple = d.mul(zero, left_witness);
                        let right_multiple = d.mul(zero, right_witness);
                        let left_sum = d.add(value, left_multiple);
                        let right_sum = d.add(zero, right_multiple);
                        let equation_ty = d.eq(left_sum, right_sum);
                        let equation_fv = d.fresh_fvar();
                        let equation = d.kernel().fvar(equation_fv);

                        let value_plus_zero = d.add(value, zero);
                        let add_zero = d.lemma(p.add_zero, &[value]);
                        let add_zero_rev = d.symm(value_plus_zero, value, add_zero);
                        let zero_mul_left = d.lemma(p.zero_mul, &[left_witness]);
                        let zero_to_left_multiple = d.symm(left_multiple, zero, zero_mul_left);
                        let expose_left_multiple =
                            d.congr(zero, left_multiple, zero_to_left_multiple, &|d, x| {
                                d.add(value, x)
                            });
                        let remove_right_zero = d.lemma(p.zero_add, &[right_multiple]);
                        let (_, witness_equation) = d.chain(
                            value,
                            &[
                                (value_plus_zero, add_zero_rev),
                                (left_sum, expose_left_multiple),
                                (right_sum, equation),
                                (right_multiple, remove_right_zero),
                            ],
                        );
                        let predicate = d.dvd_predicate(zero, value);
                        let exists_intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                        let body = d.apply(
                            exists_intro,
                            &[nat, predicate, right_witness, witness_equation],
                        );
                        let with_equation = d.lam_fv(equation_fv, equation_ty, body);
                        d.lam_fv(right_witness_fv, nat, with_equation)
                    };
                    let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
                    let body = d.apply(
                        exists_rec,
                        &[
                            nat,
                            inner_predicate,
                            inner_motive,
                            inner_minor,
                            inner_exists_proof,
                        ],
                    );
                    let with_inner = d.lam_fv(inner_exists_fv, inner_exists, body);
                    d.lam_fv(left_witness_fv, nat, with_inner)
                };
                let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
                let body = d.apply(
                    exists_rec,
                    &[nat, outer_predicate, outer_motive, outer_minor, congruence],
                );
                d.lam_fv(congruence_fv, congruence_ty, body)
            },
            &|d, predecessor, _ih| {
                let successor = d.succ(predecessor);
                let congruence_ty = d.mod_eq(successor, value, zero);
                let congruence_fv = d.fresh_fvar();
                let congruence = d.kernel().fvar(congruence_fv);
                let zero_le_predecessor = d.lemma(p.zero_le, &[predecessor]);
                let positive = d.lemma(p.le_succ_succ, &[zero, predecessor, zero_le_predecessor]);
                let body = d.lemma(
                    p.dvd_of_mod_eq_zero_of_pos,
                    &[successor, value, positive, congruence],
                );
                d.lam_fv(congruence_fv, congruence_ty, body)
            },
            modulus,
        );
        let reverse = {
            let divides_fv = d.fresh_fvar();
            let divides = d.kernel().fvar(divides_fv);
            let body = d.lemma(p.mod_eq_zero_of_dvd, &[modulus, value, divides]);
            d.lam_fv(divides_fv, divides_ty, body)
        };
        let target = d.const_app(p.logic.iff, &[congruence_ty, divides_ty]);
        let proof = d.const_app(
            p.logic.iff_intro,
            &[congruence_ty, divides_ty, forward, reverse],
        );
        (target, proof)
    })?;
    Ok(())
}

fn declare_mod_eq_trans(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mod_eq_trans, 4, &|d, v| {
        let (modulus, left, middle, right) = (v[0], v[1], v[2], v[3]);
        let first_ty = d.mod_eq(modulus, left, middle);
        let second_ty = d.mod_eq(modulus, middle, right);
        let target = d.mod_eq(modulus, left, right);
        let first_fv = d.fresh_fvar();
        let first = d.kernel().fvar(first_fv);
        let second_fv = d.fresh_fvar();
        let second = d.kernel().fvar(second_fv);
        let first_outer = d.mod_eq_outer_predicate(modulus, left, middle);
        let first_motive = d.kernel().lam(anon, first_ty, target, BinderInfo::Default);
        let first_minor = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let first_inner_ty = d.mod_eq_inner_exists(modulus, left, middle, u);
            let first_inner_fv = d.fresh_fvar();
            let first_inner = d.kernel().fvar(first_inner_fv);
            let first_inner_pred = d.mod_eq_inner_predicate(modulus, left, middle, u);
            let first_inner_motive =
                d.kernel()
                    .lam(anon, first_inner_ty, target, BinderInfo::Default);
            let first_inner_minor = {
                let v_fv = d.fresh_fvar();
                let vw = d.kernel().fvar(v_fv);
                let first_lhs = d.mod_eq_sum(modulus, left, u);
                let first_rhs = d.mod_eq_sum(modulus, middle, vw);
                let first_eq_ty = d.eq(first_lhs, first_rhs);
                let first_eq_fv = d.fresh_fvar();
                let first_eq = d.kernel().fvar(first_eq_fv);
                let second_outer = d.mod_eq_outer_predicate(modulus, middle, right);
                let second_motive = d.kernel().lam(anon, second_ty, target, BinderInfo::Default);
                let second_minor = build_mod_eq_trans_second_minor(
                    d, &p, nat, anon, one, modulus, left, middle, right, u, vw, first_eq,
                );
                let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
                let body = d.apply(
                    rec,
                    &[nat, second_outer, second_motive, second_minor, second],
                );
                let with_eq = d.lam_fv(first_eq_fv, first_eq_ty, body);
                d.lam_fv(v_fv, nat, with_eq)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(
                rec,
                &[
                    nat,
                    first_inner_pred,
                    first_inner_motive,
                    first_inner_minor,
                    first_inner,
                ],
            );
            let with_inner = d.lam_fv(first_inner_fv, first_inner_ty, body);
            d.lam_fv(u_fv, nat, with_inner)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(rec, &[nat, first_outer, first_motive, first_minor, first]);
        let second_to_target = d.arrow(second_ty, target);
        let stmt = d.arrow(first_ty, second_to_target);
        let with_second = d.lam_fv(second_fv, second_ty, body);
        let proof = d.lam_fv(first_fv, first_ty, with_second);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_mod_eq_add_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mod_eq_add_left, 4, &|d, values| {
        let (modulus, left, right, shift) = (values[0], values[1], values[2], values[3]);
        let source = d.mod_eq(modulus, left, right);
        let shifted_left = d.add(shift, left);
        let shifted_right = d.add(shift, right);
        let target = d.mod_eq(modulus, shifted_left, shifted_right);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let outer_predicate = d.mod_eq_outer_predicate(modulus, left, right);
        let outer_motive = d.kernel().lam(anon, source, target, BinderInfo::Default);
        let outer_minor = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_source = d.mod_eq_inner_exists(modulus, left, right, u);
            let inner_source_fv = d.fresh_fvar();
            let inner_source_proof = d.kernel().fvar(inner_source_fv);
            let inner_predicate = d.mod_eq_inner_predicate(modulus, left, right, u);
            let inner_motive = d
                .kernel()
                .lam(anon, inner_source, target, BinderInfo::Default);
            let inner_minor = {
                let v_fv = d.fresh_fvar();
                let v = d.kernel().fvar(v_fv);
                let du = d.mul(modulus, u);
                let dv = d.mul(modulus, v);
                let left_sum = d.add(left, du);
                let right_sum = d.add(right, dv);
                let equation_ty = d.eq(left_sum, right_sum);
                let equation_fv = d.fresh_fvar();
                let equation = d.kernel().fvar(equation_fv);
                let target_left = d.mod_eq_sum(modulus, shifted_left, u);
                let target_right = d.mod_eq_sum(modulus, shifted_right, v);
                let nested_left = d.add(shift, left_sum);
                let nested_right = d.add(shift, right_sum);
                let assoc_left = d.lemma(p.add_assoc, &[shift, left, du]);
                let step1 = assoc_left;
                let step2 = d.congr(left_sum, right_sum, equation, &|d, z| d.add(shift, z));
                let assoc_right = d.lemma(p.add_assoc, &[shift, right, dv]);
                let step3 = d.symm(target_right, nested_right, assoc_right);
                let (_, shifted_equation) = d.chain(
                    target_left,
                    &[
                        (nested_left, step1),
                        (nested_right, step2),
                        (target_right, step3),
                    ],
                );
                let target_outer = d.mod_eq_outer_predicate(modulus, shifted_left, shifted_right);
                let target_inner =
                    d.mod_eq_inner_predicate(modulus, shifted_left, shifted_right, u);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let inner_proof = d.apply(intro, &[nat, target_inner, v, shifted_equation]);
                let body = d.apply(intro, &[nat, target_outer, u, inner_proof]);
                let with_equation = d.lam_fv(equation_fv, equation_ty, body);
                d.lam_fv(v_fv, nat, with_equation)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(
                rec,
                &[
                    nat,
                    inner_predicate,
                    inner_motive,
                    inner_minor,
                    inner_source_proof,
                ],
            );
            let with_inner = d.lam_fv(inner_source_fv, inner_source, body);
            d.lam_fv(u_fv, nat, with_inner)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            rec,
            &[
                nat,
                outer_predicate,
                outer_motive,
                outer_minor,
                source_proof,
            ],
        );
        let stmt = d.arrow(source, target);
        let proof = d.lam_fv(source_fv, source, body);
        (stmt, proof)
    })?;
    Ok(())
}

fn declare_mod_eq_additive_compatibility(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // mod_eq_add_right : modEq d a b → modEq d (a+c) (b+c)
    // Reuse left-addition compatibility, then transport both endpoints across
    // proved commutativity rather than reopening the existential witnesses.
    d.theorem(p.mod_eq_add_right, 4, &|d, values| {
        let (modulus, left, right, shift) = (values[0], values[1], values[2], values[3]);
        let source = d.mod_eq(modulus, left, right);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let shift_left = d.add(shift, left);
        let left_shift = d.add(left, shift);
        let shift_right = d.add(shift, right);
        let right_shift = d.add(right, shift);
        let shifted = d.lemma(
            p.mod_eq_add_left,
            &[modulus, left, right, shift, source_proof],
        );
        let commute_left = d.lemma(p.add_comm, &[shift, left]);
        let left_motive = d.eq_motive(shift_left, &|d, value| {
            d.mod_eq(modulus, value, shift_right)
        });
        let left_transport =
            d.transport(shift_left, left_motive, shifted, left_shift, commute_left);
        let commute_right = d.lemma(p.add_comm, &[shift, right]);
        let right_motive = d.eq_motive(shift_right, &|d, value| {
            d.mod_eq(modulus, left_shift, value)
        });
        let body = d.transport(
            shift_right,
            right_motive,
            left_transport,
            right_shift,
            commute_right,
        );
        let target = d.mod_eq(modulus, left_shift, right_shift);
        let stmt = d.arrow(source, target);
        let proof = d.lam_fv(source_fv, source, body);
        (stmt, proof)
    })?;

    // mod_eq_add : modEq d a b → modEq d c e → modEq d (a+c) (b+e)
    d.theorem(p.mod_eq_add, 5, &|d, values| {
        let (modulus, a, b, c, e) = (values[0], values[1], values[2], values[3], values[4]);
        let first_ty = d.mod_eq(modulus, a, b);
        let second_ty = d.mod_eq(modulus, c, e);
        let first_fv = d.fresh_fvar();
        let first = d.kernel().fvar(first_fv);
        let second_fv = d.fresh_fvar();
        let second = d.kernel().fvar(second_fv);
        let ac = d.add(a, c);
        let bc = d.add(b, c);
        let be = d.add(b, e);
        let first_shifted = d.lemma(p.mod_eq_add_right, &[modulus, a, b, c, first]);
        let second_shifted = d.lemma(p.mod_eq_add_left, &[modulus, c, e, b, second]);
        let body = d.lemma(
            p.mod_eq_trans,
            &[modulus, ac, bc, be, first_shifted, second_shifted],
        );
        let target = d.mod_eq(modulus, ac, be);
        let second_to_target = d.arrow(second_ty, target);
        let stmt = d.arrow(first_ty, second_to_target);
        let with_second = d.lam_fv(second_fv, second_ty, body);
        let proof = d.lam_fv(first_fv, first_ty, with_second);
        (stmt, proof)
    })?;

    Ok(())
}

fn declare_mod_eq_mul_left(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.mod_eq_mul_left, 4, &|d, values| {
        let (modulus, left, right, factor) = (values[0], values[1], values[2], values[3]);
        let source = d.mod_eq(modulus, left, right);
        let scaled_left = d.mul(factor, left);
        let scaled_right = d.mul(factor, right);
        let target = d.mod_eq(modulus, scaled_left, scaled_right);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let outer_predicate = d.mod_eq_outer_predicate(modulus, left, right);
        let outer_motive = d.kernel().lam(anon, source, target, BinderInfo::Default);
        let outer_minor = {
            let u_fv = d.fresh_fvar();
            let u = d.kernel().fvar(u_fv);
            let inner_source = d.mod_eq_inner_exists(modulus, left, right, u);
            let inner_source_fv = d.fresh_fvar();
            let inner_source_proof = d.kernel().fvar(inner_source_fv);
            let inner_predicate = d.mod_eq_inner_predicate(modulus, left, right, u);
            let inner_motive = d
                .kernel()
                .lam(anon, inner_source, target, BinderInfo::Default);
            let inner_minor = {
                let v_fv = d.fresh_fvar();
                let v = d.kernel().fvar(v_fv);
                let du = d.mul(modulus, u);
                let dv = d.mul(modulus, v);
                let left_sum = d.add(left, du);
                let right_sum = d.add(right, dv);
                let equation_ty = d.eq(left_sum, right_sum);
                let equation_fv = d.fresh_fvar();
                let equation = d.kernel().fvar(equation_fv);
                let factor_u = d.mul(factor, u);
                let factor_v = d.mul(factor, v);
                let target_left = d.mod_eq_sum(modulus, scaled_left, factor_u);
                let target_right = d.mod_eq_sum(modulus, scaled_right, factor_v);
                let factor_du = d.mul(factor, du);
                let factor_dv = d.mul(factor, dv);
                let distributed_left = d.add(scaled_left, factor_du);
                let distributed_right = d.add(scaled_right, factor_dv);
                let factored_left = d.mul(factor, left_sum);
                let factored_right = d.mul(factor, right_sum);

                let scaled_u = mod_eq_scaled_multiple(d, &p, modulus, factor, u);
                let modulus_factor_u = d.mul(modulus, factor_u);
                let step1 = d.congr(modulus_factor_u, factor_du, scaled_u, &|d, value| {
                    d.add(scaled_left, value)
                });
                let left_distrib = d.lemma(p.left_distrib, &[factor, left, du]);
                let step2 = d.symm(factored_left, distributed_left, left_distrib);
                let step3 = d.congr(left_sum, right_sum, equation, &|d, value| {
                    d.mul(factor, value)
                });
                let step4 = d.lemma(p.left_distrib, &[factor, right, dv]);
                let scaled_v = mod_eq_scaled_multiple(d, &p, modulus, factor, v);
                let modulus_factor_v = d.mul(modulus, factor_v);
                let reverse_scaled_v = d.symm(modulus_factor_v, factor_dv, scaled_v);
                let step5 = d.congr(
                    factor_dv,
                    modulus_factor_v,
                    reverse_scaled_v,
                    &|d, value| d.add(scaled_right, value),
                );
                let (_, scaled_equation) = d.chain(
                    target_left,
                    &[
                        (distributed_left, step1),
                        (factored_left, step2),
                        (factored_right, step3),
                        (distributed_right, step4),
                        (target_right, step5),
                    ],
                );
                let target_outer = d.mod_eq_outer_predicate(modulus, scaled_left, scaled_right);
                let target_inner =
                    d.mod_eq_inner_predicate(modulus, scaled_left, scaled_right, factor_u);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let inner_proof = d.apply(intro, &[nat, target_inner, factor_v, scaled_equation]);
                let body = d.apply(intro, &[nat, target_outer, factor_u, inner_proof]);
                let with_equation = d.lam_fv(equation_fv, equation_ty, body);
                d.lam_fv(v_fv, nat, with_equation)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(
                rec,
                &[
                    nat,
                    inner_predicate,
                    inner_motive,
                    inner_minor,
                    inner_source_proof,
                ],
            );
            let with_inner = d.lam_fv(inner_source_fv, inner_source, body);
            d.lam_fv(u_fv, nat, with_inner)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            rec,
            &[
                nat,
                outer_predicate,
                outer_motive,
                outer_minor,
                source_proof,
            ],
        );
        let stmt = d.arrow(source, target);
        let proof = d.lam_fv(source_fv, source, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// `d * (c*u) = c * (d*u)`, from associativity and commutativity.
fn mod_eq_scaled_multiple(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    modulus: ExprId,
    factor: ExprId,
    witness: ExprId,
) -> ExprId {
    let p = *p;
    let factor_witness = d.mul(factor, witness);
    let start = d.mul(modulus, factor_witness);
    let modulus_factor = d.mul(modulus, factor);
    let modulus_factor_witness = d.mul(modulus_factor, witness);
    let factor_modulus = d.mul(factor, modulus);
    let factor_modulus_witness = d.mul(factor_modulus, witness);
    let modulus_witness = d.mul(modulus, witness);
    let target = d.mul(factor, modulus_witness);
    let assoc_left = d.lemma(p.mul_assoc, &[modulus, factor, witness]);
    let step1 = d.symm(modulus_factor_witness, start, assoc_left);
    let commute = d.lemma(p.mul_comm, &[modulus, factor]);
    let step2 = d.congr(modulus_factor, factor_modulus, commute, &|d, value| {
        d.mul(value, witness)
    });
    let step3 = d.lemma(p.mul_assoc, &[factor, modulus, witness]);
    let (_, proof) = d.chain(
        start,
        &[
            (modulus_factor_witness, step1),
            (factor_modulus_witness, step2),
            (target, step3),
        ],
    );
    proof
}

fn declare_mod_eq_multiplicative_compatibility(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;

    // mod_eq_mul_right : modEq d a b → modEq d (a*c) (b*c)
    d.theorem(p.mod_eq_mul_right, 4, &|d, values| {
        let (modulus, left, right, factor) = (values[0], values[1], values[2], values[3]);
        let source = d.mod_eq(modulus, left, right);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let factor_left = d.mul(factor, left);
        let left_factor = d.mul(left, factor);
        let factor_right = d.mul(factor, right);
        let right_factor = d.mul(right, factor);
        let scaled = d.lemma(
            p.mod_eq_mul_left,
            &[modulus, left, right, factor, source_proof],
        );
        let commute_left = d.lemma(p.mul_comm, &[factor, left]);
        let left_motive = d.eq_motive(factor_left, &|d, value| {
            d.mod_eq(modulus, value, factor_right)
        });
        let left_transport =
            d.transport(factor_left, left_motive, scaled, left_factor, commute_left);
        let commute_right = d.lemma(p.mul_comm, &[factor, right]);
        let right_motive = d.eq_motive(factor_right, &|d, value| {
            d.mod_eq(modulus, left_factor, value)
        });
        let body = d.transport(
            factor_right,
            right_motive,
            left_transport,
            right_factor,
            commute_right,
        );
        let target = d.mod_eq(modulus, left_factor, right_factor);
        let stmt = d.arrow(source, target);
        let proof = d.lam_fv(source_fv, source, body);
        (stmt, proof)
    })?;

    // mod_eq_mul : modEq d a b → modEq d c e → modEq d (a*c) (b*e)
    d.theorem(p.mod_eq_mul, 5, &|d, values| {
        let (modulus, a, b, c, e) = (values[0], values[1], values[2], values[3], values[4]);
        let first_ty = d.mod_eq(modulus, a, b);
        let second_ty = d.mod_eq(modulus, c, e);
        let first_fv = d.fresh_fvar();
        let first = d.kernel().fvar(first_fv);
        let second_fv = d.fresh_fvar();
        let second = d.kernel().fvar(second_fv);
        let ac = d.mul(a, c);
        let bc = d.mul(b, c);
        let be = d.mul(b, e);
        let first_scaled = d.lemma(p.mod_eq_mul_right, &[modulus, a, b, c, first]);
        let second_scaled = d.lemma(p.mod_eq_mul_left, &[modulus, c, e, b, second]);
        let body = d.lemma(
            p.mod_eq_trans,
            &[modulus, ac, bc, be, first_scaled, second_scaled],
        );
        let target = d.mod_eq(modulus, ac, be);
        let second_to_target = d.arrow(second_ty, target);
        let stmt = d.arrow(first_ty, second_to_target);
        let with_second = d.lam_fv(second_fv, second_ty, body);
        let proof = d.lam_fv(first_fv, first_ty, with_second);
        (stmt, proof)
    })?;

    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn build_mod_eq_trans_second_minor(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    anon: NameId,
    one: LevelId,
    modulus: ExprId,
    left: ExprId,
    middle: ExprId,
    right: ExprId,
    u: ExprId,
    v: ExprId,
    first_eq: ExprId,
) -> ExprId {
    let p = *p;
    let target = d.mod_eq(modulus, left, right);
    let x_fv = d.fresh_fvar();
    let x = d.kernel().fvar(x_fv);
    let inner_ty = d.mod_eq_inner_exists(modulus, middle, right, x);
    let inner_fv = d.fresh_fvar();
    let inner = d.kernel().fvar(inner_fv);
    let inner_predicate = d.mod_eq_inner_predicate(modulus, middle, right, x);
    let inner_motive = d.kernel().lam(anon, inner_ty, target, BinderInfo::Default);
    let inner_minor = {
        let y_fv = d.fresh_fvar();
        let y = d.kernel().fvar(y_fv);
        let middle_x = d.mod_eq_sum(modulus, middle, x);
        let right_y = d.mod_eq_sum(modulus, right, y);
        let second_eq_ty = d.eq(middle_x, right_y);
        let second_eq_fv = d.fresh_fvar();
        let second_eq = d.kernel().fvar(second_eq_fv);

        let ux = d.add(u, x);
        let yv = d.add(y, v);
        let target_left = d.mod_eq_sum(modulus, left, ux);
        let target_right = d.mod_eq_sum(modulus, right, yv);
        let du = d.mul(modulus, u);
        let dx = d.mul(modulus, x);
        let dv = d.mul(modulus, v);
        let dy = d.mul(modulus, y);
        let left_du = d.add(left, du);
        let middle_dv = d.add(middle, dv);
        let middle_dx = d.add(middle, dx);
        let right_dy = d.add(right, dy);
        let du_dx = d.add(du, dx);
        let dx_dv = d.add(dx, dv);
        let dv_dx = d.add(dv, dx);
        let dy_dv = d.add(dy, dv);
        let modulus_ux = d.mul(modulus, ux);
        let modulus_yv = d.mul(modulus, yv);
        let left_nested = d.add(left, du_dx);
        let left_grouped = d.add(left_du, dx);
        let middle_grouped_vx = d.add(middle_dv, dx);
        let middle_nested_vx = d.add(middle, dv_dx);
        let middle_nested_xv = d.add(middle, dx_dv);
        let middle_grouped_xv = d.add(middle_dx, dv);
        let right_grouped = d.add(right_dy, dv);
        let right_nested = d.add(right, dy_dv);

        let distributed_left = d.lemma(p.left_distrib, &[modulus, u, x]);
        let step1 = d.congr(modulus_ux, du_dx, distributed_left, &|d, z| d.add(left, z));
        let associated_left = d.lemma(p.add_assoc, &[left, du, dx]);
        let step2 = d.symm(left_grouped, left_nested, associated_left);
        let step3 = d.congr(left_du, middle_dv, first_eq, &|d, z| d.add(z, dx));
        let step4 = d.lemma(p.add_assoc, &[middle, dv, dx]);
        let commuted = d.lemma(p.add_comm, &[dv, dx]);
        let step5 = d.congr(dv_dx, dx_dv, commuted, &|d, z| d.add(middle, z));
        let associated_middle = d.lemma(p.add_assoc, &[middle, dx, dv]);
        let step6 = d.symm(middle_grouped_xv, middle_nested_xv, associated_middle);
        let step7 = d.congr(middle_dx, right_dy, second_eq, &|d, z| d.add(z, dv));
        let step8 = d.lemma(p.add_assoc, &[right, dy, dv]);
        let distributed_right = d.lemma(p.left_distrib, &[modulus, y, v]);
        let undistributed_right = d.symm(modulus_yv, dy_dv, distributed_right);
        let step9 = d.congr(dy_dv, modulus_yv, undistributed_right, &|d, z| {
            d.add(right, z)
        });
        let (_, equation) = d.chain(
            target_left,
            &[
                (left_nested, step1),
                (left_grouped, step2),
                (middle_grouped_vx, step3),
                (middle_nested_vx, step4),
                (middle_nested_xv, step5),
                (middle_grouped_xv, step6),
                (right_grouped, step7),
                (right_nested, step8),
                (target_right, step9),
            ],
        );
        let target_outer = d.mod_eq_outer_predicate(modulus, left, right);
        let target_inner = d.mod_eq_inner_predicate(modulus, left, right, ux);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let inner_proof = d.apply(intro, &[nat, target_inner, yv, equation]);
        let body = d.apply(intro, &[nat, target_outer, ux, inner_proof]);
        let with_eq = d.lam_fv(second_eq_fv, second_eq_ty, body);
        d.lam_fv(y_fv, nat, with_eq)
    };
    let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
    let body = d.apply(
        rec,
        &[nat, inner_predicate, inner_motive, inner_minor, inner],
    );
    let with_inner = d.lam_fv(inner_fv, inner_ty, body);
    d.lam_fv(x_fv, nat, with_inner)
}

/// Structural subtraction laws needed before subtraction can interact with
/// order. Both are kernel-checked consequences of the recursive definitions.
fn declare_subtraction_theorems(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    // succ_sub_succ : ∀ n m, sub (succ n) (succ m) = sub n m
    d.theorem(p.succ_sub_succ, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let sn = d.succ(n);
            let sx = d.succ(x);
            let lhs = d.sub(sn, sx);
            let rhs = d.sub(n, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| d.refl(n),
            &|d, j, ih| {
                let sn = d.succ(n);
                let sj = d.succ(j);
                let lhs = d.sub(sn, sj);
                let rhs = d.sub(n, j);
                d.congr(lhs, rhs, ih, &|d, x| d.pred(x))
            },
            m,
        );
        (stmt, proof)
    })?;

    // sub_self : ∀ n, sub n n = zero
    d.theorem(p.sub_self, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs = d.sub(x, x);
            let zero = d.zero();
            d.eq(lhs, zero)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                d.refl(zero)
            },
            &|d, j, ih| {
                let sj = d.succ(j);
                let start = d.sub(sj, sj);
                let middle = d.sub(j, j);
                let h1 = d.lemma(p.succ_sub_succ, &[j, j]);
                let zero = d.zero();
                let (_end, proof) = d.chain(start, &[(middle, h1), (zero, ih)]);
                proof
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `zero_add`, `succ_add`, `add_comm`, `add_assoc`, `add_right_comm`.
fn declare_additive_theorems(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    // zero_add : ∀ n, add zero n = n   (induction on n)
    d.theorem(p.zero_add, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let z = d.zero();
            let lhs = d.add(z, x);
            d.eq(lhs, x)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            &|d, j, ih| {
                let z = d.zero();
                let lhs = d.add(z, j);
                d.congr(lhs, j, ih, &|d, x| d.succ(x))
            },
            n,
        );
        (stmt, proof)
    })?;

    // succ_add : ∀ n m, add (succ n) m = succ (add n m)   (induction on m)
    d.theorem(p.succ_add, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let sn = d.succ(n);
            let lhs = d.add(sn, x);
            let inner = d.add(n, x);
            let rhs = d.succ(inner);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let sn = d.succ(n);
                d.refl(sn)
            },
            &|d, j, ih| {
                let sn = d.succ(n);
                let lhs = d.add(sn, j);
                let inner = d.add(n, j);
                let rhs = d.succ(inner);
                d.congr(lhs, rhs, ih, &|d, x| d.succ(x))
            },
            m,
        );
        (stmt, proof)
    })?;

    // add_comm : ∀ n m, add n m = add m n   (induction on m)
    d.theorem(p.add_comm, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs = d.add(n, x);
            let rhs = d.add(x, n);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                let za = d.add(z, n);
                let h = d.lemma(p.zero_add, &[n]);
                d.symm(za, n, h)
            },
            &|d, j, ih| {
                let lhs = d.add(n, j);
                let rhs = d.add(j, n);
                let h1 = d.congr(lhs, rhs, ih, &|d, x| d.succ(x));
                let s_lhs = d.succ(lhs);
                let s_rhs = d.succ(rhs);
                let sj = d.succ(j);
                let sj_n = d.add(sj, n);
                let h_sa = d.lemma(p.succ_add, &[j, n]);
                let h2 = d.symm(sj_n, s_rhs, h_sa);
                d.trans(s_lhs, s_rhs, sj_n, h1, h2)
            },
            m,
        );
        (stmt, proof)
    })?;

    // add_assoc : ∀ a b c, add (add a b) c = add a (add b c)   (induction on c)
    d.theorem(p.add_assoc, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let ab = d.add(a, b);
            let lhs = d.add(ab, x);
            let bx = d.add(b, x);
            let rhs = d.add(a, bx);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, c);
        let proof = d.induct(
            &motive,
            &|d| {
                let ab = d.add(a, b);
                d.refl(ab)
            },
            &|d, j, ih| {
                let ab = d.add(a, b);
                let lhs = d.add(ab, j);
                let bj = d.add(b, j);
                let rhs = d.add(a, bj);
                d.congr(lhs, rhs, ih, &|d, x| d.succ(x))
            },
            c,
        );
        (stmt, proof)
    })?;

    // add_right_comm : ∀ x y z, add (add x y) z = add (add x z) y   (no induction)
    d.theorem(p.add_right_comm, 3, &|d, v| {
        let (x, y, z) = (v[0], v[1], v[2]);
        let xy = d.add(x, y);
        let start = d.add(xy, z);
        let yz = d.add(y, z);
        let s1 = d.add(x, yz);
        let h1 = d.lemma(p.add_assoc, &[x, y, z]);
        let zy = d.add(z, y);
        let s2 = d.add(x, zy);
        let h_comm = d.lemma(p.add_comm, &[y, z]);
        let h2 = d.congr(yz, zy, h_comm, &|d, t| d.add(x, t));
        let xz = d.add(x, z);
        let s3 = d.add(xz, y);
        let h_assoc2 = d.lemma(p.add_assoc, &[x, z, y]);
        let h3 = d.symm(s3, s2, h_assoc2);
        let (end, proof) = d.chain(start, &[(s1, h1), (s2, h2), (s3, h3)]);
        let stmt = d.eq(start, end);
        (stmt, proof)
    })?;

    // succ_injective : ∀ n m, succ n = succ m → n = m
    // Applying the checked predecessor definition to both sides computes to
    // the desired equality; no constructor-disjointness axiom is involved.
    d.theorem(p.succ_injective, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let sn = d.succ(n);
        let sm = d.succ(m);
        let hyp_ty = d.eq(sn, sm);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let body = d.congr(sn, sm, h, &|d, x| d.pred(x));
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        let conclusion = d.eq(n, m);
        let stmt = d.arrow(hyp_ty, conclusion);
        (stmt, proof)
    })?;

    // add_right_cancel : ∀ n m k, n + k = m + k → n = m
    // Induction follows the argument on which `add` recurses.
    d.theorem(p.add_right_cancel, 3, &|d, v| {
        let (n, m, k) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let nx = d.add(n, x);
            let mx = d.add(m, x);
            let hyp = d.eq(nx, mx);
            let conclusion = d.eq(n, m);
            d.arrow(hyp, conclusion)
        };
        let stmt = motive(d, k);
        let proof = d.induct(
            &motive,
            &|d| {
                let hyp_ty = d.eq(n, m);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                d.lam_fv(h_fv, hyp_ty, h)
            },
            &|d, j, ih| {
                let nj = d.add(n, j);
                let mj = d.add(m, j);
                let snj = d.succ(nj);
                let smj = d.succ(mj);
                let hyp_ty = d.eq(snj, smj);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let stripped = d.lemma(p.succ_injective, &[nj, mj, h]);
                let body = d.apply(ih, &[stripped]);
                d.lam_fv(h_fv, hyp_ty, body)
            },
            k,
        );
        (stmt, proof)
    })?;

    // add_left_cancel : ∀ a b c, a + b = a + c → b = c
    // Commute the common operand to the right and reuse the inductive theorem.
    d.theorem(p.add_left_cancel, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let ab = d.add(a, b);
        let ac = d.add(a, c);
        let hyp_ty = d.eq(ab, ac);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ba = d.add(b, a);
        let ca = d.add(c, a);
        let h1 = d.lemma(p.add_comm, &[b, a]);
        let h3 = d.lemma(p.add_comm, &[a, c]);
        let (_end, right_common) = d.chain(ba, &[(ab, h1), (ac, h), (ca, h3)]);
        let body = d.lemma(p.add_right_cancel, &[b, c, a, right_common]);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        let conclusion = d.eq(b, c);
        let stmt = d.arrow(hyp_ty, conclusion);
        (stmt, proof)
    })?;
    Ok(())
}

/// `zero_mul`, `succ_mul`, `mul_comm`, `mul_one`, `one_mul`, `left_distrib`,
/// `mul_assoc`.
fn declare_multiplicative_theorems(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    // zero_mul : ∀ n, mul zero n = zero   (induction on n)
    d.theorem(p.zero_mul, 1, &|d, v| {
        let n = v[0];
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let z = d.zero();
            let lhs = d.mul(z, x);
            d.eq(lhs, z)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            // mul zero (succ j) ≡ add (mul zero j) zero ≡ mul zero j, so the
            // induction hypothesis *is* the step, up to definitional equality.
            &|_d, _j, ih| ih,
            n,
        );
        (stmt, proof)
    })?;

    // succ_mul : ∀ n m, mul (succ n) m = add (mul n m) m   (induction on m)
    d.theorem(p.succ_mul, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let sn = d.succ(n);
            let lhs = d.mul(sn, x);
            let nm = d.mul(n, x);
            let rhs = d.add(nm, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            &|d, j, ih| {
                // goal ≡ succ (add (mul (succ n) j) n) = succ (add (add (mul n j) n) j)
                let sn = d.succ(n);
                let snj = d.mul(sn, j);
                let start = d.add(snj, n);
                let nj = d.mul(n, j);
                let nj_j = d.add(nj, j);
                let s1 = d.add(nj_j, n);
                let h1 = d.congr(snj, nj_j, ih, &|d, t| d.add(t, n));
                let nj_n = d.add(nj, n);
                let s2 = d.add(nj_n, j);
                let h2 = d.lemma(p.add_right_comm, &[nj, j, n]);
                let (end, inner) = d.chain(start, &[(s1, h1), (s2, h2)]);
                d.congr(start, end, inner, &|d, t| d.succ(t))
            },
            m,
        );
        (stmt, proof)
    })?;

    // mul_comm : ∀ n m, mul n m = mul m n   (induction on m)
    d.theorem(p.mul_comm, 2, &|d, v| {
        let (n, m) = (v[0], v[1]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs = d.mul(n, x);
            let rhs = d.mul(x, n);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, m);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                let zn = d.mul(z, n);
                let h = d.lemma(p.zero_mul, &[n]);
                d.symm(zn, z, h)
            },
            &|d, j, ih| {
                // goal ≡ add (mul n j) n = mul (succ j) n
                let nj = d.mul(n, j);
                let start = d.add(nj, n);
                let jn = d.mul(j, n);
                let s1 = d.add(jn, n);
                let h1 = d.congr(nj, jn, ih, &|d, t| d.add(t, n));
                let sj = d.succ(j);
                let s2 = d.mul(sj, n);
                let h_sm = d.lemma(p.succ_mul, &[j, n]);
                let h2 = d.symm(s2, s1, h_sm);
                let (_end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
                proof
            },
            m,
        );
        (stmt, proof)
    })?;

    // mul_one : ∀ a, mul a 1 = a
    // mul a (succ zero) ≡ add (mul a zero) a ≡ add zero a, so `zero_add a`
    // already has this type up to definitional equality.
    d.theorem(p.mul_one, 1, &|d, v| {
        let a = v[0];
        let one = d.num(1);
        let lhs = d.mul(a, one);
        let stmt = d.eq(lhs, a);
        let proof = d.lemma(p.zero_add, &[a]);
        (stmt, proof)
    })?;

    // one_mul : ∀ a, mul 1 a = a
    d.theorem(p.one_mul, 1, &|d, v| {
        let a = v[0];
        let one = d.num(1);
        let z = d.zero();
        let start = d.mul(one, a);
        let za = d.mul(z, a);
        let s1 = d.add(za, a);
        let h1 = d.lemma(p.succ_mul, &[z, a]);
        let s2 = d.add(z, a);
        let h_zm = d.lemma(p.zero_mul, &[a]);
        let h2 = d.congr(za, z, h_zm, &|d, t| d.add(t, a));
        let h3 = d.lemma(p.zero_add, &[a]);
        let (end, proof) = d.chain(start, &[(s1, h1), (s2, h2), (a, h3)]);
        let stmt = d.eq(start, end);
        (stmt, proof)
    })?;

    // left_distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)  (ind. on c)
    d.theorem(p.left_distrib, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let bx = d.add(b, x);
            let lhs = d.mul(a, bx);
            let ab = d.mul(a, b);
            let ax = d.mul(a, x);
            let rhs = d.add(ab, ax);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, c);
        let proof = d.induct(
            &motive,
            &|d| {
                let ab = d.mul(a, b);
                d.refl(ab)
            },
            &|d, j, ih| {
                // goal ≡ add (mul a (add b j)) a = add (mul a b) (add (mul a j) a)
                let bj = d.add(b, j);
                let a_bj = d.mul(a, bj);
                let start = d.add(a_bj, a);
                let ab = d.mul(a, b);
                let aj = d.mul(a, j);
                let ab_aj = d.add(ab, aj);
                let s1 = d.add(ab_aj, a);
                let h1 = d.congr(a_bj, ab_aj, ih, &|d, t| d.add(t, a));
                let aj_a = d.add(aj, a);
                let s2 = d.add(ab, aj_a);
                let h2 = d.lemma(p.add_assoc, &[ab, aj, a]);
                let (_end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
                proof
            },
            c,
        );
        (stmt, proof)
    })?;

    // right_distrib : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
    // Derive the right-handed law from commutativity and left distribution.
    d.theorem(p.right_distrib, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let sum = d.add(a, b);
        let start = d.mul(sum, c);
        let commuted = d.mul(c, sum);
        let ca = d.mul(c, a);
        let cb = d.mul(c, b);
        let distributed = d.add(ca, cb);
        let ac = d.mul(a, c);
        let bc = d.mul(b, c);
        let target = d.add(ac, bc);
        let h1 = d.lemma(p.mul_comm, &[sum, c]);
        let h2 = d.lemma(p.left_distrib, &[c, a, b]);
        let ca_to_ac = d.lemma(p.mul_comm, &[c, a]);
        let h3 = d.congr(ca, ac, ca_to_ac, &|d, value| d.add(value, cb));
        let cb_to_bc = d.lemma(p.mul_comm, &[c, b]);
        let h4 = d.congr(cb, bc, cb_to_bc, &|d, value| d.add(ac, value));
        let partly_commuted = d.add(ac, cb);
        let (_, proof) = d.chain(
            start,
            &[
                (commuted, h1),
                (distributed, h2),
                (partly_commuted, h3),
                (target, h4),
            ],
        );
        (d.eq(start, target), proof)
    })?;

    // mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)   (induction on c)
    d.theorem(p.mul_assoc, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let ab = d.mul(a, b);
            let lhs = d.mul(ab, x);
            let bx = d.mul(b, x);
            let rhs = d.mul(a, bx);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, c);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.refl(z)
            },
            &|d, j, ih| {
                // goal ≡ add (mul (mul a b) j) (mul a b) = mul a (add (mul b j) b)
                let ab = d.mul(a, b);
                let abj = d.mul(ab, j);
                let start = d.add(abj, ab);
                let bj = d.mul(b, j);
                let a_bj = d.mul(a, bj);
                let s1 = d.add(a_bj, ab);
                let h1 = d.congr(abj, a_bj, ih, &|d, t| d.add(t, ab));
                let bj_b = d.add(bj, b);
                let s2 = d.mul(a, bj_b);
                let h_ld = d.lemma(p.left_distrib, &[a, bj, b]);
                let h2 = d.symm(s2, s1, h_ld);
                let (_end, proof) = d.chain(start, &[(s1, h1), (s2, h2)]);
                proof
            },
            c,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// The first reusable finite-sum algebra needed by the Rado sharpness proof.
/// This is a checked theorem over [`NatPrelude::sum_range`], not a specialized
/// test-only recurrence.
fn declare_finite_sum_theorems(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;

    // sumRange_congr : ∀ f g n,
    //   (∀ i, f i = g i) → sumRange f n = sumRange g n
    {
        let nat = d.nat_ty();
        let fn_ty = d.arrow(nat, nat);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pointwise = {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let fi = d.apply(f, &[i]);
            let gi = d.apply(g, &[i]);
            let eq = d.eq(fi, gi);
            d.pi_fv(i_fv, nat, eq)
        };
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs = d.sum_range(f, x);
            let rhs = d.sum_range(g, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                d.refl(zero)
            },
            &|d, j, ih| {
                let f_prior = d.sum_range(f, j);
                let g_prior = d.sum_range(g, j);
                let fj = d.apply(f, &[j]);
                let gj = d.apply(g, &[j]);
                let start = d.add(f_prior, fj);
                let mid = d.add(g_prior, fj);
                let h1 = d.congr(f_prior, g_prior, ih, &|d, t| d.add(t, fj));
                let end = d.add(g_prior, gj);
                let pointwise_j = d.apply(h, &[j]);
                let h2 = d.congr(fj, gj, pointwise_j, &|d, t| d.add(g_prior, t));
                let (_, proof) = d.chain(start, &[(mid, h1), (end, h2)]);
                proof
            },
            n,
        );
        let ty = {
            let with_h = d.pi_fv(h_fv, pointwise, stmt);
            let over_n = d.pi_fv(n_fv, nat, with_h);
            let over_g = d.pi_fv(g_fv, fn_ty, over_n);
            d.pi_fv(f_fv, fn_ty, over_g)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, pointwise, proof);
            let over_n = d.lam_fv(n_fv, nat, with_h);
            let over_g = d.lam_fv(g_fv, fn_ty, over_n);
            d.lam_fv(f_fv, fn_ty, over_g)
        };
        d.declare_theorem(p.sum_range_congr, ty, value)?;
    }

    // mul_sumRange : ∀ a f n,
    //   a * sumRange f n = sumRange (fun i => a * f i) n
    {
        let nat = d.nat_ty();
        let fn_ty = d.arrow(nat, nat);
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let scaled_fn = |d: &mut NatDev<'_>| {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let fi = d.apply(f, &[i]);
            let body = d.mul(a, fi);
            let nat = d.nat_ty();
            d.lam_fv(i_fv, nat, body)
        };
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let lhs_sum = d.sum_range(f, x);
            let lhs = d.mul(a, lhs_sum);
            let scaled = scaled_fn(d);
            let rhs = d.sum_range(scaled, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                d.refl(zero)
            },
            &|d, j, ih| {
                let prior = d.sum_range(f, j);
                let fj = d.apply(f, &[j]);
                let extended = d.add(prior, fj);
                let start = d.mul(a, extended);
                let a_prior = d.mul(a, prior);
                let a_fj = d.mul(a, fj);
                let distributed = d.add(a_prior, a_fj);
                let h1 = d.lemma(p.left_distrib, &[a, prior, fj]);
                let scaled = scaled_fn(d);
                let scaled_prior = d.sum_range(scaled, j);
                let end = d.add(scaled_prior, a_fj);
                let h2 = d.congr(a_prior, scaled_prior, ih, &|d, t| d.add(t, a_fj));
                let (_, proof) = d.chain(start, &[(distributed, h1), (end, h2)]);
                proof
            },
            n,
        );
        let ty = {
            let over_n = d.pi_fv(n_fv, nat, stmt);
            let over_f = d.pi_fv(f_fv, fn_ty, over_n);
            d.pi_fv(a_fv, nat, over_f)
        };
        let value = {
            let over_n = d.lam_fv(n_fv, nat, proof);
            let over_f = d.lam_fv(f_fv, fn_ty, over_n);
            d.lam_fv(a_fv, nat, over_f)
        };
        d.declare_theorem(p.mul_sum_range, ty, value)?;
    }

    d.theorem(p.mul_sum_range_pow, 2, &|d, v| {
        let (a, n) = (v[0], v[1]);
        let power_fn = |d: &mut NatDev<'_>, shifted: bool| {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let exponent = if shifted { d.succ(i) } else { i };
            let body = d.pow(a, exponent);
            let nat = d.nat_ty();
            d.lam_fv(i_fv, nat, body)
        };
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let unshifted = power_fn(d, false);
            let shifted = power_fn(d, true);
            let sum = d.sum_range(unshifted, x);
            let lhs = d.mul(a, sum);
            let rhs = d.sum_range(shifted, x);
            d.eq(lhs, rhs)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let zero = d.zero();
                d.refl(zero)
            },
            &|d, j, ih| {
                let unshifted = power_fn(d, false);
                let shifted = power_fn(d, true);
                let sum = d.sum_range(unshifted, j);
                let shifted_sum = d.sum_range(shifted, j);
                let power = d.pow(a, j);
                let start = {
                    let extended = d.add(sum, power);
                    d.mul(a, extended)
                };
                let a_sum = d.mul(a, sum);
                let a_power = d.mul(a, power);
                let distributed = d.add(a_sum, a_power);
                let h1 = d.lemma(p.left_distrib, &[a, sum, power]);
                let with_ih = d.add(shifted_sum, a_power);
                let h2 = d.congr(a_sum, shifted_sum, ih, &|d, t| d.add(t, a_power));
                let power_a = d.mul(power, a);
                let commuted = d.add(shifted_sum, power_a);
                let h_comm = d.lemma(p.mul_comm, &[a, power]);
                let h3 = d.congr(a_power, power_a, h_comm, &|d, t| d.add(shifted_sum, t));
                let successor_power = {
                    let sj = d.succ(j);
                    d.pow(a, sj)
                };
                let end = d.add(shifted_sum, successor_power);
                let h_pow = d.lemma(p.pow_succ, &[a, j]);
                let h_pow_rev = d.symm(successor_power, power_a, h_pow);
                let h4 = d.congr(power_a, successor_power, h_pow_rev, &|d, t| {
                    d.add(shifted_sum, t)
                });
                let (_, proof) = d.chain(
                    start,
                    &[(distributed, h1), (with_ih, h2), (commuted, h3), (end, h4)],
                );
                proof
            },
            n,
        );
        (stmt, proof)
    })?;
    Ok(())
}

/// `Nat.le`, reducible strict order, and the checked order theorems.
fn declare_order(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();

    // Le : Nat → Nat → Prop, with the first argument a PARAMETER and the second
    // an INDEX (Lean's own `Nat.le` has exactly this shape).
    let le_ty = {
        let inner = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
        d.kernel().pi(anon, nat, inner, BinderInfo::Default)
    };
    // Le.refl : Π (n : Nat), Le n n
    let refl_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.le(n, n);
        d.pi_fv(n_fv, nat, body)
    };
    // Le.step : Π (n m : Nat), Le n m → Le n (succ m)
    let step_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let hyp = d.le(n, m);
        let sm = d.succ(m);
        let concl = d.le(n, sm);
        let arrow = d.kernel().pi(anon, hyp, concl, BinderInfo::Default);
        let over_m = d.pi_fv(m_fv, nat, arrow);
        d.pi_fv(n_fv, nat, over_m)
    };
    d.kernel().add_inductive(
        p.le,
        &[],
        1,
        le_ty,
        &[(p.le_refl, refl_ty), (p.le_step, step_ty)],
    )?;

    // lt n m := Le (succ n) m
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let sn = d.succ(n);
        let body = d.le(sn, m);
        let value = {
            let inner = d.lam_fv(m_fv, nat, body);
            d.lam_fv(n_fv, nat, inner)
        };
        let ty = {
            let inner = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            d.kernel().pi(anon, nat, inner, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.lt,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })?;
    }

    // inClosedInterval lower upper value := Le lower value ∧ Le value upper
    {
        let lower_fv = d.fresh_fvar();
        let lower = d.kernel().fvar(lower_fv);
        let upper_fv = d.fresh_fvar();
        let upper = d.kernel().fvar(upper_fv);
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);
        let lower_bound = d.le(lower, value);
        let upper_bound = d.le(value, upper);
        let body = d.const_app(p.logic.and, &[lower_bound, upper_bound]);
        let definition = {
            let with_value = d.lam_fv(value_fv, nat, body);
            let with_upper = d.lam_fv(upper_fv, nat, with_value);
            d.lam_fv(lower_fv, nat, with_upper)
        };
        let ty = {
            let with_value = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            let with_upper = d.kernel().pi(anon, nat, with_value, BinderInfo::Default);
            d.kernel().pi(anon, nat, with_upper, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.in_closed_interval,
            uparams: vec![],
            ty,
            value: definition,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // zero_le : ∀ n, Le zero n   (induction on n, using only the constructors)
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let z = d.zero();
            d.le(z, x)
        };
        let stmt = motive(d, n);
        let proof = d.induct(
            &motive,
            &|d| {
                let z = d.zero();
                d.const_app(p.le_refl, &[z])
            },
            &|d, j, ih| {
                let z = d.zero();
                d.const_app(p.le_step, &[z, j, ih])
            },
            n,
        );
        let ty = d.pi_fv(n_fv, nat, stmt);
        let value = d.lam_fv(n_fv, nat, proof);
        d.declare_theorem(p.zero_le, ty, value)?;
    }

    // le_succ_succ : ∀ n m, Le n m → Le (succ n) (succ m)
    // — induction on the DERIVATION, i.e. elimination with the generated Le.rec.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp = d.le(n, m);
        let sn = d.succ(n);
        let sm = d.succ(m);
        let concl = d.le(sn, sm);

        // motive := fun (x : Nat) (_ : Le n x) => Le (succ n) (succ x)
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let sx = d.succ(x);
            let body = d.le(sn, sx);
            let dom = d.le(n, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        // minor for Le.refl : motive n (Le.refl n) = Le (succ n) (succ n)
        let minor_refl = d.const_app(p.le_refl, &[sn]);
        // minor for Le.step : Π (x : Nat) (hx : Le n x), motive x hx → motive (succ x) …
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(n, x);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let sx = d.succ(x);
            let ih_ty = d.le(sn, sx);
            let body = d.const_app(p.le_step, &[sn, sx, ih]);
            let l_ih = d.lam_fv(ih_fv, ih_ty, body);
            let l_hx = d.lam_fv(hx_fv, hx_ty, l_ih);
            d.lam_fv(x_fv, nat, l_hx)
        };
        let applied = d.const_app(p.le_rec, &[n, motive, minor_refl, minor_step, m, h]);

        let ty = {
            let arrow = d.kernel().pi(anon, hyp, concl, BinderInfo::Default);
            let over_m = d.pi_fv(m_fv, nat, arrow);
            d.pi_fv(n_fv, nat, over_m)
        };
        let value = {
            let l_h = d.lam_fv(h_fv, hyp, applied);
            let l_m = d.lam_fv(m_fv, nat, l_h);
            d.lam_fv(n_fv, nat, l_m)
        };
        d.declare_theorem(p.le_succ_succ, ty, value)?;
    }

    // le_trans : ∀ a b c, Le a b → Le b c → Le a c
    // — elimination on the SECOND derivation, with `b` as the recursor's parameter.
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let b_fv = d.fresh_fvar();
        let b = d.kernel().fvar(b_fv);
        let c_fv = d.fresh_fvar();
        let c = d.kernel().fvar(c_fv);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let h1_ty = d.le(a, b);
        let h2_ty = d.le(b, c);
        let concl = d.le(a, c);

        // motive := fun (x : Nat) (_ : Le b x) => Le a x
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let body = d.le(a, x);
            let dom = d.le(b, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        // refl case: motive b (Le.refl b) = Le a b, which is exactly `h1`.
        let minor_refl = h1;
        // step case: fun x hx ih => Le.step a x ih
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(b, x);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let ih_ty = d.le(a, x);
            let body = d.const_app(p.le_step, &[a, x, ih]);
            let l_ih = d.lam_fv(ih_fv, ih_ty, body);
            let l_hx = d.lam_fv(hx_fv, hx_ty, l_ih);
            d.lam_fv(x_fv, nat, l_hx)
        };
        let applied = d.const_app(p.le_rec, &[b, motive, minor_refl, minor_step, c, h2]);

        let ty = {
            let t = d.kernel().pi(anon, h2_ty, concl, BinderInfo::Default);
            let t = d.pi_fv(h1_fv, h1_ty, t);
            let t = d.pi_fv(c_fv, nat, t);
            let t = d.pi_fv(b_fv, nat, t);
            d.pi_fv(a_fv, nat, t)
        };
        let value = {
            let v = d.lam_fv(h2_fv, h2_ty, applied);
            let v = d.lam_fv(h1_fv, h1_ty, v);
            let v = d.lam_fv(c_fv, nat, v);
            let v = d.lam_fv(b_fv, nat, v);
            d.lam_fv(a_fv, nat, v)
        };
        d.declare_theorem(p.le_trans, ty, value)?;
    }

    // le_of_succ_le_succ : ∀ n m, Le (succ n) (succ m) → Le n m
    //
    // Eliminate the derivation with the predecessor-style family
    //   P 0        = False
    //   P (succ x) = Le n x.
    // The step case can ignore its induction hypothesis: from
    // `Le (succ n) x`, transitivity with `Le n (succ n)` gives `Le n x`.
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let sn = d.succ(n);
        let sm = d.succ(m);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let hyp = d.le(sn, sm);
        let concl = d.le(n, m);

        let predecessor_family = |d: &mut NatDev<'_>, x: ExprId| {
            let type_motive = d.kernel().lam(anon, nat, prop, BinderInfo::Default);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let step = {
                let j_fv = d.fresh_fvar();
                let j = d.kernel().fvar(j_fv);
                let ignored_fv = d.fresh_fvar();
                let body = d.le(n, j);
                let inner = d.lam_fv(ignored_fv, prop, body);
                d.lam_fv(j_fv, nat, inner)
            };
            let one = d.level_one();
            let rec = d.kernel().const_(p.rec, vec![one]);
            d.apply(rec, &[type_motive, false_ty, step, x])
        };

        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(sn, x);
            let body = predecessor_family(d, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.const_app(p.le_refl, &[n]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(sn, x);
            let hx = d.kernel().fvar(hx_fv);
            let ih_fv = d.fresh_fvar();
            let ih_ty = predecessor_family(d, x);
            let n_refl = d.const_app(p.le_refl, &[n]);
            let n_le_sn = d.const_app(p.le_step, &[n, n, n_refl]);
            let body = d.lemma(p.le_trans, &[n, sn, x, n_le_sn, hx]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let proof = d.const_app(p.le_rec, &[sn, motive, minor_refl, minor_step, sm, h]);
        let ty = {
            let arrow = d.kernel().pi(anon, hyp, concl, BinderInfo::Default);
            let over_m = d.pi_fv(m_fv, nat, arrow);
            d.pi_fv(n_fv, nat, over_m)
        };
        let value = {
            let with_h = d.lam_fv(h_fv, hyp, proof);
            let with_m = d.lam_fv(m_fv, nat, with_h);
            d.lam_fv(n_fv, nat, with_m)
        };
        d.declare_theorem(p.le_of_succ_le_succ, ty, value)?;
    }

    // le_add_right : ∀ n k, Le n (add n k)   (induction on k; both cases are
    // definitional, since `add n zero ≡ n` and `add n (succ j) ≡ succ (add n j)`)
    {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let nx = d.add(n, x);
            d.le(n, nx)
        };
        let stmt = motive(d, k);
        let proof = d.induct(
            &motive,
            &|d| d.const_app(p.le_refl, &[n]),
            &|d, j, ih| {
                let nj = d.add(n, j);
                d.const_app(p.le_step, &[n, nj, ih])
            },
            k,
        );
        let ty = {
            let t = d.pi_fv(k_fv, nat, stmt);
            d.pi_fv(n_fv, nat, t)
        };
        let value = {
            let v = d.lam_fv(k_fv, nat, proof);
            d.lam_fv(n_fv, nat, v)
        };
        d.declare_theorem(p.le_add_right, ty, value)?;
    }

    // lt_or_eq_of_le : ∀ a b, Le a b → Or (Lt a b) (Eq Nat a b)
    // Elimination on the order derivation: reflexivity gives equality, while
    // every step lifts the prior bound to a strict successor bound.
    d.theorem(p.lt_or_eq_of_le, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let hyp_ty = d.le(a, b);
        let hyp_fv = d.fresh_fvar();
        let hyp = d.kernel().fvar(hyp_fv);
        let result = |d: &mut NatDev<'_>, x: ExprId| {
            let strict = d.lt(a, x);
            let equal = d.eq(a, x);
            d.const_app(p.logic.or, &[strict, equal])
        };
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(a, x);
            let body = result(d, x);
            let with_hx = d.lam_fv(hx_fv, hx_ty, body);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let minor_refl = {
            let strict = d.lt(a, a);
            let equal = d.eq(a, a);
            let refl = d.refl(a);
            d.const_app(p.logic.or_inr, &[strict, equal, refl])
        };
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx = d.kernel().fvar(hx_fv);
            let hx_ty = d.le(a, x);
            let ih_fv = d.fresh_fvar();
            let ih_ty = result(d, x);
            let sx = d.succ(x);
            let strict = d.lt(a, sx);
            let equal = d.eq(a, sx);
            let lifted = d.lemma(p.le_succ_succ, &[a, x, hx]);
            let body = d.const_app(p.logic.or_inl, &[strict, equal, lifted]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let body = d.const_app(p.le_rec, &[a, motive, minor_refl, minor_step, b, hyp]);
        let conclusion = result(d, b);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(hyp_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // lt_of_lt_of_le : ∀ a b c, Lt a b → Le b c → Lt a c
    d.theorem(p.lt_of_lt_of_le, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let strict_ty = d.lt(a, b);
        let strict_fv = d.fresh_fvar();
        let strict = d.kernel().fvar(strict_fv);
        let bound_ty = d.le(b, c);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let sa = d.succ(a);
        let body = d.lemma(p.le_trans, &[sa, b, c, strict, bound]);
        let conclusion = d.lt(a, c);
        let stmt = {
            let with_bound = d.arrow(bound_ty, conclusion);
            d.arrow(strict_ty, with_bound)
        };
        let proof = {
            let with_bound = d.lam_fv(bound_fv, bound_ty, body);
            d.lam_fv(strict_fv, strict_ty, with_bound)
        };
        (stmt, proof)
    })?;

    // lt_of_le_of_lt : ∀ a b c, Le a b → Lt b c → Lt a c
    d.theorem(p.lt_of_le_of_lt, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let bound_ty = d.le(a, b);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let strict_ty = d.lt(b, c);
        let strict_fv = d.fresh_fvar();
        let strict = d.kernel().fvar(strict_fv);
        let sa = d.succ(a);
        let sb = d.succ(b);
        let lifted = d.lemma(p.le_succ_succ, &[a, b, bound]);
        let body = d.lemma(p.le_trans, &[sa, sb, c, lifted, strict]);
        let conclusion = d.lt(a, c);
        let stmt = {
            let with_strict = d.arrow(strict_ty, conclusion);
            d.arrow(bound_ty, with_strict)
        };
        let proof = {
            let with_strict = d.lam_fv(strict_fv, strict_ty, body);
            d.lam_fv(bound_fv, bound_ty, with_strict)
        };
        (stmt, proof)
    })?;

    // le_total : ∀ a b, Or (Le a b) (Le b a)
    // Structural induction on both naturals; the successor/successor branch
    // maps the smaller comparison through `le_succ_succ`.
    d.theorem(p.le_total, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let logic = p.logic;
        let total = |d: &mut NatDev<'_>, x: ExprId, y: ExprId| {
            let xy = d.le(x, y);
            let yx = d.le(y, x);
            d.const_app(logic.or, &[xy, yx])
        };
        let motive_a = |d: &mut NatDev<'_>, x: ExprId| {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = total(d, x, y);
            d.pi_fv(y_fv, nat, body)
        };
        let all_from_zero = |d: &mut NatDev<'_>| {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let zero = d.zero();
            let left = d.le(zero, y);
            let right = d.le(y, zero);
            let bound = d.lemma(p.zero_le, &[y]);
            let body = d.const_app(logic.or_inl, &[left, right, bound]);
            d.lam_fv(y_fv, nat, body)
        };
        let step_a = |d: &mut NatDev<'_>, x: ExprId, ih: ExprId| {
            let sx = d.succ(x);
            let motive_b = |d: &mut NatDev<'_>, y: ExprId| total(d, sx, y);
            let at_zero = |d: &mut NatDev<'_>| {
                let zero = d.zero();
                let left = d.le(sx, zero);
                let right = d.le(zero, sx);
                let bound = d.lemma(p.zero_le, &[sx]);
                d.const_app(logic.or_inr, &[left, right, bound])
            };
            let step_b = |d: &mut NatDev<'_>, y: ExprId, _inner_ih: ExprId| {
                let sy = d.succ(y);
                let xy = d.le(x, y);
                let yx = d.le(y, x);
                let old_total = d.apply(ih, &[y]);
                let sxy = d.le(sx, sy);
                let syx = d.le(sy, sx);
                let target = d.const_app(logic.or, &[sxy, syx]);
                let old_total_ty = d.const_app(logic.or, &[xy, yx]);
                let motive = d
                    .kernel()
                    .lam(anon, old_total_ty, target, BinderInfo::Default);
                let left_minor = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let lifted = d.lemma(p.le_succ_succ, &[x, y, h]);
                    let body = d.const_app(logic.or_inl, &[sxy, syx, lifted]);
                    d.lam_fv(h_fv, xy, body)
                };
                let right_minor = {
                    let h_fv = d.fresh_fvar();
                    let h = d.kernel().fvar(h_fv);
                    let lifted = d.lemma(p.le_succ_succ, &[y, x, h]);
                    let body = d.const_app(logic.or_inr, &[sxy, syx, lifted]);
                    d.lam_fv(h_fv, yx, body)
                };
                d.const_app(
                    logic.or_rec,
                    &[xy, yx, motive, left_minor, right_minor, old_total],
                )
            };
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = d.induct(&motive_b, &at_zero, &step_b, y);
            d.lam_fv(y_fv, nat, body)
        };
        let all_b = d.induct(&motive_a, &all_from_zero, &step_a, a);
        let proof = d.apply(all_b, &[b]);
        (total(d, a, b), proof)
    })?;

    // not_succ_le_zero : ∀ n, Not (Le (succ n) zero)
    // Eliminate a hypothetical derivation into a family that is `False` only
    // at index zero and `True` at every successor index.
    d.theorem(p.not_succ_le_zero, 1, &|d, v| {
        let n = v[0];
        let sn = d.succ(n);
        let zero = d.zero();
        let hyp_ty = d.le(sn, zero);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let true_ty = d.kernel().const_(p.logic.true_, vec![]);
        let family = |d: &mut NatDev<'_>, x: ExprId| {
            let motive = d.kernel().lam(anon, nat, prop, BinderInfo::Default);
            let step = {
                let j_fv = d.fresh_fvar();
                let ih_fv = d.fresh_fvar();
                let body = true_ty;
                let with_ih = d.lam_fv(ih_fv, prop, body);
                d.lam_fv(j_fv, nat, with_ih)
            };
            let one = d.level_one();
            let rec = d.kernel().const_(p.rec, vec![one]);
            d.apply(rec, &[motive, false_ty, step, x])
        };
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(sn, x);
            let body = family(d, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.kernel().const_(p.logic.true_intro, vec![]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(sn, x);
            let ih_fv = d.fresh_fvar();
            let ih_ty = family(d, x);
            let body = d.kernel().const_(p.logic.true_intro, vec![]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let body = d.const_app(p.le_rec, &[sn, motive, minor_refl, minor_step, zero, h]);
        let stmt = d.arrow(hyp_ty, false_ty);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // lt_irrefl : ∀ n, Not (Lt n n)
    d.theorem(p.lt_irrefl, 1, &|d, v| {
        let n = v[0];
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let motive = |d: &mut NatDev<'_>, x: ExprId| {
            let strict = d.lt(x, x);
            d.arrow(strict, false_ty)
        };
        let base = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let strict = d.lt(zero, zero);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = d.lemma(p.not_succ_le_zero, &[zero, h]);
            d.lam_fv(h_fv, strict, body)
        };
        let step = |d: &mut NatDev<'_>, x: ExprId, ih: ExprId| {
            let sx = d.succ(x);
            let strict = d.lt(sx, sx);
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let reduced = d.lemma(p.le_of_succ_le_succ, &[sx, x, h]);
            let body = d.apply(ih, &[reduced]);
            d.lam_fv(h_fv, strict, body)
        };
        let body = d.induct(&motive, &base, &step, n);
        (motive(d, n), body)
    })?;

    // le_antisymm : ∀ a b, Le a b → Le b a → Eq a b
    // Induct over both endpoints. Mixed zero/successor branches eliminate the
    // impossible bound; the successor/successor branch inverts both bounds
    // and lifts the induction hypothesis through `succ`.
    d.theorem(p.le_antisymm, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let antisymm_at = |d: &mut NatDev<'_>, x: ExprId| {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let xy = d.le(x, y);
            let yx = d.le(y, x);
            let equality = d.eq(x, y);
            let reverse = d.arrow(yx, equality);
            let body = d.arrow(xy, reverse);
            d.pi_fv(y_fv, nat, body)
        };
        let at_zero = |d: &mut NatDev<'_>| {
            let motive_y = |d: &mut NatDev<'_>, y: ExprId| {
                let zero = d.zero();
                let zy = d.le(zero, y);
                let yz = d.le(y, zero);
                let equality = d.eq(zero, y);
                let reverse = d.arrow(yz, equality);
                d.arrow(zy, reverse)
            };
            let y_zero = |d: &mut NatDev<'_>| {
                let zero = d.zero();
                let zz = d.le(zero, zero);
                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();
                let body = d.refl(zero);
                let with_h2 = d.lam_fv(h2_fv, zz, body);
                d.lam_fv(h1_fv, zz, with_h2)
            };
            let y_step = |d: &mut NatDev<'_>, y: ExprId, _ih: ExprId| {
                let zero = d.zero();
                let sy = d.succ(y);
                let zsy = d.le(zero, sy);
                let syz = d.le(sy, zero);
                let target = d.eq(zero, sy);
                let h1_fv = d.fresh_fvar();
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let impossible = d.lemma(p.not_succ_le_zero, &[y, h2]);
                let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
                let level_zero = d.kernel().level_zero();
                let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                let body = d.apply(rec, &[motive, impossible]);
                let with_h2 = d.lam_fv(h2_fv, syz, body);
                d.lam_fv(h1_fv, zsy, with_h2)
            };
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = d.induct(&motive_y, &y_zero, &y_step, y);
            d.lam_fv(y_fv, nat, body)
        };
        let step_a = |d: &mut NatDev<'_>, x: ExprId, ih: ExprId| {
            let sx = d.succ(x);
            let motive_y = |d: &mut NatDev<'_>, y: ExprId| {
                let sxy = d.le(sx, y);
                let ysx = d.le(y, sx);
                let equality = d.eq(sx, y);
                let reverse = d.arrow(ysx, equality);
                d.arrow(sxy, reverse)
            };
            let y_zero = |d: &mut NatDev<'_>| {
                let zero = d.zero();
                let sxz = d.le(sx, zero);
                let zsx = d.le(zero, sx);
                let target = d.eq(sx, zero);
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);
                let h2_fv = d.fresh_fvar();
                let impossible = d.lemma(p.not_succ_le_zero, &[x, h1]);
                let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
                let level_zero = d.kernel().level_zero();
                let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                let body = d.apply(rec, &[motive, impossible]);
                let with_h2 = d.lam_fv(h2_fv, zsx, body);
                d.lam_fv(h1_fv, sxz, with_h2)
            };
            let y_step = |d: &mut NatDev<'_>, y: ExprId, _inner_ih: ExprId| {
                let sy = d.succ(y);
                let sxsy = d.le(sx, sy);
                let sysx = d.le(sy, sx);
                let h1_fv = d.fresh_fvar();
                let h1 = d.kernel().fvar(h1_fv);
                let h2_fv = d.fresh_fvar();
                let h2 = d.kernel().fvar(h2_fv);
                let xy = d.lemma(p.le_of_succ_le_succ, &[x, y, h1]);
                let yx = d.lemma(p.le_of_succ_le_succ, &[y, x, h2]);
                let smaller = d.apply(ih, &[y, xy, yx]);
                let body = d.congr(x, y, smaller, &|d, value| d.succ(value));
                let with_h2 = d.lam_fv(h2_fv, sysx, body);
                d.lam_fv(h1_fv, sxsy, with_h2)
            };
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = d.induct(&motive_y, &y_zero, &y_step, y);
            d.lam_fv(y_fv, nat, body)
        };
        let all_b = d.induct(&antisymm_at, &at_zero, &step_a, a);
        let proof = d.apply(all_b, &[b]);
        let ab = d.le(a, b);
        let ba = d.le(b, a);
        let conclusion = d.eq(a, b);
        let reverse = d.arrow(ba, conclusion);
        let stmt = d.arrow(ab, reverse);
        (stmt, proof)
    })?;

    // lt_well_founded : WellFounded Nat.lt
    // Ordinary Nat induction builds accessibility. At `succ n`, every
    // predecessor `m` satisfies `m ≤ n`; strict predecessors descend through
    // `Acc.inv`, while equality transports the induction hypothesis to `m`.
    let (lt_well_founded_ty, lt_well_founded_value) = {
        let one = d.level_one();
        let relation = d.kernel().const_(p.lt, vec![]);
        let acc_at = |d: &mut NatDev<'_>, value: ExprId| {
            let acc = d.kernel().const_(p.logic.acc, vec![one]);
            d.apply(acc, &[nat, relation, value])
        };
        let motive = |d: &mut NatDev<'_>, value: ExprId| acc_at(d, value);
        let base = |d: &mut NatDev<'_>| {
            let zero = d.zero();
            let predecessor_fv = d.fresh_fvar();
            let related_fv = d.fresh_fvar();
            let predecessor = d.kernel().fvar(predecessor_fv);
            let related = d.kernel().fvar(related_fv);
            let relation_ty = d.lt(predecessor, zero);
            let impossible = d.lemma(p.not_succ_le_zero, &[predecessor, related]);
            let target = acc_at(d, predecessor);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let false_motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
            let zero_level = d.kernel().level_zero();
            let false_rec = d.kernel().const_(p.logic.false_rec, vec![zero_level]);
            let body = d.apply(false_rec, &[false_motive, impossible]);
            let with_related = d.lam_fv(related_fv, relation_ty, body);
            let field = d.lam_fv(predecessor_fv, nat, with_related);
            let intro = d.kernel().const_(p.logic.acc_intro, vec![one]);
            d.apply(intro, &[nat, relation, zero, field])
        };
        let step = |d: &mut NatDev<'_>, n: ExprId, accessible_n: ExprId| {
            let sn = d.succ(n);
            let predecessor_fv = d.fresh_fvar();
            let related_fv = d.fresh_fvar();
            let predecessor = d.kernel().fvar(predecessor_fv);
            let related = d.kernel().fvar(related_fv);
            let relation_ty = d.lt(predecessor, sn);
            let predecessor_le_n = d.lemma(p.le_of_succ_le_succ, &[predecessor, n, related]);
            let split = d.lemma(p.lt_or_eq_of_le, &[predecessor, n, predecessor_le_n]);
            let strict_ty = d.lt(predecessor, n);
            let equal_ty = d.eq(predecessor, n);
            let target = acc_at(d, predecessor);
            let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
            let split_motive = d.kernel().lam(anon, split_ty, target, BinderInfo::Default);
            let strict_minor = {
                let strict_fv = d.fresh_fvar();
                let strict = d.kernel().fvar(strict_fv);
                let inverse = d.kernel().const_(p.logic.acc_inv, vec![one]);
                let body = d.apply(
                    inverse,
                    &[nat, relation, n, predecessor, accessible_n, strict],
                );
                d.lam_fv(strict_fv, strict_ty, body)
            };
            let equal_minor = {
                let equal_fv = d.fresh_fvar();
                let equal = d.kernel().fvar(equal_fv);
                let reverse = d.symm(predecessor, n, equal);
                let transport_motive = d.eq_motive(n, &|d, value| acc_at(d, value));
                let body = d.transport(n, transport_motive, accessible_n, predecessor, reverse);
                d.lam_fv(equal_fv, equal_ty, body)
            };
            let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
            let selected = d.apply(
                or_rec,
                &[
                    strict_ty,
                    equal_ty,
                    split_motive,
                    strict_minor,
                    equal_minor,
                    split,
                ],
            );
            let with_related = d.lam_fv(related_fv, relation_ty, selected);
            let field = d.lam_fv(predecessor_fv, nat, with_related);
            let intro = d.kernel().const_(p.logic.acc_intro, vec![one]);
            d.apply(intro, &[nat, relation, sn, field])
        };
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);
        let accessible = d.induct(&motive, &base, &step, value);
        let proof = d.lam_fv(value_fv, nat, accessible);
        let well_founded = d.kernel().const_(p.logic.well_founded, vec![one]);
        let stmt = d.apply(well_founded, &[nat, relation]);
        (stmt, proof)
    };
    d.kernel().add_declaration(Declaration::Definition {
        name: p.lt_well_founded,
        uparams: vec![],
        ty: lt_well_founded_ty,
        value: lt_well_founded_value,
        hint: ReducibilityHint::Regular(6),
    })?;

    // le_intro : ∀ a b k, a+k=b → Le a b
    d.theorem(p.le_intro, 3, &|d, v| {
        let (a, b, k) = (v[0], v[1], v[2]);
        let sum = d.add(a, k);
        let hyp_ty = d.eq(sum, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let bound = d.lemma(p.le_add_right, &[a, k]);
        let motive = d.eq_motive(sum, &|d, x| d.le(a, x));
        let body = d.transport(sum, motive, bound, b, h);
        let conclusion = d.le(a, b);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // le_dest : ∀ a b, Le a b → Exists (fun k => a+k=b)
    d.theorem(p.le_dest, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let one = d.level_one();
        let exists_at = |d: &mut NatDev<'_>, x: ExprId| {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sum = d.add(a, k);
            let body = d.eq(sum, x);
            let pred = d.lam_fv(k_fv, nat, body);
            let exists = d.kernel().const_(p.logic.exists_, vec![one]);
            d.apply(exists, &[nat, pred])
        };
        let hyp_ty = d.le(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(a, x);
            let body = exists_at(d, x);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = {
            let zero = d.zero();
            let pred = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sum = d.add(a, k);
                let body = d.eq(sum, a);
                d.lam_fv(k_fv, nat, body)
            };
            let witness = d.refl(a);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            d.apply(intro, &[nat, pred, zero, witness])
        };
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(a, x);
            let ih_fv = d.fresh_fvar();
            let ih_ty = exists_at(d, x);
            let ih = d.kernel().fvar(ih_fv);
            let sx = d.succ(x);
            let target = exists_at(d, sx);
            let target_motive = d.kernel().lam(anon, ih_ty, target, BinderInfo::Default);
            let source_pred = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sum = d.add(a, k);
                let body = d.eq(sum, x);
                d.lam_fv(k_fv, nat, body)
            };
            let witness_minor = {
                let k_fv = d.fresh_fvar();
                let k = d.kernel().fvar(k_fv);
                let sum = d.add(a, k);
                let e_fv = d.fresh_fvar();
                let e_ty = d.eq(sum, x);
                let e = d.kernel().fvar(e_fv);
                let sk = d.succ(k);
                let lifted = d.congr(sum, x, e, &|d, value| d.succ(value));
                let target_pred = {
                    let j_fv = d.fresh_fvar();
                    let j = d.kernel().fvar(j_fv);
                    let target_sum = d.add(a, j);
                    let body = d.eq(target_sum, sx);
                    d.lam_fv(j_fv, nat, body)
                };
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let body = d.apply(intro, &[nat, target_pred, sk, lifted]);
                let with_e = d.lam_fv(e_fv, e_ty, body);
                d.lam_fv(k_fv, nat, with_e)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(rec, &[nat, source_pred, target_motive, witness_minor, ih]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let body = d.const_app(p.le_rec, &[a, motive, minor_refl, minor_step, b, h]);
        let conclusion = exists_at(d, b);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // add_le_add_left : ∀ c a b, Le a b → Le (add c a) (add c b)
    // Eliminate the bound derivation; `add` recurses on exactly its index.
    d.theorem(p.add_le_add_left, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let hyp_ty = d.le(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ca = d.add(c, a);
        let cb = d.add(c, b);
        let conclusion = d.le(ca, cb);
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(a, x);
            let cx = d.add(c, x);
            let body = d.le(ca, cx);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.const_app(p.le_refl, &[ca]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(a, x);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let cx = d.add(c, x);
            let ih_ty = d.le(ca, cx);
            let body = d.const_app(p.le_step, &[ca, cx, ih]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let body = d.const_app(p.le_rec, &[a, motive, minor_refl, minor_step, b, h]);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // add_lt_add_left : ∀ c a b, Lt a b → Lt (c+a) (c+b)
    d.theorem(p.add_lt_add_left, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let strict_ty = d.lt(a, b);
        let strict_fv = d.fresh_fvar();
        let strict = d.kernel().fvar(strict_fv);
        let sa = d.succ(a);
        let body = d.lemma(p.add_le_add_left, &[c, sa, b, strict]);
        let ca = d.add(c, a);
        let cb = d.add(c, b);
        let conclusion = d.lt(ca, cb);
        let stmt = d.arrow(strict_ty, conclusion);
        let proof = d.lam_fv(strict_fv, strict_ty, body);
        (stmt, proof)
    })?;

    // add_le_add_right : ∀ c a b, Le a b → Le (a+c) (b+c)
    d.theorem(p.add_le_add_right, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let hyp_ty = d.le(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ca = d.add(c, a);
        let cb = d.add(c, b);
        let ac = d.add(a, c);
        let bc = d.add(b, c);
        let shifted = d.lemma(p.add_le_add_left, &[c, a, b, h]);
        let ca_eq_ac = d.lemma(p.add_comm, &[c, a]);
        let cb_eq_bc = d.lemma(p.add_comm, &[c, b]);
        let lower_motive = d.eq_motive(ca, &|d, lower| d.le(lower, cb));
        let lower_shifted = d.transport(ca, lower_motive, shifted, ac, ca_eq_ac);
        let upper_motive = d.eq_motive(cb, &|d, upper| d.le(ac, upper));
        let body = d.transport(cb, upper_motive, lower_shifted, bc, cb_eq_bc);
        let conclusion = d.le(ac, bc);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // le_of_add_le_add_left : ∀ c a b, Le (c+a) (c+b) → Le a b
    d.theorem(p.le_of_add_le_add_left, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let ca = d.add(c, a);
        let cb = d.add(c, b);
        let hyp_ty = d.le(ca, cb);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let represented = d.lemma(p.le_dest, &[ca, cb, h]);
        let pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let cak = d.add(ca, k);
            let body = d.eq(cak, cb);
            d.lam_fv(k_fv, nat, body)
        };
        let conclusion = d.le(a, b);
        let represented_ty = {
            let one = d.level_one();
            let exists = d.kernel().const_(p.logic.exists_, vec![one]);
            d.apply(exists, &[nat, pred])
        };
        let motive = d
            .kernel()
            .lam(anon, represented_ty, conclusion, BinderInfo::Default);
        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let cak = d.add(ca, k);
            let e_fv = d.fresh_fvar();
            let e_ty = d.eq(cak, cb);
            let e = d.kernel().fvar(e_fv);
            let ak = d.add(a, k);
            let c_ak = d.add(c, ak);
            let assoc = d.lemma(p.add_assoc, &[c, a, k]);
            let assoc_rev = d.symm(cak, c_ak, assoc);
            let (_end, common_sum) = d.chain(c_ak, &[(cak, assoc_rev), (cb, e)]);
            let ak_eq_b = d.lemma(p.add_left_cancel, &[c, ak, b, common_sum]);
            let body = d.lemma(p.le_intro, &[a, b, k, ak_eq_b]);
            let with_e = d.lam_fv(e_fv, e_ty, body);
            d.lam_fv(k_fv, nat, with_e)
        };
        let one = d.level_one();
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(rec, &[nat, pred, motive, minor, represented]);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // le_of_add_le_add_right : ∀ c a b, Le (a+c) (b+c) → Le a b
    d.theorem(p.le_of_add_le_add_right, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let ac = d.add(a, c);
        let bc = d.add(b, c);
        let hyp_ty = d.le(ac, bc);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ca = d.add(c, a);
        let cb = d.add(c, b);
        let ac_eq_ca = d.lemma(p.add_comm, &[a, c]);
        let bc_eq_cb = d.lemma(p.add_comm, &[b, c]);
        let lower_motive = d.eq_motive(ac, &|d, lower| d.le(lower, bc));
        let common_lower = d.transport(ac, lower_motive, h, ca, ac_eq_ca);
        let upper_motive = d.eq_motive(bc, &|d, upper| d.le(ca, upper));
        let common = d.transport(bc, upper_motive, common_lower, cb, bc_eq_cb);
        let body = d.lemma(p.le_of_add_le_add_left, &[c, a, b, common]);
        let conclusion = d.le(a, b);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // mul_le_mul_left : ∀ c a b, Le a b → Le (mul c a) (mul c b)
    // Each derivation step appends one `c`; transitivity with `le_add_right`
    // preserves the fixed lower endpoint.
    d.theorem(p.mul_le_mul_left, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let hyp_ty = d.le(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let ca = d.mul(c, a);
        let cb = d.mul(c, b);
        let conclusion = d.le(ca, cb);
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(a, x);
            let cx = d.mul(c, x);
            let body = d.le(ca, cx);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.const_app(p.le_refl, &[ca]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(a, x);
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let cx = d.mul(c, x);
            let ih_ty = d.le(ca, cx);
            let cx_le_next = d.lemma(p.le_add_right, &[cx, c]);
            let next = d.add(cx, c);
            let body = d.lemma(p.le_trans, &[ca, cx, next, ih, cx_le_next]);
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let body = d.const_app(p.le_rec, &[a, motive, minor_refl, minor_step, b, h]);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // le_of_mul_le_mul_left_succ :
    //   ∀ c a b, Le ((succ c)*a) ((succ c)*b) → Le a b
    // Induct on both compared values. Successor/successor products expose a
    // common positive addend, which additive order reflection cancels.
    d.theorem(p.le_of_mul_le_mul_left_succ, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let factor = d.succ(c);
        let cancellation_at = |d: &mut NatDev<'_>, x: ExprId| {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let fx = d.mul(factor, x);
            let fy = d.mul(factor, y);
            let hyp = d.le(fx, fy);
            let conclusion = d.le(x, y);
            let body = d.arrow(hyp, conclusion);
            d.pi_fv(y_fv, nat, body)
        };
        let at_zero = |d: &mut NatDev<'_>| {
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let zero = d.zero();
            let fy = d.mul(factor, y);
            let hyp_ty = d.le(zero, fy);
            let h_fv = d.fresh_fvar();
            let body = d.lemma(p.zero_le, &[y]);
            let with_h = d.lam_fv(h_fv, hyp_ty, body);
            d.lam_fv(y_fv, nat, with_h)
        };
        let step_x = |d: &mut NatDev<'_>, x: ExprId, ih: ExprId| {
            let sx = d.succ(x);
            let motive_y = |d: &mut NatDev<'_>, y: ExprId| {
                let fsx = d.mul(factor, sx);
                let fy = d.mul(factor, y);
                let hyp = d.le(fsx, fy);
                let conclusion = d.le(sx, y);
                d.arrow(hyp, conclusion)
            };
            let at_y_zero = |d: &mut NatDev<'_>| {
                let zero = d.zero();
                let fx = d.mul(factor, x);
                let positive_body = d.add(fx, c);
                let positive = d.succ(positive_body);
                let hyp_ty = d.le(positive, zero);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let impossible = d.lemma(p.not_succ_le_zero, &[positive_body, h]);
                let target = d.le(sx, zero);
                let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                let motive = d.kernel().lam(anon, false_ty, target, BinderInfo::Default);
                let level_zero = d.kernel().level_zero();
                let rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                let body = d.apply(rec, &[motive, impossible]);
                d.lam_fv(h_fv, hyp_ty, body)
            };
            let step_y = |d: &mut NatDev<'_>, y: ExprId, _inner_ih: ExprId| {
                let sy = d.succ(y);
                let fx = d.mul(factor, x);
                let fy = d.mul(factor, y);
                let fsx = d.mul(factor, sx);
                let fsy = d.mul(factor, sy);
                let hyp_ty = d.le(fsx, fsy);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);
                let left_common = d.add(factor, fx);
                let right_common = d.add(factor, fy);
                let left_comm = d.lemma(p.add_comm, &[fx, factor]);
                let right_comm = d.lemma(p.add_comm, &[fy, factor]);
                let lower_motive = d.eq_motive(fsx, &|d, lower| d.le(lower, fsy));
                let common_lower = d.transport(fsx, lower_motive, h, left_common, left_comm);
                let upper_motive = d.eq_motive(fsy, &|d, upper| d.le(left_common, upper));
                let common = d.transport(fsy, upper_motive, common_lower, right_common, right_comm);
                let smaller = d.lemma(p.le_of_add_le_add_left, &[factor, fx, fy, common]);
                let prior = d.apply(ih, &[y, smaller]);
                let body = d.lemma(p.le_succ_succ, &[x, y, prior]);
                d.lam_fv(h_fv, hyp_ty, body)
            };
            let y_fv = d.fresh_fvar();
            let y = d.kernel().fvar(y_fv);
            let body = d.induct(&motive_y, &at_y_zero, &step_y, y);
            d.lam_fv(y_fv, nat, body)
        };
        let all_b = d.induct(&cancellation_at, &at_zero, &step_x, a);
        let proof = d.apply(all_b, &[b]);
        let fa = d.mul(factor, a);
        let fb = d.mul(factor, b);
        let hyp = d.le(fa, fb);
        let conclusion = d.le(a, b);
        (d.arrow(hyp, conclusion), proof)
    })?;

    // le_of_mul_le_mul_left :
    //   ∀ c a b, Le one c → Le (c*a) (c*b) → Le a b
    // Expose c as one plus a witness, normalize that sum to a successor, and
    // reuse the structural successor-factor cancellation theorem above.
    d.theorem(p.le_of_mul_le_mul_left, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let positive_ty = d.le(one, c);
        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let ca = d.mul(c, a);
        let cb = d.mul(c, b);
        let scaled_ty = d.le(ca, cb);
        let scaled_fv = d.fresh_fvar();
        let scaled = d.kernel().fvar(scaled_fv);
        let conclusion = d.le(a, b);

        let represented = d.lemma(p.le_dest, &[one, c, positive]);
        let representation_pred = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sum = d.add(one, k);
            let body = d.eq(sum, c);
            d.lam_fv(k_fv, nat, body)
        };
        let level_one = d.level_one();
        let exists = d.kernel().const_(p.logic.exists_, vec![level_one]);
        let represented_ty = d.apply(exists, &[nat, representation_pred]);
        let motive = d
            .kernel()
            .lam(anon, represented_ty, conclusion, BinderInfo::Default);
        let minor = {
            let k_fv = d.fresh_fvar();
            let k = d.kernel().fvar(k_fv);
            let sum = d.add(one, k);
            let e_fv = d.fresh_fvar();
            let e_ty = d.eq(sum, c);
            let e = d.kernel().fvar(e_fv);
            let successor = d.succ(k);

            let zero = d.zero();
            let successor_zero = d.succ(zero);
            let zero_sum = d.add(zero, k);
            let successor_sum = d.add(successor_zero, k);
            let successor_zero_sum = d.succ(zero_sum);
            let successor_k = d.succ(k);
            let h_succ_add = d.lemma(p.succ_add, &[zero, k]);
            let h_zero_add = d.lemma(p.zero_add, &[k]);
            let h_succ_zero_add = d.congr(zero_sum, k, h_zero_add, &|d, x| d.succ(x));
            let (_, sum_eq_successor) = d.chain(
                successor_sum,
                &[
                    (successor_zero_sum, h_succ_add),
                    (successor_k, h_succ_zero_add),
                ],
            );
            let successor_eq_sum = d.symm(sum, successor, sum_eq_successor);
            let (_, successor_eq_c) = d.chain(successor, &[(sum, successor_eq_sum), (c, e)]);
            let c_eq_successor = d.symm(successor, c, successor_eq_c);

            let successor_a = d.mul(successor, a);
            let successor_b = d.mul(successor, b);
            let ca_eq_successor_a = d.congr(c, successor, c_eq_successor, &|d, x| d.mul(x, a));
            let cb_eq_successor_b = d.congr(c, successor, c_eq_successor, &|d, x| d.mul(x, b));
            let lower_motive = d.eq_motive(ca, &|d, lower| d.le(lower, cb));
            let successor_lower =
                d.transport(ca, lower_motive, scaled, successor_a, ca_eq_successor_a);
            let upper_motive = d.eq_motive(cb, &|d, upper| d.le(successor_a, upper));
            let successor_scaled = d.transport(
                cb,
                upper_motive,
                successor_lower,
                successor_b,
                cb_eq_successor_b,
            );
            let body = d.lemma(p.le_of_mul_le_mul_left_succ, &[k, a, b, successor_scaled]);
            let with_e = d.lam_fv(e_fv, e_ty, body);
            d.lam_fv(k_fv, nat, with_e)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);
        let body = d.apply(rec, &[nat, representation_pred, motive, minor, represented]);
        let proof = {
            let with_scaled = d.lam_fv(scaled_fv, scaled_ty, body);
            d.lam_fv(positive_fv, positive_ty, with_scaled)
        };
        let stmt = {
            let with_scaled = d.arrow(scaled_ty, conclusion);
            d.arrow(positive_ty, with_scaled)
        };
        (stmt, proof)
    })?;

    // mul_left_cancel_of_pos :
    //   ∀ c a b, Le one c → Eq (c*a) (c*b) → Eq a b
    // Convert equality to bounds in both directions, reflect each through the
    // proof-positive factor, then apply order antisymmetry.
    d.theorem(p.mul_left_cancel_of_pos, 3, &|d, v| {
        let (c, a, b) = (v[0], v[1], v[2]);
        let one = d.num(1);
        let positive_ty = d.le(one, c);
        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let ca = d.mul(c, a);
        let cb = d.mul(c, b);
        let equality_ty = d.eq(ca, cb);
        let equality_fv = d.fresh_fvar();
        let equality = d.kernel().fvar(equality_fv);

        let ca_le_ca = d.lemma(p.le_refl, &[ca]);
        let upper_motive = d.eq_motive(ca, &|d, upper| d.le(ca, upper));
        let ca_le_cb = d.transport(ca, upper_motive, ca_le_ca, cb, equality);
        let cb_eq_ca = d.symm(ca, cb, equality);
        let cb_le_cb = d.lemma(p.le_refl, &[cb]);
        let reverse_motive = d.eq_motive(cb, &|d, upper| d.le(cb, upper));
        let cb_le_ca = d.transport(cb, reverse_motive, cb_le_cb, ca, cb_eq_ca);
        let a_le_b = d.lemma(p.le_of_mul_le_mul_left, &[c, a, b, positive, ca_le_cb]);
        let b_le_a = d.lemma(p.le_of_mul_le_mul_left, &[c, b, a, positive, cb_le_ca]);
        let body = d.lemma(p.le_antisymm, &[a, b, a_le_b, b_le_a]);
        let conclusion = d.eq(a, b);
        let proof = {
            let with_equality = d.lam_fv(equality_fv, equality_ty, body);
            d.lam_fv(positive_fv, positive_ty, with_equality)
        };
        let stmt = {
            let with_equality = d.arrow(equality_ty, conclusion);
            d.arrow(positive_ty, with_equality)
        };
        (stmt, proof)
    })?;

    // sub_add_cancel : ∀ m n, Le m n → add (sub n m) m = n
    // Induct on the subtrahend. In the successor case, eliminate the bound
    // derivation so both `Le` and `sub` expose matching successor structure.
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let cancellation_at = |d: &mut NatDev<'_>, subtrahend: ExprId| {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let hyp = d.le(subtrahend, n);
            let difference = d.sub(n, subtrahend);
            let restored = d.add(difference, subtrahend);
            let conclusion = d.eq(restored, n);
            let implication = d.arrow(hyp, conclusion);
            let nat = d.nat_ty();
            d.pi_fv(n_fv, nat, implication)
        };
        let stmt = cancellation_at(d, m);
        let proof = d.induct(
            &cancellation_at,
            &|d| {
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let zero = d.zero();
                let hyp_ty = d.le(zero, n);
                let h_fv = d.fresh_fvar();
                let body = d.refl(n);
                let with_h = d.lam_fv(h_fv, hyp_ty, body);
                let nat = d.nat_ty();
                d.lam_fv(n_fv, nat, with_h)
            },
            &|d, j, ih| {
                let sj = d.succ(j);
                let n_fv = d.fresh_fvar();
                let n = d.kernel().fvar(n_fv);
                let hyp_ty = d.le(sj, n);
                let h_fv = d.fresh_fvar();
                let h = d.kernel().fvar(h_fv);

                let le_motive = {
                    let x_fv = d.fresh_fvar();
                    let x = d.kernel().fvar(x_fv);
                    let dom = d.le(sj, x);
                    let difference = d.sub(x, sj);
                    let restored = d.add(difference, sj);
                    let body = d.eq(restored, x);
                    let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
                    d.lam_fv(x_fv, nat, inner)
                };

                let minor_refl = {
                    let difference = d.sub(sj, sj);
                    let start = d.add(difference, sj);
                    let zero = d.zero();
                    let middle = d.add(zero, sj);
                    let h_sub = d.lemma(p.sub_self, &[sj]);
                    let h1 = d.congr(difference, zero, h_sub, &|d, x| d.add(x, sj));
                    let h2 = d.lemma(p.zero_add, &[sj]);
                    let (_end, proof) = d.chain(start, &[(middle, h1), (sj, h2)]);
                    proof
                };

                let minor_step = {
                    let x_fv = d.fresh_fvar();
                    let x = d.kernel().fvar(x_fv);
                    let hx_fv = d.fresh_fvar();
                    let hx_ty = d.le(sj, x);
                    let hx = d.kernel().fvar(hx_fv);
                    let rec_ih_fv = d.fresh_fvar();
                    let difference = d.sub(x, sj);
                    let rec_restored = d.add(difference, sj);
                    let rec_ih_ty = d.eq(rec_restored, x);

                    let sx = d.succ(x);
                    let successor_difference = d.sub(sx, sj);
                    let start = d.add(successor_difference, sj);
                    let prior_difference = d.sub(x, j);
                    let middle = d.add(prior_difference, sj);
                    let h_sub = d.lemma(p.succ_sub_succ, &[x, j]);
                    let h1 = d.congr(successor_difference, prior_difference, h_sub, &|d, t| {
                        d.add(t, sj)
                    });

                    let j_refl = d.const_app(p.le_refl, &[j]);
                    let j_le_sj = d.const_app(p.le_step, &[j, j, j_refl]);
                    let j_le_x = d.lemma(p.le_trans, &[j, sj, x, j_le_sj, hx]);
                    let prior_restored = d.add(prior_difference, j);
                    let restored = d.apply(ih, &[x, j_le_x]);
                    let h2 = d.congr(prior_restored, x, restored, &|d, t| d.succ(t));
                    let (_end, body) = d.chain(start, &[(middle, h1), (sx, h2)]);

                    let with_rec_ih = d.lam_fv(rec_ih_fv, rec_ih_ty, body);
                    let with_hx = d.lam_fv(hx_fv, hx_ty, with_rec_ih);
                    d.lam_fv(x_fv, nat, with_hx)
                };

                let body = d.const_app(p.le_rec, &[sj, le_motive, minor_refl, minor_step, n, h]);
                let with_h = d.lam_fv(h_fv, hyp_ty, body);
                d.lam_fv(n_fv, nat, with_h)
            },
            m,
        );
        let ty = d.pi_fv(m_fv, nat, stmt);
        let value = d.lam_fv(m_fv, nat, proof);
        d.declare_theorem(p.sub_add_cancel, ty, value)?;
    }

    // sub_eq_zero_of_le : ∀ a b, Le a b → sub a b = zero
    d.theorem(p.sub_eq_zero_of_le, 2, &|d, v| {
        let (a, b) = (v[0], v[1]);
        let zero = d.zero();
        let hyp_ty = d.le(a, b);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);
        let motive = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let dom = d.le(a, x);
            let difference = d.sub(a, x);
            let body = d.eq(difference, zero);
            let inner = d.kernel().lam(anon, dom, body, BinderInfo::Default);
            d.lam_fv(x_fv, nat, inner)
        };
        let minor_refl = d.lemma(p.sub_self, &[a]);
        let minor_step = {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let hx_fv = d.fresh_fvar();
            let hx_ty = d.le(a, x);
            let ih_fv = d.fresh_fvar();
            let difference = d.sub(a, x);
            let ih_ty = d.eq(difference, zero);
            let ih = d.kernel().fvar(ih_fv);
            let body = d.congr(difference, zero, ih, &|d, value| d.pred(value));
            let with_ih = d.lam_fv(ih_fv, ih_ty, body);
            let with_hx = d.lam_fv(hx_fv, hx_ty, with_ih);
            d.lam_fv(x_fv, nat, with_hx)
        };
        let body = d.const_app(p.le_rec, &[a, motive, minor_refl, minor_step, b, h]);
        let difference = d.sub(a, b);
        let conclusion = d.eq(difference, zero);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // sub_le_iff_le_add : ∀ x y z, Iff (Le (sub x y) z) (Le x (add z y))
    d.theorem(p.sub_le_iff_le_add, 3, &|d, v| {
        let (x, y, z) = (v[0], v[1], v[2]);
        let difference = d.sub(x, y);
        let sum = d.add(z, y);
        let lhs = d.le(difference, z);
        let rhs = d.le(x, sum);
        let total = d.lemma(p.le_total, &[y, x]);
        let y_le_x = d.le(y, x);
        let x_le_y = d.le(x, y);
        let total_ty = d.const_app(p.logic.or, &[y_le_x, x_le_y]);

        let mp = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let motive = d.kernel().lam(anon, total_ty, rhs, BinderInfo::Default);
            let bounded_minor = {
                let hyx_fv = d.fresh_fvar();
                let hyx = d.kernel().fvar(hyx_fv);
                let restored = d.add(difference, y);
                let restored_eq_x = d.lemma(p.sub_add_cancel, &[y, x, hyx]);
                let shifted = d.lemma(p.add_le_add_right, &[y, difference, z, h]);
                let lower_motive = d.eq_motive(restored, &|d, lower| d.le(lower, sum));
                let body = d.transport(restored, lower_motive, shifted, x, restored_eq_x);
                d.lam_fv(hyx_fv, y_le_x, body)
            };
            let truncated_minor = {
                let hxy_fv = d.fresh_fvar();
                let hxy = d.kernel().fvar(hxy_fv);
                let y_plus_z = d.add(y, z);
                let y_le_y_plus_z = d.lemma(p.le_add_right, &[y, z]);
                let y_plus_z_eq_sum = d.lemma(p.add_comm, &[y, z]);
                let upper_motive = d.eq_motive(y_plus_z, &|d, upper| d.le(y, upper));
                let y_le_sum =
                    d.transport(y_plus_z, upper_motive, y_le_y_plus_z, sum, y_plus_z_eq_sum);
                let body = d.lemma(p.le_trans, &[x, y, sum, hxy, y_le_sum]);
                d.lam_fv(hxy_fv, x_le_y, body)
            };
            let rec = d.kernel().const_(p.logic.or_rec, vec![]);
            let body = d.apply(
                rec,
                &[
                    y_le_x,
                    x_le_y,
                    motive,
                    bounded_minor,
                    truncated_minor,
                    total,
                ],
            );
            d.lam_fv(h_fv, lhs, body)
        };

        let mpr = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let motive = d.kernel().lam(anon, total_ty, lhs, BinderInfo::Default);
            let bounded_minor = {
                let hyx_fv = d.fresh_fvar();
                let hyx = d.kernel().fvar(hyx_fv);
                let restored = d.add(difference, y);
                let restored_eq_x = d.lemma(p.sub_add_cancel, &[y, x, hyx]);
                let x_eq_restored = d.symm(restored, x, restored_eq_x);
                let lower_motive = d.eq_motive(x, &|d, lower| d.le(lower, sum));
                let restored_le_sum = d.transport(x, lower_motive, h, restored, x_eq_restored);
                let body = d.lemma(
                    p.le_of_add_le_add_right,
                    &[y, difference, z, restored_le_sum],
                );
                d.lam_fv(hyx_fv, y_le_x, body)
            };
            let truncated_minor = {
                let hxy_fv = d.fresh_fvar();
                let hxy = d.kernel().fvar(hxy_fv);
                let zero = d.zero();
                let zero_le_z = d.lemma(p.zero_le, &[z]);
                let difference_eq_zero = d.lemma(p.sub_eq_zero_of_le, &[x, y, hxy]);
                let zero_eq_difference = d.symm(difference, zero, difference_eq_zero);
                let lower_motive = d.eq_motive(zero, &|d, lower| d.le(lower, z));
                let body = d.transport(
                    zero,
                    lower_motive,
                    zero_le_z,
                    difference,
                    zero_eq_difference,
                );
                d.lam_fv(hxy_fv, x_le_y, body)
            };
            let rec = d.kernel().const_(p.logic.or_rec, vec![]);
            let body = d.apply(
                rec,
                &[
                    y_le_x,
                    x_le_y,
                    motive,
                    bounded_minor,
                    truncated_minor,
                    total,
                ],
            );
            d.lam_fv(h_fv, rhs, body)
        };
        let stmt = d.const_app(p.logic.iff, &[lhs, rhs]);
        let proof = d.const_app(p.logic.iff_intro, &[lhs, rhs, mp, mpr]);
        (stmt, proof)
    })?;

    // mul_sub_left_distrib : ∀ b q a, Le a q → b*(q-a) = b*q-b*a
    // Rather than postulating monotonicity, construct the scaled difference,
    // prove it restores `b*q`, transport the corresponding bound, and cancel
    // the common right summand.
    d.theorem(p.mul_sub_left_distrib, 3, &|d, v| {
        let (b, q, a) = (v[0], v[1], v[2]);
        let hyp_ty = d.le(a, q);
        let h_fv = d.fresh_fvar();
        let h = d.kernel().fvar(h_fv);

        let difference = d.sub(q, a);
        let restored = d.add(difference, a);
        let h_restore = d.lemma(p.sub_add_cancel, &[a, q, h]);
        let b_difference = d.mul(b, difference);
        let ba = d.mul(b, a);
        let bq = d.mul(b, q);
        let scaled_sum = d.mul(b, restored);
        let sum = d.add(b_difference, ba);
        let h_distribute = d.lemma(p.left_distrib, &[b, difference, a]);
        let h_distribute_rev = d.symm(scaled_sum, sum, h_distribute);
        let h_scaled_restore = d.congr(restored, q, h_restore, &|d, x| d.mul(b, x));
        let (_end, sum_eq_bq) = d.chain(
            sum,
            &[(scaled_sum, h_distribute_rev), (bq, h_scaled_restore)],
        );

        let reordered_sum = d.add(ba, b_difference);
        let ba_le_reordered = d.lemma(p.le_add_right, &[ba, b_difference]);
        let h_comm = d.lemma(p.add_comm, &[ba, b_difference]);
        let (_end, reordered_eq_bq) = d.chain(reordered_sum, &[(sum, h_comm), (bq, sum_eq_bq)]);
        let le_motive = d.eq_motive(reordered_sum, &|d, x| d.le(ba, x));
        let ba_le_bq = d.transport(
            reordered_sum,
            le_motive,
            ba_le_reordered,
            bq,
            reordered_eq_bq,
        );

        let scaled_difference = d.sub(bq, ba);
        let scaled_restored = d.add(scaled_difference, ba);
        let h_sub_restore = d.lemma(p.sub_add_cancel, &[ba, bq, ba_le_bq]);
        let h_sub_restore_rev = d.symm(scaled_restored, bq, h_sub_restore);
        let (_end, common_sum) = d.chain(
            sum,
            &[(bq, sum_eq_bq), (scaled_restored, h_sub_restore_rev)],
        );
        let body = d.lemma(
            p.add_right_cancel,
            &[b_difference, scaled_difference, ba, common_sum],
        );
        let conclusion = d.eq(b_difference, scaled_difference);
        let stmt = d.arrow(hyp_ty, conclusion);
        let proof = d.lam_fv(h_fv, hyp_ty, body);
        (stmt, proof)
    })?;

    // The total Nat identity follows by totality. The bounded branch is the
    // theorem above; in the reverse-order branch both truncated differences
    // are zero, with multiplication monotonicity supplying the scaled bound.
    d.theorem(p.mul_sub_left_distrib_total, 3, &|d, v| {
        let (b, q, a) = (v[0], v[1], v[2]);
        let difference = d.sub(q, a);
        let lhs = d.mul(b, difference);
        let bq = d.mul(b, q);
        let ba = d.mul(b, a);
        let rhs = d.sub(bq, ba);
        let target = d.eq(lhs, rhs);
        let q_le_a = d.le(q, a);
        let a_le_q = d.le(a, q);
        let total_ty = d.const_app(p.logic.or, &[q_le_a, a_le_q]);
        let total = d.lemma(p.le_total, &[q, a]);
        let anon = d.anon_name();
        let motive = d.kernel().lam(anon, total_ty, target, BinderInfo::Default);
        let truncated_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let zero = d.zero();
            let difference_zero = d.lemma(p.sub_eq_zero_of_le, &[q, a, h]);
            let lhs_to_bzero = d.congr(difference, zero, difference_zero, &|d, x| d.mul(b, x));
            let bzero = d.mul(b, zero);
            let bzero_zero = d.lemma(p.mul_zero, &[b]);
            let lhs_zero = d.trans(lhs, bzero, zero, lhs_to_bzero, bzero_zero);
            let scaled = d.lemma(p.mul_le_mul_left, &[b, q, a, h]);
            let rhs_zero = d.lemma(p.sub_eq_zero_of_le, &[bq, ba, scaled]);
            let zero_rhs = d.symm(rhs, zero, rhs_zero);
            let body = d.trans(lhs, zero, rhs, lhs_zero, zero_rhs);
            d.lam_fv(h_fv, q_le_a, body)
        };
        let bounded_minor = {
            let h_fv = d.fresh_fvar();
            let h = d.kernel().fvar(h_fv);
            let body = d.lemma(p.mul_sub_left_distrib, &[b, q, a, h]);
            d.lam_fv(h_fv, a_le_q, body)
        };
        let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
        let proof = d.apply(
            or_rec,
            &[
                q_le_a,
                a_le_q,
                motive,
                truncated_minor,
                bounded_minor,
                total,
            ],
        );
        (target, proof)
    })?;

    // add_sub_cancel_left : ∀ m n, (m+n)-m = n. Restore the subtrahend,
    // commute the original sum, then cancel the common right summand.
    d.theorem(p.add_sub_cancel_left, 2, &|d, v| {
        let (m, n) = (v[0], v[1]);
        let sum = d.add(m, n);
        let difference = d.sub(sum, m);
        let restored = d.add(difference, m);
        let m_le_sum = d.lemma(p.le_add_right, &[m, n]);
        let restore = d.lemma(p.sub_add_cancel, &[m, sum, m_le_sum]);
        let reordered = d.add(n, m);
        let commute = d.lemma(p.add_comm, &[m, n]);
        let (_, common_sum) = d.chain(restored, &[(sum, restore), (reordered, commute)]);
        let proof = d.lemma(p.add_right_cancel, &[difference, n, m, common_sum]);
        (d.eq(difference, n), proof)
    })?;
    Ok(())
}

/// Relational Euclidean division with constructive existence for every
/// positive divisor. The quotient and remainder are proof witnesses rather
/// than trusted computations.
fn declare_euclidean_division(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();
    let level_one = d.level_one();

    // divMod d n q r := n = d*q+r ∧ r<d
    {
        let divisor_fv = d.fresh_fvar();
        let divisor = d.kernel().fvar(divisor_fv);
        let dividend_fv = d.fresh_fvar();
        let dividend = d.kernel().fvar(dividend_fv);
        let quotient_fv = d.fresh_fvar();
        let quotient = d.kernel().fvar(quotient_fv);
        let remainder_fv = d.fresh_fvar();
        let remainder = d.kernel().fvar(remainder_fv);
        let product = d.mul(divisor, quotient);
        let reconstructed = d.add(product, remainder);
        let equation = d.eq(dividend, reconstructed);
        let bound = d.lt(remainder, divisor);
        let body = d.const_app(p.logic.and, &[equation, bound]);
        let value = {
            let with_remainder = d.lam_fv(remainder_fv, nat, body);
            let with_quotient = d.lam_fv(quotient_fv, nat, with_remainder);
            let with_dividend = d.lam_fv(dividend_fv, nat, with_quotient);
            d.lam_fv(divisor_fv, nat, with_dividend)
        };
        let ty = {
            let with_remainder = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            let with_quotient = d
                .kernel()
                .pi(anon, nat, with_remainder, BinderInfo::Default);
            let with_dividend = d.kernel().pi(anon, nat, with_quotient, BinderInfo::Default);
            d.kernel().pi(anon, nat, with_dividend, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.div_mod,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(7),
        })?;
    }

    // div_mod_exists : ∀ d n, Le one d → ∃ q r, divMod d n q r
    d.theorem(p.div_mod_exists, 2, &|d, v| {
        let (divisor, dividend) = (v[0], v[1]);
        let zero = d.zero();
        let one = d.num(1);
        let positive_ty = d.le(one, divisor);
        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);

        let exists_at = |d: &mut NatDev<'_>, n: ExprId| {
            let quotient_fv = d.fresh_fvar();
            let quotient = d.kernel().fvar(quotient_fv);
            let remainder_fv = d.fresh_fvar();
            let remainder = d.kernel().fvar(remainder_fv);
            let relation = d.div_mod(divisor, n, quotient, remainder);
            let remainder_predicate = d.lam_fv(remainder_fv, nat, relation);
            let exists = d.kernel().const_(p.logic.exists_, vec![level_one]);
            let remainder_exists = d.apply(exists, &[nat, remainder_predicate]);
            let quotient_predicate = d.lam_fv(quotient_fv, nat, remainder_exists);
            d.apply(exists, &[nat, quotient_predicate])
        };
        let introduce = |d: &mut NatDev<'_>,
                         n: ExprId,
                         quotient: ExprId,
                         remainder: ExprId,
                         relation_proof: ExprId| {
            let remainder_fv = d.fresh_fvar();
            let remainder_var = d.kernel().fvar(remainder_fv);
            let relation = d.div_mod(divisor, n, quotient, remainder_var);
            let remainder_predicate = d.lam_fv(remainder_fv, nat, relation);
            let intro = d.kernel().const_(p.logic.exists_intro, vec![level_one]);
            let remainder_exists = d.apply(
                intro,
                &[nat, remainder_predicate, remainder, relation_proof],
            );

            let quotient_fv = d.fresh_fvar();
            let quotient_var = d.kernel().fvar(quotient_fv);
            let inner_remainder_fv = d.fresh_fvar();
            let inner_remainder = d.kernel().fvar(inner_remainder_fv);
            let inner_relation = d.div_mod(divisor, n, quotient_var, inner_remainder);
            let inner_predicate = d.lam_fv(inner_remainder_fv, nat, inner_relation);
            let exists = d.kernel().const_(p.logic.exists_, vec![level_one]);
            let inner_exists = d.apply(exists, &[nat, inner_predicate]);
            let quotient_predicate = d.lam_fv(quotient_fv, nat, inner_exists);
            d.apply(
                intro,
                &[nat, quotient_predicate, quotient, remainder_exists],
            )
        };

        let motive = |d: &mut NatDev<'_>, n: ExprId| exists_at(d, n);
        let base = |d: &mut NatDev<'_>| {
            let product = d.mul(divisor, zero);
            let reconstructed = d.add(product, zero);
            let equation_ty = d.eq(zero, reconstructed);
            let bound_ty = d.lt(zero, divisor);
            let equation = d.refl(zero);
            let relation_proof = d.const_app(
                p.logic.and_intro,
                &[equation_ty, bound_ty, equation, positive],
            );
            introduce(d, zero, zero, zero, relation_proof)
        };
        let step = |d: &mut NatDev<'_>, n: ExprId, ih: ExprId| {
            let sn = d.succ(n);
            let target = exists_at(d, sn);
            let source = exists_at(d, n);
            let outer_motive = d.kernel().lam(anon, source, target, BinderInfo::Default);

            let outer_minor = {
                let quotient_fv = d.fresh_fvar();
                let quotient = d.kernel().fvar(quotient_fv);
                let remainder_fv = d.fresh_fvar();
                let remainder = d.kernel().fvar(remainder_fv);
                let source_relation = d.div_mod(divisor, n, quotient, remainder);
                let remainder_predicate = d.lam_fv(remainder_fv, nat, source_relation);
                let exists = d.kernel().const_(p.logic.exists_, vec![level_one]);
                let remainder_exists_ty = d.apply(exists, &[nat, remainder_predicate]);
                let remainder_exists_fv = d.fresh_fvar();
                let remainder_exists = d.kernel().fvar(remainder_exists_fv);

                let inner_motive =
                    d.kernel()
                        .lam(anon, remainder_exists_ty, target, BinderInfo::Default);
                let inner_minor = {
                    let r_fv = d.fresh_fvar();
                    let r = d.kernel().fvar(r_fv);
                    let relation_ty = d.div_mod(divisor, n, quotient, r);
                    let relation_fv = d.fresh_fvar();
                    let relation = d.kernel().fvar(relation_fv);
                    let product = d.mul(divisor, quotient);
                    let reconstructed = d.add(product, r);
                    let equation_ty = d.eq(n, reconstructed);
                    let bound_ty = d.lt(r, divisor);
                    let relation_motive =
                        d.kernel()
                            .lam(anon, relation_ty, target, BinderInfo::Default);
                    let relation_minor = {
                        let equation_fv = d.fresh_fvar();
                        let equation = d.kernel().fvar(equation_fv);
                        let bound_fv = d.fresh_fvar();
                        let bound = d.kernel().fvar(bound_fv);
                        let sr = d.succ(r);
                        let strict_ty = d.lt(sr, divisor);
                        let equal_ty = d.eq(sr, divisor);
                        let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
                        let split = d.lemma(p.lt_or_eq_of_le, &[sr, divisor, bound]);
                        let split_motive =
                            d.kernel().lam(anon, split_ty, target, BinderInfo::Default);

                        let strict_minor = {
                            let strict_fv = d.fresh_fvar();
                            let strict = d.kernel().fvar(strict_fv);
                            let next_reconstructed = d.add(product, sr);
                            let next_equation_ty = d.eq(sn, next_reconstructed);
                            let next_equation =
                                d.congr(n, reconstructed, equation, &|d, x| d.succ(x));
                            let next_relation = d.const_app(
                                p.logic.and_intro,
                                &[next_equation_ty, strict_ty, next_equation, strict],
                            );
                            let body = introduce(d, sn, quotient, sr, next_relation);
                            d.lam_fv(strict_fv, strict_ty, body)
                        };
                        let equal_minor = {
                            let equal_fv = d.fresh_fvar();
                            let equal = d.kernel().fvar(equal_fv);
                            let sq = d.succ(quotient);
                            let next_product = d.mul(divisor, sq);
                            let next_reconstructed = d.add(next_product, zero);
                            let next_equation_ty = d.eq(sn, next_reconstructed);
                            let successor_reconstructed = d.succ(reconstructed);
                            let lifted = d.congr(n, reconstructed, equation, &|d, x| d.succ(x));
                            let product_plus_sr = d.add(product, sr);
                            let successor_eq_product_plus_sr = d.refl(successor_reconstructed);
                            let product_plus_divisor = d.add(product, divisor);
                            let replace_remainder =
                                d.congr(sr, divisor, equal, &|d, x| d.add(product, x));
                            let product_plus_divisor_eq_next = d.refl(product_plus_divisor);
                            let (_, next_equation) = d.chain(
                                sn,
                                &[
                                    (successor_reconstructed, lifted),
                                    (product_plus_sr, successor_eq_product_plus_sr),
                                    (product_plus_divisor, replace_remainder),
                                    (next_reconstructed, product_plus_divisor_eq_next),
                                ],
                            );
                            let zero_bound_ty = d.lt(zero, divisor);
                            let next_relation = d.const_app(
                                p.logic.and_intro,
                                &[next_equation_ty, zero_bound_ty, next_equation, positive],
                            );
                            let body = introduce(d, sn, sq, zero, next_relation);
                            d.lam_fv(equal_fv, equal_ty, body)
                        };
                        let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                        let body = d.apply(
                            or_rec,
                            &[
                                strict_ty,
                                equal_ty,
                                split_motive,
                                strict_minor,
                                equal_minor,
                                split,
                            ],
                        );
                        let with_bound = d.lam_fv(bound_fv, bound_ty, body);
                        d.lam_fv(equation_fv, equation_ty, with_bound)
                    };
                    let level_zero = d.kernel().level_zero();
                    let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
                    let body = d.apply(
                        and_rec,
                        &[
                            equation_ty,
                            bound_ty,
                            relation_motive,
                            relation_minor,
                            relation,
                        ],
                    );
                    let with_relation = d.lam_fv(relation_fv, relation_ty, body);
                    d.lam_fv(r_fv, nat, with_relation)
                };
                let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);
                let inner = d.apply(
                    exists_rec,
                    &[
                        nat,
                        remainder_predicate,
                        inner_motive,
                        inner_minor,
                        remainder_exists,
                    ],
                );
                let with_remainder_exists =
                    d.lam_fv(remainder_exists_fv, remainder_exists_ty, inner);
                d.lam_fv(quotient_fv, nat, with_remainder_exists)
            };
            let quotient_fv = d.fresh_fvar();
            let quotient = d.kernel().fvar(quotient_fv);
            let remainder_fv = d.fresh_fvar();
            let remainder = d.kernel().fvar(remainder_fv);
            let relation = d.div_mod(divisor, n, quotient, remainder);
            let remainder_predicate = d.lam_fv(remainder_fv, nat, relation);
            let exists = d.kernel().const_(p.logic.exists_, vec![level_one]);
            let remainder_exists = d.apply(exists, &[nat, remainder_predicate]);
            let quotient_predicate = d.lam_fv(quotient_fv, nat, remainder_exists);
            let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![level_one]);
            d.apply(
                exists_rec,
                &[nat, quotient_predicate, outer_motive, outer_minor, ih],
            )
        };
        let body = d.induct(&motive, &base, &step, dividend);
        let conclusion = exists_at(d, dividend);
        let stmt = d.arrow(positive_ty, conclusion);
        let proof = d.lam_fv(positive_fv, positive_ty, body);
        (stmt, proof)
    })?;

    // div_mod_unique :
    //   ∀ d n q₁ r₁ q₂ r₂,
    //     divMod d n q₁ r₁ → divMod d n q₂ r₂ → q₁ = q₂ ∧ r₁ = r₂
    // Compare the quotients by totality. A strict gap places one reconstructed
    // dividend strictly below the other because its remainder is below the
    // divisor, contradicting their common value. Equal quotients leave equal
    // remainders by cancellation of the common product.
    d.theorem(p.div_mod_unique, 6, &|d, v| {
        let (divisor, dividend, q1, r1, q2, r2) = (v[0], v[1], v[2], v[3], v[4], v[5]);
        let relation1_ty = d.div_mod(divisor, dividend, q1, r1);
        let relation2_ty = d.div_mod(divisor, dividend, q2, r2);
        let quotient_eq_ty = d.eq(q1, q2);
        let remainder_eq_ty = d.eq(r1, r2);
        let target = d.const_app(p.logic.and, &[quotient_eq_ty, remainder_eq_ty]);

        let relation1_fv = d.fresh_fvar();
        let relation1 = d.kernel().fvar(relation1_fv);
        let relation2_fv = d.fresh_fvar();
        let relation2 = d.kernel().fvar(relation2_fv);

        let product1 = d.mul(divisor, q1);
        let product2 = d.mul(divisor, q2);
        let sum1 = d.add(product1, r1);
        let sum2 = d.add(product2, r2);
        let equation1_ty = d.eq(dividend, sum1);
        let equation2_ty = d.eq(dividend, sum2);
        let bound1_ty = d.lt(r1, divisor);
        let bound2_ty = d.lt(r2, divisor);

        let relation2_to_target = d.arrow(relation2_ty, target);
        let relation1_motive =
            d.kernel()
                .lam(anon, relation1_ty, relation2_to_target, BinderInfo::Default);
        let relation1_minor = {
            let equation1_fv = d.fresh_fvar();
            let equation1 = d.kernel().fvar(equation1_fv);
            let bound1_fv = d.fresh_fvar();
            let bound1 = d.kernel().fvar(bound1_fv);

            let relation2_motive = d
                .kernel()
                .lam(anon, relation2_ty, target, BinderInfo::Default);
            let relation2_minor = {
                let equation2_fv = d.fresh_fvar();
                let equation2 = d.kernel().fvar(equation2_fv);
                let bound2_fv = d.fresh_fvar();
                let bound2 = d.kernel().fvar(bound2_fv);

                let equation1_rev = d.symm(dividend, sum1, equation1);
                let (_, sums_equal) =
                    d.chain(sum1, &[(dividend, equation1_rev), (sum2, equation2)]);
                let order12_ty = d.le(q1, q2);
                let order21_ty = d.le(q2, q1);
                let order_split_ty = d.const_app(p.logic.or, &[order12_ty, order21_ty]);
                let order_split = d.lemma(p.le_total, &[q1, q2]);
                let order_motive =
                    d.kernel()
                        .lam(anon, order_split_ty, quotient_eq_ty, BinderInfo::Default);

                let q1_le_q2_minor = {
                    let order_fv = d.fresh_fvar();
                    let order = d.kernel().fvar(order_fv);
                    let strict_ty = d.lt(q1, q2);
                    let equal_ty = d.eq(q1, q2);
                    let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
                    let split = d.lemma(p.lt_or_eq_of_le, &[q1, q2, order]);
                    let split_motive =
                        d.kernel()
                            .lam(anon, split_ty, quotient_eq_ty, BinderInfo::Default);
                    let strict_minor = {
                        let strict_fv = d.fresh_fvar();
                        let strict = d.kernel().fvar(strict_fv);
                        let product1_plus_divisor = d.add(product1, divisor);
                        let sum1_lt_next =
                            d.lemma(p.add_lt_add_left, &[product1, r1, divisor, bound1]);
                        let sq1 = d.succ(q1);
                        let next_le_product2 =
                            d.lemma(p.mul_le_mul_left, &[divisor, sq1, q2, strict]);
                        let sum1_lt_product2 = d.lemma(
                            p.lt_of_lt_of_le,
                            &[
                                sum1,
                                product1_plus_divisor,
                                product2,
                                sum1_lt_next,
                                next_le_product2,
                            ],
                        );
                        let product2_le_sum2 = d.lemma(p.le_add_right, &[product2, r2]);
                        let sum1_lt_sum2 = d.lemma(
                            p.lt_of_lt_of_le,
                            &[sum1, product2, sum2, sum1_lt_product2, product2_le_sum2],
                        );
                        let sums_equal_rev = d.symm(sum1, sum2, sums_equal);
                        let loop_motive = d.eq_motive(sum2, &|d, x| d.lt(sum1, x));
                        let impossible_strict =
                            d.transport(sum2, loop_motive, sum1_lt_sum2, sum1, sums_equal_rev);
                        let no_loop = d.lemma(p.lt_irrefl, &[sum1]);
                        let impossible = d.apply(no_loop, &[impossible_strict]);
                        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                        let false_motive =
                            d.kernel()
                                .lam(anon, false_ty, quotient_eq_ty, BinderInfo::Default);
                        let level_zero = d.kernel().level_zero();
                        let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                        let body = d.apply(false_rec, &[false_motive, impossible]);
                        d.lam_fv(strict_fv, strict_ty, body)
                    };
                    let equal_minor = {
                        let equal_fv = d.fresh_fvar();
                        let equal = d.kernel().fvar(equal_fv);
                        d.lam_fv(equal_fv, equal_ty, equal)
                    };
                    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                    let body = d.apply(
                        or_rec,
                        &[
                            strict_ty,
                            equal_ty,
                            split_motive,
                            strict_minor,
                            equal_minor,
                            split,
                        ],
                    );
                    d.lam_fv(order_fv, order12_ty, body)
                };

                let q2_le_q1_minor = {
                    let order_fv = d.fresh_fvar();
                    let order = d.kernel().fvar(order_fv);
                    let strict_ty = d.lt(q2, q1);
                    let equal_ty = d.eq(q2, q1);
                    let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
                    let split = d.lemma(p.lt_or_eq_of_le, &[q2, q1, order]);
                    let split_motive =
                        d.kernel()
                            .lam(anon, split_ty, quotient_eq_ty, BinderInfo::Default);
                    let strict_minor = {
                        let strict_fv = d.fresh_fvar();
                        let strict = d.kernel().fvar(strict_fv);
                        let product2_plus_divisor = d.add(product2, divisor);
                        let sum2_lt_next =
                            d.lemma(p.add_lt_add_left, &[product2, r2, divisor, bound2]);
                        let sq2 = d.succ(q2);
                        let next_le_product1 =
                            d.lemma(p.mul_le_mul_left, &[divisor, sq2, q1, strict]);
                        let sum2_lt_product1 = d.lemma(
                            p.lt_of_lt_of_le,
                            &[
                                sum2,
                                product2_plus_divisor,
                                product1,
                                sum2_lt_next,
                                next_le_product1,
                            ],
                        );
                        let product1_le_sum1 = d.lemma(p.le_add_right, &[product1, r1]);
                        let sum2_lt_sum1 = d.lemma(
                            p.lt_of_lt_of_le,
                            &[sum2, product1, sum1, sum2_lt_product1, product1_le_sum1],
                        );
                        let loop_motive = d.eq_motive(sum1, &|d, x| d.lt(sum2, x));
                        let impossible_strict =
                            d.transport(sum1, loop_motive, sum2_lt_sum1, sum2, sums_equal);
                        let no_loop = d.lemma(p.lt_irrefl, &[sum2]);
                        let impossible = d.apply(no_loop, &[impossible_strict]);
                        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                        let false_motive =
                            d.kernel()
                                .lam(anon, false_ty, quotient_eq_ty, BinderInfo::Default);
                        let level_zero = d.kernel().level_zero();
                        let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                        let body = d.apply(false_rec, &[false_motive, impossible]);
                        d.lam_fv(strict_fv, strict_ty, body)
                    };
                    let equal_minor = {
                        let equal_fv = d.fresh_fvar();
                        let equal = d.kernel().fvar(equal_fv);
                        let body = d.symm(q2, q1, equal);
                        d.lam_fv(equal_fv, equal_ty, body)
                    };
                    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                    let body = d.apply(
                        or_rec,
                        &[
                            strict_ty,
                            equal_ty,
                            split_motive,
                            strict_minor,
                            equal_minor,
                            split,
                        ],
                    );
                    d.lam_fv(order_fv, order21_ty, body)
                };

                let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                let quotient_eq = d.apply(
                    or_rec,
                    &[
                        order12_ty,
                        order21_ty,
                        order_motive,
                        q1_le_q2_minor,
                        q2_le_q1_minor,
                        order_split,
                    ],
                );
                let products_equal = d.congr(q1, q2, quotient_eq, &|d, q| d.mul(divisor, q));
                let product1_sum2 = d.add(product1, r2);
                let replace_product =
                    d.congr(product1, product2, products_equal, &|d, x| d.add(x, r2));
                let replace_product_rev = d.symm(product1_sum2, sum2, replace_product);
                let (_, common_sums) = d.chain(
                    sum1,
                    &[(sum2, sums_equal), (product1_sum2, replace_product_rev)],
                );
                let remainder_eq = d.lemma(p.add_left_cancel, &[product1, r1, r2, common_sums]);
                let body = d.const_app(
                    p.logic.and_intro,
                    &[quotient_eq_ty, remainder_eq_ty, quotient_eq, remainder_eq],
                );
                let with_bound2 = d.lam_fv(bound2_fv, bound2_ty, body);
                d.lam_fv(equation2_fv, equation2_ty, with_bound2)
            };
            let level_zero = d.kernel().level_zero();
            let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
            let body = d.apply(
                and_rec,
                &[
                    equation2_ty,
                    bound2_ty,
                    relation2_motive,
                    relation2_minor,
                    relation2,
                ],
            );
            let with_relation2 = d.lam_fv(relation2_fv, relation2_ty, body);
            let with_bound1 = d.lam_fv(bound1_fv, bound1_ty, with_relation2);
            d.lam_fv(equation1_fv, equation1_ty, with_bound1)
        };
        let level_zero = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
        let body = d.apply(
            and_rec,
            &[
                equation1_ty,
                bound1_ty,
                relation1_motive,
                relation1_minor,
                relation1,
            ],
        );
        let relation2_to_target = d.arrow(relation2_ty, target);
        let stmt = d.arrow(relation1_ty, relation2_to_target);
        let proof = d.lam_fv(relation1_fv, relation1_ty, body);
        (stmt, proof)
    })?;

    // div_mod_bounds :
    //   ∀ d n q r, divMod d n q r → d*q ≤ n ∧ n < d*(succ q)
    // The relation equation supplies the lower bound by inclusion of the
    // remainder. Its strict remainder bound supplies the upper endpoint,
    // since `d*q+d` reduces to `d*(succ q)`.
    d.theorem(p.div_mod_bounds, 4, &|d, v| {
        let (divisor, dividend, quotient, remainder) = (v[0], v[1], v[2], v[3]);
        let relation_ty = d.div_mod(divisor, dividend, quotient, remainder);
        let product = d.mul(divisor, quotient);
        let reconstructed = d.add(product, remainder);
        let next_quotient = d.succ(quotient);
        let next_product = d.mul(divisor, next_quotient);
        let lower_ty = d.le(product, dividend);
        let upper_ty = d.lt(dividend, next_product);
        let target = d.const_app(p.logic.and, &[lower_ty, upper_ty]);

        let relation_fv = d.fresh_fvar();
        let relation = d.kernel().fvar(relation_fv);
        let equation_ty = d.eq(dividend, reconstructed);
        let bound_ty = d.lt(remainder, divisor);
        let relation_motive = d
            .kernel()
            .lam(anon, relation_ty, target, BinderInfo::Default);
        let relation_minor = {
            let equation_fv = d.fresh_fvar();
            let equation = d.kernel().fvar(equation_fv);
            let bound_fv = d.fresh_fvar();
            let bound = d.kernel().fvar(bound_fv);
            let reconstructed_eq_dividend = d.symm(dividend, reconstructed, equation);

            let product_le_reconstructed = d.lemma(p.le_add_right, &[product, remainder]);
            let lower_motive = d.eq_motive(reconstructed, &|d, upper| d.le(product, upper));
            let lower = d.transport(
                reconstructed,
                lower_motive,
                product_le_reconstructed,
                dividend,
                reconstructed_eq_dividend,
            );

            let reconstructed_lt_next =
                d.lemma(p.add_lt_add_left, &[product, remainder, divisor, bound]);
            let upper_motive = d.eq_motive(reconstructed, &|d, lower| d.lt(lower, next_product));
            let upper = d.transport(
                reconstructed,
                upper_motive,
                reconstructed_lt_next,
                dividend,
                reconstructed_eq_dividend,
            );
            let body = d.const_app(p.logic.and_intro, &[lower_ty, upper_ty, lower, upper]);
            let with_bound = d.lam_fv(bound_fv, bound_ty, body);
            d.lam_fv(equation_fv, equation_ty, with_bound)
        };
        let level_zero = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
        let body = d.apply(
            and_rec,
            &[
                equation_ty,
                bound_ty,
                relation_motive,
                relation_minor,
                relation,
            ],
        );
        let stmt = d.arrow(relation_ty, target);
        let proof = d.lam_fv(relation_fv, relation_ty, body);
        (stmt, proof)
    })?;

    // div_mod_mul_le_iff :
    //   ∀ d n q r s, divMod d n q r → (d*s ≤ n ↔ s ≤ q)
    // The reverse direction is multiplication monotonicity followed by the
    // lower floor bound. For the forward direction, q<s would put n strictly
    // below d*(succ q)≤d*s≤n, contradicting irreflexivity.
    d.theorem(p.div_mod_mul_le_iff, 5, &|d, v| {
        let (divisor, dividend, quotient, remainder, candidate) = (v[0], v[1], v[2], v[3], v[4]);
        let relation_ty = d.div_mod(divisor, dividend, quotient, remainder);
        let candidate_product = d.mul(divisor, candidate);
        let quotient_product = d.mul(divisor, quotient);
        let product_bound_ty = d.le(candidate_product, dividend);
        let quotient_bound_ty = d.le(candidate, quotient);
        let target = d.const_app(p.logic.iff, &[product_bound_ty, quotient_bound_ty]);

        let relation_fv = d.fresh_fvar();
        let relation = d.kernel().fvar(relation_fv);
        let bounds = d.lemma(
            p.div_mod_bounds,
            &[divisor, dividend, quotient, remainder, relation],
        );
        let next_quotient = d.succ(quotient);
        let next_product = d.mul(divisor, next_quotient);
        let lower_ty = d.le(quotient_product, dividend);
        let upper_ty = d.lt(dividend, next_product);
        let bounds_ty = d.const_app(p.logic.and, &[lower_ty, upper_ty]);
        let bounds_motive = d.kernel().lam(anon, bounds_ty, target, BinderInfo::Default);
        let bounds_minor = {
            let lower_fv = d.fresh_fvar();
            let lower = d.kernel().fvar(lower_fv);
            let upper_fv = d.fresh_fvar();
            let upper = d.kernel().fvar(upper_fv);

            let forward = {
                let product_bound_fv = d.fresh_fvar();
                let product_bound = d.kernel().fvar(product_bound_fv);
                let reverse_order_ty = d.le(quotient, candidate);
                let order_split_ty =
                    d.const_app(p.logic.or, &[quotient_bound_ty, reverse_order_ty]);
                let order_split = d.lemma(p.le_total, &[candidate, quotient]);
                let order_motive =
                    d.kernel()
                        .lam(anon, order_split_ty, quotient_bound_ty, BinderInfo::Default);
                let ordered_minor = {
                    let ordered_fv = d.fresh_fvar();
                    let ordered = d.kernel().fvar(ordered_fv);
                    d.lam_fv(ordered_fv, quotient_bound_ty, ordered)
                };
                let reverse_minor = {
                    let reverse_fv = d.fresh_fvar();
                    let reverse = d.kernel().fvar(reverse_fv);
                    let strict_ty = d.lt(quotient, candidate);
                    let equal_ty = d.eq(quotient, candidate);
                    let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
                    let split = d.lemma(p.lt_or_eq_of_le, &[quotient, candidate, reverse]);
                    let split_motive =
                        d.kernel()
                            .lam(anon, split_ty, quotient_bound_ty, BinderInfo::Default);
                    let strict_minor = {
                        let strict_fv = d.fresh_fvar();
                        let strict = d.kernel().fvar(strict_fv);
                        let next_le_candidate = d.lemma(
                            p.mul_le_mul_left,
                            &[divisor, next_quotient, candidate, strict],
                        );
                        let dividend_lt_candidate_product = d.lemma(
                            p.lt_of_lt_of_le,
                            &[
                                dividend,
                                next_product,
                                candidate_product,
                                upper,
                                next_le_candidate,
                            ],
                        );
                        let impossible_loop = d.lemma(
                            p.lt_of_lt_of_le,
                            &[
                                dividend,
                                candidate_product,
                                dividend,
                                dividend_lt_candidate_product,
                                product_bound,
                            ],
                        );
                        let no_loop = d.lemma(p.lt_irrefl, &[dividend]);
                        let impossible = d.apply(no_loop, &[impossible_loop]);
                        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                        let false_motive =
                            d.kernel()
                                .lam(anon, false_ty, quotient_bound_ty, BinderInfo::Default);
                        let level_zero = d.kernel().level_zero();
                        let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                        let body = d.apply(false_rec, &[false_motive, impossible]);
                        d.lam_fv(strict_fv, strict_ty, body)
                    };
                    let equal_minor = {
                        let equal_fv = d.fresh_fvar();
                        let equal = d.kernel().fvar(equal_fv);
                        let candidate_eq_quotient = d.symm(quotient, candidate, equal);
                        let candidate_refl = d.lemma(p.le_refl, &[candidate]);
                        let equality_motive =
                            d.eq_motive(candidate, &|d, upper| d.le(candidate, upper));
                        let body = d.transport(
                            candidate,
                            equality_motive,
                            candidate_refl,
                            quotient,
                            candidate_eq_quotient,
                        );
                        d.lam_fv(equal_fv, equal_ty, body)
                    };
                    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                    let body = d.apply(
                        or_rec,
                        &[
                            strict_ty,
                            equal_ty,
                            split_motive,
                            strict_minor,
                            equal_minor,
                            split,
                        ],
                    );
                    d.lam_fv(reverse_fv, reverse_order_ty, body)
                };
                let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                let body = d.apply(
                    or_rec,
                    &[
                        quotient_bound_ty,
                        reverse_order_ty,
                        order_motive,
                        ordered_minor,
                        reverse_minor,
                        order_split,
                    ],
                );
                d.lam_fv(product_bound_fv, product_bound_ty, body)
            };

            let reverse = {
                let quotient_bound_fv = d.fresh_fvar();
                let quotient_bound = d.kernel().fvar(quotient_bound_fv);
                let products_ordered = d.lemma(
                    p.mul_le_mul_left,
                    &[divisor, candidate, quotient, quotient_bound],
                );
                let body = d.lemma(
                    p.le_trans,
                    &[
                        candidate_product,
                        quotient_product,
                        dividend,
                        products_ordered,
                        lower,
                    ],
                );
                d.lam_fv(quotient_bound_fv, quotient_bound_ty, body)
            };

            let body = d.const_app(
                p.logic.iff_intro,
                &[product_bound_ty, quotient_bound_ty, forward, reverse],
            );
            let with_upper = d.lam_fv(upper_fv, upper_ty, body);
            d.lam_fv(lower_fv, lower_ty, with_upper)
        };
        let level_zero = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
        let body = d.apply(
            and_rec,
            &[lower_ty, upper_ty, bounds_motive, bounds_minor, bounds],
        );
        let stmt = d.arrow(relation_ty, target);
        let proof = d.lam_fv(relation_fv, relation_ty, body);
        (stmt, proof)
    })?;

    // div_mod_lt_mul_iff :
    //   ∀ d n q r s, divMod d n q r → (n < d*s ↔ q < s)
    // This is the strict dual of the floor adjunction. A candidate at or below
    // q has product at or below n; a candidate above q is at least succ q, so
    // the strict floor upper bound places n below its product.
    d.theorem(p.div_mod_lt_mul_iff, 5, &|d, v| {
        let (divisor, dividend, quotient, remainder, candidate) = (v[0], v[1], v[2], v[3], v[4]);
        let relation_ty = d.div_mod(divisor, dividend, quotient, remainder);
        let quotient_product = d.mul(divisor, quotient);
        let candidate_product = d.mul(divisor, candidate);
        let product_bound_ty = d.lt(dividend, candidate_product);
        let quotient_bound_ty = d.lt(quotient, candidate);
        let target = d.const_app(p.logic.iff, &[product_bound_ty, quotient_bound_ty]);

        let relation_fv = d.fresh_fvar();
        let relation = d.kernel().fvar(relation_fv);
        let bounds = d.lemma(
            p.div_mod_bounds,
            &[divisor, dividend, quotient, remainder, relation],
        );
        let next_quotient = d.succ(quotient);
        let next_product = d.mul(divisor, next_quotient);
        let lower_ty = d.le(quotient_product, dividend);
        let upper_ty = d.lt(dividend, next_product);
        let bounds_ty = d.const_app(p.logic.and, &[lower_ty, upper_ty]);
        let bounds_motive = d.kernel().lam(anon, bounds_ty, target, BinderInfo::Default);
        let bounds_minor = {
            let lower_fv = d.fresh_fvar();
            let lower = d.kernel().fvar(lower_fv);
            let upper_fv = d.fresh_fvar();
            let upper = d.kernel().fvar(upper_fv);

            let forward = {
                let product_bound_fv = d.fresh_fvar();
                let product_bound = d.kernel().fvar(product_bound_fv);
                let candidate_le_quotient_ty = d.le(candidate, quotient);
                let quotient_le_candidate_ty = d.le(quotient, candidate);
                let order_split_ty = d.const_app(
                    p.logic.or,
                    &[candidate_le_quotient_ty, quotient_le_candidate_ty],
                );
                let order_split = d.lemma(p.le_total, &[candidate, quotient]);
                let order_motive =
                    d.kernel()
                        .lam(anon, order_split_ty, quotient_bound_ty, BinderInfo::Default);
                let eliminate_candidate_le = |d: &mut NatDev<'_>, candidate_le_quotient: ExprId| {
                    let products_ordered = d.lemma(
                        p.mul_le_mul_left,
                        &[divisor, candidate, quotient, candidate_le_quotient],
                    );
                    let candidate_product_le_dividend = d.lemma(
                        p.le_trans,
                        &[
                            candidate_product,
                            quotient_product,
                            dividend,
                            products_ordered,
                            lower,
                        ],
                    );
                    let impossible_loop = d.lemma(
                        p.lt_of_lt_of_le,
                        &[
                            dividend,
                            candidate_product,
                            dividend,
                            product_bound,
                            candidate_product_le_dividend,
                        ],
                    );
                    let no_loop = d.lemma(p.lt_irrefl, &[dividend]);
                    let impossible = d.apply(no_loop, &[impossible_loop]);
                    let false_ty = d.kernel().const_(p.logic.false_, vec![]);
                    let false_motive =
                        d.kernel()
                            .lam(anon, false_ty, quotient_bound_ty, BinderInfo::Default);
                    let level_zero = d.kernel().level_zero();
                    let false_rec = d.kernel().const_(p.logic.false_rec, vec![level_zero]);
                    d.apply(false_rec, &[false_motive, impossible])
                };
                let candidate_le_minor = {
                    let ordered_fv = d.fresh_fvar();
                    let ordered = d.kernel().fvar(ordered_fv);
                    let body = eliminate_candidate_le(d, ordered);
                    d.lam_fv(ordered_fv, candidate_le_quotient_ty, body)
                };
                let quotient_le_minor = {
                    let ordered_fv = d.fresh_fvar();
                    let ordered = d.kernel().fvar(ordered_fv);
                    let equal_ty = d.eq(quotient, candidate);
                    let split_ty = d.const_app(p.logic.or, &[quotient_bound_ty, equal_ty]);
                    let split = d.lemma(p.lt_or_eq_of_le, &[quotient, candidate, ordered]);
                    let split_motive =
                        d.kernel()
                            .lam(anon, split_ty, quotient_bound_ty, BinderInfo::Default);
                    let strict_minor = {
                        let strict_fv = d.fresh_fvar();
                        let strict = d.kernel().fvar(strict_fv);
                        d.lam_fv(strict_fv, quotient_bound_ty, strict)
                    };
                    let equal_minor = {
                        let equal_fv = d.fresh_fvar();
                        let equal = d.kernel().fvar(equal_fv);
                        let candidate_eq_quotient = d.symm(quotient, candidate, equal);
                        let candidate_refl = d.lemma(p.le_refl, &[candidate]);
                        let equality_motive =
                            d.eq_motive(candidate, &|d, upper| d.le(candidate, upper));
                        let candidate_le_quotient = d.transport(
                            candidate,
                            equality_motive,
                            candidate_refl,
                            quotient,
                            candidate_eq_quotient,
                        );
                        let body = eliminate_candidate_le(d, candidate_le_quotient);
                        d.lam_fv(equal_fv, equal_ty, body)
                    };
                    let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                    let body = d.apply(
                        or_rec,
                        &[
                            quotient_bound_ty,
                            equal_ty,
                            split_motive,
                            strict_minor,
                            equal_minor,
                            split,
                        ],
                    );
                    d.lam_fv(ordered_fv, quotient_le_candidate_ty, body)
                };
                let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
                let body = d.apply(
                    or_rec,
                    &[
                        candidate_le_quotient_ty,
                        quotient_le_candidate_ty,
                        order_motive,
                        candidate_le_minor,
                        quotient_le_minor,
                        order_split,
                    ],
                );
                d.lam_fv(product_bound_fv, product_bound_ty, body)
            };

            let reverse = {
                let quotient_bound_fv = d.fresh_fvar();
                let quotient_bound = d.kernel().fvar(quotient_bound_fv);
                let next_le_candidate = d.lemma(
                    p.mul_le_mul_left,
                    &[divisor, next_quotient, candidate, quotient_bound],
                );
                let body = d.lemma(
                    p.lt_of_lt_of_le,
                    &[
                        dividend,
                        next_product,
                        candidate_product,
                        upper,
                        next_le_candidate,
                    ],
                );
                d.lam_fv(quotient_bound_fv, quotient_bound_ty, body)
            };

            let body = d.const_app(
                p.logic.iff_intro,
                &[product_bound_ty, quotient_bound_ty, forward, reverse],
            );
            let with_upper = d.lam_fv(upper_fv, upper_ty, body);
            d.lam_fv(lower_fv, lower_ty, with_upper)
        };
        let level_zero = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
        let body = d.apply(
            and_rec,
            &[lower_ty, upper_ty, bounds_motive, bounds_minor, bounds],
        );
        let stmt = d.arrow(relation_ty, target);
        let proof = d.lam_fv(relation_fv, relation_ty, body);
        (stmt, proof)
    })?;

    // div_mod_add_multiple :
    //   ∀ d n q r k, divMod d n q r → divMod d (n+d*k) (q+k) r
    // Shift a relational decomposition by a multiple of its divisor. This is
    // the reusable closure fact needed to compare balanced congruence witnesses
    // through div_mod_unique.
    d.theorem(p.div_mod_add_multiple, 5, &|d, v| {
        let (divisor, dividend, quotient, remainder, shift) = (v[0], v[1], v[2], v[3], v[4]);
        let relation_ty = d.div_mod(divisor, dividend, quotient, remainder);
        let shift_product = d.mul(divisor, shift);
        let shifted_dividend = d.add(dividend, shift_product);
        let shifted_quotient = d.add(quotient, shift);
        let target = d.div_mod(divisor, shifted_dividend, shifted_quotient, remainder);
        let relation_fv = d.fresh_fvar();
        let relation = d.kernel().fvar(relation_fv);

        let quotient_product = d.mul(divisor, quotient);
        let reconstructed = d.add(quotient_product, remainder);
        let equation_ty = d.eq(dividend, reconstructed);
        let bound_ty = d.lt(remainder, divisor);
        let relation_motive = d
            .kernel()
            .lam(anon, relation_ty, target, BinderInfo::Default);
        let relation_minor = {
            let equation_fv = d.fresh_fvar();
            let equation = d.kernel().fvar(equation_fv);
            let bound_fv = d.fresh_fvar();
            let bound = d.kernel().fvar(bound_fv);

            let expanded = d.add(reconstructed, shift_product);
            let products_sum = d.add(quotient_product, shift_product);
            let regrouped = d.add(products_sum, remainder);
            let shifted_quotient_product = d.mul(divisor, shifted_quotient);
            let shifted_reconstructed = d.add(shifted_quotient_product, remainder);
            let expand = d.congr(dividend, reconstructed, equation, &|d, value| {
                d.add(value, shift_product)
            });
            let regroup = d.lemma(
                p.add_right_comm,
                &[quotient_product, remainder, shift_product],
            );
            let distribute = d.lemma(p.left_distrib, &[divisor, quotient, shift]);
            let factor = d.symm(shifted_quotient_product, products_sum, distribute);
            let factor_under_remainder = d.congr(
                products_sum,
                shifted_quotient_product,
                factor,
                &|d, value| d.add(value, remainder),
            );
            let (_, shifted_equation) = d.chain(
                shifted_dividend,
                &[
                    (expanded, expand),
                    (regrouped, regroup),
                    (shifted_reconstructed, factor_under_remainder),
                ],
            );
            let shifted_equation_ty = d.eq(shifted_dividend, shifted_reconstructed);
            let body = d.const_app(
                p.logic.and_intro,
                &[shifted_equation_ty, bound_ty, shifted_equation, bound],
            );
            let with_bound = d.lam_fv(bound_fv, bound_ty, body);
            d.lam_fv(equation_fv, equation_ty, with_bound)
        };
        let level_zero = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
        let body = d.apply(
            and_rec,
            &[
                equation_ty,
                bound_ty,
                relation_motive,
                relation_minor,
                relation,
            ],
        );
        let stmt = d.arrow(relation_ty, target);
        let proof = d.lam_fv(relation_fv, relation_ty, body);
        (stmt, proof)
    })?;
    Ok(())
}

/// Prove that the executable projections satisfy the relational Euclidean
/// specification for every positive divisor, represented constructively as a
/// successor. The proof follows the same Boolean rollover transition as the
/// shared computational state.
fn declare_executable_division_spec(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    anon: NameId,
) -> Result<(), KernelError> {
    let p = *p;
    d.theorem(p.div_mod_exec, 2, &|d, values| {
        let (divisor_predecessor, dividend) = (values[0], values[1]);
        let divisor = d.succ(divisor_predecessor);
        let spec = |d: &mut NatDev<'_>, value: ExprId| {
            let quotient = d.div(value, divisor);
            let remainder = d.modulo(value, divisor);
            d.div_mod(divisor, value, quotient, remainder)
        };

        let proof = d.induct(
            &spec,
            &|d| {
                let zero = d.zero();
                let quotient = d.div(zero, divisor);
                let remainder = d.modulo(zero, divisor);
                let product = d.mul(divisor, quotient);
                let reconstructed = d.add(product, remainder);
                let equation_ty = d.eq(zero, reconstructed);
                let equation = d.refl(zero);
                let bound_ty = d.lt(remainder, divisor);
                let zero_le_predecessor = d.lemma(p.zero_le, &[divisor_predecessor]);
                let bound = d.lemma(
                    p.le_succ_succ,
                    &[zero, divisor_predecessor, zero_le_predecessor],
                );
                d.const_app(p.logic.and_intro, &[equation_ty, bound_ty, equation, bound])
            },
            &|d, prior_dividend, prior_relation| {
                executable_division_spec_step(
                    d,
                    &p,
                    anon,
                    divisor_predecessor,
                    divisor,
                    prior_dividend,
                    prior_relation,
                )
            },
            dividend,
        );
        (spec(d, dividend), proof)
    })?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn executable_division_spec_step(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    anon: NameId,
    divisor_predecessor: ExprId,
    divisor: ExprId,
    prior_dividend: ExprId,
    prior_relation: ExprId,
) -> ExprId {
    let bool_ty = d.bool_ty();
    let zero = d.zero();
    let successor_dividend = d.succ(prior_dividend);
    let quotient = d.div(prior_dividend, divisor);
    let remainder = d.modulo(prior_dividend, divisor);
    let successor_quotient = d.succ(quotient);
    let successor_remainder = d.succ(remainder);
    let condition = d.beq(remainder, divisor_predecessor);

    let target_for = |d: &mut NatDev<'_>, selector: ExprId| {
        let next_quotient = d.bool_select_nat(selector, successor_quotient, quotient);
        let next_remainder = d.bool_select_nat(selector, zero, successor_remainder);
        d.div_mod(divisor, successor_dividend, next_quotient, next_remainder)
    };
    let branch_for = |d: &mut NatDev<'_>, selector: ExprId| {
        let equality = d.bool_eq(condition, selector);
        let target = target_for(d, selector);
        d.arrow(equality, target)
    };

    let false_value = d.bool_false();
    let true_value = d.bool_true();
    let false_minor = executable_division_spec_no_rollover(
        d,
        p,
        anon,
        divisor_predecessor,
        divisor,
        prior_dividend,
        prior_relation,
        quotient,
        remainder,
        condition,
        false_value,
    );
    let true_minor = executable_division_spec_rollover(
        d,
        p,
        anon,
        divisor_predecessor,
        divisor,
        prior_dividend,
        prior_relation,
        quotient,
        remainder,
        condition,
        true_value,
    );
    let motive = {
        let selector_fv = d.fresh_fvar();
        let selector = d.kernel().fvar(selector_fv);
        let body = branch_for(d, selector);
        d.lam_fv(selector_fv, bool_ty, body)
    };
    let level_zero = d.kernel().level_zero();
    let bool_rec = d.kernel().const_(p.logic.bool_rec, vec![level_zero]);
    let selected = d.apply(bool_rec, &[motive, true_minor, false_minor, condition]);
    let condition_refl = d.bool_refl(condition);
    d.apply(selected, &[condition_refl])
}

#[allow(clippy::too_many_arguments)]
fn executable_division_spec_no_rollover(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    anon: NameId,
    divisor_predecessor: ExprId,
    divisor: ExprId,
    prior_dividend: ExprId,
    prior_relation: ExprId,
    quotient: ExprId,
    remainder: ExprId,
    condition: ExprId,
    false_value: ExprId,
) -> ExprId {
    let false_equality_ty = d.bool_eq(condition, false_value);
    let false_equality_fv = d.fresh_fvar();
    let false_equality = d.kernel().fvar(false_equality_fv);
    let successor_dividend = d.succ(prior_dividend);
    let successor_remainder = d.succ(remainder);
    let target = d.div_mod(divisor, successor_dividend, quotient, successor_remainder);
    let relation_ty = d.div_mod(divisor, prior_dividend, quotient, remainder);
    let product = d.mul(divisor, quotient);
    let reconstructed = d.add(product, remainder);
    let equation_ty = d.eq(prior_dividend, reconstructed);
    let bound_ty = d.lt(remainder, divisor);
    let relation_motive = d
        .kernel()
        .lam(anon, relation_ty, target, BinderInfo::Default);
    let relation_minor = {
        let equation_fv = d.fresh_fvar();
        let equation = d.kernel().fvar(equation_fv);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let remainder_le_predecessor = d.lemma(
            p.le_of_succ_le_succ,
            &[remainder, divisor_predecessor, bound],
        );
        let strict_ty = d.lt(remainder, divisor_predecessor);
        let equal_ty = d.eq(remainder, divisor_predecessor);
        let split_ty = d.const_app(p.logic.or, &[strict_ty, equal_ty]);
        let split = d.lemma(
            p.lt_or_eq_of_le,
            &[remainder, divisor_predecessor, remainder_le_predecessor],
        );
        let split_motive = d.kernel().lam(anon, split_ty, target, BinderInfo::Default);
        let strict_minor = {
            let strict_fv = d.fresh_fvar();
            let strict = d.kernel().fvar(strict_fv);
            let next_reconstructed = d.add(product, successor_remainder);
            let next_equation_ty = d.eq(successor_dividend, next_reconstructed);
            let next_equation = d.congr(prior_dividend, reconstructed, equation, &|d, value| {
                d.succ(value)
            });
            let next_bound_ty = d.lt(successor_remainder, divisor);
            let next_bound = d.lemma(
                p.le_succ_succ,
                &[successor_remainder, divisor_predecessor, strict],
            );
            let body = d.const_app(
                p.logic.and_intro,
                &[next_equation_ty, next_bound_ty, next_equation, next_bound],
            );
            d.lam_fv(strict_fv, strict_ty, body)
        };
        let equal_minor = {
            let equal_fv = d.fresh_fvar();
            let equal = d.kernel().fvar(equal_fv);
            let true_value = d.bool_true();
            let true_equality = d.lemma(
                p.beq_eq_true_of_eq,
                &[remainder, divisor_predecessor, equal],
            );
            let reverse_false = d.bool_symm(condition, false_value, false_equality);
            let impossible = d.bool_trans(
                false_value,
                condition,
                true_value,
                reverse_false,
                true_equality,
            );
            let body = d.false_true_elim(target, impossible);
            d.lam_fv(equal_fv, equal_ty, body)
        };
        let or_rec = d.kernel().const_(p.logic.or_rec, vec![]);
        let body = d.apply(
            or_rec,
            &[
                strict_ty,
                equal_ty,
                split_motive,
                strict_minor,
                equal_minor,
                split,
            ],
        );
        let with_bound = d.lam_fv(bound_fv, bound_ty, body);
        d.lam_fv(equation_fv, equation_ty, with_bound)
    };
    let level_zero = d.kernel().level_zero();
    let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
    let body = d.apply(
        and_rec,
        &[
            equation_ty,
            bound_ty,
            relation_motive,
            relation_minor,
            prior_relation,
        ],
    );
    d.lam_fv(false_equality_fv, false_equality_ty, body)
}

#[allow(clippy::too_many_arguments)]
fn executable_division_spec_rollover(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    anon: NameId,
    divisor_predecessor: ExprId,
    divisor: ExprId,
    prior_dividend: ExprId,
    prior_relation: ExprId,
    quotient: ExprId,
    remainder: ExprId,
    condition: ExprId,
    true_value: ExprId,
) -> ExprId {
    let true_equality_ty = d.bool_eq(condition, true_value);
    let true_equality_fv = d.fresh_fvar();
    let true_equality = d.kernel().fvar(true_equality_fv);
    let zero = d.zero();
    let successor_dividend = d.succ(prior_dividend);
    let successor_quotient = d.succ(quotient);
    let target = d.div_mod(divisor, successor_dividend, successor_quotient, zero);
    let relation_ty = d.div_mod(divisor, prior_dividend, quotient, remainder);
    let product = d.mul(divisor, quotient);
    let reconstructed = d.add(product, remainder);
    let equation_ty = d.eq(prior_dividend, reconstructed);
    let bound_ty = d.lt(remainder, divisor);
    let relation_motive = d
        .kernel()
        .lam(anon, relation_ty, target, BinderInfo::Default);
    let relation_minor = {
        let equation_fv = d.fresh_fvar();
        let equation = d.kernel().fvar(equation_fv);
        let bound_fv = d.fresh_fvar();
        let _bound = d.kernel().fvar(bound_fv);
        let remainder_eq_predecessor = d.lemma(
            p.eq_of_beq_eq_true,
            &[remainder, divisor_predecessor, true_equality],
        );
        let successor_remainder = d.succ(remainder);
        let successor_remainder_eq_divisor = d.congr(
            remainder,
            divisor_predecessor,
            remainder_eq_predecessor,
            &|d, value| d.succ(value),
        );
        let next_product = d.mul(divisor, successor_quotient);
        let next_reconstructed = d.add(next_product, zero);
        let next_equation_ty = d.eq(successor_dividend, next_reconstructed);
        let successor_reconstructed = d.succ(reconstructed);
        let lifted = d.congr(prior_dividend, reconstructed, equation, &|d, value| {
            d.succ(value)
        });
        let product_plus_successor_remainder = d.add(product, successor_remainder);
        let successor_eq_product_plus_successor_remainder = d.refl(successor_reconstructed);
        let product_plus_divisor = d.add(product, divisor);
        let replace_remainder = d.congr(
            successor_remainder,
            divisor,
            successor_remainder_eq_divisor,
            &|d, value| d.add(product, value),
        );
        let product_plus_divisor_eq_next = d.refl(product_plus_divisor);
        let (_, next_equation) = d.chain(
            successor_dividend,
            &[
                (successor_reconstructed, lifted),
                (
                    product_plus_successor_remainder,
                    successor_eq_product_plus_successor_remainder,
                ),
                (product_plus_divisor, replace_remainder),
                (next_reconstructed, product_plus_divisor_eq_next),
            ],
        );
        let zero_bound_ty = d.lt(zero, divisor);
        let zero_le_predecessor = d.lemma(p.zero_le, &[divisor_predecessor]);
        let zero_bound = d.lemma(
            p.le_succ_succ,
            &[zero, divisor_predecessor, zero_le_predecessor],
        );
        let body = d.const_app(
            p.logic.and_intro,
            &[next_equation_ty, zero_bound_ty, next_equation, zero_bound],
        );
        let with_bound = d.lam_fv(bound_fv, bound_ty, body);
        d.lam_fv(equation_fv, equation_ty, with_bound)
    };
    let level_zero = d.kernel().level_zero();
    let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
    let body = d.apply(
        and_rec,
        &[
            equation_ty,
            bound_ty,
            relation_motive,
            relation_minor,
            prior_relation,
        ],
    );
    d.lam_fv(true_equality_fv, true_equality_ty, body)
}

/// `Nat.dvd`, `dvd_mul`, and `dvd_add`, all constructed from the logic
/// prelude's checked `Exists` eliminator and the proved Nat multiplication
/// laws. No proposition is admitted as an axiom.
fn declare_divisibility(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();
    let one = d.level_one();

    // dvd a n := Exists Nat (fun q => Eq Nat n (a * q))
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let pred = d.dvd_predicate(a, n);
        let exists = d.kernel().const_(p.logic.exists_, vec![one]);
        let body = d.apply(exists, &[nat, pred]);
        let value = {
            let inner = d.lam_fv(n_fv, nat, body);
            d.lam_fv(a_fv, nat, inner)
        };
        let ty = {
            let inner = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            d.kernel().pi(anon, nat, inner, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.dvd,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(4),
        })?;
    }

    // valuationAt a n e := dvd (a^e) n ∧ Not (dvd (a^(succ e)) n)
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let e_fv = d.fresh_fvar();
        let e = d.kernel().fvar(e_fv);
        let power = d.pow(a, e);
        let se = d.succ(e);
        let next_power = d.pow(a, se);
        let divides = d.dvd(power, n);
        let next_divides = d.dvd(next_power, n);
        let not_next = d.const_app(p.logic.not, &[next_divides]);
        let body = d.const_app(p.logic.and, &[divides, not_next]);
        let value = {
            let with_e = d.lam_fv(e_fv, nat, body);
            let with_n = d.lam_fv(n_fv, nat, with_e);
            d.lam_fv(a_fv, nat, with_n)
        };
        let ty = {
            let with_e = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
            let with_n = d.kernel().pi(anon, nat, with_e, BinderInfo::Default);
            d.kernel().pi(anon, nat, with_n, BinderInfo::Default)
        };
        d.kernel().add_declaration(Declaration::Definition {
            name: p.valuation_at,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(6),
        })?;
    }

    // div_mod_remainder_eq_zero_iff_dvd :
    //   ∀ d n q r, divMod d n q r → (r=0 ↔ dvd d n)
    // A zero remainder exposes q as a divisibility witness. Conversely, any
    // divisibility witness gives a zero-remainder decomposition; uniqueness
    // against the supplied decomposition forces its remainder to be zero.
    d.theorem(p.div_mod_remainder_eq_zero_iff_dvd, 4, &|d, v| {
        let (divisor, dividend, quotient, remainder) = (v[0], v[1], v[2], v[3]);
        let zero = d.zero();
        let product = d.mul(divisor, quotient);
        let reconstructed = d.add(product, remainder);
        let relation_ty = d.div_mod(divisor, dividend, quotient, remainder);
        let equation_ty = d.eq(dividend, reconstructed);
        let bound_ty = d.lt(remainder, divisor);
        let zero_remainder_ty = d.eq(remainder, zero);
        let divides_ty = d.dvd(divisor, dividend);
        let target = d.const_app(p.logic.iff, &[zero_remainder_ty, divides_ty]);

        let relation_fv = d.fresh_fvar();
        let relation = d.kernel().fvar(relation_fv);
        let relation_motive = d
            .kernel()
            .lam(anon, relation_ty, target, BinderInfo::Default);
        let relation_minor = {
            let equation_fv = d.fresh_fvar();
            let equation = d.kernel().fvar(equation_fv);
            let bound_fv = d.fresh_fvar();
            let bound = d.kernel().fvar(bound_fv);

            let forward = {
                let zero_remainder_fv = d.fresh_fvar();
                let zero_remainder = d.kernel().fvar(zero_remainder_fv);
                let product_plus_zero = d.add(product, zero);
                let replace_remainder =
                    d.congr(remainder, zero, zero_remainder, &|d, x| d.add(product, x));
                let remove_zero = d.lemma(p.add_zero, &[product]);
                let (_, witness_equation) = d.chain(
                    dividend,
                    &[
                        (reconstructed, equation),
                        (product_plus_zero, replace_remainder),
                        (product, remove_zero),
                    ],
                );
                let predicate = d.dvd_predicate(divisor, dividend);
                let exists_intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let body = d.apply(exists_intro, &[nat, predicate, quotient, witness_equation]);
                d.lam_fv(zero_remainder_fv, zero_remainder_ty, body)
            };

            let reverse = {
                let divides_fv = d.fresh_fvar();
                let divides = d.kernel().fvar(divides_fv);
                let zero_le_remainder = d.lemma(p.zero_le, &[remainder]);
                let positive = d.lemma(
                    p.lt_of_le_of_lt,
                    &[zero, remainder, divisor, zero_le_remainder, bound],
                );
                let predicate = d.dvd_predicate(divisor, dividend);
                let exists_motive =
                    d.kernel()
                        .lam(anon, divides_ty, zero_remainder_ty, BinderInfo::Default);
                let exists_minor = {
                    let candidate_fv = d.fresh_fvar();
                    let candidate = d.kernel().fvar(candidate_fv);
                    let candidate_product = d.mul(divisor, candidate);
                    let witness_equation_fv = d.fresh_fvar();
                    let witness_equation_ty = d.eq(dividend, candidate_product);
                    let witness_equation = d.kernel().fvar(witness_equation_fv);
                    let candidate_plus_zero = d.add(candidate_product, zero);
                    let candidate_add_zero = d.lemma(p.add_zero, &[candidate_product]);
                    let candidate_add_zero_rev =
                        d.symm(candidate_plus_zero, candidate_product, candidate_add_zero);
                    let (_, zero_equation) = d.chain(
                        dividend,
                        &[
                            (candidate_product, witness_equation),
                            (candidate_plus_zero, candidate_add_zero_rev),
                        ],
                    );
                    let zero_equation_ty = d.eq(dividend, candidate_plus_zero);
                    let zero_bound_ty = d.lt(zero, divisor);
                    let zero_relation = d.const_app(
                        p.logic.and_intro,
                        &[zero_equation_ty, zero_bound_ty, zero_equation, positive],
                    );
                    let unique = d.lemma(
                        p.div_mod_unique,
                        &[
                            divisor,
                            dividend,
                            quotient,
                            remainder,
                            candidate,
                            zero,
                            relation,
                            zero_relation,
                        ],
                    );
                    let quotient_eq_ty = d.eq(quotient, candidate);
                    let unique_ty = d.const_app(p.logic.and, &[quotient_eq_ty, zero_remainder_ty]);
                    let unique_motive =
                        d.kernel()
                            .lam(anon, unique_ty, zero_remainder_ty, BinderInfo::Default);
                    let unique_minor = {
                        let quotient_eq_fv = d.fresh_fvar();
                        let remainder_eq_fv = d.fresh_fvar();
                        let remainder_eq = d.kernel().fvar(remainder_eq_fv);
                        let with_remainder =
                            d.lam_fv(remainder_eq_fv, zero_remainder_ty, remainder_eq);
                        d.lam_fv(quotient_eq_fv, quotient_eq_ty, with_remainder)
                    };
                    let level_zero = d.kernel().level_zero();
                    let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
                    let body = d.apply(
                        and_rec,
                        &[
                            quotient_eq_ty,
                            zero_remainder_ty,
                            unique_motive,
                            unique_minor,
                            unique,
                        ],
                    );
                    let with_equation = d.lam_fv(witness_equation_fv, witness_equation_ty, body);
                    d.lam_fv(candidate_fv, nat, with_equation)
                };
                let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
                let body = d.apply(
                    exists_rec,
                    &[nat, predicate, exists_motive, exists_minor, divides],
                );
                d.lam_fv(divides_fv, divides_ty, body)
            };

            let body = d.const_app(
                p.logic.iff_intro,
                &[zero_remainder_ty, divides_ty, forward, reverse],
            );
            let with_bound = d.lam_fv(bound_fv, bound_ty, body);
            d.lam_fv(equation_fv, equation_ty, with_bound)
        };
        let level_zero = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![level_zero]);
        let body = d.apply(
            and_rec,
            &[
                equation_ty,
                bound_ty,
                relation_motive,
                relation_minor,
                relation,
            ],
        );
        let stmt = d.arrow(relation_ty, target);
        let proof = d.lam_fv(relation_fv, relation_ty, body);
        (stmt, proof)
    })?;

    // div_mod_exact_exists :
    //   ∀ d n, Le one d → dvd d n → ∃ q, divMod d n q zero
    // Eliminate the factorization witness and reuse it as the quotient. The
    // positive divisor hypothesis is definitionally the zero-remainder bound.
    d.theorem(p.div_mod_exact_exists, 2, &|d, v| {
        let (divisor, dividend) = (v[0], v[1]);
        let unit = d.num(1);
        let zero = d.zero();
        let positive_ty = d.le(unit, divisor);
        let divides_ty = d.dvd(divisor, dividend);
        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let divides_fv = d.fresh_fvar();
        let divides = d.kernel().fvar(divides_fv);

        let quotient_fv = d.fresh_fvar();
        let quotient = d.kernel().fvar(quotient_fv);
        let relation = d.div_mod(divisor, dividend, quotient, zero);
        let exact_predicate = d.lam_fv(quotient_fv, nat, relation);
        let exists = d.kernel().const_(p.logic.exists_, vec![one]);
        let target = d.apply(exists, &[nat, exact_predicate]);
        let divides_predicate = d.dvd_predicate(divisor, dividend);
        let exists_motive = d
            .kernel()
            .lam(anon, divides_ty, target, BinderInfo::Default);
        let exists_minor = {
            let candidate_fv = d.fresh_fvar();
            let candidate = d.kernel().fvar(candidate_fv);
            let product = d.mul(divisor, candidate);
            let witness_equation_fv = d.fresh_fvar();
            let witness_equation_ty = d.eq(dividend, product);
            let witness_equation = d.kernel().fvar(witness_equation_fv);
            let product_plus_zero = d.add(product, zero);
            let add_zero = d.lemma(p.add_zero, &[product]);
            let add_zero_rev = d.symm(product_plus_zero, product, add_zero);
            let (_, zero_equation) = d.chain(
                dividend,
                &[
                    (product, witness_equation),
                    (product_plus_zero, add_zero_rev),
                ],
            );
            let zero_equation_ty = d.eq(dividend, product_plus_zero);
            let zero_bound_ty = d.lt(zero, divisor);
            let exact_relation = d.const_app(
                p.logic.and_intro,
                &[zero_equation_ty, zero_bound_ty, zero_equation, positive],
            );
            let exact_intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
            let body = d.apply(
                exact_intro,
                &[nat, exact_predicate, candidate, exact_relation],
            );
            let with_equation = d.lam_fv(witness_equation_fv, witness_equation_ty, body);
            d.lam_fv(candidate_fv, nat, with_equation)
        };
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(
            exists_rec,
            &[nat, divides_predicate, exists_motive, exists_minor, divides],
        );
        let divides_to_target = d.arrow(divides_ty, target);
        let stmt = d.arrow(positive_ty, divides_to_target);
        let with_divides = d.lam_fv(divides_fv, divides_ty, body);
        let proof = d.lam_fv(positive_fv, positive_ty, with_divides);
        (stmt, proof)
    })?;

    declare_executable_division_spec(d, &p, anon)?;

    // dvd_mul : ∀ a q, dvd a (a * q)
    d.theorem(p.dvd_mul, 2, &|d, v| {
        let (a, q) = (v[0], v[1]);
        let aq = d.mul(a, q);
        let stmt = d.dvd(a, aq);
        let pred = d.dvd_predicate(a, aq);
        let witness_proof = d.refl(aq);
        let one = d.level_one();
        let intro_name = d.prelude().logic.exists_intro;
        let intro = d.kernel().const_(intro_name, vec![one]);
        let nat = d.nat_ty();
        let proof = d.apply(intro, &[nat, pred, q, witness_proof]);
        (stmt, proof)
    })?;

    d.theorem(p.dvd_refl, 1, &|d, v| {
        let a = v[0];
        let unit = d.num(1);
        let product = d.mul(a, unit);
        let product_eq = d.lemma(p.mul_one, &[a]);
        let witness_eq = d.symm(product, a, product_eq);
        let predicate = d.dvd_predicate(a, a);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let proof = d.apply(intro, &[nat, predicate, unit, witness_eq]);
        (d.dvd(a, a), proof)
    })?;

    d.theorem(p.dvd_zero, 1, &|d, v| {
        let a = v[0];
        let zero = d.zero();
        let product = d.mul(a, zero);
        let product_eq = d.lemma(p.mul_zero, &[a]);
        let witness_eq = d.symm(product, zero, product_eq);
        let predicate = d.dvd_predicate(a, zero);
        let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
        let proof = d.apply(intro, &[nat, predicate, zero, witness_eq]);
        (d.dvd(a, zero), proof)
    })?;

    // Divisibility transitivity composes the two existential factors and uses
    // associativity to expose their product as the new witness.
    d.theorem(p.dvd_trans, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let hab_ty = d.dvd(a, b);
        let hbc_ty = d.dvd(b, c);
        let target = d.dvd(a, c);
        let hab_fv = d.fresh_fvar();
        let hab = d.kernel().fvar(hab_fv);
        let hbc_fv = d.fresh_fvar();
        let hbc = d.kernel().fvar(hbc_fv);
        let pred_ab = d.dvd_predicate(a, b);
        let pred_bc = d.dvd_predicate(b, c);
        let motive_ab = d.kernel().lam(anon, hab_ty, target, BinderInfo::Default);
        let minor_ab = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let aq = d.mul(a, q);
            let eq_ab_fv = d.fresh_fvar();
            let eq_ab_ty = d.eq(b, aq);
            let eq_ab = d.kernel().fvar(eq_ab_fv);
            let motive_bc = d.kernel().lam(anon, hbc_ty, target, BinderInfo::Default);
            let minor_bc = {
                let r_fv = d.fresh_fvar();
                let r = d.kernel().fvar(r_fv);
                let br = d.mul(b, r);
                let eq_bc_fv = d.fresh_fvar();
                let eq_bc_ty = d.eq(c, br);
                let eq_bc = d.kernel().fvar(eq_bc_fv);
                let aqr = d.mul(aq, r);
                let qr = d.mul(q, r);
                let target_product = d.mul(a, qr);
                let replace_b = d.congr(b, aq, eq_ab, &|d, x| d.mul(x, r));
                let associate = d.lemma(p.mul_assoc, &[a, q, r]);
                let (_, witness_eq) = d.chain(
                    c,
                    &[(br, eq_bc), (aqr, replace_b), (target_product, associate)],
                );
                let predicate = d.dvd_predicate(a, c);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let body = d.apply(intro, &[nat, predicate, qr, witness_eq]);
                let with_eq = d.lam_fv(eq_bc_fv, eq_bc_ty, body);
                d.lam_fv(r_fv, nat, with_eq)
            };
            let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(exists_rec, &[nat, pred_bc, motive_bc, minor_bc, hbc]);
            let with_eq = d.lam_fv(eq_ab_fv, eq_ab_ty, body);
            d.lam_fv(q_fv, nat, with_eq)
        };
        let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(exists_rec, &[nat, pred_ab, motive_ab, minor_ab, hab]);
        let proof = {
            let with_hbc = d.lam_fv(hbc_fv, hbc_ty, body);
            d.lam_fv(hab_fv, hab_ty, with_hbc)
        };
        let hbc_to_target = d.arrow(hbc_ty, target);
        let stmt = d.arrow(hab_ty, hbc_to_target);
        (stmt, proof)
    })?;

    // Multiplication on the right preserves divisibility by transitivity with
    // the canonical factor witness.
    d.theorem(p.dvd_mul_right_of_dvd, 3, &|d, v| {
        let (a, b, c) = (v[0], v[1], v[2]);
        let source = d.dvd(a, b);
        let target_product = d.mul(b, c);
        let target = d.dvd(a, target_product);
        let source_fv = d.fresh_fvar();
        let source_proof = d.kernel().fvar(source_fv);
        let b_divides_product = d.lemma(p.dvd_mul, &[b, c]);
        let body = d.lemma(
            p.dvd_trans,
            &[a, b, target_product, source_proof, b_divides_product],
        );
        let proof = d.lam_fv(source_fv, source, body);
        (d.arrow(source, target), proof)
    })?;

    // dvd_add : ∀ a m n, dvd a m → dvd a n → dvd a (m + n)
    {
        let a_fv = d.fresh_fvar();
        let a = d.kernel().fvar(a_fv);
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let h1_fv = d.fresh_fvar();
        let h1 = d.kernel().fvar(h1_fv);
        let h2_fv = d.fresh_fvar();
        let h2 = d.kernel().fvar(h2_fv);
        let h1_ty = d.dvd(a, m);
        let h2_ty = d.dvd(a, n);
        let mn = d.add(m, n);
        let goal = d.dvd(a, mn);
        let p1 = d.dvd_predicate(a, m);
        let p2 = d.dvd_predicate(a, n);
        let one = d.level_one();

        let motive_for = |d: &mut NatDev<'_>, pred: ExprId| {
            let exists_name = d.prelude().logic.exists_;
            let exists = d.kernel().const_(exists_name, vec![one]);
            let nat = d.nat_ty();
            let dom = d.apply(exists, &[nat, pred]);
            let anon = d.anon_name();
            d.kernel().lam(anon, dom, goal, BinderInfo::Default)
        };

        let minor1 = {
            let q1_fv = d.fresh_fvar();
            let q1 = d.kernel().fvar(q1_fv);
            let aq1 = d.mul(a, q1);
            let e1_fv = d.fresh_fvar();
            let e1_ty = d.eq(m, aq1);
            let e1 = d.kernel().fvar(e1_fv);
            let minor2 = {
                let q2_fv = d.fresh_fvar();
                let q2 = d.kernel().fvar(q2_fv);
                let aq2 = d.mul(a, q2);
                let e2_fv = d.fresh_fvar();
                let e2_ty = d.eq(n, aq2);
                let e2 = d.kernel().fvar(e2_fv);

                // m+n = a*q1+n = a*q1+a*q2 = a*(q1+q2)
                let s1 = d.add(aq1, n);
                let c1 = d.congr(m, aq1, e1, &|d, t| d.add(t, n));
                let s2 = d.add(aq1, aq2);
                let c2 = d.congr(n, aq2, e2, &|d, t| d.add(aq1, t));
                let q12 = d.add(q1, q2);
                let aq12 = d.mul(a, q12);
                let h_distrib = d.lemma(p.left_distrib, &[a, q1, q2]);
                let c3 = d.symm(aq12, s2, h_distrib);
                let (_, witness_proof) = d.chain(mn, &[(s1, c1), (s2, c2), (aq12, c3)]);
                let pred = d.dvd_predicate(a, mn);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let nat = d.nat_ty();
                let body = d.apply(intro, &[nat, pred, q12, witness_proof]);
                let with_e2 = d.lam_fv(e2_fv, e2_ty, body);
                d.lam_fv(q2_fv, nat, with_e2)
            };
            let motive2 = motive_for(d, p2);
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let nat = d.nat_ty();
            let inner = d.apply(rec, &[nat, p2, motive2, minor2, h2]);
            let with_e1 = d.lam_fv(e1_fv, e1_ty, inner);
            d.lam_fv(q1_fv, nat, with_e1)
        };
        let motive1 = motive_for(d, p1);
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let proof = d.apply(rec, &[nat, p1, motive1, minor1, h1]);

        let ty = {
            let t = d.kernel().pi(anon, h2_ty, goal, BinderInfo::Default);
            let t = d.pi_fv(h1_fv, h1_ty, t);
            let t = d.pi_fv(n_fv, nat, t);
            let t = d.pi_fv(m_fv, nat, t);
            d.pi_fv(a_fv, nat, t)
        };
        let value = {
            let v = d.lam_fv(h2_fv, h2_ty, proof);
            let v = d.lam_fv(h1_fv, h1_ty, v);
            let v = d.lam_fv(n_fv, nat, v);
            let v = d.lam_fv(m_fv, nat, v);
            d.lam_fv(a_fv, nat, v)
        };
        d.declare_theorem(p.dvd_add, ty, value)?;
    }

    // dvd_add_iff_right : dvd k m -> (dvd k n <-> dvd k (m+n)). The reverse
    // direction is all-Nat: subtract the factor for m from the factor for the
    // sum, using total truncated distributivity rather than a positivity case.
    d.theorem(p.dvd_add_iff_right, 3, &|d, v| {
        let (k, m, n) = (v[0], v[1], v[2]);
        let sum = d.add(m, n);
        let divides_m_ty = d.dvd(k, m);
        let divides_n_ty = d.dvd(k, n);
        let divides_sum_ty = d.dvd(k, sum);
        let iff_ty = d.const_app(p.logic.iff, &[divides_n_ty, divides_sum_ty]);
        let divides_m_fv = d.fresh_fvar();
        let divides_m = d.kernel().fvar(divides_m_fv);

        let forward = {
            let divides_n_fv = d.fresh_fvar();
            let divides_n = d.kernel().fvar(divides_n_fv);
            let body = d.lemma(p.dvd_add, &[k, m, n, divides_m, divides_n]);
            d.lam_fv(divides_n_fv, divides_n_ty, body)
        };

        let reverse = {
            let divides_sum_fv = d.fresh_fvar();
            let divides_sum = d.kernel().fvar(divides_sum_fv);
            let pred_m = d.dvd_predicate(k, m);
            let pred_sum = d.dvd_predicate(k, sum);
            let motive_m = d
                .kernel()
                .lam(anon, divides_m_ty, divides_n_ty, BinderInfo::Default);
            let minor_m = {
                let left_factor_fv = d.fresh_fvar();
                let left_factor = d.kernel().fvar(left_factor_fv);
                let k_left = d.mul(k, left_factor);
                let left_eq_fv = d.fresh_fvar();
                let left_eq_ty = d.eq(m, k_left);
                let left_eq = d.kernel().fvar(left_eq_fv);
                let motive_sum =
                    d.kernel()
                        .lam(anon, divides_sum_ty, divides_n_ty, BinderInfo::Default);
                let minor_sum = {
                    let sum_factor_fv = d.fresh_fvar();
                    let sum_factor = d.kernel().fvar(sum_factor_fv);
                    let k_sum = d.mul(k, sum_factor);
                    let sum_eq_fv = d.fresh_fvar();
                    let sum_eq_ty = d.eq(sum, k_sum);
                    let sum_eq = d.kernel().fvar(sum_eq_fv);
                    let factor_difference = d.sub(sum_factor, left_factor);
                    let k_difference = d.mul(k, factor_difference);
                    let sum_minus_m = d.sub(sum, m);
                    let ksum_minus_m = d.sub(k_sum, m);
                    let ksum_minus_kleft = d.sub(k_sum, k_left);
                    let cancel = d.lemma(p.add_sub_cancel_left, &[m, n]);
                    let n_to_difference = d.symm(sum_minus_m, n, cancel);
                    let replace_sum = d.congr(sum, k_sum, sum_eq, &|d, x| d.sub(x, m));
                    let replace_m = d.congr(m, k_left, left_eq, &|d, x| d.sub(k_sum, x));
                    let distribute =
                        d.lemma(p.mul_sub_left_distrib_total, &[k, sum_factor, left_factor]);
                    let undistribute = d.symm(k_difference, ksum_minus_kleft, distribute);
                    let (_, witness_eq) = d.chain(
                        n,
                        &[
                            (sum_minus_m, n_to_difference),
                            (ksum_minus_m, replace_sum),
                            (ksum_minus_kleft, replace_m),
                            (k_difference, undistribute),
                        ],
                    );
                    let predicate = d.dvd_predicate(k, n);
                    let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                    let body = d.apply(intro, &[nat, predicate, factor_difference, witness_eq]);
                    let with_eq = d.lam_fv(sum_eq_fv, sum_eq_ty, body);
                    d.lam_fv(sum_factor_fv, nat, with_eq)
                };
                let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
                let body = d.apply(
                    exists_rec,
                    &[nat, pred_sum, motive_sum, minor_sum, divides_sum],
                );
                let with_eq = d.lam_fv(left_eq_fv, left_eq_ty, body);
                d.lam_fv(left_factor_fv, nat, with_eq)
            };
            let exists_rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(exists_rec, &[nat, pred_m, motive_m, minor_m, divides_m]);
            d.lam_fv(divides_sum_fv, divides_sum_ty, body)
        };

        let iff_proof = d.const_app(
            p.logic.iff_intro,
            &[divides_n_ty, divides_sum_ty, forward, reverse],
        );
        let proof = d.lam_fv(divides_m_fv, divides_m_ty, iff_proof);
        (d.arrow(divides_m_ty, iff_ty), proof)
    })?;

    // dvd_mod_iff : dvd k (succ d) ->
    //   (dvd k (mod n (succ d)) <-> dvd k n).
    // The executable division equation writes n as divisor*quotient+remainder;
    // `dvd_add_iff_right` removes that known divisible multiple in either
    // direction, including the k=0 corner.
    d.theorem(p.dvd_mod_iff, 3, &|d, v| {
        let (k, divisor_predecessor, dividend) = (v[0], v[1], v[2]);
        let divisor = d.succ(divisor_predecessor);
        let quotient = d.div(dividend, divisor);
        let remainder = d.modulo(dividend, divisor);
        let multiple = d.mul(divisor, quotient);
        let reconstructed = d.add(multiple, remainder);
        let divides_divisor_ty = d.dvd(k, divisor);
        let divides_remainder_ty = d.dvd(k, remainder);
        let divides_dividend_ty = d.dvd(k, dividend);
        let target = d.const_app(p.logic.iff, &[divides_remainder_ty, divides_dividend_ty]);
        let divides_divisor_fv = d.fresh_fvar();
        let divides_divisor = d.kernel().fvar(divides_divisor_fv);
        let divides_multiple = d.lemma(
            p.dvd_mul_right_of_dvd,
            &[k, divisor, quotient, divides_divisor],
        );
        let add_iff = d.lemma(
            p.dvd_add_iff_right,
            &[k, multiple, remainder, divides_multiple],
        );
        let divides_reconstructed_ty = d.dvd(k, reconstructed);
        let add_forward = iff_forward(d, divides_remainder_ty, divides_reconstructed_ty, add_iff);
        let add_reverse = iff_reverse(d, divides_remainder_ty, divides_reconstructed_ty, add_iff);

        let equation_ty = d.eq(dividend, reconstructed);
        let bound_ty = d.lt(remainder, divisor);
        let relation_ty = d.const_app(p.logic.and, &[equation_ty, bound_ty]);
        let relation = d.lemma(p.div_mod_exec, &[divisor_predecessor, dividend]);
        let relation_motive = d
            .kernel()
            .lam(anon, relation_ty, equation_ty, BinderInfo::Default);
        let relation_minor = {
            let equation_fv = d.fresh_fvar();
            let equation = d.kernel().fvar(equation_fv);
            let bound_fv = d.fresh_fvar();
            let with_bound = d.lam_fv(bound_fv, bound_ty, equation);
            d.lam_fv(equation_fv, equation_ty, with_bound)
        };
        let zero_level = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![zero_level]);
        let equation = d.apply(
            and_rec,
            &[
                equation_ty,
                bound_ty,
                relation_motive,
                relation_minor,
                relation,
            ],
        );

        let forward = {
            let proof_fv = d.fresh_fvar();
            let proof = d.kernel().fvar(proof_fv);
            let reconstructed_proof = d.apply(add_forward, &[proof]);
            let equation_rev = d.symm(dividend, reconstructed, equation);
            let motive = d.eq_motive(reconstructed, &|d, value| d.dvd(k, value));
            let body = d.transport(
                reconstructed,
                motive,
                reconstructed_proof,
                dividend,
                equation_rev,
            );
            d.lam_fv(proof_fv, divides_remainder_ty, body)
        };
        let reverse = {
            let proof_fv = d.fresh_fvar();
            let proof = d.kernel().fvar(proof_fv);
            let motive = d.eq_motive(dividend, &|d, value| d.dvd(k, value));
            let reconstructed_proof = d.transport(dividend, motive, proof, reconstructed, equation);
            let body = d.apply(add_reverse, &[reconstructed_proof]);
            d.lam_fv(proof_fv, divides_dividend_ty, body)
        };
        let iff_proof = d.const_app(
            p.logic.iff_intro,
            &[divides_remainder_ty, divides_dividend_ty, forward, reverse],
        );
        let proof = d.lam_fv(divides_divisor_fv, divides_divisor_ty, iff_proof);
        (d.arrow(divides_divisor_ty, target), proof)
    })?;

    // dvd_add_right_cancel_of_pos :
    //   ∀ a m n, Le one a → dvd a m → dvd a (m+n) → dvd a n
    // Expose both divisibility witnesses. Order reflection proves the first
    // quotient is bounded by the second; their difference is then a witness
    // for `n`, after checked subtraction restoration and additive cancellation.
    d.theorem(p.dvd_add_right_cancel_of_pos, 3, &|d, v| {
        let (a, m, n) = (v[0], v[1], v[2]);
        let unit = d.num(1);
        let positive_ty = d.le(unit, a);
        let positive_fv = d.fresh_fvar();
        let positive = d.kernel().fvar(positive_fv);
        let divides_m_ty = d.dvd(a, m);
        let divides_m_fv = d.fresh_fvar();
        let divides_m = d.kernel().fvar(divides_m_fv);
        let mn = d.add(m, n);
        let divides_sum_ty = d.dvd(a, mn);
        let divides_sum_fv = d.fresh_fvar();
        let divides_sum = d.kernel().fvar(divides_sum_fv);
        let goal = d.dvd(a, n);
        let pred_m = d.dvd_predicate(a, m);
        let pred_sum = d.dvd_predicate(a, mn);

        let motive_for = |d: &mut NatDev<'_>, domain: ExprId| {
            d.kernel().lam(anon, domain, goal, BinderInfo::Default)
        };
        let minor_m = {
            let q1_fv = d.fresh_fvar();
            let q1 = d.kernel().fvar(q1_fv);
            let aq1 = d.mul(a, q1);
            let e1_fv = d.fresh_fvar();
            let e1_ty = d.eq(m, aq1);
            let e1 = d.kernel().fvar(e1_fv);
            let minor_sum = {
                let q2_fv = d.fresh_fvar();
                let q2 = d.kernel().fvar(q2_fv);
                let aq2 = d.mul(a, q2);
                let e2_fv = d.fresh_fvar();
                let e2_ty = d.eq(mn, aq2);
                let e2 = d.kernel().fvar(e2_fv);

                let m_le_sum = d.lemma(p.le_add_right, &[m, n]);
                let aq1_le_sum = {
                    let motive = d.eq_motive(m, &|d, lower| d.le(lower, mn));
                    d.transport(m, motive, m_le_sum, aq1, e1)
                };
                let aq1_le_aq2 = {
                    let motive = d.eq_motive(mn, &|d, upper| d.le(aq1, upper));
                    d.transport(mn, motive, aq1_le_sum, aq2, e2)
                };
                let q1_le_q2 = d.lemma(p.le_of_mul_le_mul_left, &[a, q1, q2, positive, aq1_le_aq2]);

                let difference = d.sub(q2, q1);
                let a_difference = d.mul(a, difference);
                let scaled_difference = d.sub(aq2, aq1);
                let h_scaled_difference = d.lemma(p.mul_sub_left_distrib, &[a, q2, q1, q1_le_q2]);
                let restored = d.add(scaled_difference, aq1);
                let h_restored = d.lemma(p.sub_add_cancel, &[aq1, aq2, aq1_le_aq2]);

                let start = d.add(a_difference, m);
                let with_scaled_difference = d.add(scaled_difference, m);
                let h1 = d.congr(
                    a_difference,
                    scaled_difference,
                    h_scaled_difference,
                    &|d, x| d.add(x, m),
                );
                let h2 = d.congr(m, aq1, e1, &|d, x| d.add(scaled_difference, x));
                let aq2_eq_sum = d.symm(mn, aq2, e2);
                let n_plus_m = d.add(n, m);
                let h_sum_comm = d.lemma(p.add_comm, &[n, m]);
                let sum_eq_n_plus_m = d.symm(n_plus_m, mn, h_sum_comm);
                let (_, common_sum) = d.chain(
                    start,
                    &[
                        (with_scaled_difference, h1),
                        (restored, h2),
                        (aq2, h_restored),
                        (mn, aq2_eq_sum),
                        (n_plus_m, sum_eq_n_plus_m),
                    ],
                );
                let a_difference_eq_n =
                    d.lemma(p.add_right_cancel, &[a_difference, n, m, common_sum]);
                let witness_proof = d.symm(a_difference, n, a_difference_eq_n);
                let pred = d.dvd_predicate(a, n);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let body = d.apply(intro, &[nat, pred, difference, witness_proof]);
                let with_e2 = d.lam_fv(e2_fv, e2_ty, body);
                d.lam_fv(q2_fv, nat, with_e2)
            };
            let motive_sum = motive_for(d, divides_sum_ty);
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let inner = d.apply(rec, &[nat, pred_sum, motive_sum, minor_sum, divides_sum]);
            let with_e1 = d.lam_fv(e1_fv, e1_ty, inner);
            d.lam_fv(q1_fv, nat, with_e1)
        };
        let motive_m = motive_for(d, divides_m_ty);
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(rec, &[nat, pred_m, motive_m, minor_m, divides_m]);
        let proof = {
            let with_sum = d.lam_fv(divides_sum_fv, divides_sum_ty, body);
            let with_m = d.lam_fv(divides_m_fv, divides_m_ty, with_sum);
            d.lam_fv(positive_fv, positive_ty, with_m)
        };
        let stmt = {
            let with_sum = d.arrow(divides_sum_ty, goal);
            let with_m = d.arrow(divides_m_ty, with_sum);
            d.arrow(positive_ty, with_m)
        };
        (stmt, proof)
    })?;

    // not_dvd_one_of_two_le : ∀ a, Le two a → Not (dvd a one)
    // Eliminate a hypothetical witness `one=a*q`, then inspect `q`. At zero
    // the equality makes one bounded by zero. At a successor, monotonicity
    // gives `a<=a*q=one`, contradicting `two<=a` after successor inversion.
    d.theorem(p.not_dvd_one_of_two_le, 1, &|d, v| {
        let a = v[0];
        let unit = d.num(1);
        let two = d.num(2);
        let bound_ty = d.le(two, a);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let divides_ty = d.dvd(a, unit);
        let divides_fv = d.fresh_fvar();
        let divides = d.kernel().fvar(divides_fv);
        let false_ty = d.kernel().const_(p.logic.false_, vec![]);
        let pred = d.dvd_predicate(a, unit);
        let motive = d
            .kernel()
            .lam(anon, divides_ty, false_ty, BinderInfo::Default);
        let minor = {
            let q_fv = d.fresh_fvar();
            let q = d.kernel().fvar(q_fv);
            let aq = d.mul(a, q);
            let e_fv = d.fresh_fvar();
            let e_ty = d.eq(unit, aq);
            let e = d.kernel().fvar(e_fv);
            let impossible_at = |d: &mut NatDev<'_>, x: ExprId| {
                let ax = d.mul(a, x);
                let equality = d.eq(unit, ax);
                d.arrow(equality, false_ty)
            };
            let at_zero = |d: &mut NatDev<'_>| {
                let zero = d.zero();
                let e0_ty = d.eq(unit, zero);
                let e0_fv = d.fresh_fvar();
                let e0 = d.kernel().fvar(e0_fv);
                let reflexive = d.lemma(p.le_refl, &[unit]);
                let upper_motive = d.eq_motive(unit, &|d, upper| d.le(unit, upper));
                let one_le_zero = d.transport(unit, upper_motive, reflexive, zero, e0);
                let body = d.lemma(p.not_succ_le_zero, &[zero, one_le_zero]);
                d.lam_fv(e0_fv, e0_ty, body)
            };
            let at_succ = |d: &mut NatDev<'_>, j: ExprId, _ih: ExprId| {
                let sj = d.succ(j);
                let asj = d.mul(a, sj);
                let es_ty = d.eq(unit, asj);
                let es_fv = d.fresh_fvar();
                let es = d.kernel().fvar(es_fv);
                let zero = d.zero();
                let one_le_sj = {
                    let zero_le_j = d.lemma(p.zero_le, &[j]);
                    d.lemma(p.le_succ_succ, &[zero, j, zero_le_j])
                };
                let a_one = d.mul(a, unit);
                let a_one_le_asj = d.lemma(p.mul_le_mul_left, &[a, unit, sj, one_le_sj]);
                let a_one_eq_a = d.lemma(p.mul_one, &[a]);
                let a_le_asj = {
                    let lower_motive = d.eq_motive(a_one, &|d, lower| d.le(lower, asj));
                    d.transport(a_one, lower_motive, a_one_le_asj, a, a_one_eq_a)
                };
                let asj_eq_one = d.symm(unit, asj, es);
                let a_le_one = {
                    let upper_motive = d.eq_motive(asj, &|d, upper| d.le(a, upper));
                    d.transport(asj, upper_motive, a_le_asj, unit, asj_eq_one)
                };
                let two_le_one = d.lemma(p.le_trans, &[two, a, unit, bound, a_le_one]);
                let one_le_zero = d.lemma(p.le_of_succ_le_succ, &[unit, zero, two_le_one]);
                let body = d.lemma(p.not_succ_le_zero, &[zero, one_le_zero]);
                d.lam_fv(es_fv, es_ty, body)
            };
            let body = d.induct(&impossible_at, &at_zero, &at_succ, q);
            let applied = d.apply(body, &[e]);
            let with_e = d.lam_fv(e_fv, e_ty, applied);
            d.lam_fv(q_fv, nat, with_e)
        };
        let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
        let body = d.apply(rec, &[nat, pred, motive, minor, divides]);
        let proof = {
            let with_divides = d.lam_fv(divides_fv, divides_ty, body);
            d.lam_fv(bound_fv, bound_ty, with_divides)
        };
        let not_divides = d.const_app(p.logic.not, &[divides_ty]);
        let stmt = d.arrow(bound_ty, not_divides);
        (stmt, proof)
    })?;

    // not_dvd_one_add_mul_of_two_le :
    //   ∀ a t, Le two a → Not (dvd a (one+a*t))
    // A divisor of the whole sum also divides the multiple `a*t`; cancel it
    // with the preceding theorem and contradict nondivisibility of one.
    d.theorem(p.not_dvd_one_add_mul_of_two_le, 2, &|d, v| {
        let (a, t) = (v[0], v[1]);
        let unit = d.num(1);
        let two = d.num(2);
        let bound_ty = d.le(two, a);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let at = d.mul(a, t);
        let sum = d.add(unit, at);
        let divides_sum_ty = d.dvd(a, sum);
        let divides_sum_fv = d.fresh_fvar();
        let divides_sum = d.kernel().fvar(divides_sum_fv);

        let at_plus_one = d.add(at, unit);
        let sum_eq_reordered = d.lemma(p.add_comm, &[unit, at]);
        let reordered_divides = {
            let motive = d.eq_motive(sum, &|d, value| d.dvd(a, value));
            d.transport(sum, motive, divides_sum, at_plus_one, sum_eq_reordered)
        };
        let one_le_two = d.lemma(p.le_add_right, &[unit, unit]);
        let positive = d.lemma(p.le_trans, &[unit, two, a, one_le_two, bound]);
        let divides_at = d.lemma(p.dvd_mul, &[a, t]);
        let divides_one = d.lemma(
            p.dvd_add_right_cancel_of_pos,
            &[a, at, unit, positive, divides_at, reordered_divides],
        );
        let one_not_divides = d.lemma(p.not_dvd_one_of_two_le, &[a, bound]);
        let body = d.apply(one_not_divides, &[divides_one]);
        let proof = {
            let with_divides = d.lam_fv(divides_sum_fv, divides_sum_ty, body);
            d.lam_fv(bound_fv, bound_ty, with_divides)
        };
        let not_divides = d.const_app(p.logic.not, &[divides_sum_ty]);
        let stmt = d.arrow(bound_ty, not_divides);
        (stmt, proof)
    })?;

    // valuation_at_two_mul_sq :
    //   ∀ a u, Le two a → Not (dvd a u) → valuationAt a ((a*a)*u) two
    d.theorem(p.valuation_at_two_mul_sq, 2, &|d, v| {
        let (a, u) = (v[0], v[1]);
        let unit = d.num(1);
        let two = d.num(2);
        let bound_ty = d.le(two, a);
        let bound_fv = d.fresh_fvar();
        let bound = d.kernel().fvar(bound_fv);
        let a_dvd_u = d.dvd(a, u);
        let not_dvd_u_ty = d.const_app(p.logic.not, &[a_dvd_u]);
        let not_dvd_u_fv = d.fresh_fvar();
        let not_dvd_u = d.kernel().fvar(not_dvd_u_fv);

        let zero = d.zero();
        let one_exp = d.succ(zero);
        let two_exp = d.succ(one_exp);
        let three_exp = d.succ(two_exp);
        let pow0 = d.pow(a, zero);
        let pow1 = d.pow(a, one_exp);
        let pow2 = d.pow(a, two_exp);
        let pow3 = d.pow(a, three_exp);
        let aa = d.mul(a, a);
        let z = d.mul(aa, u);

        let pow1_step = d.mul(pow0, a);
        let one_a = d.mul(unit, a);
        let h_pow1_step = d.lemma(p.pow_succ, &[a, zero]);
        let h_pow0 = d.lemma(p.pow_zero, &[a]);
        let h_pow0_under_mul = d.congr(pow0, unit, h_pow0, &|d, x| d.mul(x, a));
        let h_one_mul = d.lemma(p.one_mul, &[a]);
        let (_, pow1_eq_a) = d.chain(
            pow1,
            &[
                (pow1_step, h_pow1_step),
                (one_a, h_pow0_under_mul),
                (a, h_one_mul),
            ],
        );
        let pow1_a = d.mul(pow1, a);
        let h_pow2_step = d.lemma(p.pow_succ, &[a, one_exp]);
        let h_pow1_under_mul = d.congr(pow1, a, pow1_eq_a, &|d, x| d.mul(x, a));
        let (_, pow2_eq_aa) = d.chain(pow2, &[(pow1_a, h_pow2_step), (aa, h_pow1_under_mul)]);

        let divides_aa = d.lemma(p.dvd_mul, &[aa, u]);
        let aa_eq_pow2 = d.symm(pow2, aa, pow2_eq_aa);
        let divides_pow2 = {
            let motive = d.eq_motive(aa, &|d, divisor| d.dvd(divisor, z));
            d.transport(aa, motive, divides_aa, pow2, aa_eq_pow2)
        };

        let pow2_a = d.mul(pow2, a);
        let cube = d.mul(aa, a);
        let h_pow3_step = d.lemma(p.pow_succ, &[a, two_exp]);
        let h_pow2_under_mul = d.congr(pow2, aa, pow2_eq_aa, &|d, x| d.mul(x, a));
        let (_, pow3_eq_cube) = d.chain(pow3, &[(pow2_a, h_pow3_step), (cube, h_pow2_under_mul)]);
        let pow3_dvd_z = d.dvd(pow3, z);
        let not_pow3_dvd_z = {
            let divides_fv = d.fresh_fvar();
            let divides = d.kernel().fvar(divides_fv);
            let cube_divides_ty = d.dvd(cube, z);
            let cube_divides = {
                let motive = d.eq_motive(pow3, &|d, divisor| d.dvd(divisor, z));
                d.transport(pow3, motive, divides, cube, pow3_eq_cube)
            };
            let pred = d.dvd_predicate(cube, z);
            let false_ty = d.kernel().const_(p.logic.false_, vec![]);
            let motive = d
                .kernel()
                .lam(anon, cube_divides_ty, false_ty, BinderInfo::Default);
            let minor = {
                let q_fv = d.fresh_fvar();
                let q = d.kernel().fvar(q_fv);
                let cube_q = d.mul(cube, q);
                let e_fv = d.fresh_fvar();
                let e_ty = d.eq(z, cube_q);
                let e = d.kernel().fvar(e_fv);
                let aq = d.mul(a, q);
                let aa_aq = d.mul(aa, aq);
                let h_assoc = d.lemma(p.mul_assoc, &[aa, a, q]);
                let (_, common_product) = d.chain(z, &[(cube_q, e), (aa_aq, h_assoc)]);

                let one_le_two = d.lemma(p.le_add_right, &[unit, unit]);
                let one_le_a = d.lemma(p.le_trans, &[unit, two, a, one_le_two, bound]);
                let a_one = d.mul(a, unit);
                let a_one_le_aa = d.lemma(p.mul_le_mul_left, &[a, unit, a, one_le_a]);
                let a_one_eq_a = d.lemma(p.mul_one, &[a]);
                let a_le_aa = {
                    let lower_motive = d.eq_motive(a_one, &|d, lower| d.le(lower, aa));
                    d.transport(a_one, lower_motive, a_one_le_aa, a, a_one_eq_a)
                };
                let one_le_aa = d.lemma(p.le_trans, &[unit, a, aa, one_le_a, a_le_aa]);
                let u_eq_aq = d.lemma(
                    p.mul_left_cancel_of_pos,
                    &[aa, u, aq, one_le_aa, common_product],
                );
                let pred_u = d.dvd_predicate(a, u);
                let intro = d.kernel().const_(p.logic.exists_intro, vec![one]);
                let a_dvd_u_proof = d.apply(intro, &[nat, pred_u, q, u_eq_aq]);
                let body = d.apply(not_dvd_u, &[a_dvd_u_proof]);
                let with_e = d.lam_fv(e_fv, e_ty, body);
                d.lam_fv(q_fv, nat, with_e)
            };
            let rec = d.kernel().const_(p.logic.exists_rec, vec![one]);
            let body = d.apply(rec, &[nat, pred, motive, minor, cube_divides]);
            d.lam_fv(divides_fv, pow3_dvd_z, body)
        };

        let divides_pow2_ty = d.dvd(pow2, z);
        let next_not = d.const_app(p.logic.not, &[pow3_dvd_z]);
        let proof_pair = d.const_app(
            p.logic.and_intro,
            &[divides_pow2_ty, next_not, divides_pow2, not_pow3_dvd_z],
        );
        let conclusion = d.valuation_at(a, z, two);
        let proof = {
            let with_not_dvd = d.lam_fv(not_dvd_u_fv, not_dvd_u_ty, proof_pair);
            d.lam_fv(bound_fv, bound_ty, with_not_dvd)
        };
        let stmt = {
            let with_not_dvd = d.arrow(not_dvd_u_ty, conclusion);
            d.arrow(bound_ty, with_not_dvd)
        };
        (stmt, proof)
    })?;
    Ok(())
}

/// Bound executable remainder by its positive divisor, then use that checked
/// decrease to define Euclid's algorithm through the logic prelude's generic
/// well-founded fixpoint. This establishes computation and unfolding only;
/// the greatest-common-divisor characterization is intentionally separate.
fn declare_executable_gcd(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();

    // mod_lt : ∀ k n, mod n (succ k) < succ k
    d.theorem(p.mod_lt, 2, &|d, values| {
        let (divisor_predecessor, dividend) = (values[0], values[1]);
        let divisor = d.succ(divisor_predecessor);
        let quotient = d.div(dividend, divisor);
        let remainder = d.modulo(dividend, divisor);
        let equation_ty = {
            let product = d.mul(divisor, quotient);
            let reconstructed = d.add(product, remainder);
            d.eq(dividend, reconstructed)
        };
        let bound_ty = d.lt(remainder, divisor);
        let relation_ty = d.const_app(p.logic.and, &[equation_ty, bound_ty]);
        let relation = d.lemma(p.div_mod_exec, &[divisor_predecessor, dividend]);
        let motive = {
            let relation_fv = d.fresh_fvar();
            d.lam_fv(relation_fv, relation_ty, bound_ty)
        };
        let minor = {
            let equation_fv = d.fresh_fvar();
            let bound_fv = d.fresh_fvar();
            let bound = d.kernel().fvar(bound_fv);
            let with_bound = d.lam_fv(bound_fv, bound_ty, bound);
            d.lam_fv(equation_fv, equation_ty, with_bound)
        };
        let zero = d.kernel().level_zero();
        let and_rec = d.kernel().const_(p.logic.and_rec, vec![zero]);
        let proof = d.apply(and_rec, &[equation_ty, bound_ty, motive, minor, relation]);
        (bound_ty, proof)
    })?;

    // gcd m n := WellFounded.fix lt_well_founded step m n, where the
    // successor branch recursively calls gcd (n % succ k) (succ k).
    let (relation, family, well_founded, step) = gcd_fix_parts(d, &p);
    let one = d.level_one();
    let fix = d.kernel().const_(p.logic.well_founded_fix, vec![one, one]);
    let value = d.apply(fix, &[nat, relation, family, well_founded, step]);
    let nat_to_nat = d.arrow(nat, nat);
    let ty = d.arrow(nat, nat_to_nat);
    d.kernel().add_declaration(Declaration::Definition {
        name: p.gcd,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(10),
    })?;

    // Both public equations are pointwise consequences of the checked generic
    // fixpoint equation. The RHSs reduce through Nat.rec at zero/successor.
    d.theorem(p.gcd_zero_left, 1, &|d, values| {
        let value = values[0];
        let zero = d.zero();
        let gcd_zero = d.gcd(zero, value);
        let equation = gcd_fix_equation(d, &p, zero);
        let left_function = d.const_app(p.gcd, &[zero]);
        let identity = {
            let argument_fv = d.fresh_fvar();
            let argument = d.kernel().fvar(argument_fv);
            d.lam_fv(argument_fv, nat, argument)
        };
        let proof = apply_nat_function_equality(d, left_function, identity, equation, value);
        (d.eq(gcd_zero, value), proof)
    })?;

    d.theorem(p.gcd_succ, 2, &|d, values| {
        let (predecessor, value) = (values[0], values[1]);
        let divisor = d.succ(predecessor);
        let left = d.gcd(divisor, value);
        let remainder = d.modulo(value, divisor);
        let right = d.gcd(remainder, divisor);
        let equation = gcd_fix_equation(d, &p, divisor);
        let left_function = d.const_app(p.gcd, &[divisor]);
        let right_function = {
            let argument_fv = d.fresh_fvar();
            let argument = d.kernel().fvar(argument_fv);
            let recursive_remainder = d.modulo(argument, divisor);
            let body = d.gcd(recursive_remainder, divisor);
            d.lam_fv(argument_fv, nat, body)
        };
        let proof = apply_nat_function_equality(d, left_function, right_function, equation, value);
        (d.eq(left, right), proof)
    })?;

    Ok(())
}

/// Establish the semantic greatest-common-divisor contract over all naturals.
/// Both recursive directions follow the executable Euclidean transition and
/// consume `dvd_mod_iff`; neither direction assumes a positive common divisor.
fn declare_gcd_semantics(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();
    let relation = d.kernel().const_(p.lt, vec![]);
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);

    let gcd_dvd_at = |d: &mut NatDev<'_>, m: ExprId, n: ExprId| {
        let common = d.gcd(m, n);
        let left = d.dvd(common, m);
        let right = d.dvd(common, n);
        d.const_app(p.logic.and, &[left, right])
    };
    let gcd_dvd_row = |d: &mut NatDev<'_>, m: ExprId| {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = gcd_dvd_at(d, m, n);
        d.pi_fv(n_fv, nat, body)
    };
    let gcd_dvd_family = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let row = gcd_dvd_row(d, m);
        d.lam_fv(m_fv, nat, row)
    };
    let gcd_dvd_recursive_ty = |d: &mut NatDev<'_>, upper: ExprId| {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let related_fv = d.fresh_fvar();
        let related_ty = d.lt(predecessor, upper);
        let row = gcd_dvd_row(d, predecessor);
        let at_relation = d.pi_fv(related_fv, related_ty, row);
        d.pi_fv(predecessor_fv, nat, at_relation)
    };
    let gcd_dvd_step_motive = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let recursive = gcd_dvd_recursive_ty(d, m);
        let row = gcd_dvd_row(d, m);
        let body = d.arrow(recursive, row);
        d.lam_fv(m_fv, nat, body)
    };
    let gcd_dvd_zero_minor = {
        let recursive_fv = d.fresh_fvar();
        let zero = d.zero();
        let recursive_ty = gcd_dvd_recursive_ty(d, zero);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let common = d.gcd(zero, n);
        let equation = d.lemma(p.gcd_zero_left, &[n]);
        let n_to_common = d.symm(common, n, equation);
        let n_divides_zero = d.lemma(p.dvd_zero, &[n]);
        let n_divides_n = d.lemma(p.dvd_refl, &[n]);
        let common_divides_zero =
            transport_dvd_left(d, n, common, n_to_common, zero, n_divides_zero);
        let common_divides_n = transport_dvd_left(d, n, common, n_to_common, n, n_divides_n);
        let left_ty = d.dvd(common, zero);
        let right_ty = d.dvd(common, n);
        let pair = d.const_app(
            p.logic.and_intro,
            &[left_ty, right_ty, common_divides_zero, common_divides_n],
        );
        let with_n = d.lam_fv(n_fv, nat, pair);
        d.lam_fv(recursive_fv, recursive_ty, with_n)
    };
    let gcd_dvd_succ_minor = {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let divisor = d.succ(predecessor);
        let ih_fv = d.fresh_fvar();
        let ih_ty = {
            let recursive = gcd_dvd_recursive_ty(d, predecessor);
            let row = gcd_dvd_row(d, predecessor);
            d.arrow(recursive, row)
        };
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_ty = gcd_dvd_recursive_ty(d, divisor);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let remainder = d.modulo(n, divisor);
        let decrease = d.lemma(p.mod_lt, &[predecessor, n]);
        let at_remainder = d.apply(recursive, &[remainder, decrease]);
        let recursive_pair = d.apply(at_remainder, &[divisor]);
        let recursive_common = d.gcd(remainder, divisor);
        let recursive_left_ty = d.dvd(recursive_common, remainder);
        let recursive_right_ty = d.dvd(recursive_common, divisor);
        let recursive_left = and_left(d, recursive_left_ty, recursive_right_ty, recursive_pair);
        let recursive_right = and_right(d, recursive_left_ty, recursive_right_ty, recursive_pair);
        let remainder_iff = d.lemma(
            p.dvd_mod_iff,
            &[recursive_common, predecessor, n, recursive_right],
        );
        let recursive_divides_n_ty = d.dvd(recursive_common, n);
        let remainder_forward =
            iff_forward(d, recursive_left_ty, recursive_divides_n_ty, remainder_iff);
        let recursive_divides_n = d.apply(remainder_forward, &[recursive_left]);
        let common = d.gcd(divisor, n);
        let equation = d.lemma(p.gcd_succ, &[predecessor, n]);
        let recursive_to_common = d.symm(common, recursive_common, equation);
        let common_divides_divisor = transport_dvd_left(
            d,
            recursive_common,
            common,
            recursive_to_common,
            divisor,
            recursive_right,
        );
        let common_divides_n = transport_dvd_left(
            d,
            recursive_common,
            common,
            recursive_to_common,
            n,
            recursive_divides_n,
        );
        let left_ty = d.dvd(common, divisor);
        let right_ty = d.dvd(common, n);
        let pair = d.const_app(
            p.logic.and_intro,
            &[left_ty, right_ty, common_divides_divisor, common_divides_n],
        );
        let with_n = d.lam_fv(n_fv, nat, pair);
        let with_recursive = d.lam_fv(recursive_fv, recursive_ty, with_n);
        let with_ih = d.lam_fv(ih_fv, ih_ty, with_recursive);
        d.lam_fv(predecessor_fv, nat, with_ih)
    };
    let gcd_dvd_step = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_ty = gcd_dvd_recursive_ty(d, m);
        let rec = d.kernel().const_(p.rec, vec![zero_level]);
        let selected = d.apply(
            rec,
            &[
                gcd_dvd_step_motive,
                gcd_dvd_zero_minor,
                gcd_dvd_succ_minor,
                m,
            ],
        );
        let body = d.apply(selected, &[recursive]);
        let with_recursive = d.lam_fv(recursive_fv, recursive_ty, body);
        d.lam_fv(m_fv, nat, with_recursive)
    };
    let gcd_dvd_fix = d
        .kernel()
        .const_(p.logic.well_founded_fix, vec![one, zero_level]);
    let gcd_dvd_all = d.apply(
        gcd_dvd_fix,
        &[nat, relation, gcd_dvd_family, well_founded, gcd_dvd_step],
    );
    let m_fv = d.fresh_fvar();
    let m = d.kernel().fvar(m_fv);
    let n_fv = d.fresh_fvar();
    let n = d.kernel().fvar(n_fv);
    let gcd_dvd_value = d.apply(gcd_dvd_all, &[m, n]);
    let gcd_dvd_body_ty = gcd_dvd_at(d, m, n);
    let gcd_dvd_decl_ty = {
        let with_n = d.pi_fv(n_fv, nat, gcd_dvd_body_ty);
        d.pi_fv(m_fv, nat, with_n)
    };
    let gcd_dvd_decl_value = {
        let with_n = d.lam_fv(n_fv, nat, gcd_dvd_value);
        d.lam_fv(m_fv, nat, with_n)
    };
    d.declare_theorem(p.gcd_dvd, gcd_dvd_decl_ty, gcd_dvd_decl_value)?;

    d.theorem(p.gcd_dvd_left, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let common = d.gcd(m, n);
        let left_ty = d.dvd(common, m);
        let right_ty = d.dvd(common, n);
        let pair = d.lemma(p.gcd_dvd, &[m, n]);
        (left_ty, and_left(d, left_ty, right_ty, pair))
    })?;
    d.theorem(p.gcd_dvd_right, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let common = d.gcd(m, n);
        let left_ty = d.dvd(common, m);
        let right_ty = d.dvd(common, n);
        let pair = d.lemma(p.gcd_dvd, &[m, n]);
        (right_ty, and_right(d, left_ty, right_ty, pair))
    })?;

    declare_dvd_gcd_semantics(d, &p, nat, relation, well_founded, one, zero_level)?;
    Ok(())
}

fn bezout_after_np_exists<D: NatOps>(
    d: &mut D,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    mp: ExprId,
    mn: ExprId,
    np: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let exists_name = d.prelude().logic.exists_;
    let nn_fv = d.fresh_fvar();
    let nn = d.kernel().fvar(nn_fv);
    let equation = d.bezout_equation(m, n, g, mp, mn, np, nn);
    let predicate = d.lam_fv(nn_fv, nat, equation);
    let exists = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists, &[nat, predicate])
}

fn bezout_tail_exists<D: NatOps>(
    d: &mut D,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    mp: ExprId,
    mn: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let exists_name = d.prelude().logic.exists_;
    let np_fv = d.fresh_fvar();
    let np = d.kernel().fvar(np_fv);
    let body = bezout_after_np_exists(d, m, n, g, mp, mn, np);
    let predicate = d.lam_fv(np_fv, nat, body);
    let exists = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists, &[nat, predicate])
}

fn bezout_after_mp_exists<D: NatOps>(
    d: &mut D,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    mp: ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let exists_name = d.prelude().logic.exists_;
    let mn_fv = d.fresh_fvar();
    let mn = d.kernel().fvar(mn_fv);
    let body = bezout_tail_exists(d, m, n, g, mp, mn);
    let predicate = d.lam_fv(mn_fv, nat, body);
    let exists = d.kernel().const_(exists_name, vec![one]);
    d.apply(exists, &[nat, predicate])
}

fn bezout_mp_predicate<D: NatOps>(d: &mut D, m: ExprId, n: ExprId, g: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let mp_fv = d.fresh_fvar();
    let mp = d.kernel().fvar(mp_fv);
    let body = bezout_after_mp_exists(d, m, n, g, mp);
    d.lam_fv(mp_fv, nat, body)
}

fn left_sum(d: &mut NatDev<'_>, terms: &[ExprId]) -> ExprId {
    let mut sum = terms[0];
    for &term in &terms[1..] {
        sum = d.add(sum, term);
    }
    sum
}

fn lift_sum_equality(
    d: &mut NatDev<'_>,
    mut left: ExprId,
    mut right: ExprId,
    mut proof: ExprId,
    suffix: &[ExprId],
) -> (ExprId, ExprId, ExprId) {
    for &term in suffix {
        proof = d.congr(left, right, proof, &|d, value| d.add(value, term));
        left = d.add(left, term);
        right = d.add(right, term);
    }
    (left, right, proof)
}

fn left_sum_adjacent_swap(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    terms: &[ExprId],
    index: usize,
) -> (Vec<ExprId>, ExprId) {
    let mut swapped = terms.to_vec();
    swapped.swap(index, index + 1);
    let (prefix_left, prefix_right, prefix_proof, suffix_start) = if index == 0 {
        let a = terms[0];
        let b = terms[1];
        (d.add(a, b), d.add(b, a), d.lemma(p.add_comm, &[a, b]), 2)
    } else {
        let prefix = left_sum(d, &terms[..index]);
        let a = terms[index];
        let b = terms[index + 1];
        let prefix_a = d.add(prefix, a);
        let prefix_b = d.add(prefix, b);
        (
            d.add(prefix_a, b),
            d.add(prefix_b, a),
            d.lemma(p.add_right_comm, &[prefix, a, b]),
            index + 2,
        )
    };
    let (_, _, proof) = lift_sum_equality(
        d,
        prefix_left,
        prefix_right,
        prefix_proof,
        &terms[suffix_start..],
    );
    (swapped, proof)
}

fn prove_left_sum_permutation(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    source: &[ExprId],
    target: &[ExprId],
) -> ExprId {
    let start = left_sum(d, source);
    let mut current = source.to_vec();
    let mut current_expr = start;
    let mut proof = d.refl(start);
    for index in 0..target.len() {
        let mut found = current[index..]
            .iter()
            .position(|item| *item == target[index])
            .expect("sum permutation target must contain the same atoms")
            + index;
        while found > index {
            let (next, swap) = left_sum_adjacent_swap(d, p, &current, found - 1);
            let next_expr = left_sum(d, &next);
            proof = d.trans(start, current_expr, next_expr, proof, swap);
            current = next;
            current_expr = next_expr;
            found -= 1;
        }
    }
    proof
}

fn prove_bezout_zero_equation(d: &mut NatDev<'_>, p: &NatPrelude, n: ExprId) -> ExprId {
    let zero = d.zero();
    let unit = d.num(1);
    let left = {
        let zero_zero = d.mul(zero, zero);
        let n_zero = d.mul(n, zero);
        let first = d.add(n, zero_zero);
        d.add(first, n_zero)
    };
    let n_one = d.mul(n, unit);
    let right = {
        let zero_zero = d.mul(zero, zero);
        d.add(zero_zero, n_one)
    };
    let left_to_n = d.refl(n);
    let right_to_n_one = d.lemma(p.zero_add, &[n_one]);
    let n_one_to_n = d.lemma(p.mul_one, &[n]);
    let right_to_n = d.trans(right, n_one, n, right_to_n_one, n_one_to_n);
    let n_to_right = d.symm(right, n, right_to_n);
    d.trans(left, n, right, left_to_n, n_to_right)
}

#[allow(clippy::too_many_arguments)]
fn prove_bezout_euclidean_update(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    divisor: ExprId,
    dividend: ExprId,
    remainder: ExprId,
    quotient: ExprId,
    common: ExprId,
    mp: ExprId,
    mn: ExprId,
    np: ExprId,
    nn: ExprId,
    division_equation: ExprId,
    recursive_equation: ExprId,
) -> (ExprId, ExprId, ExprId, ExprId, ExprId) {
    let qmp = d.mul(quotient, mp);
    let qmn = d.mul(quotient, mn);
    let new_mp = d.add(np, qmn);
    let new_mn = d.add(nn, qmp);
    let new_np = mp;
    let new_nn = mn;

    let dnn = d.mul(divisor, nn);
    let d_qmp = d.mul(divisor, qmp);
    let dq = d.mul(divisor, quotient);
    let dqmp = d.mul(dq, mp);
    let dqmn = d.mul(dq, mn);
    let rmn = d.mul(remainder, mn);
    let rmp = d.mul(remainder, mp);
    let dnp = d.mul(divisor, np);
    let nmn = d.mul(dividend, mn);
    let nmp = d.mul(dividend, mp);

    let lhs = {
        let d_new_mn = d.mul(divisor, new_mn);
        let first = d.add(common, d_new_mn);
        d.add(first, nmn)
    };
    let rhs = {
        let d_new_mp = d.mul(divisor, new_mp);
        d.add(d_new_mp, nmp)
    };

    let distributed_negative = d.add(dnn, d_qmp);
    let common_distributed_negative = d.add(common, distributed_negative);
    let lhs1 = d.add(common_distributed_negative, nmn);
    let distribute_negative = d.lemma(p.left_distrib, &[divisor, nn, qmp]);
    let d_new_mn = d.mul(divisor, new_mn);
    let lhs_h1 = d.congr(
        d_new_mn,
        distributed_negative,
        distribute_negative,
        &|d, value| {
            let first = d.add(common, value);
            d.add(first, nmn)
        },
    );
    let common_dnn = d.add(common, dnn);
    let lhs2_prefix = d.add(common_dnn, d_qmp);
    let lhs2 = d.add(lhs2_prefix, nmn);
    let reassociate_negative = d.lemma(p.add_assoc, &[common, dnn, d_qmp]);
    let reassociate_negative = d.symm(
        lhs2_prefix,
        common_distributed_negative,
        reassociate_negative,
    );
    let lhs_h2 = d.congr(
        common_distributed_negative,
        lhs2_prefix,
        reassociate_negative,
        &|d, value| d.add(value, nmn),
    );
    let d_qmp_to_dqmp = {
        let assoc = d.lemma(p.mul_assoc, &[divisor, quotient, mp]);
        d.symm(dqmp, d_qmp, assoc)
    };
    let lhs3_prefix = d.add(common_dnn, dqmp);
    let lhs3 = d.add(lhs3_prefix, nmn);
    let lhs_h3 = d.congr(d_qmp, dqmp, d_qmp_to_dqmp, &|d, value| {
        let prefix = d.add(common_dnn, value);
        d.add(prefix, nmn)
    });
    let dq_plus_r = d.add(dq, remainder);
    let nmn_to_expanded = {
        let replace_n = d.congr(dividend, dq_plus_r, division_equation, &|d, value| {
            d.mul(value, mn)
        });
        let distribute = d.lemma(p.right_distrib, &[dq, remainder, mn]);
        let expanded_product = d.mul(dq_plus_r, mn);
        let expanded_sum = d.add(dqmn, rmn);
        d.trans(nmn, expanded_product, expanded_sum, replace_n, distribute)
    };
    let expanded_nmn = d.add(dqmn, rmn);
    let lhs4 = d.add(lhs3_prefix, expanded_nmn);
    let lhs_h4 = d.congr(nmn, expanded_nmn, nmn_to_expanded, &|d, value| {
        d.add(lhs3_prefix, value)
    });
    let lhs_normal = left_sum(d, &[common, dnn, dqmp, dqmn, rmn]);
    let flatten_lhs = d.lemma(p.add_assoc, &[lhs3_prefix, dqmn, rmn]);
    let lhs_h5 = d.symm(lhs_normal, lhs4, flatten_lhs);
    let (_, lhs_to_normal) = d.chain(
        lhs,
        &[
            (lhs1, lhs_h1),
            (lhs2, lhs_h2),
            (lhs3, lhs_h3),
            (lhs4, lhs_h4),
            (lhs_normal, lhs_h5),
        ],
    );

    let left_canonical_terms = [common, rmn, dnn, dqmp, dqmn];
    let left_normal_terms = [common, dnn, dqmp, dqmn, rmn];
    let lhs_permutation =
        prove_left_sum_permutation(d, p, &left_normal_terms, &left_canonical_terms);
    let left_canonical = left_sum(d, &left_canonical_terms);

    let recursive_left = left_sum(d, &[common, rmn, dnn]);
    let recursive_right = left_sum(d, &[rmp, dnp]);
    let (_, right_canonical, lifted_recursive) = lift_sum_equality(
        d,
        recursive_left,
        recursive_right,
        recursive_equation,
        &[dqmp, dqmn],
    );

    let d_qmn = d.mul(divisor, qmn);
    let distributed_positive = d.add(dnp, d_qmn);
    let rhs1 = d.add(distributed_positive, nmp);
    let distribute_positive = d.lemma(p.left_distrib, &[divisor, np, qmn]);
    let d_new_mp = d.mul(divisor, new_mp);
    let rhs_h1 = d.congr(
        d_new_mp,
        distributed_positive,
        distribute_positive,
        &|d, value| d.add(value, nmp),
    );
    let d_qmn_to_dqmn = {
        let assoc = d.lemma(p.mul_assoc, &[divisor, quotient, mn]);
        d.symm(dqmn, d_qmn, assoc)
    };
    let rhs2_left = d.add(dnp, dqmn);
    let rhs2 = d.add(rhs2_left, nmp);
    let rhs_h2 = d.congr(d_qmn, dqmn, d_qmn_to_dqmn, &|d, value| {
        let left = d.add(dnp, value);
        d.add(left, nmp)
    });
    let nmp_to_expanded = {
        let replace_n = d.congr(dividend, dq_plus_r, division_equation, &|d, value| {
            d.mul(value, mp)
        });
        let distribute = d.lemma(p.right_distrib, &[dq, remainder, mp]);
        let expanded_product = d.mul(dq_plus_r, mp);
        let expanded_sum = d.add(dqmp, rmp);
        d.trans(nmp, expanded_product, expanded_sum, replace_n, distribute)
    };
    let expanded_nmp = d.add(dqmp, rmp);
    let rhs3 = d.add(rhs2_left, expanded_nmp);
    let rhs_h3 = d.congr(nmp, expanded_nmp, nmp_to_expanded, &|d, value| {
        d.add(rhs2_left, value)
    });
    let rhs_normal_terms = [dnp, dqmn, dqmp, rmp];
    let rhs_normal = left_sum(d, &rhs_normal_terms);
    let flatten_rhs = d.lemma(p.add_assoc, &[rhs2_left, dqmp, rmp]);
    let rhs_h4 = d.symm(rhs_normal, rhs3, flatten_rhs);
    let (_, rhs_to_normal) = d.chain(
        rhs,
        &[
            (rhs1, rhs_h1),
            (rhs2, rhs_h2),
            (rhs3, rhs_h3),
            (rhs_normal, rhs_h4),
        ],
    );
    let right_canonical_terms = [rmp, dnp, dqmp, dqmn];
    let rhs_permutation =
        prove_left_sum_permutation(d, p, &rhs_normal_terms, &right_canonical_terms);
    debug_assert_eq!(right_canonical, left_sum(d, &right_canonical_terms));

    let normal_to_left_canonical = d.trans(
        lhs,
        lhs_normal,
        left_canonical,
        lhs_to_normal,
        lhs_permutation,
    );
    let through_recursive = d.trans(
        lhs,
        left_canonical,
        right_canonical,
        normal_to_left_canonical,
        lifted_recursive,
    );
    let normal_to_canonical_rhs = rhs_permutation;
    let canonical_to_normal_rhs = d.symm(rhs_normal, right_canonical, normal_to_canonical_rhs);
    let through_rhs_normal = d.trans(
        lhs,
        right_canonical,
        rhs_normal,
        through_recursive,
        canonical_to_normal_rhs,
    );
    let normal_to_rhs = d.symm(rhs, rhs_normal, rhs_to_normal);
    let proof = d.trans(lhs, rhs_normal, rhs, through_rhs_normal, normal_to_rhs);
    (new_mp, new_mn, new_np, new_nn, proof)
}

#[allow(clippy::too_many_arguments)]
fn eliminate_bezout(
    d: &mut NatDev<'_>,
    m: ExprId,
    n: ExprId,
    g: ExprId,
    source: ExprId,
    target: ExprId,
    build: &dyn Fn(&mut NatDev<'_>, ExprId, ExprId, ExprId, ExprId, ExprId) -> ExprId,
) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let rec_name = d.prelude().logic.exists_rec;
    let outer_predicate = bezout_mp_predicate(d, m, n, g);
    let outer_motive_fv = d.fresh_fvar();
    let outer_ty = d.bezout_witnesses(m, n, g);
    let outer_motive = d.lam_fv(outer_motive_fv, outer_ty, target);
    let outer_minor = {
        let mp_fv = d.fresh_fvar();
        let mp = d.kernel().fvar(mp_fv);
        let after_mp_ty = bezout_after_mp_exists(d, m, n, g, mp);
        let after_mp_fv = d.fresh_fvar();
        let after_mp = d.kernel().fvar(after_mp_fv);
        let after_mp_motive_fv = d.fresh_fvar();
        let after_mp_motive = d.lam_fv(after_mp_motive_fv, after_mp_ty, target);
        let after_mp_minor = {
            let mn_fv = d.fresh_fvar();
            let mn = d.kernel().fvar(mn_fv);
            let tail_ty = bezout_tail_exists(d, m, n, g, mp, mn);
            let tail_fv = d.fresh_fvar();
            let tail = d.kernel().fvar(tail_fv);
            let tail_motive_fv = d.fresh_fvar();
            let tail_motive = d.lam_fv(tail_motive_fv, tail_ty, target);
            let tail_minor = {
                let np_fv = d.fresh_fvar();
                let np = d.kernel().fvar(np_fv);
                let nn_exists_ty = bezout_after_np_exists(d, m, n, g, mp, mn, np);
                let nn_exists_fv = d.fresh_fvar();
                let nn_exists = d.kernel().fvar(nn_exists_fv);
                let nn_motive_fv = d.fresh_fvar();
                let nn_motive = d.lam_fv(nn_motive_fv, nn_exists_ty, target);
                let nn_minor = {
                    let nn_fv = d.fresh_fvar();
                    let nn = d.kernel().fvar(nn_fv);
                    let equation_ty = d.bezout_equation(m, n, g, mp, mn, np, nn);
                    let equation_fv = d.fresh_fvar();
                    let equation = d.kernel().fvar(equation_fv);
                    let body = build(d, mp, mn, np, nn, equation);
                    let with_equation = d.lam_fv(equation_fv, equation_ty, body);
                    d.lam_fv(nn_fv, nat, with_equation)
                };
                let nn_predicate = {
                    let nn_fv = d.fresh_fvar();
                    let nn = d.kernel().fvar(nn_fv);
                    let equation = d.bezout_equation(m, n, g, mp, mn, np, nn);
                    d.lam_fv(nn_fv, nat, equation)
                };
                let rec = d.kernel().const_(rec_name, vec![one]);
                let body = d.apply(rec, &[nat, nn_predicate, nn_motive, nn_minor, nn_exists]);
                let with_exists = d.lam_fv(nn_exists_fv, nn_exists_ty, body);
                d.lam_fv(np_fv, nat, with_exists)
            };
            let np_predicate = {
                let np_fv = d.fresh_fvar();
                let np = d.kernel().fvar(np_fv);
                let body = bezout_after_np_exists(d, m, n, g, mp, mn, np);
                d.lam_fv(np_fv, nat, body)
            };
            let rec = d.kernel().const_(rec_name, vec![one]);
            let body = d.apply(rec, &[nat, np_predicate, tail_motive, tail_minor, tail]);
            let with_tail = d.lam_fv(tail_fv, tail_ty, body);
            d.lam_fv(mn_fv, nat, with_tail)
        };
        let mn_predicate = {
            let mn_fv = d.fresh_fvar();
            let mn = d.kernel().fvar(mn_fv);
            let body = bezout_tail_exists(d, m, n, g, mp, mn);
            d.lam_fv(mn_fv, nat, body)
        };
        let rec = d.kernel().const_(rec_name, vec![one]);
        let body = d.apply(
            rec,
            &[nat, mn_predicate, after_mp_motive, after_mp_minor, after_mp],
        );
        let with_after_mp = d.lam_fv(after_mp_fv, after_mp_ty, body);
        d.lam_fv(mp_fv, nat, with_after_mp)
    };
    let rec = d.kernel().const_(rec_name, vec![one]);
    d.apply(
        rec,
        &[nat, outer_predicate, outer_motive, outer_minor, source],
    )
}

/// Constructive, all-natural Bézout identity for the executable Euclidean gcd.
/// Four naturals encode the positive and negative parts of the two signed
/// coefficients, preserving the zero-axiom Nat lane while retaining the full
/// mathematical content needed by later Gauss and reconstruction theorems.
fn declare_gcd_bezout(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let p = *p;
    let nat = d.nat_ty();
    let prop = d.kernel().sort_zero();
    let anon = d.anon_name();
    let one = d.level_one();
    let zero_level = d.kernel().level_zero();

    // bezout m n g := ∃ mp mn np nn, g + m*mn + n*nn = m*mp + n*np
    {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);
        let body = d.bezout_witnesses(m, n, g);
        let with_g = d.lam_fv(g_fv, nat, body);
        let with_n = d.lam_fv(n_fv, nat, with_g);
        let value = d.lam_fv(m_fv, nat, with_n);
        let g_ty = d.kernel().pi(anon, nat, prop, BinderInfo::Default);
        let n_ty = d.kernel().pi(anon, nat, g_ty, BinderInfo::Default);
        let ty = d.kernel().pi(anon, nat, n_ty, BinderInfo::Default);
        d.kernel().add_declaration(Declaration::Definition {
            name: p.bezout,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(12),
        })?;
    }

    let row = |d: &mut NatDev<'_>, m: ExprId| {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let common = d.gcd(m, n);
        let target = d.bezout(m, n, common);
        d.pi_fv(n_fv, nat, target)
    };
    let recursive_ty = |d: &mut NatDev<'_>, upper: ExprId| {
        let lower_fv = d.fresh_fvar();
        let lower = d.kernel().fvar(lower_fv);
        let related_fv = d.fresh_fvar();
        let related = d.lt(lower, upper);
        let lower_row = row(d, lower);
        let body = d.pi_fv(related_fv, related, lower_row);
        d.pi_fv(lower_fv, nat, body)
    };
    let family = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let body = row(d, m);
        d.lam_fv(m_fv, nat, body)
    };
    let step_motive = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let recursive = recursive_ty(d, m);
        let result = row(d, m);
        let body = d.arrow(recursive, result);
        d.lam_fv(m_fv, nat, body)
    };
    let zero_minor = {
        let zero = d.zero();
        let recursive_fv = d.fresh_fvar();
        let recursive = recursive_ty(d, zero);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let unit = d.num(1);
        let base_equation = prove_bezout_zero_equation(d, &p, n);
        let base = d.bezout_intro(zero, n, n, zero, zero, unit, zero, base_equation);
        let common = d.gcd(zero, n);
        let common_eq_n = d.lemma(p.gcd_zero_left, &[n]);
        let n_eq_common = d.symm(common, n, common_eq_n);
        let motive = d.eq_motive(n, &|d, value| d.bezout(zero, n, value));
        let body = d.transport(n, motive, base, common, n_eq_common);
        let with_n = d.lam_fv(n_fv, nat, body);
        d.lam_fv(recursive_fv, recursive, with_n)
    };
    let succ_minor = {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let divisor = d.succ(predecessor);
        let ignored_ih_fv = d.fresh_fvar();
        let predecessor_recursive = recursive_ty(d, predecessor);
        let predecessor_row = row(d, predecessor);
        let ignored_ih_ty = d.arrow(predecessor_recursive, predecessor_row);
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_type = recursive_ty(d, divisor);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let remainder = d.modulo(n, divisor);
        let quotient = d.div(n, divisor);
        let decrease = d.lemma(p.mod_lt, &[predecessor, n]);
        let recursive_row = d.apply(recursive, &[remainder, decrease]);
        let recursive_proof = d.apply(recursive_row, &[divisor]);
        let recursive_common = d.gcd(remainder, divisor);
        let target_common = d.gcd(divisor, n);
        let recursive_target = d.bezout(divisor, n, recursive_common);
        let division_relation = d.lemma(p.div_mod_exec, &[predecessor, n]);
        let division_equation_ty = {
            let product = d.mul(divisor, quotient);
            let reconstructed = d.add(product, remainder);
            d.eq(n, reconstructed)
        };
        let division_bound_ty = d.lt(remainder, divisor);
        let division_equation = and_left(
            d,
            division_equation_ty,
            division_bound_ty,
            division_relation,
        );
        let transformed = eliminate_bezout(
            d,
            remainder,
            divisor,
            recursive_common,
            recursive_proof,
            recursive_target,
            &|d, mp, mn, np, nn, equation| {
                let (new_mp, new_mn, new_np, new_nn, proof) = prove_bezout_euclidean_update(
                    d,
                    &p,
                    divisor,
                    n,
                    remainder,
                    quotient,
                    recursive_common,
                    mp,
                    mn,
                    np,
                    nn,
                    division_equation,
                    equation,
                );
                d.bezout_intro(
                    divisor,
                    n,
                    recursive_common,
                    new_mp,
                    new_mn,
                    new_np,
                    new_nn,
                    proof,
                )
            },
        );
        let target_eq_recursive = d.lemma(p.gcd_succ, &[predecessor, n]);
        let recursive_eq_target = d.symm(target_common, recursive_common, target_eq_recursive);
        let motive = d.eq_motive(recursive_common, &|d, value| d.bezout(divisor, n, value));
        let body = d.transport(
            recursive_common,
            motive,
            transformed,
            target_common,
            recursive_eq_target,
        );
        let with_n = d.lam_fv(n_fv, nat, body);
        let with_recursive = d.lam_fv(recursive_fv, recursive_type, with_n);
        let with_ignored_ih = d.lam_fv(ignored_ih_fv, ignored_ih_ty, with_recursive);
        d.lam_fv(predecessor_fv, nat, with_ignored_ih)
    };
    let step = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_type = recursive_ty(d, m);
        let rec = d.kernel().const_(p.rec, vec![zero_level]);
        let selected = d.apply(rec, &[step_motive, zero_minor, succ_minor, m]);
        let body = d.apply(selected, &[recursive]);
        let with_recursive = d.lam_fv(recursive_fv, recursive_type, body);
        d.lam_fv(m_fv, nat, with_recursive)
    };
    let relation = d.kernel().const_(p.lt, vec![]);
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);
    let fix = d
        .kernel()
        .const_(p.logic.well_founded_fix, vec![one, zero_level]);
    let all = d.apply(fix, &[nat, relation, family, well_founded, step]);
    d.theorem(p.gcd_bezout, 2, &|d, values| {
        let (m, n) = (values[0], values[1]);
        let common = d.gcd(m, n);
        let target = d.bezout(m, n, common);
        (target, d.apply(all, &[m, n]))
    })?;
    Ok(())
}

/// The relation, motive, well-foundedness witness, and Euclidean step shared by
/// `Nat.gcd` and its checked unfolding equations.
fn gcd_fix_parts(d: &mut NatDev<'_>, p: &NatPrelude) -> (ExprId, ExprId, ExprId, ExprId) {
    let nat = d.nat_ty();
    let one = d.level_one();
    let relation = d.kernel().const_(p.lt, vec![]);
    let nat_to_nat = d.arrow(nat, nat);
    let family = {
        let value_fv = d.fresh_fvar();
        d.lam_fv(value_fv, nat, nat_to_nat)
    };
    let recursive_ty = |d: &mut NatDev<'_>, upper: ExprId| {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let related_fv = d.fresh_fvar();
        let related_ty = d.lt(predecessor, upper);
        let at_relation = d.pi_fv(related_fv, related_ty, nat_to_nat);
        d.pi_fv(predecessor_fv, nat, at_relation)
    };
    let motive = {
        let upper_fv = d.fresh_fvar();
        let upper = d.kernel().fvar(upper_fv);
        let recursive = recursive_ty(d, upper);
        let result = d.arrow(recursive, nat_to_nat);
        d.lam_fv(upper_fv, nat, result)
    };
    let zero_minor = {
        let recursive_fv = d.fresh_fvar();
        let zero = d.zero();
        let recursive = recursive_ty(d, zero);
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);
        let identity = d.lam_fv(value_fv, nat, value);
        d.lam_fv(recursive_fv, recursive, identity)
    };
    let succ_minor = {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let divisor = d.succ(predecessor);
        let ih_fv = d.fresh_fvar();
        let ih_ty = {
            let recursive = recursive_ty(d, predecessor);
            d.arrow(recursive, nat_to_nat)
        };
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_at_divisor = recursive_ty(d, divisor);
        let value_fv = d.fresh_fvar();
        let value = d.kernel().fvar(value_fv);
        let remainder = d.modulo(value, divisor);
        let decrease = d.lemma(p.mod_lt, &[predecessor, value]);
        let recursive_gcd = d.apply(recursive, &[remainder, decrease]);
        let body = d.apply(recursive_gcd, &[divisor]);
        let with_value = d.lam_fv(value_fv, nat, body);
        let with_recursive = d.lam_fv(recursive_fv, recursive_at_divisor, with_value);
        let with_ih = d.lam_fv(ih_fv, ih_ty, with_recursive);
        d.lam_fv(predecessor_fv, nat, with_ih)
    };
    let step = {
        let upper_fv = d.fresh_fvar();
        let upper = d.kernel().fvar(upper_fv);
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_type = recursive_ty(d, upper);
        let rec = d.kernel().const_(p.rec, vec![one]);
        let selected = d.apply(rec, &[motive, zero_minor, succ_minor, upper]);
        let body = d.apply(selected, &[recursive]);
        let with_recursive = d.lam_fv(recursive_fv, recursive_type, body);
        d.lam_fv(upper_fv, nat, with_recursive)
    };
    let well_founded = d.kernel().const_(p.lt_well_founded, vec![]);
    (relation, family, well_founded, step)
}

#[allow(clippy::too_many_arguments)]
fn declare_dvd_gcd_semantics(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
    nat: ExprId,
    relation: ExprId,
    well_founded: ExprId,
    one: LevelId,
    zero_level: LevelId,
) -> Result<(), KernelError> {
    let p = *p;
    let dvd_gcd_target = |d: &mut NatDev<'_>, m: ExprId, n: ExprId, k: ExprId| {
        let common = d.gcd(m, n);
        let divides_m = d.dvd(k, m);
        let divides_n = d.dvd(k, n);
        let divides_common = d.dvd(k, common);
        let n_to_common = d.arrow(divides_n, divides_common);
        d.arrow(divides_m, n_to_common)
    };
    let dvd_gcd_row = |d: &mut NatDev<'_>, m: ExprId| {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let body = dvd_gcd_target(d, m, n, k);
        let with_k = d.pi_fv(k_fv, nat, body);
        d.pi_fv(n_fv, nat, with_k)
    };
    let family = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let row = dvd_gcd_row(d, m);
        d.lam_fv(m_fv, nat, row)
    };
    let recursive_ty = |d: &mut NatDev<'_>, upper: ExprId| {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let related_fv = d.fresh_fvar();
        let related_ty = d.lt(predecessor, upper);
        let row = dvd_gcd_row(d, predecessor);
        let at_relation = d.pi_fv(related_fv, related_ty, row);
        d.pi_fv(predecessor_fv, nat, at_relation)
    };
    let step_motive = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let recursive = recursive_ty(d, m);
        let row = dvd_gcd_row(d, m);
        let body = d.arrow(recursive, row);
        d.lam_fv(m_fv, nat, body)
    };
    let zero_minor = {
        let zero = d.zero();
        let recursive_fv = d.fresh_fvar();
        let recursive = recursive_ty(d, zero);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let divides_zero_ty = d.dvd(k, zero);
        let divides_zero_fv = d.fresh_fvar();
        let divides_n_ty = d.dvd(k, n);
        let divides_n_fv = d.fresh_fvar();
        let divides_n = d.kernel().fvar(divides_n_fv);
        let common = d.gcd(zero, n);
        let equation = d.lemma(p.gcd_zero_left, &[n]);
        let n_to_common = d.symm(common, n, equation);
        let body = transport_dvd_right(d, k, n, common, n_to_common, divides_n);
        let with_divides_n = d.lam_fv(divides_n_fv, divides_n_ty, body);
        let with_divides_zero = d.lam_fv(divides_zero_fv, divides_zero_ty, with_divides_n);
        let with_k = d.lam_fv(k_fv, nat, with_divides_zero);
        let with_n = d.lam_fv(n_fv, nat, with_k);
        d.lam_fv(recursive_fv, recursive, with_n)
    };
    let succ_minor = {
        let predecessor_fv = d.fresh_fvar();
        let predecessor = d.kernel().fvar(predecessor_fv);
        let divisor = d.succ(predecessor);
        let ih_fv = d.fresh_fvar();
        let ih_ty = {
            let recursive = recursive_ty(d, predecessor);
            let row = dvd_gcd_row(d, predecessor);
            d.arrow(recursive, row)
        };
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_type = recursive_ty(d, divisor);
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let k_fv = d.fresh_fvar();
        let k = d.kernel().fvar(k_fv);
        let divides_divisor_ty = d.dvd(k, divisor);
        let divides_divisor_fv = d.fresh_fvar();
        let divides_divisor = d.kernel().fvar(divides_divisor_fv);
        let divides_n_ty = d.dvd(k, n);
        let divides_n_fv = d.fresh_fvar();
        let divides_n = d.kernel().fvar(divides_n_fv);
        let remainder = d.modulo(n, divisor);
        let divides_remainder_ty = d.dvd(k, remainder);
        let remainder_iff = d.lemma(p.dvd_mod_iff, &[k, predecessor, n, divides_divisor]);
        let dividend_to_remainder =
            iff_reverse(d, divides_remainder_ty, divides_n_ty, remainder_iff);
        let divides_remainder = d.apply(dividend_to_remainder, &[divides_n]);
        let decrease = d.lemma(p.mod_lt, &[predecessor, n]);
        let at_remainder = d.apply(recursive, &[remainder, decrease]);
        let at_divisor = d.apply(at_remainder, &[divisor]);
        let at_k = d.apply(at_divisor, &[k]);
        let recursive_proof = d.apply(at_k, &[divides_remainder, divides_divisor]);
        let recursive_common = d.gcd(remainder, divisor);
        let common = d.gcd(divisor, n);
        let equation = d.lemma(p.gcd_succ, &[predecessor, n]);
        let recursive_to_common = d.symm(common, recursive_common, equation);
        let body = transport_dvd_right(
            d,
            k,
            recursive_common,
            common,
            recursive_to_common,
            recursive_proof,
        );
        let with_divides_n = d.lam_fv(divides_n_fv, divides_n_ty, body);
        let with_divides_divisor = d.lam_fv(divides_divisor_fv, divides_divisor_ty, with_divides_n);
        let with_k = d.lam_fv(k_fv, nat, with_divides_divisor);
        let with_n = d.lam_fv(n_fv, nat, with_k);
        let with_recursive = d.lam_fv(recursive_fv, recursive_type, with_n);
        let with_ih = d.lam_fv(ih_fv, ih_ty, with_recursive);
        d.lam_fv(predecessor_fv, nat, with_ih)
    };
    let step = {
        let m_fv = d.fresh_fvar();
        let m = d.kernel().fvar(m_fv);
        let recursive_fv = d.fresh_fvar();
        let recursive = d.kernel().fvar(recursive_fv);
        let recursive_type = recursive_ty(d, m);
        let rec = d.kernel().const_(p.rec, vec![zero_level]);
        let selected = d.apply(rec, &[step_motive, zero_minor, succ_minor, m]);
        let body = d.apply(selected, &[recursive]);
        let with_recursive = d.lam_fv(recursive_fv, recursive_type, body);
        d.lam_fv(m_fv, nat, with_recursive)
    };
    let fix = d
        .kernel()
        .const_(p.logic.well_founded_fix, vec![one, zero_level]);
    let all = d.apply(fix, &[nat, relation, family, well_founded, step]);
    d.theorem(p.dvd_gcd, 3, &|d, values| {
        let (k, m, n) = (values[0], values[1], values[2]);
        let proof = d.apply(all, &[m, n, k]);
        (dvd_gcd_target(d, m, n, k), proof)
    })?;

    d.theorem(p.dvd_gcd_iff, 3, &|d, values| {
        let (k, m, n) = (values[0], values[1], values[2]);
        let common = d.gcd(m, n);
        let divides_common_ty = d.dvd(k, common);
        let divides_m_ty = d.dvd(k, m);
        let divides_n_ty = d.dvd(k, n);
        let pair_ty = d.const_app(p.logic.and, &[divides_m_ty, divides_n_ty]);
        let forward = {
            let proof_fv = d.fresh_fvar();
            let proof = d.kernel().fvar(proof_fv);
            let common_divides_m = d.lemma(p.gcd_dvd_left, &[m, n]);
            let common_divides_n = d.lemma(p.gcd_dvd_right, &[m, n]);
            let divides_m = d.lemma(p.dvd_trans, &[k, common, m, proof, common_divides_m]);
            let divides_n = d.lemma(p.dvd_trans, &[k, common, n, proof, common_divides_n]);
            let pair = d.const_app(
                p.logic.and_intro,
                &[divides_m_ty, divides_n_ty, divides_m, divides_n],
            );
            d.lam_fv(proof_fv, divides_common_ty, pair)
        };
        let reverse = {
            let pair_fv = d.fresh_fvar();
            let pair = d.kernel().fvar(pair_fv);
            let divides_m = and_left(d, divides_m_ty, divides_n_ty, pair);
            let divides_n = and_right(d, divides_m_ty, divides_n_ty, pair);
            let body = d.lemma(p.dvd_gcd, &[k, m, n, divides_m, divides_n]);
            d.lam_fv(pair_fv, pair_ty, body)
        };
        let stmt = d.const_app(p.logic.iff, &[divides_common_ty, pair_ty]);
        let proof = d.const_app(
            p.logic.iff_intro,
            &[divides_common_ty, pair_ty, forward, reverse],
        );
        (stmt, proof)
    })?;
    Ok(())
}

fn gcd_fix_equation(d: &mut NatDev<'_>, p: &NatPrelude, value: ExprId) -> ExprId {
    let nat = d.nat_ty();
    let one = d.level_one();
    let (relation, family, well_founded, step) = gcd_fix_parts(d, p);
    let fix_eq = d
        .kernel()
        .const_(p.logic.well_founded_fix_eq, vec![one, one]);
    d.apply(fix_eq, &[nat, relation, family, well_founded, step, value])
}

#[cfg(test)]
mod nat_prelude_tests;
