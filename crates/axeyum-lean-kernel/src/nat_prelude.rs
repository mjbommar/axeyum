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
//! `left_distrib`, `right_distrib`, `mul_assoc`, `one_mul`, `mul_one`,
//! `mul_eq_zero` (no zero divisors).
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
mod binary;
mod binomial;
mod ble;
mod catalan;
mod choose;
mod defs;
mod diagonal;
mod divisibility;
mod division;
mod fermat;
mod fibonacci;
mod finite;
mod finite_set;
mod gcd;
mod helpers;
mod lcm;
mod modular;
mod no_confusion;
mod ops;
mod order;
mod order_extra;
mod order_more;
mod primes;
mod rectangle;
mod relation;
mod restrict_pair;
mod totient;
pub(crate) mod transposition;
mod vandermonde;

pub use ops::{NatDev, NatOps, NatState};

use algebra::{
    declare_additive_theorems, declare_finite_sum_theorems, declare_mul_no_zero_divisors,
    declare_multiplicative_theorems, declare_subtraction_theorems,
};
use bezout::{declare_euclid_lemma, declare_gcd_bezout, declare_prime_dvd_choose};
use binary::{declare_binary_all, declare_size_all};
use binomial::{
    declare_binomial_theorem, declare_combinatorial_identities, declare_succ_mul_choose_eq,
    declare_succ_sub_of_le,
};
use ble::declare_boolean_le;
use catalan::declare_catalan_all;
use choose::declare_choose_all;
use defs::{
    declare_arithmetic, declare_boolean_equality, declare_defining_equations,
    declare_executable_division, declare_finite_ranges, declare_subtraction,
};
use diagonal::declare_diagonal;
use divisibility::declare_divisibility;
use division::declare_euclidean_division;
use fermat::declare_fermat;
use fibonacci::declare_fib_all;
use finite::{
    declare_fin, declare_injective_surjective, declare_pigeonhole, declare_restrict_injective,
    declare_restrict_maps_into,
};
use finite_set::declare_finite_set_all;
use gcd::{declare_executable_gcd, declare_gcd_semantics};
use lcm::{
    declare_coprime_lcm_eq_mul, declare_dvd_antisymm, declare_gauss_lemma, declare_lcm,
    declare_lcm_comm, declare_lcm_dvd,
};
use modular::declare_modular_congruence;
use no_confusion::declare_no_confusion;
use order::declare_order;
use order_extra::declare_order_extra;
use order_more::declare_order_more;
use primes::{declare_coprime_of_lt_prime, declare_euclid, declare_primes};
use rectangle::declare_rectangle;
use relation::{
    declare_bijective_of_injective_on, declare_bijective_on, declare_comp,
    declare_eq_equivalence_on, declare_injective_on_comp, declare_mod_eq_equivalence_on,
    declare_relation_properties,
};
use restrict_pair::{
    declare_restrict_pair_injective, declare_restrict_pair_maps_into, declare_setwise_fixed,
};
use totient::declare_totient_all;
use transposition::{
    declare_conjugate_injective, declare_conjugate_maps_into, declare_transposition,
    declare_transposition_injective, declare_transposition_involutive,
    declare_transposition_maps_into,
};
use vandermonde::declare_vandermonde_all;

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
    /// `Nat.factorial : Nat → Nat`, by structural recursion on its argument:
    /// `factorial zero ≡ 1` and `factorial (succ n) ≡ factorial n * succ n`
    /// hold **definitionally** (β/δ/ι), exactly as for [`pow`](Self::pow), so a
    /// proof can step through them without an explicit rewrite.
    ///
    /// The first half of Euclid's theorem (`F:nat-exists-prime-gt`): the number
    /// that every `d` with `1 ≤ d ≤ n` divides. See
    /// [`dvd_factorial_of_le`](Self::dvd_factorial_of_le).
    pub factorial: NameId,
    /// `Nat.pred : Nat → Nat`, with `pred zero = zero`.
    pub pred: NameId,
    /// `Nat.sub : Nat → Nat → Nat`, truncated at zero and recursive in the
    /// second argument.
    pub sub: NameId,

    /// `Nat.noConfusionType : Sort u -> Nat -> Nat -> Sort u` — generated
    /// constructor disjointness/injectivity machinery (mirrors what Lean's
    /// elaborator synthesizes for every inductive).
    pub no_confusion_type: NameId,
    /// `Nat.noConfusion : Π (P:Sort u) (n1 n2:Nat), n1 = n2 -> noConfusionType P n1 n2`.
    pub no_confusion: NameId,
    /// `Nat.succ_ne_zero : ∀ n, Not (Eq Nat (succ n) zero)`, proved via `noConfusion`.
    pub succ_ne_zero: NameId,
    /// `Nat.not_lt_zero : ∀ n, Not (Lt n zero)`, proved via `noConfusion` (not a
    /// bespoke discriminator, unlike `not_succ_le_zero` above).
    pub not_lt_zero: NameId,

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
    /// `factorial_zero : factorial zero = succ zero`.
    pub factorial_zero: NameId,
    /// `factorial_succ : ∀ n, factorial (succ n) = factorial n * succ n`.
    pub factorial_succ: NameId,

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

    // --- additional order/pred/sub lemmas (imported-corpus bridge names) ----
    // These are the exact Lean-core flat names a reconstructed corpus proof's
    // type closure resolves against; several are thin wrappers restating an
    // existing prelude fact (a constructor, or a differently-named theorem)
    // under its Lean-core name, proved independently from our own
    // definitions rather than aliased.
    /// `Nat.le_refl : ∀ (n : Nat), Le n n` — the flat top-level name matching
    /// [`le_refl`](Self::le_refl) (`Nat.le.refl`, the constructor).
    pub le_refl_thm: NameId,
    /// `Nat.le_succ : ∀ (n : Nat), Le n (succ n)`.
    pub le_succ: NameId,
    /// `Nat.succ_le_succ : ∀ (n m : Nat), Le n m → Le (succ n) (succ m)` — the
    /// Lean-core name matching [`le_succ_succ`](Self::le_succ_succ).
    pub succ_le_succ: NameId,
    /// `Nat.le_of_lt_succ : ∀ (n m : Nat), Lt n (succ m) → Le n m`.
    pub le_of_lt_succ: NameId,
    /// `Nat.lt_succ_self : ∀ (n : Nat), Lt n (succ n)`.
    pub lt_succ_self: NameId,
    /// `Nat.lt_succ_of_le : ∀ (n m : Nat), Le n m → Lt n (succ m)`.
    pub lt_succ_of_le: NameId,
    /// `Nat.lt_add_one : ∀ (n : Nat), Lt n (add n (succ zero))`.
    pub lt_add_one: NameId,
    /// `Nat.not_succ_le_self : ∀ (n : Nat), Not (Le (succ n) n)` — the
    /// Lean-core name matching [`lt_irrefl`](Self::lt_irrefl) unfolded at
    /// `Lt n n`.
    pub not_succ_le_self: NameId,
    /// `Nat.le_succ_of_le : ∀ (n m : Nat), Le n m → Le n (succ m)` — the
    /// Lean-core name matching the [`le_step`](Self::le_step) constructor.
    pub le_succ_of_le: NameId,
    /// `Nat.zero_lt_succ : ∀ (n : Nat), Lt zero (succ n)`.
    pub zero_lt_succ: NameId,
    /// `Nat.pred_le : ∀ (n : Nat), Le (pred n) n`.
    pub pred_le: NameId,
    /// `Nat.pred_le_pred : ∀ (n m : Nat), Le n m → Le (pred n) (pred m)`.
    pub pred_le_pred: NameId,
    /// `Nat.sub_le : ∀ (n m : Nat), Le (sub n m) n`.
    pub sub_le: NameId,
    /// `Nat.sub_lt : ∀ (n m : Nat), Lt zero n → Lt zero m → Lt (sub n m) n`.
    pub sub_lt: NameId,
    /// `Nat.succ_sub_succ_eq_sub : ∀ (n m : Nat), sub (succ n) (succ m) = sub n m`
    /// — the Lean-core name matching [`succ_sub_succ`](Self::succ_sub_succ).
    pub succ_sub_succ_eq_sub: NameId,

    // --- five more order/beq bridge lemmas (order_more.rs) ------------------
    /// `Nat.lt_of_not_le : ∀ (a b : Nat), Not (Le a b) → Lt b a` — the
    /// constructive trichotomy route (via the internal `le_or_gt` double
    /// induction, not excluded middle): `Nat.le` is decidable, so refuting
    /// `Le a b` picks out the other side of `Or (Le a b) (Lt b a)`.
    pub lt_of_not_le: NameId,
    /// `Nat.lt_or_ge : ∀ (a b : Nat), Or (Lt a b) (Le b a)` — `a ≥ b` unfolds
    /// to `Le b a` (this kernel has no separate `Nat.ge`).
    pub lt_or_ge: NameId,
    /// `Nat.le_of_lt_add_one : ∀ (a b : Nat), Lt a (add b (succ zero)) → Le a b`
    /// — `add b (succ zero)` is definitionally `succ b`, so this is
    /// [`le_of_lt_succ`](Self::le_of_lt_succ) restated at the `+1` spelling.
    pub le_of_lt_add_one: NameId,
    /// `Nat.zero_lt_of_ne_zero : ∀ (n : Nat), Not (Eq Nat n zero) → Lt zero n`.
    pub zero_lt_of_ne_zero: NameId,
    /// `Nat.ne_of_beq_eq_false : ∀ (a b : Nat), beq a b = Bool.false → Not (Eq Nat a b)`
    /// — bridges the boolean and propositional worlds via
    /// [`beq_eq_true_of_eq`](Self::beq_eq_true_of_eq) and the existing
    /// `Bool.false ≠ Bool.true` discriminator (`NatOps::false_true_elim`), so
    /// no new `Bool.noConfusion` machinery was needed for this one.
    pub ne_of_beq_eq_false: NameId,

    // --- boolean `≤`, bridging `Nat.ble` to `Nat.le` -------------------------
    /// `Nat.ble : Nat → Nat → Bool` — the executable analogue of [`beq`](Self::beq):
    /// `ble zero _ ≡ true`, `ble (succ _) zero ≡ false`,
    /// `ble (succ x) (succ y) ≡ ble x y`, all definitionally.
    pub ble: NameId,
    /// `Nat.ble_self_eq_true : ∀ (n : Nat), ble n n = true`.
    pub ble_self_eq_true: NameId,
    /// `Nat.ble_succ_eq_true : ∀ (n m : Nat), ble n m = true → ble n (succ m) = true`.
    pub ble_succ_eq_true: NameId,
    /// `Nat.ble_eq_true_of_le : ∀ (n m : Nat), Le n m → ble n m = true`.
    pub ble_eq_true_of_le: NameId,
    /// `Nat.le_of_ble_eq_true : ∀ (n m : Nat), ble n m = true → Le n m`.
    pub le_of_ble_eq_true: NameId,
    /// `Nat.not_le_of_not_ble_eq_true :
    ///   ∀ (n m : Nat), Not (ble n m = true) → Not (Le n m)`.
    pub not_le_of_not_ble_eq_true: NameId,

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
    /// `Nat.mod_lt : ∀ x y, 0 < y → mod x y < y`.
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
    /// `Nat.lcm a b := div (mul a b) (gcd a b)` — the least common multiple.
    /// `lcm 0 0 = 0` matches Mathlib's convention: at that one degenerate point
    /// `gcd a b = 0` too, and `div _ 0 = 0`, so `lcm 0 0` computes to `0` and
    /// `gcd_mul_lcm` still holds there as `0 * 0 = 0 * 0`.
    pub lcm: NameId,
    /// `Nat.lcm_zero_left : ∀ b, lcm zero b = zero` — `zero_mul`/`zero_div`
    /// collapse the numerator without ever needing `gcd zero b`'s value.
    pub lcm_zero_left: NameId,
    /// `Nat.dvd_lcm_left : ∀ a b, dvd a (lcm a b)`.
    pub dvd_lcm_left: NameId,
    /// `Nat.dvd_lcm_right : ∀ a b, dvd b (lcm a b)`.
    pub dvd_lcm_right: NameId,
    /// `Nat.gcd_mul_lcm : ∀ a b, gcd a b * lcm a b = a * b` — the headline
    /// identity, unconditional (including at `a = b = 0`).
    pub gcd_mul_lcm: NameId,
    /// `Nat.gauss_lemma : ∀ x y z, gcd x y = 1 → x ∣ y*z → x ∣ z` — a
    /// coprime divisor of a product divides the other factor. Built from
    /// `gcd_bezout` by induction on `x`: `x = 0` forces `y = 1` via
    /// `gcd_zero_left`, and `x = succ k` scales the Bézout identity by `z`
    /// and cancels through `dvd_add_right_cancel_of_pos`, exactly the `g = 1`
    /// branch of `euclid_lemma` with the primality side condition dropped.
    pub gauss_lemma: NameId,
    /// `Nat.lcm_dvd : ∀ a b c, dvd a c → dvd b c → dvd (lcm a b) c` — the
    /// "least" half of the least common multiple's universal property.
    pub lcm_dvd: NameId,
    /// `Nat.dvd_antisymm : ∀ a b, dvd a b → dvd b a → Eq a b` — antisymmetry
    /// of divisibility. Conceptually belongs beside `dvd_gcd`/`dvd_gcd_iff`
    /// in `nat_prelude/divisibility.rs`; it lands in `nat_prelude/lcm.rs`
    /// instead (flagged for promotion) because it needs `le_of_dvd`
    /// (declared in `primes.rs`, after `lcm.rs` runs) and another lane held
    /// `divisibility.rs` when this was built. Double induction (`a` then
    /// `b`, both inner IHs unused — a case split, not real recursion):
    /// `a = 0` forces `b = 0` from `dvd 0 b` alone via `zero_mul`; at
    /// `a = succ k`, `b = 0` forces `a = 0` symmetrically from `dvd 0 a`
    /// (no absurdity lemma needed — it *is* the goal at that branch), and
    /// `b = succ j` closes via `le_of_dvd` in both directions plus
    /// `le_antisymm`.
    pub dvd_antisymm: NameId,

    // --- Catalan numbers (`catalan.rs`) --------------------------------------
    /// `Nat.catalan n := choose (n+n) n − choose (n+n) (n+1)` — the closed
    /// form. `Nat.sub` is TOTAL, so the definition needs no `≤` side
    /// condition; the recursive convolution form was priced and NOT built
    /// (it is course-of-values, so a curried accumulator does not reach it).
    pub catalan: NameId,
    /// `Nat.catalan_mul_succ : ∀ n, succ n · catalan n = choose (n+n) n` —
    /// the multiplicative identity tying `catalan` to `choose`, stated so no
    /// division is needed. Proved from two instances of
    /// `Nat.succ_mul_choose_eq` on the odd row `2n−1`, tied together by
    /// `Nat.choose_symm`; the truncated subtraction is handled by the
    /// UNCONDITIONAL `Nat.mul_sub_left_distrib_total`, so no `≤` proof is
    /// required anywhere.
    pub catalan_mul_succ: NameId,
    /// `Nat.lcm_comm : ∀ a b, lcm a b = lcm b a`. Direct from `dvd_antisymm`
    /// fed the two `lcm_dvd` applications (each built from
    /// `dvd_lcm_left`/`dvd_lcm_right` with the endpoints swapped).
    pub lcm_comm: NameId,
    /// `Nat.coprime_lcm_eq_mul : ∀ a b, gcd a b = 1 → lcm a b = a * b`. From
    /// the unconditional `gcd_mul_lcm`, substituting the coprimality
    /// hypothesis and cancelling the leading `1` with `one_mul`.
    pub coprime_lcm_eq_mul: NameId,
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
    /// `Nat.euclid_lemma : ∀ p a b, prime p → p ∣ a*b → p ∣ a ∨ p ∣ b`.
    ///
    /// Primality is spelled out inline as `2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p`
    /// rather than through a `Prime` predicate, because that is the shape the
    /// ledger's `F:nat-euclid-lemma` states and a fact is only closed by the
    /// statement it actually makes.
    pub euclid_lemma: NameId,
    /// `Nat.prime_dvd_choose : ∀ p k, prime p → 0 < k → k < p → p ∣ choose p
    /// k` — a live lane's blocker on the way to Fermat's little theorem.
    /// Primality is spelled inline, matching `euclid_lemma`'s own convention.
    /// From `euclid_lemma` plus `succ_mul_choose_eq`: the absorption identity
    /// gives `k * choose p k = p * choose (p-1) (k-1)`, so `p ∣ k * choose p
    /// k`; `euclid_lemma` splits that into `p ∣ k ∨ p ∣ choose p k`, and
    /// `0 < k < p` rules out the first disjunct (`le_of_dvd` would force
    /// `p ≤ k`).
    pub prime_dvd_choose: NameId,
    /// `Nat.one_le_factorial : ∀ n, Le one (factorial n)`.
    pub one_le_factorial: NameId,
    /// `Nat.exists_prime_gt : ∀ n, ∃ p, n < p ∧ (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p)`.
    ///
    /// Euclid's theorem. Closes ledger fact `F:nat-exists-prime-gt`, whose two
    /// dependencies (`F:nat-dvd-add`, `F:nat-exists-prime-dvd`) are settled.
    pub exists_prime_gt: NameId,
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
    /// `Nat.mul_eq_zero : ∀ a b, a * b = 0 → a = 0 ∨ b = 0` — `ℕ` has no zero
    /// divisors. Proved by a constructor case-split on both factors (not
    /// induction): `a = 0` or `b = 0` are immediate, and `a = succ x`,
    /// `b = succ y` makes the product `succ_mul` + `add_succ` away from a bare
    /// successor, which `succ_ne_zero` refutes against the hypothesis.
    pub mul_eq_zero: NameId,
    /// `Nat.dvd_factorial_of_le : ∀ d n, Le 1 d → Le d n → dvd d (factorial n)`.
    ///
    /// Every positive number at most `n` divides `n!`. This is the first of the
    /// two ingredients Euclid's theorem (`F:nat-exists-prime-gt`) needs — the
    /// number divisible by everything in range — and it is what makes
    /// `1 + n!` have no divisor in `[2, n]`. The other ingredient, "every
    /// `m ≥ 2` has a prime divisor", is
    /// [`exists_prime_dvd`](Self::exists_prime_dvd).
    pub dvd_factorial_of_le: NameId,
    /// `Nat.not_dvd_one_add_mul_of_two_le : ∀ a t, Le two a → Not (dvd a (one+a*t))`.
    pub not_dvd_one_add_mul_of_two_le: NameId,
    /// `Nat.valuation_at_two_mul_sq : ∀ a u, Le two a → Not (dvd a u) → valuationAt a ((a*a)*u) two`.
    pub valuation_at_two_mul_sq: NameId,
    /// `Nat.le_of_dvd : ∀ a n, Le 1 n → dvd a n → Le a n`.
    ///
    /// A divisor of a **positive** number is bounded by it. The positivity
    /// hypothesis is load-bearing: `2 ∣ 0` and `2 ≤ 0` is false.
    pub le_of_dvd: NameId,
    /// `Nat.two_le_succ_or_eq_one : ∀ j, Or (Le two (succ j)) (Eq (succ j) one)`.
    ///
    /// The only successor below `2` is `1` — the dichotomy the least-divisor
    /// search needs before it may offer `succ j` as a candidate divisor.
    pub two_le_succ_or_eq_one: NameId,
    /// `Nat.least_divisor_search : ∀ k m, Or (∃ x, Le two x ∧ (dvd x m ∧ ∀ e, Le two e → Lt e x → Not (dvd e m))) (∀ c, Le two c → Le c k → Not (dvd c m))`.
    ///
    /// Bounded search for the **least** divisor `≥ 2` of `m`, by ordinary
    /// `Nat.rec` on the bound `k`. Constructive: each step decides `succ j ∣ m`
    /// by reducing `beq (mod m (succ j)) 0`, with the two branches separated by
    /// [`div_mod_remainder_eq_zero_iff_dvd`](Self::div_mod_remainder_eq_zero_iff_dvd).
    pub least_divisor_search: NameId,
    /// `Nat.exists_prime_dvd : ∀ m, Le two m → ∃ p, (Le two p ∧ ∀ d, dvd d p → Or (Eq d one) (Eq d p)) ∧ dvd p m`.
    ///
    /// Every `m ≥ 2` has a prime divisor — the second of the two ingredients
    /// Euclid's theorem (`F:nat-exists-prime-gt`) needs, the first being
    /// [`dvd_factorial_of_le`](Self::dvd_factorial_of_le). Primality is spelled
    /// inline because the prelude has no `Prime` predicate. The prime is the
    /// least divisor `≥ 2` supplied by
    /// [`least_divisor_search`](Self::least_divisor_search); minimality is
    /// exactly what makes it prime.
    pub exists_prime_dvd: NameId,
    /// `Nat.coprime_of_lt_prime : ∀ p a, (Le two p ∧ ∀ d, dvd d p → Or (Eq d one) (Eq d p)) → Lt zero a → Lt a p → Eq (gcd a p) one`.
    ///
    /// Every nonzero residue below a prime is invertible modulo it — the fact
    /// that makes ℤ/p a field, proved here as: `gcd a p` divides `p`, so
    /// primality forces it to be `1` or `p`; it also divides `a`, and `a < p`
    /// rules out `p` (`le_of_dvd` would force `p ≤ a`, contradicting `a < p`
    /// via `lt_of_le_of_lt`/`lt_irrefl`), so it is `1`.
    pub coprime_of_lt_prime: NameId,

    // --- binomial coefficients (`choose.rs`) --------------------------------
    /// `Nat.choose : Nat → Nat → Nat`, by structural recursion on both
    /// arguments: `choose n 0 ≡ 1`, `choose 0 (succ k) ≡ 0`,
    /// `choose (succ n) (succ k) ≡ choose n k + choose n (succ k)`.
    pub choose: NameId,
    /// `Nat.choose_zero_right : ∀ n, choose n 0 = 1`.
    pub choose_zero_right: NameId,
    /// `Nat.choose_succ_succ : ∀ n k, choose (succ n) (succ k) = choose n k + choose n (succ k)`
    /// — Pascal's rule.
    pub choose_succ_succ: NameId,
    /// `Nat.zero_choose_succ : ∀ k, choose 0 (succ k) = 0`.
    pub zero_choose_succ: NameId,
    /// `Nat.choose_succ_self_eq_zero : ∀ n, choose n (succ n) = 0`.
    pub choose_succ_self_eq_zero: NameId,
    /// `Nat.choose_self : ∀ n, choose n n = 1`.
    pub choose_self: NameId,
    /// `Nat.choose_symm : ∀ n k, Le k n → choose n k = choose n (sub n k)`.
    pub choose_symm: NameId,

    // --- binomial theorem (`binomial.rs`) -----------------------------------
    /// `Nat.sumRange_add : ∀ f g n, sumRange (fun i => f i + g i) n = sumRange f n + sumRange g n`.
    pub sum_range_add: NameId,
    /// `Nat.sumRange_shiftFront : ∀ f n, sumRange f (succ n) = f 0 + sumRange (fun k => f (succ k)) n`
    /// — peeling the FRONT term off a finite sum, the reindexing counterpart to
    /// the defining (back-peeling) `sum_range_succ`.
    pub sum_range_shift_front: NameId,
    /// `Nat.sumRange_congr_lt : ∀ f g n, (∀ i, Lt i n → f i = g i) → sumRange f n = sumRange g n`
    /// — the BOUNDED pointwise congruence: unlike `sum_range_congr`, the
    /// hypothesis only needs to hold below the sum's own bound.
    pub sum_range_congr_lt: NameId,
    /// `Nat.add_pow_zero : ∀ a b, (a+b)^0 = sumRange (fun k => choose 0 k * a^k * b^(0-k)) 1`
    /// — the `n=0` sanity instance of `add_pow`, checked directly (no
    /// induction) before the general theorem.
    pub add_pow_zero: NameId,
    /// `Nat.add_pow_one : ∀ a b, (a+b)^1 = sumRange (fun k => choose 1 k * a^k * b^(1-k)) 2`
    /// — the `n=1` sanity instance.
    pub add_pow_one: NameId,
    /// `Nat.add_pow : ∀ a b n, (a+b)^n = sumRange (fun k => choose n k * a^k * b^(n-k)) (succ n)`
    /// — the binomial theorem, by induction on `n`.
    pub add_pow: NameId,

    // --- row sum, term bound (`binomial.rs`) --------------------------------
    /// `Nat.one_pow : ∀ m, pow 1 m = 1`. Collapses every `1^k`/`1^(n-k)`
    /// factor of `add_pow`'s summand when specialized at `a = b = 1`.
    pub one_pow: NameId,
    /// `Nat.le_sumRange_of_lt : ∀ f n k, Lt k n → Le (f k) (sumRange f n)` —
    /// a term inside a finite sum's range is at most the sum.
    pub le_sum_range_of_lt: NameId,
    /// `Nat.sum_choose_row : ∀ n, sumRange (fun k => choose n k) (succ n) = pow 2 n`
    /// — the row sum, via `add_pow` at `a = b = 1`.
    pub sum_choose_row: NameId,
    /// `Nat.choose_le_two_pow : ∀ n k, Le k n → Le (choose n k) (pow 2 n)` —
    /// a binomial coefficient is at most `2^n`, an immediate consequence of
    /// [`sum_choose_row`](Self::sum_choose_row) and
    /// [`le_sum_range_of_lt`](Self::le_sum_range_of_lt).
    pub choose_le_two_pow: NameId,

    // --- Vandermonde's convolution prep (`binomial.rs`) ---------------------
    /// `Nat.succ_sub_of_le : ∀ m i, Le i m → sub (succ m) i = succ (sub m i)`
    /// — gives the truncated difference a successor shape once its subtrahend
    /// is known to be at most the minuend. `Nat.sub` recurses on its SECOND
    /// argument, so `sub (succ m) i` does not reduce for a bound `i` the way
    /// `sub m (succ i)` does; this is the lemma that supplies the missing
    /// successor shape Vandermonde's convolution needs to drive Pascal's rule
    /// on the `n`-side index. See the doc comment on
    /// `declare_combinatorial_identities` in `binomial.rs` for the stall this
    /// unblocks. Proved via `le_dest` + `add_sub_cancel_left`, mirroring
    /// `super::choose::sub_succ_of_lt`'s use of `le_dest`/`exists_rec`.
    pub succ_sub_of_le: NameId,
    /// `Nat.succ_mul_choose_eq : ∀ n k, succ k * choose (succ n)(succ k) =
    /// succ n * choose n k` — multiplying a row of Pascal's triangle by its
    /// column index reindexes it one row up. The absorption identity behind
    /// [`prime_dvd_choose`](Self::prime_dvd_choose). Induction on `n`,
    /// generalized over `k`; the successor step splits on `k` too (Pascal
    /// needs a `succ` shape there as well).
    pub succ_mul_choose_eq: NameId,

    // --- Fermat's little theorem (`fermat.rs`) ------------------------------
    /// `Nat.modEq_pow : ∀ d a b k, modEq d a b → modEq d (pow a k) (pow b k)`.
    pub mod_eq_pow: NameId,
    /// `Nat.dvd_sum_range_of_forall_lt :
    ///   ∀ d f n, (∀ k, Lt k n → dvd d (f k)) → dvd d (sumRange f n)`.
    pub dvd_sum_range_of_forall_lt: NameId,
    /// `Nat.add_pow_modeq_prime : prime p → (a+b)^p ≡ a^p + b^p [p]` — the
    /// Frobenius endomorphism / "freshman's dream" over ℕ.
    pub add_pow_modeq_prime: NameId,
    /// `Nat.pow_prime_modeq_self : prime p → a^p ≡ a [p]` — Fermat's little
    /// theorem.
    pub pow_prime_modeq_self: NameId,

    // --- Euler's totient (`totient.rs`) -------------------------------------
    /// `Nat.countRange p n := |{k < n : p k = true}|` — the count of a
    /// decidable (`Bool`-valued) predicate over `[0,n)`, by structural
    /// recursion on `n`. Nothing in this prelude could count a decidable
    /// subset before this.
    pub count_range: NameId,
    /// `Nat.countRange_zero : ∀ p, countRange p 0 = 0`.
    pub count_range_zero: NameId,
    /// `Nat.countRange_succ : ∀ p n, countRange p (succ n) =
    /// countRange p n + (if p n then 1 else 0)`.
    pub count_range_succ: NameId,
    /// `Nat.countRange_le : ∀ p n, countRange p n ≤ n`.
    pub count_range_le: NameId,
    /// `Nat.countRange_congr : ∀ f g n, (∀ i, Eq Bool (f i) (g i)) →
    /// countRange f n = countRange g n` — two predicates that agree
    /// pointwise (everywhere, not just below `n`) count the same subset of
    /// `[0,n)`. Mirrors `sumRange_congr` (`algebra.rs`), the unconditional
    /// congruence law for `sumRange`.
    pub count_range_congr: NameId,
    /// `Nat.countRange_split : ∀ f m j, countRange f (add m j) =
    /// add (countRange f m) (countRange (fun k => f (add m k)) j)` — the
    /// `countRange` analogue of `sumRange_split` (`rectangle.rs`), by
    /// induction on `j` alone (`f`, `m` held fixed).
    pub count_range_split: NameId,
    /// `Nat.beq_eq_false_of_ne : ∀ a b, Not (Eq Nat a b) → beq a b = false` —
    /// the converse of `ne_of_beq_eq_false`, closing the boolean/propositional
    /// bridge from the other side. Proved by deciding `beq a b` itself
    /// (`Bool.rec` into `Or (Eq Bool _ true) (Eq Bool _ false)`, fully
    /// constructive) and refuting the `true` branch via `eq_of_beq_eq_true`.
    pub beq_eq_false_of_ne: NameId,
    /// `Nat.totient n := countRange (fun k => beq (gcd k n) 1) n` — Euler's
    /// totient, the count of residues in `[0,n)` coprime to `n`. `k = 0` is
    /// never counted for `n > 1` (`gcd 0 n = n ≠ 1`), so this matches the
    /// textbook `[1,n]` convention (`n` itself is out of range but was never
    /// coprime to itself for `n > 1` either).
    pub totient: NameId,
    /// `Nat.countRange_eq_pred_of_only_zero_false : ∀ f n, (∀ k, 0 < k → k <
    /// succ n → f k = true) → f 0 = false → countRange f (succ n) = n` — the
    /// counting lemma `totient_prime` rests on: a predicate false at exactly
    /// one endpoint and true everywhere else in the range counts one short of
    /// the range's length.
    pub count_range_eq_pred_of_only_zero_false: NameId,
    /// `Nat.totient_prime : Prime p → totient p = sub p 1` — the bridge that
    /// makes Euler's theorem generalize Fermat's: every prime's totient is
    /// `p - 1`.
    pub totient_prime: NameId,

    // --- `Fin`, and the pigeonhole notions (`finite.rs`) --------------------
    /// `Nat.Fin : Nat → Type 0` — the canonical finite index type
    /// `{0, …, n-1}`, the subtype form `⟨val : Nat, isLt : val < n⟩` declared
    /// as a one-parameter, one-constructor inductive family (the same
    /// data-field-plus-dependent-`Prop`-field shape `CReal` carries, with `n`
    /// as a genuine shared parameter — see `finite.rs`'s module doc).
    pub fin: NameId,
    /// `Nat.Fin.mk : Π (n val : Nat), Lt val n → Fin n`.
    pub fin_mk: NameId,
    /// `Nat.Fin.rec` — the kernel-generated recursor `Fin.val`/`Fin.isLt`
    /// project through.
    pub fin_rec: NameId,
    /// `Nat.Fin.val : Π (n : Nat), Fin n → Nat` — the underlying index.
    pub fin_val: NameId,
    /// `Nat.Fin.isLt : Π (n : Nat) (x : Fin n), Lt (val n x) n`.
    pub fin_is_lt: NameId,
    /// `Nat.Fin.val_mk : ∀ n val (h : Lt val n), Eq Nat (val n (mk n val h)) val`
    /// — `Fin.mk`'s defining equation for its data field, closed by `Eq.refl`
    /// (the recursor ι-reduces on the literal constructor).
    pub fin_val_mk: NameId,
    /// `Nat.injectiveOn f n := ∀ i j, i < n → j < n → f i = f j → i = j` —
    /// injectivity restricted to `{0, …, n-1}`, stated directly over a plain
    /// `Nat → Nat` function (no `Fin` needed: `finite.rs`'s module doc).
    pub injective_on: NameId,
    /// `Nat.surjectiveOn f n := ∀ k, k < n → ∃ i, i < n ∧ f i = k`.
    pub surjective_on: NameId,
    /// `Nat.mapsInto f n := ∀ i, i < n → f i < n` — `f` is a self-map of
    /// `{0, …, n-1}`. The pigeonhole principle needs this hypothesis
    /// explicitly: an injective function into a *larger* codomain need not be
    /// surjective onto a smaller one.
    pub maps_into: NameId,
    /// `Nat.injective_on_imp_surjective_on : ∀ f n, InjectiveOn f n →
    /// MapsInto f n → SurjectiveOn f n` — the finite pigeonhole principle.
    pub injective_on_imp_surjective_on: NameId,
    /// `Nat.restrict_injective : ∀ σ i0 n, InjectiveOn σ (succ n) → Lt i0 n →
    /// InjectiveOn (fun k => point_override σ i0 (σ n) k) n` — restricting an
    /// injective self-map of `{0,…,n}` to `{0,…,n-1}` by overriding the
    /// value at interior index `i0` with `σ n`, one of the two pieces
    /// `Int.prodRange_permute` needs (`finite.rs`'s module doc,
    /// `point_override`).
    pub restrict_injective: NameId,
    /// `Nat.restrict_maps_into : ∀ σ i0 n, InjectiveOn σ (succ n) →
    /// MapsInto σ (succ n) → Lt i0 n → Eq Nat (σ i0) n →
    /// MapsInto (fun k => point_override σ i0 (σ n) k) n` — the companion
    /// closure lemma to [`Self::restrict_injective`].
    pub restrict_maps_into: NameId,
    /// `Nat.transposition : Nat → Nat → Nat → Nat` — `transposition i j k`
    /// swaps `i` and `j` and fixes everything else, built from four nested
    /// `Nat.ble` cuts in the style of `point_override`/`point_swap`
    /// (`transposition.rs`'s module doc). The reusable object
    /// `Int.prodRange_swap` does not give: it takes its swapped function by
    /// hypothesis rather than constructing one.
    pub transposition: NameId,
    /// `Nat.transposition_involutive : ∀ i j, Lt i j → ∀ k,
    /// Eq Nat (transposition i j (transposition i j k)) k`.
    pub transposition_involutive: NameId,
    /// `Nat.transposition_injective : ∀ i j n, Lt i j →
    /// InjectiveOn (fun k => transposition i j k) n` — any involution is
    /// injective, applying [`Self::transposition_involutive`].
    pub transposition_injective: NameId,
    /// `Nat.transposition_maps_into : ∀ i j n, Lt i j → Lt j n →
    /// MapsInto (fun k => transposition i j k) n`.
    pub transposition_maps_into: NameId,
    /// `Nat.conjugate_injective : ∀ t σ n, (∀ x, Eq Nat (t (t x)) x) →
    /// MapsInto t n → InjectiveOn σ n →
    /// InjectiveOn (fun k => t (σ (t k))) n` — conjugating an injective
    /// self-map by any involutive self-map preserves injectivity, generic
    /// over `t` (not specialized to [`Self::transposition`]).
    pub conjugate_injective: NameId,
    /// `Nat.conjugate_maps_into : ∀ t σ n, MapsInto t n → MapsInto σ n →
    /// MapsInto (fun k => t (σ (t k))) n` — the companion closure lemma to
    /// [`Self::conjugate_injective`], needing no involution law.
    pub conjugate_maps_into: NameId,

    // --- `Nat.restrict_pair_*` (`restrict_pair.rs`) — the `N → N-2` step ----
    /// `Nat.setwise_fixed σ i j := And (Eq Nat (σ i) i) (Eq Nat (σ j) j)` —
    /// the POINTWISE form of "σ fixes `{i,j}` setwise" (`restrict_pair.rs`'s
    /// module doc explains why the pointwise form, not the disjunctive
    /// "swaps or fixes" one, is what the interior-collapse application has).
    pub setwise_fixed: NameId,
    /// `Nat.add_sub_cancel_of_le : ∀ i k, Le i k → add i (sub k i) = k` — the
    /// round trip the OTHER way from `sub_add_cancel`: `i` plus its
    /// complement-to-`k` restores `k`, for `i ≤ k`. Immediate from
    /// `sub_add_cancel` plus `add_comm`, but stated on its own because this is
    /// exactly the diagonal pairing `(i, k−i)` over `{(i,j) : i+j=k, i ≤ k}`
    /// — the fact `Nat.sumRange_diagonal`'s antidiagonal index `i` never
    /// appears un-paired with the fact that it, plus its `sub`-computed
    /// partner, IS `k`.
    pub add_sub_cancel_of_le: NameId,
    /// `Nat.sumRange_diagonal : ∀ F n,
    ///   sumRange (fun k => sumRange (fun i => F i (sub k i)) (succ k)) n
    ///     = sumRange (fun i => sumRange (fun j => F i j) (sub n i)) n`
    /// — the Cauchy-product diagonal reindexing: summing `F i j` over the
    /// triangle `{(i,j) : i+j < n}` by ANTIDIAGONAL `k = i+j` (outer bound
    /// `n`, inner index `i` ranging `0..=k` with its partner `k−i`) equals
    /// summing it by ROW `i` (outer bound `n`, inner `j` ranging `0..(n−i)`).
    /// `Nat.sub` appears in both sides' index arithmetic — the diagonal's
    /// partner `k−i` for `i ≤ k`, and the row's remaining budget `n−i` for
    /// `i < n` — but every equation the PROOF uses about it goes through
    /// `succ_sub_of_le`/`sub_self` (the additive round-trip), never through
    /// induction on `sub`'s own recursion. Proved by induction on `n`; see
    /// `nat_prelude/diagonal.rs`'s module doc for why a computationally
    /// subtraction-free statement is not available here (`Exists`'s witness
    /// is not exposed by `Exists.rec`, so `le_dest` cannot supply a VALUE, only
    /// further propositions).
    pub sum_range_diagonal: NameId,

    // --- `rectangle = triangle + corner` (`rectangle.rs`) -------------------
    /// `Nat.sumRange_split : ∀ f m j,
    ///   sumRange f (add m j) = add (sumRange f m) (sumRange (fun k => f (add m k)) j)`
    /// — splitting a finite sum at an arbitrary point, quantified over the
    /// split point `m` and the tail length `j` directly (bound `:= m+j`)
    /// rather than over `m ≤ n`, so the proof (induction on `j`, `f`/`m` held
    /// fixed) never touches `Nat.sub` — the same shape
    /// `Rat.prob_complement`'s private `sum_range_split` uses. ℝ
    /// (`CRealPrelude::sum_range_split`) and ℂ (`ComplexPrelude::sum_range_split`)
    /// already had this; ℕ did not.
    pub sum_range_split: NameId,
    /// `Nat.sumRange_rect_eq_diag_add_corner : ∀ F n,
    ///   sumRange (fun i => sumRange (fun j => F i j) n) n
    ///     = add (sumRange (fun k => sumRange (fun i => F i (sub k i)) (succ k)) n)
    ///           (sumRange (fun i => sumRange (fun k => F i (add (sub n i) k)) i) n)`
    /// — `rectangle = triangle + corner`: the RECTANGLE sum `Σ_{i<n} Σ_{j<n}
    /// F i j` equals the antidiagonal TRIANGLE (`sumRange_diagonal`'s own
    /// LHS, the sum over `{(i,j) : i+j<n}`) plus the CORNER (the sum over
    /// `{(i,j) : i<n, j<n, i+j≥n}`, row `i`'s width-`i` suffix reindexed from
    /// `n−i`). This is the correct replacement for the FALSE naive finite
    /// Cauchy identity `(Σ a)·(Σ b) = Σ_{k<n} Σ_{i≤k} a i · b(k−i)` — false at
    /// `n=2` already, where the rectangle's `a1 b1` term is outside the
    /// triangle. Proved by splitting every row via `sumRange_split` at
    /// `n=(n−i)+i` (pointwise for `i<n`, lifted via `sumRange_congr_lt`),
    /// regrouping via `sumRange_add`, then replacing the row-major half by
    /// the triangle via [`Self::sum_range_diagonal`].
    pub sum_range_rect_eq_diag_add_corner: NameId,

    // --- Vandermonde's convolution (`vandermonde.rs`) -----------------------
    /// `Nat.choose_add_convolution : ∀ m n k, choose (add m n) k = sumRange
    /// (fun i => choose m i * choose n (sub k i)) (succ k)` — Vandermonde's
    /// convolution: binomial coefficients as a convolution algebra. By
    /// induction on `m` (not `n`, and not `m+n`); see `vandermonde.rs`'s
    /// module doc for why that avoids the successor-shape obstruction an
    /// induction on `n` runs into.
    pub choose_add_convolution: NameId,
    /// `Nat.sum_choose_sq : ∀ n, sumRange (fun i => choose n i * choose n i)
    /// (succ n) = choose (add n n) n` — the `m = n = k = n` instance of
    /// [`Self::choose_add_convolution`], via `choose_symm` collapsing
    /// `choose n (sub n i)` to `choose n i` for `i ≤ n`.
    pub sum_choose_sq: NameId,

    /// `Nat.restrict_pair_injective : ∀ σ i j n,
    /// InjectiveOn σ (succ (succ n)) → Lt i j → Lt j (succ (succ n)) →
    /// setwise_fixed σ i j →
    /// InjectiveOn (fun k => compact_pair i j (σ (expand_pair i j k))) n` —
    /// a bijection of `[0, succ (succ n))` fixing `{i,j}` setwise restricts
    /// to an injective self-map of the complement, reindexed to `[0,n)`.
    pub restrict_pair_injective: NameId,
    /// `Nat.restrict_pair_maps_into : ∀ σ i j n,
    /// InjectiveOn σ (succ (succ n)) → MapsInto σ (succ (succ n)) →
    /// Lt i j → Lt j (succ (succ n)) → setwise_fixed σ i j →
    /// MapsInto (fun k => compact_pair i j (σ (expand_pair i j k))) n` — the
    /// companion closure lemma to [`Self::restrict_pair_injective`].
    pub restrict_pair_maps_into: NameId,

    // --- Binary representation (`binary.rs`) ---------------------------------
    /// `Nat.testBitAux : Nat → Nat → Nat`, recursion on the FIRST argument
    /// (the bit index — structural, the fuel route), carrying the second
    /// argument (the number) through unchanged: `testBitAux 0 n ≡ mod n 2`,
    /// `testBitAux (succ i) n ≡ testBitAux i (div n 2)`. Not the public name;
    /// [`Self::test_bit`] flips the argument order to Lean's convention.
    pub test_bit_aux: NameId,
    /// `Nat.testBit n i := testBitAux i n` — the `i`-th binary digit of `n`,
    /// `0` or `1`.
    pub test_bit: NameId,
    /// `Nat.testBit_zero : ∀ n, testBit n 0 = mod n 2` (refl).
    pub test_bit_zero: NameId,
    /// `Nat.testBit_succ : ∀ n i, testBit n (succ i) = testBit (div n 2) i`
    /// (refl — the defining recursion, exposed by name).
    pub test_bit_succ: NameId,
    /// `Nat.testBit_le_one : ∀ n i, Le (testBit n i) 1` — every bit is `0` or
    /// `1`.
    pub test_bit_le_one: NameId,
    /// `Nat.mod_two_mul_split : ∀ n m, Lt 0 m →
    /// add (mul 2 (mod (div n 2) m)) (mod n 2) = mod n (mul m 2)` — peeling
    /// the low bit of `n` before dividing by `m`, the reusable arithmetic
    /// fact `sum_testBit_lt`'s step needs (a general fact, not specific to
    /// `testBit`).
    pub mod_two_mul_split: NameId,
    /// `Nat.sum_testBit_lt : ∀ k n,
    /// sumRange (fun i => mul (testBit n i) (pow 2 i)) k = mod n (pow 2 k)` —
    /// the partial-sum form: the low `k` bits of `n`, read back as a number,
    /// equal `n mod 2^k`.
    pub sum_test_bit_lt: NameId,
    /// `Nat.sizeAux : Nat → Nat → Nat`, `sizeAux fuel n`: recursion on the
    /// FIRST argument (`fuel`, structural — the same fuel route `testBitAux`
    /// uses), with a zero-check Boolean guard on the SECOND argument so the
    /// answer stops changing once `n` hits `0`:
    /// `sizeAux 0 n ≡ 0`; `sizeAux (succ f) n ≡`
    /// `if beq n 0 then 0 else succ (sizeAux f (n / 2))`. Not the public name;
    /// [`Self::size`] supplies fuel `n` itself, which
    /// [`Self::size_aux_lt_pow`] proves is always enough.
    pub size_aux: NameId,
    /// `Nat.size n := sizeAux n n` — the number of binary digits of `n`
    /// (`size 0 = 0`, `size 1 = 1`, `size 13 = 4`, `size 16 = 5`).
    pub size: NameId,
    /// `Nat.size_zero : size 0 = 0` (refl).
    pub size_zero: NameId,
    /// `Nat.size_aux_lt_pow : ∀ fuel n, Le n fuel → Lt n (pow 2 (sizeAux fuel n))`
    /// — for any fuel at least as large as `n`, `sizeAux fuel n` reports enough
    /// bits to bound `n`. This is the fuel-sufficiency fact
    /// [`Self::size`] relies on (specializing at `fuel := n` via `le_refl`
    /// both proves [`Self::lt_pow_size`] and witnesses that `n` itself is
    /// always enough fuel), proved by induction on `fuel` generalized over
    /// `n`, matching [`Self::test_bit_le_one`]/[`Self::sum_test_bit_lt`]'s
    /// shape.
    pub size_aux_lt_pow: NameId,
    /// `Nat.lt_pow_size : ∀ n, Lt n (pow 2 (size n))` — a natural number is
    /// strictly bounded by 2 raised to its own bit count. The
    /// `fuel := n` instance of [`Self::size_aux_lt_pow`].
    pub lt_pow_size: NameId,
    /// `Nat.mod_eq_self_of_lt : ∀ n m, Lt n m → mod n m = n` — a general
    /// division fact (not specific to binary representation), needed as glue
    /// for [`Self::sum_test_bit_eq`]. Proved by comparing the executable
    /// `divMod` witness against the hand-built witness `(quotient := 0,
    /// remainder := n)` via `div_mod_unique`.
    pub mod_eq_self_of_lt: NameId,
    /// `Nat.sum_testBit_eq : ∀ n,
    /// sumRange (fun i => mul (testBit n i) (pow 2 i)) (size n) = n` — a
    /// natural number IS the sum of its own bits. [`Self::sum_test_bit_lt`]
    /// at `k := size n`, closed by [`Self::lt_pow_size`] and
    /// [`Self::mod_eq_self_of_lt`].
    pub sum_test_bit_eq: NameId,

    // --- Fibonacci numbers (`fibonacci.rs`) ----------------------------------
    /// `Nat.fibAux : Nat -> Nat -> Nat -> Nat`, `fibAux i a b`: recursion on
    /// the FIRST argument `i` (the fuel/step-count — structural), threading
    /// TWO ordinary curried `Nat` parameters `a b` through as the accumulator
    /// pair (there is no tuple type in this kernel; two curried parameters
    /// serve the same purpose without one — see `fibonacci.rs`'s module doc
    /// for why the `And`-pairing trick used to prove properties TOGETHER by
    /// ordinary `Nat.rec` does not by itself give a way to DEFINE a
    /// `Nat`-valued function). `fibAux 0 a b ≡ a`; `fibAux (succ i) a b ≡
    /// fibAux i b (add a b)`. Not the public name; [`Self::fib`] supplies the
    /// seed `(0, 1)`.
    pub fib_aux: NameId,
    /// `Nat.fib n := fibAux n 0 1` — the Fibonacci numbers. `fib 0 ≡ 0`,
    /// `fib 1 ≡ 1` by pure `δ`/`ι` reduction (no theorem needed);
    /// `fib (n+2) = fib (n+1) + fib n` is [`Self::fib_add_two`], which is
    /// NOT a bare `δ`/`ι` fact (see its own doc).
    pub fib: NameId,
    /// `Nat.fib_add_two : ∀ n, fib (succ (succ n)) = add (fib (succ n)) (fib n)`
    /// — the defining recurrence, stated over `fib` rather than `fibAux`.
    /// Proved from a STRONGER internal fact generalized over the accumulator
    /// seed (`∀ i a b, fibAux (succ (succ i)) a b = add (fibAux (succ i) a b)
    /// (fibAux i a b)`, built by `fibonacci.rs`'s private
    /// `fib_aux_add_two_gen` and specialized at `a=0, b=1` — the general
    /// statement's induction step closes by defeq alone (the induction
    /// hypothesis applied at the shifted seed `(b, a+b)` already has the
    /// exact type the goal unfolds to); only the base case needs an actual
    /// rewrite, `add_comm`.
    pub fib_add_two: NameId,
    /// `Nat.fib_le_succ : ∀ n, Le (fib n) (fib (succ n))` — the Fibonacci
    /// sequence is non-decreasing. By induction on `n`; the base case is
    /// `zero_le`, and the step needs no induction hypothesis at all —
    /// `fib_add_two` plus `le_add_right` gives it unconditionally.
    pub fib_le_succ: NameId,
    /// `Nat.fib_pos_of_pos : ∀ n, Lt zero n → Lt zero (fib n)` — every `fib`
    /// value past the zeroth is positive. From the unconditional `∀ i, Lt
    /// zero (fib (succ i))` (induction on `i`, base `le_refl`, step
    /// `fib_le_succ` chained through `lt_of_lt_of_le`), transported along
    /// `pos_implies_succ_pred` (`finite.rs`) to discharge the hypothesis.
    pub fib_pos_of_pos: NameId,
    /// `Nat.sum_fib : ∀ n, sumRange fib n = sub (fib (succ n)) one` —
    /// `Σ_{i<n} fib i = fib(n+1) - 1`. Proved from the SUBTRACTION-FREE
    /// internal fact `∀ n, add (sumRange fib n) 1 = fib (succ n)`
    /// (`sum_fib_add_one_gen`, straight induction using `add_right_comm` and
    /// `fib_add_two`), converted to the truncated-subtraction form by
    /// `add_comm` + `add_sub_cancel_left` — `Nat.sub` never drives an
    /// induction step here, only the final one-line conversion.
    pub sum_fib: NameId,
    /// `Nat.fib_add : ∀ m n, fib (succ (add m n)) =
    /// add (mul (fib m) (fib n)) (mul (fib (succ m)) (fib (succ n)))` — the
    /// Fibonacci addition formula, `succ`-shaped so `Nat.sub` never appears.
    /// Proved by pairing `stmt_at n` with `stmt_at (succ n)` and inducting
    /// ordinarily on `n` — the device `fibonacci.rs`'s own module doc names
    /// for PROVING a proposition about two indices at once, as opposed to
    /// DEFINING a function, which is why it was ruled out for `fib` itself.
    /// The successor step folds two `fib_add_two` applications together
    /// through `left_distrib` and a private four-term commutative regroup
    /// (`add_regroup_four`; this prelude has no `add_add_add_comm`).
    pub fib_add: NameId,
    /// `Nat.coprime_fib_succ : ∀ n, gcd (fib n) (fib (succ n)) = 1` —
    /// consecutive Fibonacci numbers are coprime. Induction on `n`; the step
    /// never computes the new `gcd` equation, it shows the new gcd divides
    /// `1` (via `gcd_dvd`, `fib_add_two`, `dvd_add_iff_right`, `dvd_gcd` and
    /// the induction hypothesis) and closes with `eq_one_of_dvd_one`.
    pub coprime_fib_succ: NameId,

    // --- relation properties bounded on `n` (`relation.rs`) -----------------
    /// `Nat.ReflexiveOn r n := ∀ i, i < n → r i i`, for `r : Nat → Nat → Prop`.
    pub reflexive_on: NameId,
    /// `Nat.SymmetricOn r n := ∀ i j, i < n → j < n → r i j → r j i`.
    pub symmetric_on: NameId,
    /// `Nat.TransitiveOn r n := ∀ i j k, i < n → j < n → k < n → r i j →
    /// r j k → r i k`.
    pub transitive_on: NameId,
    /// `Nat.EquivalenceOn r n := ReflexiveOn r n ∧ SymmetricOn r n ∧
    /// TransitiveOn r n` (right-nested `And`).
    pub equivalence_on: NameId,
    /// `Nat.eq_equivalence_on : ∀ n, EquivalenceOn (Eq Nat) n` — equality is
    /// an equivalence relation, the canonical worked instance.
    pub eq_equivalence_on: NameId,
    /// `Nat.modEq_equivalence_on : ∀ m n, EquivalenceOn (Nat.modEq m) n` —
    /// congruence mod `m` is an equivalence relation; connects this L0 node
    /// to the `modular-arithmetic` L2 node.
    pub mod_eq_equivalence_on: NameId,
    /// `Nat.BijectiveOn f n := InjectiveOn f n ∧ MapsInto f n ∧
    /// SurjectiveOn f n`.
    pub bijective_on: NameId,
    /// `Nat.bijective_of_injective_on : ∀ n f, InjectiveOn f n →
    /// MapsInto f n → BijectiveOn f n` — packaging over
    /// [`Self::injective_on_imp_surjective_on`] (`finite.rs`).
    pub bijective_of_injective_on: NameId,
    /// `Nat.comp f g := fun x => f (g x)`.
    pub comp: NameId,
    /// `Nat.injective_on_comp : ∀ n f g, MapsInto g n → InjectiveOn g n →
    /// InjectiveOn f n → InjectiveOn (comp f g) n`.
    pub injective_on_comp: NameId,

    // --- finite sets over a bounded universe (`finite_set.rs`) --------------
    // Curriculum node `sets` (Layer 0, docs/curriculum/00-foundations/sets.md).
    /// `Nat.setUnion p q := fun k => if p k then true else q k`.
    pub set_union: NameId,
    /// `Nat.setInter p q := fun k => if p k then q k else false`.
    pub set_inter: NameId,
    /// `Nat.setCompl p := fun k => if p k then false else true`.
    pub set_compl: NameId,
    /// `Nat.setDiff p q := fun k => if p k then (if q k then false else true) else false`
    /// — `p k ∧ ¬ q k`.
    pub set_diff: NameId,
    /// `Nat.Subset p q n := ∀ k, k < n → p k = true → q k = true` — a
    /// `Prop`-valued `Definition`, the same shape
    /// [`Self::injective_on`] already uses.
    pub subset: NameId,
    /// `Nat.countRange_union_add_inter : ∀ p q n,
    ///   countRange (setUnion p q) n + countRange (setInter p q) n =
    ///   countRange p n + countRange q n` — the two-set inclusion–exclusion
    /// law, stated additively (`Nat.sub` is truncated).
    pub count_range_union_add_inter: NameId,
    /// `Nat.countRange_le_of_subset : ∀ p q n,
    ///   Subset p q n → countRange p n ≤ countRange q n` — cardinality
    /// monotonicity.
    pub count_range_le_of_subset: NameId,
    /// `Nat.countRange_compl : ∀ p n,
    ///   countRange p n + countRange (setCompl p) n = n`.
    pub count_range_compl: NameId,

    // --- pointwise Boolean-lattice laws for finite sets (`finite_set.rs`) --
    // The `sets` curriculum node's own claim: "the same Boolean laws as in
    // propositional logic, one level up". Every statement here is pointwise
    // (`∀ k, … p k … = … q k …`), not an equality of functions — this kernel
    // has no `funext`.
    /// `Nat.setUnion_comm : ∀ p q k, Eq Bool (setUnion p q k) (setUnion q p k)`.
    pub set_union_comm: NameId,
    /// `Nat.setInter_comm : ∀ p q k, Eq Bool (setInter p q k) (setInter q p k)`.
    pub set_inter_comm: NameId,
    /// `Nat.setUnion_assoc : ∀ p q r k,
    ///   Eq Bool (setUnion (setUnion p q) r k) (setUnion p (setUnion q r) k)`.
    pub set_union_assoc: NameId,
    /// `Nat.setInter_assoc : ∀ p q r k,
    ///   Eq Bool (setInter (setInter p q) r k) (setInter p (setInter q r) k)`.
    pub set_inter_assoc: NameId,
    /// `Nat.setUnion_idem : ∀ p k, Eq Bool (setUnion p p k) (p k)`.
    pub set_union_idem: NameId,
    /// `Nat.setInter_idem : ∀ p k, Eq Bool (setInter p p k) (p k)`.
    pub set_inter_idem: NameId,
    /// `Nat.setInter_union_distrib : ∀ p q r k,
    ///   Eq Bool (setInter p (setUnion q r) k)
    ///           (setUnion (setInter p q) (setInter p r) k)`.
    pub set_inter_union_distrib: NameId,
    /// `Nat.setUnion_inter_distrib : ∀ p q r k,
    ///   Eq Bool (setUnion p (setInter q r) k)
    ///           (setInter (setUnion p q) (setUnion p r) k)`.
    pub set_union_inter_distrib: NameId,
    /// `Nat.setUnion_absorb : ∀ p q k, Eq Bool (setUnion p (setInter p q) k) (p k)`.
    pub set_union_absorb: NameId,
    /// `Nat.setInter_absorb : ∀ p q k, Eq Bool (setInter p (setUnion p q) k) (p k)`.
    pub set_inter_absorb: NameId,
    /// `Nat.setCompl_union : ∀ p q k,
    ///   Eq Bool (setCompl (setUnion p q) k) (setInter (setCompl p) (setCompl q) k)`.
    pub set_compl_union: NameId,
    /// `Nat.setCompl_inter : ∀ p q k,
    ///   Eq Bool (setCompl (setInter p q) k) (setUnion (setCompl p) (setCompl q) k)`.
    pub set_compl_inter: NameId,
    /// `Nat.setCompl_involutive : ∀ p k, Eq Bool (setCompl (setCompl p) k) (p k)`.
    pub set_compl_involutive: NameId,
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
        let fin = kernel.name_str(nat, "Fin");
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
            factorial: kernel.name_str(nat, "factorial"),
            pred: kernel.name_str(nat, "pred"),
            sub: kernel.name_str(nat, "sub"),
            no_confusion_type: kernel.name_str(nat, "noConfusionType"),
            no_confusion: kernel.name_str(nat, "noConfusion"),
            succ_ne_zero: kernel.name_str(nat, "succ_ne_zero"),
            not_lt_zero: kernel.name_str(nat, "not_lt_zero"),
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
            factorial_zero: kernel.name_str(nat, "factorial_zero"),
            factorial_succ: kernel.name_str(nat, "factorial_succ"),
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
            le_refl_thm: kernel.name_str(nat, "le_refl"),
            le_succ: kernel.name_str(nat, "le_succ"),
            succ_le_succ: kernel.name_str(nat, "succ_le_succ"),
            le_of_lt_succ: kernel.name_str(nat, "le_of_lt_succ"),
            lt_succ_self: kernel.name_str(nat, "lt_succ_self"),
            lt_succ_of_le: kernel.name_str(nat, "lt_succ_of_le"),
            lt_add_one: kernel.name_str(nat, "lt_add_one"),
            not_succ_le_self: kernel.name_str(nat, "not_succ_le_self"),
            le_succ_of_le: kernel.name_str(nat, "le_succ_of_le"),
            zero_lt_succ: kernel.name_str(nat, "zero_lt_succ"),
            pred_le: kernel.name_str(nat, "pred_le"),
            pred_le_pred: kernel.name_str(nat, "pred_le_pred"),
            sub_le: kernel.name_str(nat, "sub_le"),
            sub_lt: kernel.name_str(nat, "sub_lt"),
            succ_sub_succ_eq_sub: kernel.name_str(nat, "succ_sub_succ_eq_sub"),
            lt_of_not_le: kernel.name_str(nat, "lt_of_not_le"),
            lt_or_ge: kernel.name_str(nat, "lt_or_ge"),
            le_of_lt_add_one: kernel.name_str(nat, "le_of_lt_add_one"),
            zero_lt_of_ne_zero: kernel.name_str(nat, "zero_lt_of_ne_zero"),
            ne_of_beq_eq_false: kernel.name_str(nat, "ne_of_beq_eq_false"),
            ble: kernel.name_str(nat, "ble"),
            ble_self_eq_true: kernel.name_str(nat, "ble_self_eq_true"),
            ble_succ_eq_true: kernel.name_str(nat, "ble_succ_eq_true"),
            ble_eq_true_of_le: kernel.name_str(nat, "ble_eq_true_of_le"),
            le_of_ble_eq_true: kernel.name_str(nat, "le_of_ble_eq_true"),
            not_le_of_not_ble_eq_true: kernel.name_str(nat, "not_le_of_not_ble_eq_true"),
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
            lcm: kernel.name_str(nat, "lcm"),
            lcm_zero_left: kernel.name_str(nat, "lcm_zero_left"),
            dvd_lcm_left: kernel.name_str(nat, "dvd_lcm_left"),
            dvd_lcm_right: kernel.name_str(nat, "dvd_lcm_right"),
            gcd_mul_lcm: kernel.name_str(nat, "gcd_mul_lcm"),
            gauss_lemma: kernel.name_str(nat, "gauss_lemma"),
            lcm_dvd: kernel.name_str(nat, "lcm_dvd"),
            dvd_antisymm: kernel.name_str(nat, "dvd_antisymm"),
            catalan: kernel.name_str(nat, "catalan"),
            catalan_mul_succ: kernel.name_str(nat, "catalan_mul_succ"),
            lcm_comm: kernel.name_str(nat, "lcm_comm"),
            coprime_lcm_eq_mul: kernel.name_str(nat, "coprime_lcm_eq_mul"),
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
            euclid_lemma: kernel.name_str(nat, "euclid_lemma"),
            prime_dvd_choose: kernel.name_str(nat, "prime_dvd_choose"),
            one_le_factorial: kernel.name_str(nat, "one_le_factorial"),
            exists_prime_gt: kernel.name_str(nat, "exists_prime_gt"),
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
            mul_eq_zero: kernel.name_str(nat, "mul_eq_zero"),
            dvd_factorial_of_le: kernel.name_str(nat, "dvd_factorial_of_le"),
            not_dvd_one_add_mul_of_two_le: kernel.name_str(nat, "not_dvd_one_add_mul_of_two_le"),
            valuation_at_two_mul_sq: kernel.name_str(nat, "valuation_at_two_mul_sq"),
            le_of_dvd: kernel.name_str(nat, "le_of_dvd"),
            two_le_succ_or_eq_one: kernel.name_str(nat, "two_le_succ_or_eq_one"),
            least_divisor_search: kernel.name_str(nat, "least_divisor_search"),
            exists_prime_dvd: kernel.name_str(nat, "exists_prime_dvd"),
            coprime_of_lt_prime: kernel.name_str(nat, "coprime_of_lt_prime"),
            choose: kernel.name_str(nat, "choose"),
            choose_zero_right: kernel.name_str(nat, "choose_zero_right"),
            choose_succ_succ: kernel.name_str(nat, "choose_succ_succ"),
            zero_choose_succ: kernel.name_str(nat, "zero_choose_succ"),
            choose_succ_self_eq_zero: kernel.name_str(nat, "choose_succ_self_eq_zero"),
            choose_self: kernel.name_str(nat, "choose_self"),
            choose_symm: kernel.name_str(nat, "choose_symm"),
            sum_range_add: kernel.name_str(nat, "sumRange_add"),
            sum_range_shift_front: kernel.name_str(nat, "sumRange_shiftFront"),
            sum_range_congr_lt: kernel.name_str(nat, "sumRange_congr_lt"),
            add_pow_zero: kernel.name_str(nat, "add_pow_zero"),
            add_pow_one: kernel.name_str(nat, "add_pow_one"),
            add_pow: kernel.name_str(nat, "add_pow"),
            one_pow: kernel.name_str(nat, "one_pow"),
            le_sum_range_of_lt: kernel.name_str(nat, "le_sumRange_of_lt"),
            sum_choose_row: kernel.name_str(nat, "sum_choose_row"),
            choose_le_two_pow: kernel.name_str(nat, "choose_le_two_pow"),
            succ_sub_of_le: kernel.name_str(nat, "succ_sub_of_le"),
            succ_mul_choose_eq: kernel.name_str(nat, "succ_mul_choose_eq"),
            mod_eq_pow: kernel.name_str(nat, "modEq_pow"),
            dvd_sum_range_of_forall_lt: kernel.name_str(nat, "dvd_sumRange_of_forall_lt"),
            add_pow_modeq_prime: kernel.name_str(nat, "add_pow_modeq_prime"),
            pow_prime_modeq_self: kernel.name_str(nat, "pow_prime_modeq_self"),
            count_range: kernel.name_str(nat, "countRange"),
            count_range_zero: kernel.name_str(nat, "countRange_zero"),
            count_range_succ: kernel.name_str(nat, "countRange_succ"),
            count_range_le: kernel.name_str(nat, "countRange_le"),
            count_range_congr: kernel.name_str(nat, "countRange_congr"),
            count_range_split: kernel.name_str(nat, "countRange_split"),
            beq_eq_false_of_ne: kernel.name_str(nat, "beq_eq_false_of_ne"),
            totient: kernel.name_str(nat, "totient"),
            count_range_eq_pred_of_only_zero_false: kernel
                .name_str(nat, "countRange_eq_pred_of_only_zero_false"),
            totient_prime: kernel.name_str(nat, "totient_prime"),
            fin,
            fin_mk: kernel.name_str(fin, "mk"),
            fin_rec: kernel.name_str(fin, "rec"),
            fin_val: kernel.name_str(fin, "val"),
            fin_is_lt: kernel.name_str(fin, "isLt"),
            fin_val_mk: kernel.name_str(fin, "val_mk"),
            injective_on: kernel.name_str(nat, "injectiveOn"),
            surjective_on: kernel.name_str(nat, "surjectiveOn"),
            maps_into: kernel.name_str(nat, "mapsInto"),
            injective_on_imp_surjective_on: kernel.name_str(nat, "injective_on_imp_surjective_on"),
            restrict_injective: kernel.name_str(nat, "restrict_injective"),
            restrict_maps_into: kernel.name_str(nat, "restrict_maps_into"),
            transposition: kernel.name_str(nat, "transposition"),
            transposition_involutive: kernel.name_str(nat, "transposition_involutive"),
            transposition_injective: kernel.name_str(nat, "transposition_injective"),
            transposition_maps_into: kernel.name_str(nat, "transposition_maps_into"),
            conjugate_injective: kernel.name_str(nat, "conjugate_injective"),
            conjugate_maps_into: kernel.name_str(nat, "conjugate_maps_into"),
            setwise_fixed: kernel.name_str(nat, "setwise_fixed"),
            add_sub_cancel_of_le: kernel.name_str(nat, "add_sub_cancel_of_le"),
            sum_range_diagonal: kernel.name_str(nat, "sumRange_diagonal"),
            sum_range_split: kernel.name_str(nat, "sumRange_split"),
            sum_range_rect_eq_diag_add_corner: kernel
                .name_str(nat, "sumRange_rect_eq_diag_add_corner"),
            choose_add_convolution: kernel.name_str(nat, "choose_add_convolution"),
            sum_choose_sq: kernel.name_str(nat, "sum_choose_sq"),
            restrict_pair_injective: kernel.name_str(nat, "restrict_pair_injective"),
            restrict_pair_maps_into: kernel.name_str(nat, "restrict_pair_maps_into"),
            test_bit_aux: kernel.name_str(nat, "testBitAux"),
            test_bit: kernel.name_str(nat, "testBit"),
            test_bit_zero: kernel.name_str(nat, "testBit_zero"),
            test_bit_succ: kernel.name_str(nat, "testBit_succ"),
            test_bit_le_one: kernel.name_str(nat, "testBit_le_one"),
            mod_two_mul_split: kernel.name_str(nat, "mod_two_mul_split"),
            sum_test_bit_lt: kernel.name_str(nat, "sum_testBit_lt"),
            size_aux: kernel.name_str(nat, "sizeAux"),
            size: kernel.name_str(nat, "size"),
            size_zero: kernel.name_str(nat, "size_zero"),
            size_aux_lt_pow: kernel.name_str(nat, "size_aux_lt_pow"),
            lt_pow_size: kernel.name_str(nat, "lt_pow_size"),
            mod_eq_self_of_lt: kernel.name_str(nat, "mod_eq_self_of_lt"),
            sum_test_bit_eq: kernel.name_str(nat, "sum_testBit_eq"),
            fib_aux: kernel.name_str(nat, "fibAux"),
            fib: kernel.name_str(nat, "fib"),
            fib_add_two: kernel.name_str(nat, "fib_add_two"),
            fib_le_succ: kernel.name_str(nat, "fib_le_succ"),
            fib_pos_of_pos: kernel.name_str(nat, "fib_pos_of_pos"),
            sum_fib: kernel.name_str(nat, "sum_fib"),
            fib_add: kernel.name_str(nat, "fib_add"),
            coprime_fib_succ: kernel.name_str(nat, "coprime_fib_succ"),
            reflexive_on: kernel.name_str(nat, "reflexiveOn"),
            symmetric_on: kernel.name_str(nat, "symmetricOn"),
            transitive_on: kernel.name_str(nat, "transitiveOn"),
            equivalence_on: kernel.name_str(nat, "equivalenceOn"),
            eq_equivalence_on: kernel.name_str(nat, "eq_equivalence_on"),
            mod_eq_equivalence_on: kernel.name_str(nat, "modEq_equivalence_on"),
            bijective_on: kernel.name_str(nat, "bijectiveOn"),
            bijective_of_injective_on: kernel.name_str(nat, "bijective_of_injective_on"),
            comp: kernel.name_str(nat, "comp"),
            injective_on_comp: kernel.name_str(nat, "injective_on_comp"),
            set_union: kernel.name_str(nat, "setUnion"),
            set_inter: kernel.name_str(nat, "setInter"),
            set_compl: kernel.name_str(nat, "setCompl"),
            set_diff: kernel.name_str(nat, "setDiff"),
            subset: kernel.name_str(nat, "Subset"),
            count_range_union_add_inter: kernel.name_str(nat, "countRange_union_add_inter"),
            count_range_le_of_subset: kernel.name_str(nat, "countRange_le_of_subset"),
            count_range_compl: kernel.name_str(nat, "countRange_compl"),
            set_union_comm: kernel.name_str(nat, "setUnion_comm"),
            set_inter_comm: kernel.name_str(nat, "setInter_comm"),
            set_union_assoc: kernel.name_str(nat, "setUnion_assoc"),
            set_inter_assoc: kernel.name_str(nat, "setInter_assoc"),
            set_union_idem: kernel.name_str(nat, "setUnion_idem"),
            set_inter_idem: kernel.name_str(nat, "setInter_idem"),
            set_inter_union_distrib: kernel.name_str(nat, "setInter_union_distrib"),
            set_union_inter_distrib: kernel.name_str(nat, "setUnion_inter_distrib"),
            set_union_absorb: kernel.name_str(nat, "setUnion_absorb"),
            set_inter_absorb: kernel.name_str(nat, "setInter_absorb"),
            set_compl_union: kernel.name_str(nat, "setCompl_union"),
            set_compl_inter: kernel.name_str(nat, "setCompl_inter"),
            set_compl_involutive: kernel.name_str(nat, "setCompl_involutive"),
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
        declare_no_confusion(&mut d, &p)?;
        declare_mul_no_zero_divisors(&mut d, &p)?;
        declare_order_extra(&mut d, &p)?;
        declare_order_more(&mut d, &p)?;
        declare_boolean_le(&mut d, &p)?;
        declare_euclidean_division(&mut d, &p)?;
        declare_divisibility(&mut d, &p)?;
        declare_executable_gcd(&mut d, &p)?;
        declare_gcd_semantics(&mut d, &p)?;
        declare_lcm(&mut d, &p)?;
        declare_gcd_bezout(&mut d, &p)?;
        declare_gauss_lemma(&mut d, &p)?;
        declare_lcm_dvd(&mut d, &p)?;
        declare_euclid_lemma(&mut d, &p)?;
        declare_modular_congruence(&mut d, &p)?;
        declare_primes(&mut d, &p)?;
        // Needs `le_of_dvd` (just declared by `declare_primes`), so these
        // cannot run inside `declare_lcm` above despite conceptually
        // belonging there — see `dvd_antisymm`'s doc comment.
        declare_dvd_antisymm(&mut d, &p)?;
        declare_lcm_comm(&mut d, &p)?;
        declare_coprime_lcm_eq_mul(&mut d, &p)?;
        declare_coprime_of_lt_prime(&mut d, &p)?;
        declare_euclid(&mut d, &p)?;
        declare_choose_all(&mut d, &p)?;
        declare_binomial_theorem(&mut d, &p)?;
        declare_combinatorial_identities(&mut d, &p)?;
        declare_succ_sub_of_le(&mut d, &p)?;
        declare_succ_mul_choose_eq(&mut d, &p)?;
        declare_prime_dvd_choose(&mut d, &p)?;
        declare_fermat(&mut d, &p)?;
        declare_totient_all(&mut d, &p)?;
        declare_finite_set_all(&mut d, &p)?;
        declare_fin(&mut d, &p)?;
        declare_injective_surjective(&mut d, &p)?;
        declare_pigeonhole(&mut d, &p)?;
        declare_restrict_injective(&mut d, &p)?;
        declare_restrict_maps_into(&mut d, &p)?;
        declare_transposition(&mut d, &p)?;
        declare_transposition_involutive(&mut d, &p)?;
        declare_transposition_injective(&mut d, &p)?;
        declare_transposition_maps_into(&mut d, &p)?;
        declare_conjugate_injective(&mut d, &p)?;
        declare_conjugate_maps_into(&mut d, &p)?;
        declare_setwise_fixed(&mut d, &p)?;
        declare_restrict_pair_injective(&mut d, &p)?;
        declare_restrict_pair_maps_into(&mut d, &p)?;
        declare_diagonal(&mut d, &p)?;
        declare_rectangle(&mut d, &p)?;
        declare_vandermonde_all(&mut d, &p)?;
        declare_catalan_all(&mut d, &p)?;
        declare_binary_all(&mut d, &p)?;
        declare_size_all(&mut d, &p)?;
        declare_fib_all(&mut d, &p)?;
        declare_relation_properties(&mut d, &p)?;
        declare_eq_equivalence_on(&mut d, &p)?;
        declare_mod_eq_equivalence_on(&mut d, &p)?;
        declare_bijective_on(&mut d, &p)?;
        declare_bijective_of_injective_on(&mut d, &p)?;
        declare_comp(&mut d, &p)?;
        declare_injective_on_comp(&mut d, &p)?;
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
