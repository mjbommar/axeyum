//! The **rational prelude**: `ℚ` **constructed** over the proved `ℤ` and `ℕ`
//! developments, as an ordered field, declared through the trusted
//! [`Kernel::add_declaration`](crate::Kernel::add_declaration) gate.
//!
//! ## Why this is the missing rung
//!
//! `AxReal` is 30 trusted constants. Enumerate them and 22 are the laws of an
//! **ordered commutative ring with `1`** — no inverse, no completeness, no
//! Archimedean axiom (`crate::arith_model`, ADR-0456). `ℤ` already models all
//! 22 with an empty axiom footprint. `ℚ` is the next rung because it is the
//! smallest carrier that is also a *field*, and it is the carrier a
//! Farkas/`LRA` refutation actually lives over: Farkas multipliers are
//! rational, so "no rational solution" wants an axiom-free `ℚ` to be a
//! statement about rather than an assumption of.
//!
//! ## Representation: a normalised structure, not a quotient
//!
//! The carrier itself — `Rat`, `Rat.mk`, `Rat.normalize`, the projections,
//! `Rat.add`, `Rat.mul`, `Rat.neg` — is declared by
//! [`build_int_prelude`](crate::build_int_prelude), because it is built out of
//! `Int` and `Nat` names and nothing outside used it yet. This module adds
//! everything that makes it an **ordered field**: the constants, the order, the
//! inverse, and the laws.
//!
//! A setoid quotient of `ℤ × ℤ≠0` is the textbook route and is **inexpressible
//! in this kernel**: the quotient package is `Quot`, `Quot.mk`, `Quot.lift`,
//! `Quot.ind` with **no `Quot.sound`**, so nothing can prove two `Quot.mk`s
//! equal (ADR-0456). A normalised pair `num/den` with `1 ≤ den` and
//! `gcd |num| den = 1` gives every rational exactly one representative, so
//! `Eq Rat` is ordinary propositional equality — the same move `Int` makes with
//! `ofNat`/`negSucc`, and the reason a derived law's footprint is genuinely
//! empty.
//!
//! The price of that choice is paid once, in [`core`]: because `Rat.add` and
//! `Rat.mul` renormalise, no ring law is definitional, and every one of them
//! goes through the **uniqueness of the reduced representative**
//! (`Rat.eq_of_cross`), which needs Gauss's lemma over `ℕ` and cancellation
//! over `ℤ`. Once that is paid, a ring law reduces to a cross-multiplication
//! identity in the constructed `ℤ`.
// Proof scripts are long, straight-line term constructions with short
// mathematical names, exactly as in `nat_prelude` and `int_prelude`.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_arguments,
    clippy::too_many_lines,
    clippy::type_complexity,
    clippy::large_types_passed_by_value
)]

use crate::int_prelude::{IntPrelude, build_int_prelude};
use crate::name::NameId;
use crate::{Kernel, KernelError};

mod abs;
mod archimedean;
mod core;
mod decide;
mod defs;
mod field;
pub(crate) mod group;
pub(crate) mod lattice;
mod laws;
mod model;
pub(crate) mod ops;
mod probability;
mod product;
mod scaling;
mod statements;
mod sum;

pub use model::{RatModel, RatModelLaw, build_rat_model_of_arith};

use crate::int_prelude::ops::IntDev;

/// The interned names produced by [`build_rat_prelude`]: the field constants,
/// the order, the inverse, the structural characterisation of the normalised
/// representative, and every law of the ordered commutative ring — plus the
/// embedded [`IntPrelude`] that carries the carrier itself.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RatPrelude {
    /// The integer development `Rat` is constructed over. It also carries the
    /// carrier (`int.rat`), the constructor, the projections, and `add`, `mul`,
    /// `neg`.
    pub int: IntPrelude,

    // --- constants, order, inverse -------------------------------------------
    /// `Rat.zero : Rat` — `0/1`, built with `Rat.mk` so both projections
    /// compute.
    pub zero: NameId,
    /// `Rat.one : Rat` — `1/1`.
    pub one: NameId,
    /// `Rat.le : Rat → Rat → Prop`, by cross-multiplication into `Int.le`.
    pub le: NameId,
    /// `Rat.lt : Rat → Rat → Prop`, by cross-multiplication into `Int.lt`.
    pub lt: NameId,
    /// `Rat.mul_inv_cancel : ∀ q, Rat.lt Rat.zero q →
    /// Eq Rat (Rat.mul q (Rat.inv q)) Rat.one`.
    ///
    /// **The law that makes `ℚ` a field.** `Rat.inv` existed as a definition
    /// from the start and nothing said it inverted anything; this is the gap
    /// between the 22 ordered-*ring* laws and an ordered *field*. The proof is
    /// the only one in the field module that touches the representation — a
    /// three-way case split on `Rat.num q` — because `Rat.inv q` is stuck until
    /// the numerator is in constructor form.
    ///
    /// The hypothesis is `0 < q`, not `q ≠ 0`: over `ℚ` the two are one
    /// (proved) case split apart, but they are **not** interchangeable over the
    /// reals, and stating it positively is what lets `CReal`'s inverse consume
    /// it without a sign decision it cannot make.
    pub mul_inv_cancel: NameId,
    /// `Rat.mul_inv_cancel_of_neg : ∀ q, Rat.lt q Rat.zero →
    /// Eq Rat (Rat.mul q (Rat.inv q)) Rat.one` — the companion for `q < 0`.
    ///
    /// Over `ℚ` there is no Markov obstruction to a single `q ≠ 0` statement
    /// (the order is decidable — `le_or_lt`/`lt_trichotomy` are proved — so a
    /// trichotomy witness would do), but a **companion theorem** is what this
    /// development actually needed and what stays parallel to
    /// [`Self::mul_inv_cancel`]'s own hypothesis shape. It is a **second**
    /// three-way case split on `Rat.num q` — not a reduction to the positive
    /// case via `Rat.inv (Rat.neg q) = Rat.neg (Rat.inv q)`, because *that*
    /// identity is exactly as representation-heavy to prove as this theorem
    /// is directly (both need `Rat.normalize` to know how it interacts with a
    /// negated numerator), so reducing to it buys nothing. The good branch is
    /// `num q = negSucc m` (mirrored from `mul_inv_cancel`'s `ofNat (k+1)`);
    /// unlike the positive proof's two dead branches (needing
    /// `eq_zero_of_num_zero` and an `ι`-reduction to `False` respectively), the
    /// single dead branch here — `num q = ofNat n` for *any* `n`, `0` or
    /// `succ` — collapses in one shot: `Rat.lt q Rat.zero` unfolds (via
    /// `int.mul_one`/`int_zero_mul`, the same rewrite `int_pos_of_pos` uses)
    /// to `Int.lt (num q) Int.zero`, and at `num q = ofNat n` that is `ι`-equal
    /// to `Nat.lt n 0`, refuted uniformly by `Nat.not_lt_zero` — no nested
    /// `Nat.rec` on `n` needed, unlike the positive proof's `n = 0` sub-case.
    pub mul_inv_cancel_of_neg: NameId,
    /// `Rat.mul_pos : ∀ a b, Rat.lt Rat.zero a → Rat.lt Rat.zero b →
    /// Rat.lt Rat.zero (Rat.mul a b)`.
    ///
    /// **A field lemma, not a ring one.** The 22 give `mul_nonneg` and the
    /// strict version does not follow from it by any rearrangement — `0 ≤ a·b`
    /// holds of the zero product too. This one goes through [`Self::inv_pos`].
    pub mul_pos: NameId,
    /// `Rat.natDivSucc_pos : ∀ (k j : Nat), Nat.le 1 k →
    /// Rat.lt Rat.zero (Rat.natDivSucc k j)` — the **strict** companion of
    /// [`Self::zero_le_nat_div_succ`].
    pub nat_div_succ_pos: NameId,
    /// `Rat.sub_mul : ∀ a b w, Rat.sub (Rat.mul a w) (Rat.mul b w) =
    /// Rat.mul (Rat.sub a b) w` — the right-hand distributive law over a
    /// difference, which is [`Self::mul_sub_mul`] with its first summand
    /// collapsed.
    pub sub_mul: NameId,
    /// `Rat.mul_inv_sub_one : ∀ a b, Rat.lt Rat.zero b →
    /// Rat.sub (Rat.mul a (Rat.inv b)) Rat.one = Rat.mul (Rat.sub a b) (Rat.inv b)`.
    ///
    /// The shape `x · x⁻¹ ≈ 1` is estimated in one level up: the residue of a
    /// quotient from `1` is the numerator's error, scaled by the reciprocal.
    pub mul_inv_sub_one: NameId,
    /// `Rat.inv_sub_inv : ∀ a b, 0 < a → 0 < b →
    /// Rat.sub (Rat.inv a) (Rat.inv b) =
    /// Rat.mul (Rat.sub b a) (Rat.mul (Rat.inv a) (Rat.inv b))`.
    ///
    /// The identity the *regularity* of a reciprocal sequence rests on: two
    /// reciprocals differ by their arguments' difference, scaled by both
    /// reciprocals.
    pub inv_sub_inv: NameId,
    /// `Rat.inv_le_of_pos_le : ∀ c a, Rat.lt Rat.zero c → Rat.le c a →
    /// Rat.le (Rat.inv a) (Rat.inv c)` — the inverse is **antitone on the
    /// positives**, which is what turns a lower bound on a sample into an upper
    /// bound on its reciprocal.
    pub inv_le_of_pos_le: NameId,
    /// `Rat.inv_natDivSucc : ∀ (m : Nat),
    /// Rat.inv (Rat.natDivSucc 1 m) = Rat.natDivSucc (Nat.succ m) 0`.
    ///
    /// **The reciprocal of a modulus is a whole number, and that number is a
    /// `Nat`.** Every bound in the real construction is a single
    /// [`Self::nat_div_succ`] whose numerator is a natural, so an estimate that
    /// produced `(1/(m+1))⁻¹` as an opaque `Rat` would not fuse with anything.
    /// This is the one place the *value* of an inverse is computed rather than
    /// a property of it derived, and it is what turns
    /// [`crate::CRealPrelude::pos_bound`]'s modulus into the constant that
    /// bounds the inverse sequence.
    pub inv_nat_div_succ: NameId,
    /// `Rat.inv_pos : ∀ q, Rat.lt Rat.zero q → Rat.lt Rat.zero (Rat.inv q)`.
    ///
    /// Derived from [`Self::mul_inv_cancel`] and the 22 laws alone — no
    /// numerator — so it is a theorem of ordered fields.
    pub inv_pos: NameId,
    /// `Rat.inv : Rat → Rat` — the multiplicative inverse, with `inv 0 = 0`
    /// (the standard total convention; `ℚ` has no partial operations here for
    /// the same reason SMT-LIB's `bvudiv` is total).
    pub inv: NameId,
    /// `Rat.sub a b := add a (neg b)`.
    pub sub: NameId,
    /// `Rat.div a b := mul a (inv b)`.
    pub div: NameId,

    // --- supporting ℕ / ℤ lemmas ---------------------------------------------
    /// `Rat.gcd_one_right : ∀ (m : Nat), gcd m 1 = 1`.
    pub gcd_one_right: NameId,
    /// `Rat.nat_gauss : ∀ (k a b : Nat), 1 ≤ k → gcd a k = 1 → k ∣ a*b → k ∣ b`
    /// — Gauss's lemma, the coprime-cancellation step uniqueness rests on.
    ///
    /// The coprimality is `gcd a k`, not `gcd k a`, because that is the order
    /// `Rat.reduced` produces (`gcd (natAbs num) den = 1`) and this prelude has
    /// no `gcd` commutativity. Bézout is symmetric, so the orientation is free.
    pub nat_gauss: NameId,
    /// `Rat.nat_dvd_antisymm_pos : ∀ (a b : Nat), 1 ≤ a → 1 ≤ b → a ∣ b → b ∣ a → a = b`.
    pub nat_dvd_antisymm_pos: NameId,
    /// `Rat.nat_mul_right_cancel : ∀ (c a b : Nat), 1 ≤ c → a*c = b*c → a = b`.
    pub nat_mul_right_cancel: NameId,
    /// `Rat.nat_div_cross : ∀ (g x y : Nat), 1 ≤ g → g ∣ x → g ∣ y →
    /// (x/g)*y = x*(y/g)` — dividing either side of a product by a common
    /// divisor gives the same answer. What makes `Rat.normalize` value-preserving.
    pub nat_div_cross: NameId,
    /// `Rat.nat_abs_mul_of_nat : ∀ (x : Int) (k : Nat),
    /// natAbs (x * ofNat k) = natAbs x * k`.
    pub nat_abs_mul_of_nat: NameId,
    /// `Rat.of_nat_inj : ∀ (a b : Nat), Int.ofNat a = Int.ofNat b → a = b`.
    pub of_nat_inj: NameId,
    /// `Rat.not_zero_le_neg_of_nat : ∀ (k : Nat), 1 ≤ k →
    /// Int.le Int.zero (Int.negOfNat k) → False` — a negated *positive* natural
    /// is negative. The sign discriminator every mixed-constructor branch of
    /// [`Self::int_mul_right_cancel`] closes with.
    pub not_zero_le_neg_of_nat: NameId,
    /// `Rat.int_mul_right_cancel : ∀ (a b : Int) (c : Nat), 1 ≤ c →
    /// a * ofNat c = b * ofNat c → a = b`.
    pub int_mul_right_cancel: NameId,
    /// `Rat.int_le_of_mul_le_mul_right : ∀ (a b : Int) (c : Nat), 1 ≤ c →
    /// Int.le (a * ofNat c) (b * ofNat c) → Int.le a b`.
    pub int_le_of_mul_le_mul_right: NameId,
    /// `Rat.int_lt_of_mul_lt_mul_right : ∀ (a b : Int) (c : Nat), 1 ≤ c →
    /// Int.lt (a * ofNat c) (b * ofNat c) → Int.lt a b`.
    pub int_lt_of_mul_lt_mul_right: NameId,
    /// `Rat.int_mul_le_mul_right : ∀ (a b : Int) (c : Nat),
    /// Int.le a b → Int.le (a * ofNat c) (b * ofNat c)`.
    pub int_mul_le_mul_right: NameId,
    /// `Rat.int_mul_lt_mul_right : ∀ (a b : Int) (c : Nat), 1 ≤ c →
    /// Int.lt a b → Int.lt (a * ofNat c) (b * ofNat c)`.
    pub int_mul_lt_mul_right: NameId,
    /// `Rat.int_right_distrib : ∀ (a b c : Int), (a+b)*c = a*c + b*c` — the
    /// integer prelude has `left_distrib` only, and every cross-multiplication
    /// of a *sum* needs the other side.
    pub int_right_distrib: NameId,
    /// `Rat.int_zero_mul : ∀ (a : Int), Int.zero * a = Int.zero`.
    pub int_zero_mul: NameId,
    /// `Rat.eq_zero_of_num_zero : ∀ q, Int.Eq (num q) Int.zero → q = 0`.
    pub eq_zero_of_num_zero: NameId,
    /// `Rat.int_nonneg_of_nonneg : ∀ q, le 0 q → Int.le Int.zero (num q)`.
    pub int_nonneg_of_nonneg: NameId,
    /// `Rat.nonneg_of_int_nonneg : ∀ q, Int.le Int.zero (num q) → le 0 q`.
    pub nonneg_of_int_nonneg: NameId,
    /// `Rat.int_zero_le_of_nat : ∀ (n : Nat), Int.le Int.zero (Int.ofNat n)`.
    pub int_zero_le_of_nat: NameId,
    /// `Rat.int_of_nat_pos : ∀ (n : Nat), 1 ≤ n → Int.lt Int.zero (Int.ofNat n)`.
    pub int_of_nat_pos: NameId,

    // --- the structural characterisation of the normalised representative ----
    /// `Rat.mk_congr` — two `Rat.mk`s with equal numerators and equal
    /// denominators are equal, whatever their proof fields (definitional proof
    /// irrelevance does the rest).
    pub mk_congr: NameId,
    /// `Rat.eta : ∀ q, q = Rat.mk (num q) (den q) (den_pos q) (reduced q)`.
    pub eta: NameId,
    /// `Rat.ext : ∀ q r, num q = num r → den q = den r → q = r`.
    pub ext: NameId,
    /// `Rat.eq_of_cross : ∀ q r, num q * ofNat (den r) = num r * ofNat (den q) → q = r`
    /// — **uniqueness of the reduced representative**, the keystone.
    pub eq_of_cross: NameId,
    /// `Rat.cross_of_eq : ∀ q r, q = r → num q * ofNat (den r) = num r * ofNat (den q)`.
    pub cross_of_eq: NameId,
    /// `Rat.normalize_cross : ∀ n d (h : 1 ≤ d),
    /// num (normalize n d h) * ofNat d = n * ofNat (den (normalize n d h))`
    /// — `normalize` keeps the value it was given.
    pub normalize_cross: NameId,
    /// `Rat.normalize_congr : ∀ n1 d1 h1 n2 d2 h2,
    /// n1 * ofNat d2 = n2 * ofNat d1 → normalize n1 d1 h1 = normalize n2 d2 h2`.
    pub normalize_congr: NameId,
    /// `Rat.self_normalize : ∀ q, normalize (num q) (den q) (den_pos q) = q`.
    pub self_normalize: NameId,
    /// `Rat.normalize_add_normalize : ∀ n1 e1 h1 n2 e2 h2,
    /// normalize n1 e1 h1 + normalize n2 e2 h2
    ///   = normalize (n1 * ofNat e2 + n2 * ofNat e1) (e1*e2) _`.
    ///
    /// Adding two normalised fractions is normalising the naive sum. With
    /// [`Self::self_normalize`] this is what makes `add_assoc` and
    /// `left_distrib` reachable: every compound `Rat` expression collapses to a
    /// **single** `Rat.normalize`, and the law becomes one identity in `ℤ`.
    pub normalize_add_normalize: NameId,
    /// `Rat.normalize_mul_normalize : ∀ n1 e1 h1 n2 e2 h2,
    /// normalize n1 e1 h1 * normalize n2 e2 h2 = normalize (n1*n2) (e1*e2) _`.
    pub normalize_mul_normalize: NameId,
    /// `Rat.add_cross : ∀ a b,
    /// num (a+b) * ofNat (den a * den b)
    ///   = (num a * ofNat (den b) + num b * ofNat (den a)) * ofNat (den (a+b))`.
    pub add_cross: NameId,
    /// `Rat.mul_cross : ∀ a b,
    /// num (a*b) * ofNat (den a * den b) = (num a * num b) * ofNat (den (a*b))`.
    pub mul_cross: NameId,

    // --- the 22 ordered-commutative-ring laws --------------------------------
    /// `Rat.le_refl : ∀ a, le a a`.
    pub le_refl: NameId,
    /// `Rat.le_trans : ∀ a b c, le a b → le b c → le a c`.
    pub le_trans: NameId,
    /// `Rat.lt_irrefl : ∀ a, Not (lt a a)`.
    pub lt_irrefl: NameId,
    /// `Rat.lt_trans : ∀ a b c, lt a b → lt b c → lt a c`.
    pub lt_trans: NameId,
    /// `Rat.lt_of_lt_of_le : ∀ a b c, lt a b → le b c → lt a c`.
    pub lt_of_lt_of_le: NameId,
    /// `Rat.lt_of_le_of_lt : ∀ a b c, le a b → lt b c → lt a c`.
    pub lt_of_le_of_lt: NameId,
    /// `Rat.le_of_lt : ∀ a b, lt a b → le a b`.
    pub le_of_lt: NameId,
    /// `Rat.add_le_add : ∀ a b c d, le a b → le c d → le (a+c) (b+d)`.
    pub add_le_add: NameId,
    /// `Rat.add_comm : ∀ a b, a + b = b + a`.
    pub add_comm: NameId,
    /// `Rat.add_assoc : ∀ a b c, (a + b) + c = a + (b + c)`.
    pub add_assoc: NameId,
    /// `Rat.add_zero : ∀ a, a + 0 = a`.
    pub add_zero: NameId,
    /// `Rat.add_neg : ∀ a, a + (-a) = 0`.
    pub add_neg: NameId,
    /// `Rat.mul_le_mul_of_nonneg_left : ∀ a b c, le 0 a → le b c → le (a*b) (a*c)`.
    pub mul_le_mul_of_nonneg_left: NameId,
    /// `Rat.zero_lt_one : lt 0 1`.
    pub zero_lt_one: NameId,
    /// `Rat.add_lt_add_of_le_of_lt : ∀ a b c d, le a b → lt c d → lt (a+c) (b+d)`.
    pub add_lt_add_of_le_of_lt: NameId,
    /// `Rat.mul_comm : ∀ a b, a * b = b * a`.
    pub mul_comm: NameId,
    /// `Rat.mul_assoc : ∀ a b c, (a * b) * c = a * (b * c)`.
    pub mul_assoc: NameId,
    /// `Rat.mul_one : ∀ a, a * 1 = a`.
    pub mul_one: NameId,
    /// `Rat.mul_zero : ∀ a, a * 0 = 0`.
    pub mul_zero: NameId,
    /// `Rat.left_distrib : ∀ a b c, a * (b + c) = a*b + a*c`.
    pub left_distrib: NameId,
    /// `Rat.mul_nonneg : ∀ a b, le 0 a → le 0 b → le 0 (a*b)`.
    pub mul_nonneg: NameId,
    /// `Rat.sq_nonneg : ∀ a, le 0 (a*a)`.
    pub sq_nonneg: NameId,

    // --- beyond the ring interface -------------------------------------------
    /// `Rat.le_total : ∀ a b, Or (le a b) (le b a)`.
    ///
    /// **Not** one of the 22: the `AxReal` package does not assume totality
    /// (ADR-0456 counted it as absent), so this is a property `ℚ` has and the
    /// axiomatized `AxReal` does not. It is one line — `Rat.le` unfolds to
    /// `Int.le` on cross-products, and `Int.le_total` is already proved.
    pub le_total: NameId,
    /// `Rat.lt_of_not_le : ∀ a b, Not (le a b) → lt b a`.
    ///
    /// The entry point for any argument by contradiction on the order, and in
    /// particular the first step of an Archimedean argument: `¬(a ≤ b)` gives
    /// `b < a`, and only then is there a positive quantity to bound.
    pub lt_of_not_le: NameId,
    /// `Rat.le_antisymm : ∀ a b, le a b → le b a → a = b`.
    ///
    /// **Also missing until now.** Not one of the 22 either — the `Real`
    /// package states no antisymmetry law — but unlike `le_total` it is not a
    /// one-line transcription: `le a b` and `le b a` unfold to `Int.le` on the
    /// two cross-products, and `int_prelude`'s own `Int.le_antisymm` applied to
    /// them gives exactly the hypothesis `eq_of_cross` needs.
    pub le_antisymm: NameId,
    /// `Rat.lt_trichotomy : ∀ a b, Or (lt a b) (Or (a = b) (lt b a))`.
    ///
    /// The genuinely constructive trichotomy: two applications of
    /// [`Self::le_or_lt`] (first at `(a,b)`, then, in the `le a b` branch, at
    /// `(b,a)`) and one of [`Self::le_antisymm`] close every case, with no
    /// step that is an argument by contradiction. `CReal.Equiv` has no
    /// analogue — cotransitivity is the most a setoid over an undecidable
    /// order can offer — so this is a property `ℚ` has purely because its
    /// order is *decidable* and `ℝ` cannot inherit by transcription.
    pub lt_trichotomy: NameId,
    /// `Rat.mul_eq_zero : ∀ a b, a * b = 0 → Or (a = 0) (b = 0)` — `ℚ` has no
    /// zero divisors.
    ///
    /// Not a cross-multiplication transcription like the order laws: `a*b`
    /// *normalises* its numerator, so `num (a*b)` is not literally
    /// `num a * num b`. The route is `cross_of_eq` at `(a*b, 0)` to get
    /// `num (a*b) = 0` outright (the cross product collapses via `mul_one` and
    /// `int_zero_mul`), `normalize_cross` to move that across the
    /// normalisation and `int_mul_right_cancel` to drop the positive
    /// denominator, landing on the clean integer fact `num a * num b = 0`;
    /// then `Int.natAbs` and `Nat.mul_eq_zero` decide which numerator
    /// vanishes, and `eq_zero_of_num_zero` lifts that back to `ℚ`.
    pub mul_eq_zero: NameId,
    /// `Rat.right_distrib : ∀ a b c, (a+b)*c = a*c + b*c`.
    ///
    /// Not one of the ring interface's 22 (only `left_distrib` is stated
    /// there). One `mul_comm`/`left_distrib`/`mul_comm` chain, no
    /// representation reasoning — the same route `Rat.int_right_distrib`
    /// takes over `ℤ`, one level down. Every sum distributed on the right —
    /// starting with [`RatPrelude::expectation_add`]'s pointwise step —
    /// needs it directly.
    pub right_distrib: NameId,

    // --- the Archimedean property (ADR-0512 phase R1) -------------------------
    /// `Rat.natDivSucc : Nat → Nat → Rat` — the rational `k/(j+1)`, as a single
    /// `Rat.normalize` whose denominator is positive by construction.
    ///
    /// One definition serves the regularity bound (`k = 1`), the setoid
    /// closeness bound (`k = 2`) and the Archimedean bound (`k = 6`) of
    /// ADR-0512's real construction, and `Rat.abs` is never needed because
    /// `|a| ≤ b` is written as the pair `−b ≤ a ∧ a ≤ b`.
    pub nat_div_succ: NameId,
    /// `Rat.int_le_or_lt : ∀ (x y : Int), Or (Int.le x y) (Int.lt y x)`.
    ///
    /// The *decidable* form of the order. `¬¬P → P` does not exist in this
    /// logic prelude, so an argument that wants "suppose not" takes this
    /// instead — which is available because `Int.le_total` and `Int.eq_em` are
    /// both proved.
    pub int_le_or_lt: NameId,
    /// `Rat.le_or_lt : ∀ (a b : Rat), Or (Rat.le a b) (Rat.lt b a)` — the same,
    /// read through the cross-multiplication definition, so it costs nothing.
    pub le_or_lt: NameId,
    /// `Rat.int_pos_of_pos : ∀ q, Rat.lt Rat.zero q → Int.lt Int.zero (Rat.num q)`
    /// — the strict companion of [`Self::int_nonneg_of_nonneg`].
    pub int_pos_of_pos: NameId,
    /// `Rat.int_one_le_of_pos : ∀ (x : Int), Int.lt Int.zero x → Int.le (Int.ofNat 1) x`
    /// — the **discreteness** of `ℤ`, which is what makes `ℚ` Archimedean.
    pub int_one_le_of_pos: NameId,
    /// `Rat.natDivSucc_lt_of_pos : ∀ (k : Nat) (c : Rat), Rat.lt Rat.zero c →
    /// Rat.lt (Rat.natDivSucc k (Nat.mul k (Rat.den c))) c`.
    ///
    /// The Archimedean **witness**, computed rather than asserted to exist: for
    /// `c = p/q` with `p ≥ 1`, the index `k·q` works because `k·q < p·(k·q+1)`.
    /// No `Exists`, so no elimination at the use site.
    pub nat_div_succ_lt_of_pos: NameId,
    /// `Rat.le_of_le_add_natDivSucc : ∀ (a b : Rat) (k : Nat),
    /// (∀ (j : Nat), Rat.le a (Rat.add b (Rat.natDivSucc k j))) → Rat.le a b`.
    ///
    /// **The Archimedean property of `ℚ`.** ADR-0512 identifies this as the one
    /// genuinely new rational lemma the Bishop-setoid construction of `ℝ` needs:
    /// transitivity of `CReal.Equiv` only reaches `|x_n − z_n| ≤ 2/n + 6/j` for
    /// every `j`, and this is what turns that into `≤ 2/n`.
    pub le_of_le_add_nat_div_succ: NameId,

    // --- the ordered-group toolkit (ADR-0512 phase R1) ------------------------
    /// `Rat.zero_add : ∀ a, Rat.add Rat.zero a = a`.
    pub zero_add: NameId,
    /// `Rat.neg_add_cancel : ∀ a, Rat.add (Rat.neg a) a = Rat.zero`.
    pub neg_add_cancel: NameId,
    /// `Rat.neg_eq_of_add_eq_zero : ∀ a b, Rat.add a b = Rat.zero → Rat.neg a = b`
    /// — **uniqueness of the additive inverse**, which makes `neg_neg` and
    /// `neg_add` one line each instead of a rearrangement each.
    pub neg_eq_of_add_eq_zero: NameId,
    /// `Rat.neg_neg : ∀ a, Rat.neg (Rat.neg a) = a`.
    pub neg_neg: NameId,
    /// `Rat.neg_zero : Rat.neg Rat.zero = Rat.zero`.
    pub neg_zero: NameId,
    /// `Rat.neg_add : ∀ a b, Rat.neg (Rat.add a b) = Rat.add (Rat.neg a) (Rat.neg b)`.
    pub neg_add: NameId,
    /// `Rat.neg_le_neg : ∀ a b, Rat.le a b → Rat.le (Rat.neg b) (Rat.neg a)`.
    pub neg_le_neg: NameId,
    /// `Rat.sub_self : ∀ a, Rat.sub a a = Rat.zero`.
    pub sub_self: NameId,
    /// `Rat.neg_sub : ∀ a b, Rat.neg (Rat.sub a b) = Rat.sub b a` — what makes
    /// `CReal.Equiv` symmetric.
    pub neg_sub: NameId,
    /// `Rat.sub_neg_sub : ∀ a b, Rat.sub (Rat.neg a) (Rat.neg b) = Rat.sub b a`
    /// — what makes `CReal.neg` regular.
    pub sub_neg_sub: NameId,
    /// `Rat.sub_add_add : ∀ a b c e,
    /// Rat.sub (Rat.add a b) (Rat.add c e) = Rat.add (Rat.sub a c) (Rat.sub b e)`
    /// — the error of a sum is the sum of the errors.
    pub sub_add_add: NameId,
    /// `Rat.sub_add_sub : ∀ a b c, Rat.add (Rat.sub a b) (Rat.sub b c) = Rat.sub a c`
    /// — the telescoping identity Bishop's four-term estimate is assembled from.
    pub sub_add_sub: NameId,
    /// `Rat.bounds_add : ∀ u p v q, Rat.le (neg p) u → Rat.le u p →
    /// Rat.le (neg q) v → Rat.le v q →
    /// And (Rat.le (neg (p+q)) (u+v)) (Rat.le (u+v) (p+q))`.
    ///
    /// The triangle inequality in ADR-0512's encoding, where `|a| ≤ b` is the
    /// **pair** `−b ≤ a ∧ a ≤ b` and `Rat.abs` never exists.
    pub bounds_add: NameId,
    /// `Rat.natDivSucc_add : ∀ (a b j : Nat),
    /// Rat.add (natDivSucc a j) (natDivSucc b j) = natDivSucc (a+b) j`.
    pub nat_div_succ_add: NameId,
    /// `Rat.natDivSucc_halve : ∀ (m : Nat), natDivSucc 2 (2·m + 1) = natDivSucc 1 m`
    /// — the identity that pays for Bishop's index shift in `CReal.add`.
    pub nat_div_succ_halve: NameId,
    /// `Rat.natDivSucc_scale : ∀ (c m : Nat),
    /// natDivSucc (c+1) ((c+1)·m + c) = natDivSucc 1 m` —
    /// [`Self::nat_div_succ_halve`] at an **arbitrary** factor, and `halve` is
    /// its `c = 1` instance definitionally.
    ///
    /// This is what keeps `Rat.natDivSucc` **antitone in its index** off the
    /// critical path a second time. `CReal.add_zero` and `CReal.add_assoc`
    /// avoided it because Bishop's shift is the *fixed* `2n+1`, so both sides
    /// could be read at the common denominator `2n+2`. `CReal.mul` cannot: its
    /// sampling index is `K·(n+1) − 1` with `K` depending on the two factors'
    /// canonical bounds, so there is no fixed common denominator — but there
    /// is still a common denominator *per instance*, and this supplies it.
    /// With [`Self::nat_div_succ_le_add_left`] the whole comparison
    /// `1/(K(n+1)) ≤ 1/(n+1)` becomes `1 ≤ K` at one denominator.
    pub nat_div_succ_scale: NameId,
    /// `Rat.natDivSucc_le_add_left : ∀ (a e j : Nat),
    /// Rat.le (natDivSucc a j) (natDivSucc (a+e) j)` — monotone in the
    /// **numerator**, stated additively so that ℕ-subtraction never appears.
    pub nat_div_succ_le_add_left: NameId,
    /// `Rat.zero_le_natDivSucc : ∀ (k j : Nat), Rat.le Rat.zero (natDivSucc k j)`.
    pub zero_le_nat_div_succ: NameId,
    /// `Rat.neg_nonpos_of_nonneg : ∀ a, Rat.le Rat.zero a → Rat.le (Rat.neg a) Rat.zero`.
    pub neg_nonpos_of_nonneg: NameId,
    /// `Rat.bounds_neg : ∀ r q, Rat.le (neg q) r → Rat.le r q →
    /// And (Rat.le (neg q) (neg r)) (Rat.le (neg r) q)` — negating a two-sided
    /// bound keeps it.
    pub bounds_neg: NameId,
    /// `Rat.add_nonneg : ∀ a b, Rat.le Rat.zero a → Rat.le Rat.zero b →
    /// Rat.le Rat.zero (Rat.add a b)`.
    pub add_nonneg: NameId,

    // --- the multiplicative toolkit (ADR-0512 phase R2, `CReal.mul`) ----------
    /// `Rat.mul_neg : ∀ a b, Rat.mul a (Rat.neg b) = Rat.neg (Rat.mul a b)`.
    pub mul_neg: NameId,
    /// `Rat.neg_mul : ∀ a b, Rat.mul (Rat.neg a) b = Rat.neg (Rat.mul a b)`.
    pub neg_mul: NameId,
    /// `Rat.mul_le_mul_of_nonneg_right : ∀ a b c, Rat.le Rat.zero c →
    /// Rat.le a b → Rat.le (Rat.mul a c) (Rat.mul b c)` — the side
    /// [`Self::mul_le_mul_of_nonneg_left`] does not give, one `mul_comm` away.
    pub mul_le_mul_of_nonneg_right: NameId,
    /// `Rat.mul_sub_mul : ∀ a b c e,
    /// Rat.sub (a·b) (c·e) = Rat.add (a · Rat.sub b e) (Rat.sub a c · e)`.
    ///
    /// **The identity Bishop's product estimate is the shadow of.** A difference
    /// of two products only ever becomes bounded by splitting this way: each
    /// summand pairs a factor bounded by a canonical magnitude with a factor
    /// bounded by regularity.
    pub mul_sub_mul: NameId,
    /// `Rat.bounds_mul : ∀ u p v q, Rat.le Rat.zero p →
    /// Rat.le (neg p) u → Rat.le u p → Rat.le (neg q) v → Rat.le v q →
    /// And (Rat.le (neg (p·q)) (u·v)) (Rat.le (u·v) (p·q))`.
    ///
    /// The **product** form of [`Self::bounds_add`], in the same
    /// `−b ≤ a ∧ a ≤ b` encoding, so `Rat.abs` still never exists. The sign
    /// analysis happens once, on the proved `Rat.le_or_lt`, and never as an
    /// argument by contradiction.
    pub bounds_mul: NameId,
    /// `Rat.neg_mul_le_of_bounds : ∀ u v e b, Rat.le Rat.zero e →
    /// Rat.le Rat.zero b → Rat.le (neg e) u → Rat.le u b → Rat.le (neg e) v →
    /// Rat.le v b → Rat.le (neg (e·b)) (u·v)`.
    ///
    /// The **one-sided** product estimate. `0 ≤ x` over the reals does not say
    /// any sample of `x` is non-negative — only that each is above `−2/(n+1)` —
    /// so a lower bound on a product has to trade that residue off against the
    /// other factor's canonical magnitude. This is what `CReal.mul_nonneg` runs
    /// on, and the resulting `e·b` fuses back into a single `natDivSucc` by
    /// [`Self::nat_div_succ_mul`].
    pub neg_mul_le_of_bounds: NameId,
    /// `Rat.natDivSucc_mul : ∀ (a b j : Nat),
    /// Rat.mul (natDivSucc a 0) (natDivSucc b j) = natDivSucc (a·b) j`.
    ///
    /// Scaling a bound by a whole number keeps it a **single** `natDivSucc`,
    /// which is what stops `CReal.mul`'s estimate from degenerating into a
    /// product of two rationals whose projections are opaque.
    pub nat_div_succ_mul: NameId,
    /// `Rat.nat_index_compose : ∀ (a b n : Nat),
    /// Nat.add (Nat.mul (a+1) (Nat.add (Nat.mul (b+1) n) b)) a
    ///   = Nat.add (Nat.mul (D+1) n) D`, where `D = Nat.add (Nat.mul (a+1) b) a`.
    ///
    /// **Bishop's sampling indices are closed under composition.** `CReal.mul`
    /// samples at `(c+1)·n + c` and `CReal.add` at `2n+1`, which *is*
    /// `(1+1)·n + 1`, so every nested product samples at an index of the same
    /// shape and [`Self::nat_div_succ_le_scaled`] applies to it unchanged.
    /// Without this, each nesting would need its own index arithmetic.
    pub nat_index_compose: NameId,
    /// `Rat.nat_index_symm : ∀ (a b : Nat),
    /// Nat.add (Nat.mul (Nat.succ a) b) a = Nat.add (Nat.mul (Nat.succ b) a) b`.
    ///
    /// **Bishop's sampling index is symmetric in its shift and its argument.**
    /// `index c n := (c+1)·n + c` is what [`Self::nat_div_succ_le_scaled`]
    /// recognises, and it recognises it *in the second slot*: a bound read at
    /// `index c n` comes back to `n`, never to `c`. So an index that has to be
    /// read back to the **shift** instead — which is exactly what the real
    /// inverse needs, its samples being bounded below by a constant derived
    /// from the modulus rather than by anything shrinking in `n` — is the same
    /// index with its two arguments swapped, and this is the swap.
    ///
    /// Degree 2 in the two variables, and still not an induction: `succ_mul`
    /// opens both sides to `a·b + b + a` up to
    /// [`Nat.mul_comm`](crate::NatPrelude::mul_comm) and
    /// [`Nat.add_right_comm`](crate::NatPrelude::add_right_comm).
    pub nat_index_symm: NameId,
    /// `Rat.natDivSucc_le_scaled : ∀ (k c n : Nat),
    /// Rat.le (natDivSucc k (Nat.add (Nat.mul (c+1) n) c)) (natDivSucc k n)`.
    ///
    /// **The general index-comparison lemma**, and it is still not
    /// antitonicity of `natDivSucc`. A sampling index of the shape
    /// `(c+1)·n + c` — Bishop's product index, and every composite of it — is
    /// deeper than `n`, and a bound read at that depth has to come back to `n`.
    /// [`Self::nat_div_succ_le_add_left`] widens the numerator `k ↦ k·(c+1)` at
    /// the *same* index, [`Self::nat_div_succ_mul`] factors it, and
    /// [`Self::nat_div_succ_scale`] reads the deep factor as `1/(n+1)`: three
    /// steps, one denominator each.
    pub nat_div_succ_le_scaled: NameId,
    /// `Rat.natDivSucc_le_one : ∀ (j : Nat),
    /// Rat.le (natDivSucc 1 j) (natDivSucc 1 0)`.
    ///
    /// Still **not** antitonicity of `natDivSucc` in its index:
    /// [`Self::nat_div_succ_le_add_left`] widens the numerator `1 ↦ 1 + j` at
    /// the index `j`, and [`Self::nat_div_succ_scale`] at `m = 0` says
    /// `(j+1)/(j+1)` is `1/1`. Both steps compare at one denominator.
    pub nat_div_succ_le_one: NameId,
    /// `Rat.int_le_natAbs : ∀ (x : Int), Int.le x (Int.ofNat (Int.natAbs x))`.
    pub int_le_nat_abs: NameId,
    /// `Rat.int_neg_natAbs_le : ∀ (x : Int),
    /// Int.le (Int.neg (Int.ofNat (Int.natAbs x))) x`.
    pub int_neg_nat_abs_le: NameId,
    // --- the lattice (ADR-0519 phase R5) --------------------------------------
    /// `Rat.max : Rat → Rat → Rat` — defined **on the representation**, by
    /// `Int.rec` on the sign of `num b · den a − num a · den b`, so no `Prop`
    /// is eliminated into `Type` and `Rat.le_or_lt` is never consulted.
    pub max: NameId,
    /// `Rat.min : Rat → Rat → Rat` — the same dispatch with the branches
    /// swapped.
    pub min: NameId,
    /// `Rat.max_cases : ∀ (a b : Rat) (P : Rat → Prop),
    /// (Rat.le a b → P b) → (Rat.le b a → P a) → P (Rat.max a b)`.
    ///
    /// The **only** case split in `rat_prelude::lattice`: every law below is one
    /// application of it with `P` instantiated. It eliminates into `Prop`, so
    /// it is not a decision procedure and gives nothing `Rat.le_or_lt` does not
    /// already give.
    pub max_cases: NameId,
    /// `Rat.min_cases : ∀ (a b : Rat) (P : Rat → Prop),
    /// (Rat.le a b → P a) → (Rat.le b a → P b) → P (Rat.min a b)`.
    pub min_cases: NameId,
    /// `Rat.le_max_left : ∀ a b, Rat.le a (Rat.max a b)`.
    pub le_max_left: NameId,
    /// `Rat.le_max_right : ∀ a b, Rat.le b (Rat.max a b)`.
    pub le_max_right: NameId,
    /// `Rat.max_le : ∀ a b c, Rat.le a c → Rat.le b c → Rat.le (Rat.max a b) c`.
    pub max_le: NameId,
    /// `Rat.min_le_left : ∀ a b, Rat.le (Rat.min a b) a`.
    pub min_le_left: NameId,
    /// `Rat.min_le_right : ∀ a b, Rat.le (Rat.min a b) b`.
    pub min_le_right: NameId,
    /// `Rat.le_min : ∀ a b c, Rat.le c a → Rat.le c b → Rat.le c (Rat.min a b)`.
    pub le_min: NameId,
    /// `Rat.le_of_sub_le : ∀ u v q, Rat.le (Rat.sub u v) q → Rat.le u (Rat.add v q)`.
    pub le_of_sub_le: NameId,
    /// `Rat.sub_le_of_le : ∀ u v q, Rat.le u (Rat.add v q) → Rat.le (Rat.sub u v) q`.
    pub sub_le_of_le: NameId,
    /// `Rat.sub_max_le : ∀ a b c e q, Rat.le (Rat.sub a c) q →
    /// Rat.le (Rat.sub b e) q → Rat.le (Rat.sub (Rat.max a b) (Rat.max c e)) q`
    /// — `max` is **one-Lipschitz**, which is exactly what makes `CReal.max`
    /// regular with no index shift.
    pub sub_max_le: NameId,
    /// `Rat.sub_min_le : ∀ a b c e q, Rat.le (Rat.sub a c) q →
    /// Rat.le (Rat.sub b e) q → Rat.le (Rat.sub (Rat.min a b) (Rat.min c e)) q`.
    pub sub_min_le: NameId,
    /// `Rat.zero_le_max_neg : ∀ a, Rat.le Rat.zero (Rat.max a (Rat.neg a))` —
    /// the one `ℚ` fact `CReal.abs_nonneg` needs, and the only consumer of
    /// [`Self::le_total`] in the lattice.
    pub zero_le_max_neg: NameId,

    /// `Rat.bounds_num : ∀ q,
    /// And (Rat.le (neg (natDivSucc (natAbs (num q)) 0)) q)
    ///     (Rat.le q (natDivSucc (natAbs (num q)) 0))`.
    ///
    /// **The canonical magnitude of a rational, as a natural number.** This is
    /// what makes `CReal.bound` a projection rather than a search: a regular
    /// sequence's zeroth sample is a rational, its numerator an integer, and
    /// `Int.natAbs` of that is the `ℕ` `CReal.mul`'s sampling index is scaled
    /// by. A development over an *existential* modulus (Bishop's own, and
    /// Mathlib's `CauSeq`) has to extract that number; the fixed modulus of
    /// ADR-0512 computes it.
    pub bounds_num: NameId,

    // --- absolute value and the triangle inequality (`rat_prelude::abs`) ----
    /// `Rat.abs : Rat → Rat`, defined `Rat.abs a := Rat.max a (Rat.neg a)` —
    /// the same "define on the representation, do not derive from the order"
    /// move [`Self::max`]/[`Self::min`] make, so every law below is a lattice
    /// argument (`max_le`, `le_max_left`, `le_max_right`, `le_antisymm`)
    /// rather than a fresh case split on the sign of `a`.
    pub abs: NameId,
    /// `Rat.abs_nonneg : ∀ a, Rat.le Rat.zero (Rat.abs a)` — literally
    /// [`Self::zero_le_max_neg`] at `a`, restated through the new constant.
    pub abs_nonneg: NameId,
    /// `Rat.le_abs_self : ∀ a, Rat.le a (Rat.abs a)` — [`Self::le_max_left`]
    /// at `(a, Rat.neg a)`.
    pub le_abs_self: NameId,
    /// `Rat.neg_le_abs : ∀ a, Rat.le (Rat.neg a) (Rat.abs a)` —
    /// [`Self::le_max_right`] at `(a, Rat.neg a)`.
    pub neg_le_abs: NameId,
    /// `Rat.abs_zero : Rat.abs Rat.zero = Rat.zero`.
    pub abs_zero: NameId,
    /// `Rat.abs_neg : ∀ a, Rat.abs (Rat.neg a) = Rat.abs a` — `neg_neg`
    /// collapses the double negation, then a locally-built `max_comm`
    /// (`lattice` deliberately has none; nothing consumed it before this
    /// file) puts the arguments back in order.
    pub abs_neg: NameId,
    /// `Rat.abs_add : ∀ a b, Rat.le (Rat.abs (Rat.add a b))
    /// (Rat.add (Rat.abs a) (Rat.abs b))` — **the triangle inequality.** One
    /// `max_le` closes it once the two branches are in hand: `a + b ≤ |a| +
    /// |b|` is `add_le_add` on [`Self::le_abs_self`] twice, and
    /// `−(a+b) ≤ |a| + |b|` is `add_le_add` on [`Self::neg_le_abs`] twice
    /// followed by rewriting along [`Self::neg_add`].
    pub abs_add: NameId,
    /// `Rat.abs_mul : ∀ a b, Rat.abs (Rat.mul a b) = Rat.mul (Rat.abs a) (Rat.abs b)`.
    ///
    /// An `Eq`, not an inequality, so the lattice route `abs_add` takes does
    /// not carry: `max` does not commute with multiplication without sign
    /// information. The case split is a **Prop-level** sign decision on `a`
    /// and `b` via [`Self::le_or_lt`] (nested, four branches), never a fresh
    /// `Int.rec` on a numerator — `Rat.abs` already carries its
    /// representation-level cost in [`Self::max`], and every branch here is
    /// ordinary ordered-ring algebra (`mul_nonneg`, `mul_neg`, `neg_mul`,
    /// `neg_neg`) once the sign of each factor is in hand.
    pub abs_mul: NameId,
    /// `Rat.abs_le_of_le_of_neg_le : ∀ a b, Rat.le (Rat.neg b) a → Rat.le a b →
    /// Rat.le (Rat.abs a) b` — the introduction rule for a two-sided bound on
    /// `|a|`, and the bridge to ADR-0512's `−q ≤ r ∧ r ≤ q` encoding of
    /// closeness: one `max_le` once both `a ≤ b` and `−a ≤ b` (the latter from
    /// `neg_le_neg` on the hypothesis, rewritten along `neg_neg`) are in hand.
    pub abs_le_of_le_of_neg_le: NameId,
    /// `Rat.le_of_abs_le : ∀ a b, Rat.le (Rat.abs a) b → Rat.le a b` — half of
    /// the converse of [`Self::abs_le_of_le_of_neg_le`], split into two names
    /// because this development has no `Iff`: `a ≤ |a| ≤ b` via
    /// [`Self::le_abs_self`] and `le_trans`.
    pub le_of_abs_le: NameId,
    /// `Rat.neg_le_of_abs_le : ∀ a b, Rat.le (Rat.abs a) b → Rat.le (Rat.neg b) a`
    /// — the other half: `−a ≤ |a| ≤ b` via [`Self::neg_le_abs`] gives
    /// `−a ≤ b`, and `neg_le_neg` plus `neg_neg` turns that into `−b ≤ a`.
    pub neg_le_of_abs_le: NameId,
    /// `Rat.abs_sub_comm : ∀ a b, Rat.abs (Rat.sub a b) = Rat.abs (Rat.sub b a)`.
    ///
    /// Falls out of [`Self::abs_neg`] and [`Self::neg_sub`] alone — no sign
    /// case split, unlike [`Self::abs_mul`] — since `sub a b` and `sub b a`
    /// are already related by `neg`.
    pub abs_sub_comm: NameId,

    // --- boolean decision (`Rat.ble`) ---------------------------------------
    /// `Rat.ble : Rat → Rat → Bool` — decidable `≤`, a genuine `Bool` in
    /// `Type`, computable. Defined on the representation exactly like
    /// [`Self::max`]/[`Self::min`]: `Int.rec` (motive `Bool`) on the sign of
    /// the same cross-multiplication gap `num b · den a − num a · den b`,
    /// dispatching to `true` on `Int.ofNat` and `false` on `Int.negSucc`. No
    /// `Prop` is eliminated into `Type` and [`Self::le_or_lt`] is never
    /// consulted — which is exactly what makes this a genuine *decision*
    /// rather than a case split on an already-proved disjunction.
    pub ble: NameId,
    /// `Rat.ble_eq_true_of_le : ∀ a b, Rat.le a b → Rat.ble a b = true`.
    pub ble_eq_true_of_le: NameId,
    /// `Rat.le_of_ble_eq_true : ∀ a b, Rat.ble a b = true → Rat.le a b` — the
    /// converse, ruling out the `Int.negSucc` branch by `Bool.false ≠ true`.
    /// Together with [`Self::ble_eq_true_of_le`] this is the full spec —
    /// `Rat.ble a b = true ↔ Rat.le a b` — split into two names because this
    /// development has no `Iff`.
    pub le_of_ble_eq_true: NameId,
    /// `Rat.ble_refl : ∀ a, Rat.ble a a = true` — one application of
    /// [`Self::ble_eq_true_of_le`] to [`Self::le_refl`].
    pub ble_refl: NameId,
    /// `Rat.ble_trans : ∀ a b c, Rat.ble a b = true → Rat.ble b c = true →
    /// Rat.ble a c = true` — [`Self::le_of_ble_eq_true`] twice,
    /// [`Self::le_trans`] once, [`Self::ble_eq_true_of_le`] once.
    pub ble_trans: NameId,
    /// `Rat.ble_total : ∀ a b, Or (Rat.ble a b = true) (Rat.ble b a = true)` —
    /// the constructive decision [`Self::le_or_lt`] does not itself give as
    /// data (it is `Or (le a b) (lt b a)`, a `Prop`): this is the same fact
    /// restated in `Bool`, via [`Self::le_or_lt`] and [`Self::le_of_lt`].
    pub ble_total: NameId,

    // --- `Rat.sumRange`: finite sums over ℚ (rat_prelude::sum) -------------
    /// `Rat.sumRange : (Nat → Rat) → Nat → Rat`, `Nat.rec` on the bound:
    /// `sumRange f zero ≡ zero`, `sumRange f (succ n) ≡ sumRange f n + f n`.
    pub sum_range: NameId,
    /// `Rat.sumRange_zero : ∀ f, sumRange f zero = zero` — `Eq.refl`.
    pub sum_range_zero: NameId,
    /// `Rat.sumRange_succ : ∀ f n, sumRange f (succ n) = sumRange f n + f n`
    /// — `Eq.refl`.
    pub sum_range_succ: NameId,
    /// `Rat.sumRange_congr : ∀ f g n, (∀ i, f i = g i) → sumRange f n =
    /// sumRange g n`.
    pub sum_range_congr: NameId,
    /// `Rat.sumRange_add : ∀ f g n, sumRange (fun i => f i + g i) n =
    /// sumRange f n + sumRange g n`.
    pub sum_range_add: NameId,
    /// `Rat.mul_sumRange : ∀ c f n, c * sumRange f n = sumRange (fun i => c *
    /// f i) n`.
    pub mul_sum_range: NameId,
    /// `Rat.sumRange_le : ∀ f g n, (∀ i, Lt i n → le (f i) (g i)) → le
    /// (sumRange f n) (sumRange g n)` — monotonicity.
    pub sum_range_le: NameId,
    /// `Rat.sumRange_nonneg : ∀ f n, (∀ i, Lt i n → le zero (f i)) → le zero
    /// (sumRange f n)`.
    pub sum_range_nonneg: NameId,

    // --- finite probability distributions (rat_prelude::probability) -------
    /// `Rat.IsDistribution p n := (∀ k, Lt k n → le zero (p k)) ∧ sumRange p
    /// n = one`.
    pub is_distribution: NameId,
    /// `Rat.prob_le_one : ∀ p n, IsDistribution p n → ∀ k, Lt k n → le (p k)
    /// one` — every individual probability is at most `1`.
    pub prob_le_one: NameId,
    /// `Rat.prob_complement : ∀ p m j, IsDistribution p (m+j) →
    /// sumRange p m + sumRange (fun k => p (m+k)) j = one` — the mass of a
    /// prefix and its complementary tail sum to `1`.
    pub prob_complement: NameId,

    // --- expectation and its linearity (rat_prelude::probability) ----------
    /// `Rat.expectation X p n := sumRange (fun k => X k * p k) n` — the
    /// expected value of `X` under the (not-necessarily-normalised) weights
    /// `p`, over the first `n` outcomes.
    pub expectation: NameId,
    /// `Rat.expectation_add : ∀ X Y p n,
    /// expectation (fun k => X k + Y k) p n = expectation X p n + expectation Y p n`.
    ///
    /// Half of linearity — the additive half. [`Self::right_distrib`]
    /// distributes pointwise (`sumRange_congr`), then [`Self::sum_range_add`]
    /// splits the sum.
    pub expectation_add: NameId,
    /// `Rat.expectation_smul : ∀ a X p n,
    /// expectation (fun k => a * X k) p n = a * expectation X p n`.
    ///
    /// The other half of linearity — the scalar half. [`Self::mul_assoc`]
    /// regroups pointwise, then [`Self::mul_sum_range`] pulls the constant
    /// out of the sum. Stated separately from [`Self::expectation_add`]
    /// rather than as one two-scalar theorem, so each names exactly what it
    /// proves.
    pub expectation_smul: NameId,
    /// `Rat.expectation_const : ∀ c p n, IsDistribution p n →
    /// expectation (fun _ => c) p n = c` — the expectation of a constant is
    /// itself, over a genuine distribution. The first theorem in this file
    /// that *uses* `IsDistribution`'s `sumRange p n = 1` rather than just
    /// carrying it.
    pub expectation_const: NameId,
    /// `Rat.uniform (n k : Nat) := Rat.inv (Rat.natDivSucc n 0)` — the
    /// uniform distribution on `n` outcomes, each weighted `1/n`.
    pub uniform: NameId,
    /// `Rat.uniform_is_distribution : ∀ n, Nat.lt Nat.zero n →
    /// IsDistribution (uniform n) n`.
    ///
    /// **The negative control [`Self::is_distribution`] needs**: without an
    /// instance, every `IsDistribution` theorem in this kernel is vacuously
    /// true. `0 < n` (not `n ≠ 0`) because that is exactly the hypothesis
    /// [`Self::nat_div_succ_pos`] wants, and `Nat.lt Nat.zero n` is
    /// definitionally `Nat.le 1 n` — no separate conversion lemma needed.
    pub uniform_is_distribution: NameId,

    // --- probability bounds (rat_prelude::probability) ---------------------
    /// `Rat.expectation_nonneg : ∀ X p n, (∀ k, Lt k n → le zero (X k)) →
    /// IsDistribution p n → le zero (expectation X p n)`.
    pub expectation_nonneg: NameId,
    /// `Rat.expectation_le : ∀ X Y p n, (∀ k, Lt k n → le (X k) (Y k)) →
    /// IsDistribution p n → le (expectation X p n) (expectation Y p n)` —
    /// monotonicity.
    pub expectation_le: NameId,
    /// `Rat.markov_inequality : ∀ a X ind p n, IsDistribution p n → (∀ k, Lt
    /// k n → le zero (X k)) → lt zero a → (∀ k, Lt k n → le (a * ind k) (X
    /// k)) → le (a * expectation ind p n) (expectation X p n)` — the
    /// multiplied form (no `Rat.inv` needed), with the indicator supplied as
    /// a hypothesis. This project's first genuine probability BOUND.
    pub markov_inequality: NameId,
    /// `Rat.expectation_indicator_le_one : ∀ ind p n, IsDistribution p n →
    /// (∀ k, Lt k n → Or (ind k = zero) (ind k = one)) →
    /// le (expectation ind p n) one` — the expectation of any `{0,1}`-valued
    /// sequence, under a genuine distribution, is itself at most `1`. `ind` is
    /// a HYPOTHESIS (any `{0,1}`-valued sequence), the same choice
    /// [`Self::markov_inequality`] makes for its own `ind` — `Rat.indicator`
    /// satisfies the hypothesis by construction, but nothing here is tied to
    /// that specific definition. What makes Markov/Chebyshev over
    /// `Rat.indicator` READ as a probability bound rather than a bare sum
    /// inequality.
    pub expectation_indicator_le_one: NameId,
    /// `Rat.variance X p n := expectation (fun k => sub (X k) (expectation X
    /// p n) * sub (X k) (expectation X p n)) p n` — `Var[X] := E[(X −
    /// E[X])²]`.
    pub variance: NameId,
    /// `Rat.variance_nonneg : ∀ X p n, IsDistribution p n → le zero (variance
    /// X p n)`.
    pub variance_nonneg: NameId,
    /// `Rat.variance_eq : ∀ X p n, IsDistribution p n → variance X p n = sub
    /// (expectation (fun k => X k * X k) p n) (mul (expectation X p n)
    /// (expectation X p n))` — `Var[X] = E[X²] − E[X]²`.
    pub variance_eq: NameId,
    /// `Rat.variance_smul : ∀ a X p n, IsDistribution p n →
    /// variance (fun k => a * X k) p n = (a*a) * variance X p n` — the scaling
    /// law `Var[a·X] = a²·Var[X]`.
    pub variance_smul: NameId,
    /// `Rat.covariance X Y p n := sub (expectation (fun k => X k * Y k) p n)
    /// (mul (expectation X p n) (expectation Y p n))` — `Cov[X,Y] := E[X·Y] −
    /// E[X]·E[Y]`.
    ///
    /// **There is no independence predicate anywhere in this development.**
    /// Independence is a statement about a JOINT distribution over a product
    /// space, and this development has only a single `p` over one index
    /// range — there is no way to state `P(X=x ∧ Y=y) = P(X=x)·P(Y=y)`.
    /// `Cov[X,Y] ~ 0` (uncorrelatedness) is the honest, strictly weaker
    /// hypothesis every theorem here uses instead.
    pub covariance: NameId,
    /// `Rat.variance_add_eq : ∀ X Y p n, IsDistribution p n →
    /// variance (fun k => X k + Y k) p n =
    /// add (variance X p n)
    ///     (add (covariance X Y p n) (add (covariance X Y p n) (variance Y p n)))` —
    /// `Var[X+Y] = Var[X] + (Cov[X,Y] + (Cov[X,Y] + Var[Y]))`, with the two
    /// copies of `Cov[X,Y]` standing in for the classical `2·Cov[X,Y]` (the
    /// same reason `rat_prelude::probability::sub_sq_expand` keeps two copies
    /// of `neg b * a` instead of `neg (2*b) * a`). **The headline: variance of
    /// a sum, with the cross term named rather than assumed away.**
    pub variance_add_eq: NameId,
    /// `Rat.variance_add_of_uncorrelated : ∀ X Y p n, IsDistribution p n →
    /// covariance X Y p n = zero → variance (fun k => X k + Y k) p n =
    /// add (variance X p n) (variance Y p n)` — the specialisation
    /// [`Self::variance_add_eq`] collapses to when the cross term vanishes.
    /// Uncorrelatedness, not independence — see [`Self::covariance`]'s doc.
    pub variance_add_of_uncorrelated: NameId,

    // --- the constructed indicator (rat_prelude::probability) --------------
    /// `Rat.indicator a X k := if Rat.ble a (X k) then Rat.one else
    /// Rat.zero` — the `{0,1}`-valued indicator `Rat.ble` was built to make
    /// constructible, discharging what [`Self::markov_inequality`] had to
    /// take as a hypothesis.
    pub indicator: NameId,
    /// `Rat.indicator_nonneg : ∀ a X k, le zero (Rat.indicator a X k)`.
    pub indicator_nonneg: NameId,
    /// `Rat.indicator_le : ∀ a X k, le zero (X k) → le (a * Rat.indicator a X
    /// k) (X k)` — exactly [`Self::markov_inequality`]'s fourth hypothesis,
    /// now discharged rather than assumed.
    pub indicator_le: NameId,
    /// `Rat.markov_constructed : ∀ a X p n, IsDistribution p n → (∀ k, Lt k n
    /// → le zero (X k)) → lt zero a → le (a * expectation (Rat.indicator a
    /// X) p n) (expectation X p n)` — [`Self::markov_inequality`] with the
    /// indicator supplied rather than hypothesised: an unconditional
    /// statement.
    pub markov_constructed: NameId,
    /// `Rat.chebyshev_inequality : ∀ a X p n, IsDistribution p n → lt zero a
    /// → le ((a*a) * expectation (Rat.indicator (a*a) (fun k => (X k −
    /// expectation X p n) * (X k − expectation X p n))) p n) (variance X p
    /// n)` — [`Self::markov_constructed`] applied to the squared deviation at
    /// threshold `a²`, in the multiplied-through form that needs no
    /// `Rat.inv`.
    pub chebyshev_inequality: NameId,

    // --- the weak law of large numbers scaffolding (rat_prelude::probability) --
    /// `Rat.covariance_add_right : ∀ X Y Z p n,
    /// covariance X (fun k => Y k + Z k) p n =
    /// add (covariance X Y p n) (covariance X Z p n)` — bilinearity of
    /// covariance in its second argument. Purely algebraic, no
    /// `IsDistribution` hypothesis needed (matching [`Self::expectation_add`]'s
    /// own unconditional linearity): `Cov[X,Y+Z] = E[X(Y+Z)] − E[X]E[Y+Z] =
    /// (E[XY]+E[XZ]) − (E[X]E[Y]+E[X]E[Z]) = Cov[X,Y]+Cov[X,Z]`.
    pub covariance_add_right: NameId,
    /// `Rat.sumVars X m k := sumRange (fun j => X j k) m` — the pointwise sum
    /// of `m` variables `X 0, X 1, …, X (m-1)`, each a `Nat → Rat` sequence
    /// over the same outcome index `k`.
    pub sum_vars: NameId,
    /// `Rat.expectation_sumVars : ∀ X p n m,
    /// expectation (sumVars X m) p n = sumRange (fun j => expectation (X j) p n) m`
    /// — linearity of expectation over a FAMILY of variables, by induction on
    /// `m` from [`Self::expectation_add`]. The scaffolding
    /// [`Self::variance_add_of_uncorrelated`] alone does not give: every
    /// multi-variable statement (the finite weak law of large numbers
    /// included) needs `E[Σ_j X_j] = Σ_j E[X_j]`, not just `E[X+Y]=E[X]+E[Y]`.
    pub expectation_sum_vars: NameId,
}

impl RatPrelude {
    /// The 22 ordered-commutative-ring laws, in the **declaration order of the
    /// `AxReal` package** — which is the order
    /// [`build_rat_model_of_arith`](crate::build_rat_model_of_arith) pairs them
    /// in, and the order `generalize_over_ordered_ring` binds them in.
    #[must_use]
    pub fn ring_laws(&self) -> [NameId; 22] {
        [
            self.le_refl,
            self.le_trans,
            self.lt_irrefl,
            self.lt_trans,
            self.lt_of_lt_of_le,
            self.lt_of_le_of_lt,
            self.le_of_lt,
            self.add_le_add,
            self.add_comm,
            self.add_assoc,
            self.add_zero,
            self.add_neg,
            self.mul_le_mul_of_nonneg_left,
            self.zero_lt_one,
            self.add_lt_add_of_le_of_lt,
            self.mul_comm,
            self.mul_assoc,
            self.mul_one,
            self.mul_zero,
            self.left_distrib,
            self.mul_nonneg,
            self.sq_nonneg,
        ]
    }
}

/// Intern every name the rational development uses, without declaring
/// anything: the proof scripts may name a law they have not yet reached.
fn intern_names(kernel: &mut Kernel, int: IntPrelude) -> RatPrelude {
    let root = int.rat;
    let child = |kernel: &mut Kernel, name: &str| kernel.name_str(root, name);
    RatPrelude {
        int,
        zero: child(kernel, "zero"),
        one: child(kernel, "one"),
        le: child(kernel, "le"),
        lt: child(kernel, "lt"),
        inv: child(kernel, "inv"),
        mul_inv_cancel: child(kernel, "mul_inv_cancel"),
        mul_inv_cancel_of_neg: child(kernel, "mul_inv_cancel_of_neg"),
        inv_pos: child(kernel, "inv_pos"),
        mul_pos: child(kernel, "mul_pos"),
        nat_div_succ_pos: child(kernel, "natDivSucc_pos"),
        sub_mul: child(kernel, "sub_mul"),
        mul_inv_sub_one: child(kernel, "mul_inv_sub_one"),
        inv_sub_inv: child(kernel, "inv_sub_inv"),
        inv_le_of_pos_le: child(kernel, "inv_le_of_pos_le"),
        inv_nat_div_succ: child(kernel, "inv_natDivSucc"),
        sub: child(kernel, "sub"),
        div: child(kernel, "div"),
        gcd_one_right: child(kernel, "gcd_one_right"),
        nat_gauss: child(kernel, "nat_gauss"),
        nat_dvd_antisymm_pos: child(kernel, "nat_dvd_antisymm_pos"),
        nat_mul_right_cancel: child(kernel, "nat_mul_right_cancel"),
        nat_div_cross: child(kernel, "nat_div_cross"),
        nat_abs_mul_of_nat: child(kernel, "nat_abs_mul_of_nat"),
        of_nat_inj: child(kernel, "of_nat_inj"),
        not_zero_le_neg_of_nat: child(kernel, "not_zero_le_neg_of_nat"),
        int_mul_right_cancel: child(kernel, "int_mul_right_cancel"),
        int_le_of_mul_le_mul_right: child(kernel, "int_le_of_mul_le_mul_right"),
        int_lt_of_mul_lt_mul_right: child(kernel, "int_lt_of_mul_lt_mul_right"),
        int_mul_le_mul_right: child(kernel, "int_mul_le_mul_right"),
        int_mul_lt_mul_right: child(kernel, "int_mul_lt_mul_right"),
        int_right_distrib: child(kernel, "int_right_distrib"),
        int_zero_mul: child(kernel, "int_zero_mul"),
        eq_zero_of_num_zero: child(kernel, "eq_zero_of_num_zero"),
        int_nonneg_of_nonneg: child(kernel, "int_nonneg_of_nonneg"),
        nonneg_of_int_nonneg: child(kernel, "nonneg_of_int_nonneg"),
        int_zero_le_of_nat: child(kernel, "int_zero_le_of_nat"),
        int_of_nat_pos: child(kernel, "int_of_nat_pos"),
        mk_congr: child(kernel, "mk_congr"),
        eta: child(kernel, "eta"),
        ext: child(kernel, "ext"),
        eq_of_cross: child(kernel, "eq_of_cross"),
        cross_of_eq: child(kernel, "cross_of_eq"),
        normalize_cross: child(kernel, "normalize_cross"),
        normalize_congr: child(kernel, "normalize_congr"),
        self_normalize: child(kernel, "self_normalize"),
        normalize_add_normalize: child(kernel, "normalize_add_normalize"),
        normalize_mul_normalize: child(kernel, "normalize_mul_normalize"),
        add_cross: child(kernel, "add_cross"),
        mul_cross: child(kernel, "mul_cross"),
        le_refl: child(kernel, "le_refl"),
        le_trans: child(kernel, "le_trans"),
        lt_irrefl: child(kernel, "lt_irrefl"),
        lt_trans: child(kernel, "lt_trans"),
        lt_of_lt_of_le: child(kernel, "lt_of_lt_of_le"),
        lt_of_le_of_lt: child(kernel, "lt_of_le_of_lt"),
        le_of_lt: child(kernel, "le_of_lt"),
        add_le_add: child(kernel, "add_le_add"),
        add_comm: child(kernel, "add_comm"),
        add_assoc: child(kernel, "add_assoc"),
        add_zero: child(kernel, "add_zero"),
        add_neg: child(kernel, "add_neg"),
        mul_le_mul_of_nonneg_left: child(kernel, "mul_le_mul_of_nonneg_left"),
        zero_lt_one: child(kernel, "zero_lt_one"),
        add_lt_add_of_le_of_lt: child(kernel, "add_lt_add_of_le_of_lt"),
        mul_comm: child(kernel, "mul_comm"),
        mul_assoc: child(kernel, "mul_assoc"),
        mul_one: child(kernel, "mul_one"),
        mul_zero: child(kernel, "mul_zero"),
        left_distrib: child(kernel, "left_distrib"),
        mul_nonneg: child(kernel, "mul_nonneg"),
        sq_nonneg: child(kernel, "sq_nonneg"),
        le_total: child(kernel, "le_total"),
        lt_of_not_le: child(kernel, "lt_of_not_le"),
        le_antisymm: child(kernel, "le_antisymm"),
        lt_trichotomy: child(kernel, "lt_trichotomy"),
        mul_eq_zero: child(kernel, "mul_eq_zero"),
        right_distrib: child(kernel, "right_distrib"),
        nat_div_succ: child(kernel, "natDivSucc"),
        int_le_or_lt: child(kernel, "int_le_or_lt"),
        le_or_lt: child(kernel, "le_or_lt"),
        int_pos_of_pos: child(kernel, "int_pos_of_pos"),
        int_one_le_of_pos: child(kernel, "int_one_le_of_pos"),
        nat_div_succ_lt_of_pos: child(kernel, "natDivSucc_lt_of_pos"),
        le_of_le_add_nat_div_succ: child(kernel, "le_of_le_add_natDivSucc"),
        zero_add: child(kernel, "zero_add"),
        neg_add_cancel: child(kernel, "neg_add_cancel"),
        neg_eq_of_add_eq_zero: child(kernel, "neg_eq_of_add_eq_zero"),
        neg_neg: child(kernel, "neg_neg"),
        neg_zero: child(kernel, "neg_zero"),
        neg_add: child(kernel, "neg_add"),
        neg_le_neg: child(kernel, "neg_le_neg"),
        sub_self: child(kernel, "sub_self"),
        neg_sub: child(kernel, "neg_sub"),
        sub_add_add: child(kernel, "sub_add_add"),
        sub_neg_sub: child(kernel, "sub_neg_sub"),
        sub_add_sub: child(kernel, "sub_add_sub"),
        bounds_add: child(kernel, "bounds_add"),
        nat_div_succ_add: child(kernel, "natDivSucc_add"),
        nat_div_succ_halve: child(kernel, "natDivSucc_halve"),
        nat_div_succ_scale: child(kernel, "natDivSucc_scale"),
        nat_div_succ_le_add_left: child(kernel, "natDivSucc_le_add_left"),
        zero_le_nat_div_succ: child(kernel, "zero_le_natDivSucc"),
        neg_nonpos_of_nonneg: child(kernel, "neg_nonpos_of_nonneg"),
        bounds_neg: child(kernel, "bounds_neg"),
        add_nonneg: child(kernel, "add_nonneg"),
        mul_neg: child(kernel, "mul_neg"),
        neg_mul: child(kernel, "neg_mul"),
        mul_le_mul_of_nonneg_right: child(kernel, "mul_le_mul_of_nonneg_right"),
        mul_sub_mul: child(kernel, "mul_sub_mul"),
        bounds_mul: child(kernel, "bounds_mul"),
        neg_mul_le_of_bounds: child(kernel, "neg_mul_le_of_bounds"),
        nat_div_succ_mul: child(kernel, "natDivSucc_mul"),
        nat_index_compose: child(kernel, "nat_index_compose"),
        nat_index_symm: child(kernel, "nat_index_symm"),
        nat_div_succ_le_scaled: child(kernel, "natDivSucc_le_scaled"),
        nat_div_succ_le_one: child(kernel, "natDivSucc_le_one"),
        int_le_nat_abs: child(kernel, "int_le_natAbs"),
        int_neg_nat_abs_le: child(kernel, "int_neg_natAbs_le"),
        bounds_num: child(kernel, "bounds_num"),
        abs: child(kernel, "abs"),
        abs_nonneg: child(kernel, "abs_nonneg"),
        le_abs_self: child(kernel, "le_abs_self"),
        neg_le_abs: child(kernel, "neg_le_abs"),
        abs_zero: child(kernel, "abs_zero"),
        abs_neg: child(kernel, "abs_neg"),
        abs_add: child(kernel, "abs_add"),
        abs_mul: child(kernel, "abs_mul"),
        abs_le_of_le_of_neg_le: child(kernel, "abs_le_of_le_of_neg_le"),
        le_of_abs_le: child(kernel, "le_of_abs_le"),
        neg_le_of_abs_le: child(kernel, "neg_le_of_abs_le"),
        abs_sub_comm: child(kernel, "abs_sub_comm"),
        max: child(kernel, "max"),
        min: child(kernel, "min"),
        max_cases: child(kernel, "max_cases"),
        min_cases: child(kernel, "min_cases"),
        le_max_left: child(kernel, "le_max_left"),
        le_max_right: child(kernel, "le_max_right"),
        max_le: child(kernel, "max_le"),
        min_le_left: child(kernel, "min_le_left"),
        min_le_right: child(kernel, "min_le_right"),
        le_min: child(kernel, "le_min"),
        le_of_sub_le: child(kernel, "le_of_sub_le"),
        sub_le_of_le: child(kernel, "sub_le_of_le"),
        sub_max_le: child(kernel, "sub_max_le"),
        sub_min_le: child(kernel, "sub_min_le"),
        zero_le_max_neg: child(kernel, "zero_le_max_neg"),
        ble: child(kernel, "ble"),
        ble_eq_true_of_le: child(kernel, "ble_eq_true_of_le"),
        le_of_ble_eq_true: child(kernel, "le_of_ble_eq_true"),
        ble_refl: child(kernel, "ble_refl"),
        ble_trans: child(kernel, "ble_trans"),
        ble_total: child(kernel, "ble_total"),
        sum_range: child(kernel, "sumRange"),
        sum_range_zero: child(kernel, "sumRange_zero"),
        sum_range_succ: child(kernel, "sumRange_succ"),
        sum_range_congr: child(kernel, "sumRange_congr"),
        sum_range_add: child(kernel, "sumRange_add"),
        mul_sum_range: child(kernel, "mul_sumRange"),
        sum_range_le: child(kernel, "sumRange_le"),
        sum_range_nonneg: child(kernel, "sumRange_nonneg"),
        is_distribution: child(kernel, "IsDistribution"),
        prob_le_one: child(kernel, "prob_le_one"),
        prob_complement: child(kernel, "prob_complement"),
        expectation: child(kernel, "expectation"),
        expectation_add: child(kernel, "expectation_add"),
        expectation_smul: child(kernel, "expectation_smul"),
        expectation_const: child(kernel, "expectation_const"),
        uniform: child(kernel, "uniform"),
        uniform_is_distribution: child(kernel, "uniform_is_distribution"),
        expectation_nonneg: child(kernel, "expectation_nonneg"),
        expectation_le: child(kernel, "expectation_le"),
        markov_inequality: child(kernel, "markov_inequality"),
        expectation_indicator_le_one: child(kernel, "expectation_indicator_le_one"),
        variance: child(kernel, "variance"),
        variance_nonneg: child(kernel, "variance_nonneg"),
        variance_eq: child(kernel, "variance_eq"),
        variance_smul: child(kernel, "variance_smul"),
        covariance: child(kernel, "covariance"),
        variance_add_eq: child(kernel, "variance_add_eq"),
        variance_add_of_uncorrelated: child(kernel, "variance_add_of_uncorrelated"),
        indicator: child(kernel, "indicator"),
        indicator_nonneg: child(kernel, "indicator_nonneg"),
        indicator_le: child(kernel, "indicator_le"),
        markov_constructed: child(kernel, "markov_constructed"),
        chebyshev_inequality: child(kernel, "chebyshev_inequality"),
        covariance_add_right: child(kernel, "covariance_add_right"),
        sum_vars: child(kernel, "sumVars"),
        expectation_sum_vars: child(kernel, "expectation_sumVars"),
    }
}

/// Build the rational prelude: `ℚ` as an ordered field over the constructed
/// `ℤ`, **asserting nothing**.
///
/// Idempotent on a kernel that already carries it — the second call returns the
/// interned handles without re-declaring. A failure rolls the environment back
/// to the pre-call state.
///
/// # Errors
///
/// Returns the trusted gate's rejection. An `Err` from a `Theorem` here means
/// the kernel **refused** a proof, not that a script gave up.
pub fn build_rat_prelude(kernel: &mut Kernel) -> Result<RatPrelude, KernelError> {
    let int = build_int_prelude(kernel)?;
    let prelude = intern_names(kernel, int);
    if kernel.environment().get(prelude.zero).is_some() {
        return Ok(prelude);
    }
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<(), KernelError> {
        let mut d = IntDev::new(kernel, int);
        defs::declare_support(&mut d, prelude)?;
        defs::declare_constants(&mut d, prelude)?;
        defs::declare_order(&mut d, prelude)?;
        defs::declare_inverse(&mut d, prelude)?;
        core::declare_structural(&mut d, prelude)?;
        core::declare_arithmetic_support(&mut d, prelude)?;
        core::declare_uniqueness(&mut d, prelude)?;
        core::declare_normalize_laws(&mut d, prelude)?;
        laws::declare_order_laws(&mut d, prelude)?;
        laws::declare_ring_laws(&mut d, prelude)?;
        scaling::declare_scaling_laws(&mut d, prelude)?;
        laws::declare_right_distrib(&mut d, prelude)?;
        archimedean::declare_archimedean(&mut d, prelude)?;
        laws::declare_trichotomy(&mut d, prelude)?;
        group::declare_group_laws(&mut d, prelude)?;
        product::declare_product_laws(&mut d, prelude)?;
        field::declare_field_laws(&mut d, prelude)?;
        lattice::declare_lattice(&mut d, prelude)?;
        abs::declare_abs(&mut d, prelude)?;
        decide::declare_decide(&mut d, prelude)?;
        sum::declare_sum(&mut d, prelude)?;
        probability::declare_probability(&mut d, prelude)?;
        Ok(())
    })();
    match built {
        Ok(()) => Ok(prelude),
        Err(error) => {
            kernel.rollback_prelude(checkpoint);
            Err(error)
        }
    }
}

#[cfg(test)]
mod rat_prelude_tests;
