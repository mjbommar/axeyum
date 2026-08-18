//! The **rational prelude**: `ℚ` **constructed** over the proved `ℤ` and `ℕ`
//! developments, as an ordered field, declared through the trusted
//! [`Kernel::add_declaration`](crate::Kernel::add_declaration) gate.
//!
//! ## Why this is the missing rung
//!
//! `Real` is 30 trusted constants. Enumerate them and 22 are the laws of an
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

mod archimedean;
mod core;
mod defs;
mod field;
pub(crate) mod group;
mod laws;
mod model;
pub(crate) mod ops;
mod product;
mod scaling;
mod statements;

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
    /// **Not** one of the 22: the `Real` package does not assume totality
    /// (ADR-0456 counted it as absent), so this is a property `ℚ` has and the
    /// axiomatized `Real` does not. It is one line — `Rat.le` unfolds to
    /// `Int.le` on cross-products, and `Int.le_total` is already proved.
    pub le_total: NameId,
    /// `Rat.lt_of_not_le : ∀ a b, Not (le a b) → lt b a`.
    ///
    /// The entry point for any argument by contradiction on the order, and in
    /// particular the first step of an Archimedean argument: `¬(a ≤ b)` gives
    /// `b < a`, and only then is there a positive quantity to bound.
    pub lt_of_not_le: NameId,

    // --- the Archimedean property (ADR-0483 phase R1) -------------------------
    /// `Rat.natDivSucc : Nat → Nat → Rat` — the rational `k/(j+1)`, as a single
    /// `Rat.normalize` whose denominator is positive by construction.
    ///
    /// One definition serves the regularity bound (`k = 1`), the setoid
    /// closeness bound (`k = 2`) and the Archimedean bound (`k = 6`) of
    /// ADR-0483's real construction, and `Rat.abs` is never needed because
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
    /// **The Archimedean property of `ℚ`.** ADR-0483 identifies this as the one
    /// genuinely new rational lemma the Bishop-setoid construction of `ℝ` needs:
    /// transitivity of `CReal.Equiv` only reaches `|x_n − z_n| ≤ 2/n + 6/j` for
    /// every `j`, and this is what turns that into `≤ 2/n`.
    pub le_of_le_add_nat_div_succ: NameId,

    // --- the ordered-group toolkit (ADR-0483 phase R1) ------------------------
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
    /// The triangle inequality in ADR-0483's encoding, where `|a| ≤ b` is the
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

    // --- the multiplicative toolkit (ADR-0483 phase R2, `CReal.mul`) ----------
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
    /// ADR-0483 computes it.
    pub bounds_num: NameId,
}

impl RatPrelude {
    /// The 22 ordered-commutative-ring laws, in the **declaration order of the
    /// `Real` package** — which is the order
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
        archimedean::declare_archimedean(&mut d, prelude)?;
        group::declare_group_laws(&mut d, prelude)?;
        product::declare_product_laws(&mut d, prelude)?;
        field::declare_field_laws(&mut d, prelude)?;
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
