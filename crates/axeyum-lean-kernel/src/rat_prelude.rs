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

pub(crate) mod abs;
pub mod algebra_instances;
mod archimedean;
mod bernoulli;
mod clear_below;
mod core;
mod decidable;
mod decide;
mod defs;
mod det_mul;
mod diagonal;
mod echelon;
mod echelon_invariant;
mod echelon_section;
mod field;
pub(crate) mod group;
pub(crate) mod lattice;
mod laws;
mod leading_index;
mod matrix;
mod matrix_det;
mod matrix_det_mul;
mod matrix_det_selection;
mod matrix_invertible;
mod matrix_n;
mod matrix_transpose;
mod model;
mod nullity;
pub(crate) mod ops;
mod pivot_bound;
mod pivot_content;
mod polynomial;
mod pow_bridge;
mod probability;
mod product;
mod rank;
mod rank_bridge;
mod scaling;
mod statements;
mod sum;
mod sum_maps;
mod taylor;
mod vector;

pub use model::{RatModel, RatModelLaw, build_rat_model_of_arith};

use crate::int_prelude::ops::IntDev;
use crate::nat_prelude::NatOps;
use algebra_instances::AlgebraNames;

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
    /// `Rat.mul_inv_cancel_of_ne_zero : ∀ q, Not (Eq Rat q Rat.zero) →
    /// Eq Rat (Rat.mul q (Rat.inv q)) Rat.one`.
    ///
    /// The `q ≠ 0` unification of [`Self::mul_inv_cancel`] and
    /// [`Self::mul_inv_cancel_of_neg`], via [`Self::lt_trichotomy`] (which is
    /// itself constructive — no excluded middle). Useful anywhere a caller has
    /// only a disequality and not a sign.
    pub mul_inv_cancel_of_ne_zero: NameId,
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
    /// `Rat.one_ne_zero : Not (Eq Rat Rat.one Rat.zero)`.
    ///
    /// The nontriviality axiom `Rat.IsField`'s bundle needs and nothing
    /// upstream ever phrased: [`Self::zero_lt_one`] (`0 < 1`) is `Rat`'s own
    /// positivity fact, rewritten to a disequality by one transport against
    /// [`Self::lt_irrefl`] — no case split, no representation reasoning.
    pub one_ne_zero: NameId,
    /// `Rat.IsField (add mul : Rat → Rat → Rat) (neg inv : Rat → Rat) (zero
    /// one : Rat) : Prop` — the bundled-predicate shape
    /// (`nat_prelude::group::declare_group_all`'s `Nat.IsGroupOn` is the house
    /// pattern) for "these six operations make a commutative field", packed
    /// right-nested exactly as `IsGroupOn` is:
    ///
    /// `add_comm ∧ (add_assoc ∧ (add_zero ∧ (add_neg ∧ (mul_comm ∧ (mul_assoc
    /// ∧ (mul_one ∧ (distrib ∧ (one_ne_zero ∧ inv_cancel))))))))`
    ///
    /// **No bound parameter** (`IsGroupOn`'s `n`), and named `IsField` rather
    /// than `IsFieldOn` for exactly that reason: `Rat` is already the whole
    /// carrier the operations range over, unlike `Nat.IsGroupOn`'s
    /// `{0,…,n-1}`, so there is no domain to close the operations over.
    /// `inv_cancel`'s hypothesis is `a ≠ 0`, not `0 < a` — `Rat.inv`'s totality
    /// (`inv 0 = 0`) makes the unconditional law false, and a field in
    /// general has no order to phrase a positive version in.
    pub is_field: NameId,
    /// `Rat.rat_isField : Rat.IsField Rat.add Rat.mul Rat.neg Rat.inv
    /// Rat.zero Rat.one` — **the worked instance**, assembled from the ten
    /// existing laws (`Self::add_comm`/`add_assoc`/`add_zero`/`add_neg`/
    /// `mul_comm`/`mul_assoc`/`mul_one`/`left_distrib`/[`Self::one_ne_zero`]/
    /// `mul_inv_cancel_of_ne_zero`) via nested `And.intro` — no new algebra,
    /// every leaf a bare reference to an already-admitted theorem, because
    /// each one's *stated* type already matches the bundle's corresponding
    /// component verbatim.
    pub rat_is_field: NameId,
    /// `Rat.mul_left_cancel_of_ne_zero : ∀ a b c, Not (Eq Rat a Rat.zero) →
    /// Eq Rat (Rat.mul a b) (Rat.mul a c) → Eq Rat b c`.
    ///
    /// The consequence a field gives that a ring does not: scale by `a⁻¹`.
    /// The same `b = b·1 = b·(a⁻¹·a)⁻¹ …` shape
    /// `nat_prelude::group::declare_group_left_cancel` runs over an abstract
    /// `IsGroupOn`, specialised to `Rat`'s own commutative multiplication —
    /// only the one inverse law `a⁻¹·a = 1` is needed, not a bounded group's
    /// closure/membership bookkeeping.
    pub mul_left_cancel_of_ne_zero: NameId,
    /// `Rat.IsOrderedField (add mul : Rat → Rat → Rat) (neg inv : Rat → Rat)
    /// (zero one : Rat) : Prop := Rat.IsField add mul neg inv zero one ∧
    /// (translation ∧ mul_nonneg)` — `IsField` extended with the two order
    /// axioms of an ordered field:
    ///
    /// - translation invariance: `∀ x y z, le x y → le (add x z) (add y z)`;
    /// - closure of the nonnegatives under multiplication: `∀ x y, le zero x
    ///   → le zero y → le zero (mul x y)`.
    ///
    /// Composition, not restatement: the ten field leaves are never rebuilt,
    /// `Rat.IsField` is reused as this bundle's first conjunct verbatim.
    /// `Rat.le` is fixed rather than a bundle parameter, exactly as `Eq Rat`
    /// is fixed in `IsField`'s own leaves — the same "no bound parameter"
    /// reason `IsField` gives for its own name (`Rat` is already the whole
    /// carrier).
    pub is_ordered_field: NameId,
    /// `Rat.rat_isOrderedField : Rat.IsOrderedField Rat.add Rat.mul Rat.neg
    /// Rat.inv Rat.zero Rat.one` — the worked instance. The field component
    /// is [`Self::rat_is_field`] verbatim; translation invariance is
    /// [`Self::add_le_add`] paired with a reflexive hypothesis on the shared
    /// summand ([`Self::le_refl`]); closure of the nonnegatives is
    /// [`Self::mul_nonneg`] verbatim — its stated type already matches this
    /// bundle's second order axiom, so neither order axiom needs new
    /// algebra.
    pub rat_is_ordered_field: NameId,
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
    /// `Rat.lt_of_sq_lt : ∀ a b, Rat.le Rat.zero a → Rat.le Rat.zero b →
    /// Rat.lt (Rat.mul a a) (Rat.mul b b) → Rat.lt a b`.
    ///
    /// The **strict companion** to `CReal.ratSqLe` (`creal::mul_self_zero`,
    /// `u·u ≤ s·s → 0 ≤ s → u ≤ s`) — its own contrapositive, proved
    /// independently rather than derived from it since the `<`/`≤` swap does
    /// not go through `Classical`. Case split on
    /// [`Self::le_or_lt`]`(b, a) : Or (le b a) (lt a b)`: the right branch is
    /// the goal directly; the left branch (`b ≤ a`) gives `b·b ≤ b·a` (by
    /// [`Self::mul_le_mul_of_nonneg_left`] at `0 ≤ b`) and `b·a ≤ a·a` (by
    /// [`Self::mul_le_mul_of_nonneg_right`] at `0 ≤ a`), chaining to
    /// `b·b ≤ a·a` — which contradicts the hypothesis `a·a < b·b` via
    /// `lt_of_le_of_lt`/`lt_irrefl`. No difference-of-squares identity is
    /// needed (unlike `ratSqLe`'s own proof), since both monotonicity
    /// directions are already Rat-level facts.
    pub lt_of_sq_lt: NameId,
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
    /// `Rat.natDivSucc_antitone : ∀ (j j' : Nat), Nat.le j j' →
    /// Rat.le (natDivSucc 1 j') (natDivSucc 1 j)`.
    ///
    /// **Antitonicity, at last** — the lemma [`Self::nat_div_succ_scale`]'s doc
    /// says was kept off the critical path. Direct route, not the reciprocal
    /// one: unfold `Rat.le` to its cross-multiplication definition and cancel
    /// the (positive) product of the two denominators via
    /// [`Self::int_le_of_mul_le_mul_right`], after regrouping both sides
    /// through [`Self::normalize_cross`] applied at each `natDivSucc`
    /// separately. No `Rat.inv` is touched, so this needs neither `inv_inv`
    /// (which this prelude still does not have) nor a `Nat → Rat`
    /// order-transport lemma — `Int.le (ofNat m) (ofNat n)` already unfolds to
    /// `Nat.le m n` definitionally (the four-case table in `int_prelude`'s
    /// definitions module), so `Nat.succ_le_succ` on the hypothesis serves
    /// directly wherever `Int.le` on the two successor denominators is needed.
    pub nat_div_succ_antitone: NameId,
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

    // --- `Decidable` instances (rat_prelude::decidable) ---------------------
    /// `Rat.decidable_le : ∀ a b, Decidable (Rat.le a b)` — the `logic`
    /// prelude's `Decidable.ofBool` bridge applied to [`Self::ble`] and its
    /// two spec directions ([`Self::le_of_ble_eq_true`],
    /// [`Self::ble_eq_true_of_le`]), the same pattern
    /// `string_prelude/decidable.rs` uses for `Char.decidable_eq` /
    /// `Str.decidable_eq` / `Str.decidable_isPrefix`. The negative direction
    /// (`Rat.ble a b = false → ¬ Rat.le a b`) is derived by contraposition
    /// against [`Self::ble_eq_true_of_le`], via the generic
    /// `NatOps::bool_symm`/`bool_trans`/`false_true_elim` combinators — no new
    /// case split on `Rat`'s representation.
    pub decidable_le: NameId,

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
    /// `Rat.sumRange_congr_lt : ∀ f g n, (∀ i, Lt i n → f i = g i) →
    /// sumRange f n = sumRange g n` — [`Self::sum_range_congr`]'s pointwise
    /// hypothesis weakened to indices below the bound, exactly
    /// `Nat.sumRange_congr_lt`'s own shape carried over to `ℚ`. A
    /// general-purpose gap in `ℚ`'s sum development: what a sum whose
    /// summand identity holds only on a bounded range can actually supply.
    pub sum_range_congr_lt: NameId,
    /// `Rat.sumRange_eq_zero_of_lt : ∀ f n, (∀ i, Lt i n → f i = zero) →
    /// sumRange f n = zero` — "a sum of pointwise, bounded zeros is zero".
    /// The prerequisite [`Self::covariance_sum_vars_left`]'s successor step
    /// needs when specialised at `PairwiseUncorrelated`'s zero facts (which
    /// are supplied for `i ≠ j` within a range, never universally, so
    /// [`Self::sum_range_congr`]'s UNRESTRICTED hypothesis cannot be used).
    pub sum_range_eq_zero_of_lt: NameId,
    /// `Rat.sumRange_swap : ∀ f n m, sumRange (fun i => sumRange (fun j => f
    /// i j) n) m = sumRange (fun j => sumRange (fun i => f i j) m) n` — the
    /// **binder order is `f`, then the INNER bound, then the OUTER bound**
    /// (`rat_prelude/sum.rs`'s `declare_sum_range_swap`, which allocates
    /// `n_fv` before `m_fv`). This line read `∀ f m n` until 2026-08-30 and
    /// the transposition is invisible at the call site — both arguments are
    /// `Nat` — so it costs one kernel rejection whose message names the two
    /// bounds and not the lemma. `rat_prelude/matrix_n.rs`'s associativity
    /// proof took exactly that rejection.
    /// Fubini/rectangle-swap over a `ℚ`-valued double sum, `f`/`n` fixed and
    /// induction on `m` alone. Not `Nat`'s `rectangle`/`diagonal`
    /// triangle+corner decomposition — this is the plain order-of-summation
    /// swap a Cauchy product's `(Σa)(Σb)` side needs before any antidiagonal
    /// reindexing, and it needs no `Nat.sub`.
    pub sum_range_swap: NameId,
    /// `Rat.sumRange_split : ∀ f m j, sumRange f (add m j) = add (sumRange f
    /// m) (sumRange (fun k => f (add m k)) j)` — the `Rat` port of
    /// `Nat.sumRange_split` (`nat_prelude::rectangle`). By induction on `j`
    /// alone, `f`/`m` fixed; needs no `Nat.sub`.
    pub sum_range_split: NameId,
    /// `Rat.sumRange_diagonal : ∀ F n, sumRange (fun k => sumRange (fun i =>
    /// F i (sub k i)) (succ k)) n = sumRange (fun i => sumRange (fun j => F i
    /// j) (sub n i)) n` — the antidiagonal-triangle-by-`k` sum equals the
    /// same triangle grouped by row `i`. The `Rat` port of
    /// `Nat.sumRange_diagonal` (`nat_prelude::diagonal`,
    /// `rat_prelude::diagonal`).
    pub sum_range_diagonal: NameId,
    /// `Rat.sumRange_rect_eq_diag_add_corner : ∀ F n, sumRange (fun i =>
    /// sumRange (fun j => F i j) n) n = add (sumRange (fun k => sumRange (fun
    /// i => F i (sub k i)) (succ k)) n) (sumRange (fun i => sumRange (fun k
    /// => F i (add (sub n i) k)) i) n)` — rectangle equals the antidiagonal
    /// triangle plus the corner, the same-bound `n×n` square decomposition
    /// the naive finite Cauchy identity's refutation forces
    /// (`rat_prelude/diagonal.rs`'s module doc). The `Rat` port of
    /// `Nat.sumRange_rect_eq_diag_add_corner` (`nat_prelude::rectangle`).
    pub sum_range_rect_eq_diag_add_corner: NameId,
    /// `Rat.sumRange_mul : ∀ f g m n, mul (sumRange f m) (sumRange g n) =
    /// sumRange (fun i => mul (f i) (sumRange g n)) m` — one factor's sum
    /// distributes over a product with a second sum. TWO independent bounds:
    /// nothing requires `m = n`. Not an induction — `sumRange g n` plays the
    /// "constant" role [`Self::mul_sum_range`] already handles, reached by
    /// `mul_comm` on both sides of it.
    pub sum_range_mul: NameId,
    /// `Rat.sumRange_mul_double : ∀ f g m n, mul (sumRange f m) (sumRange g n)
    /// = sumRange (fun i => sumRange (fun j => mul (f i) (g j)) n) m` — the
    /// un-grouped, **subtraction-free** rectangle form of the Cauchy product,
    /// `f i * g j` at every `(i, j)` with `i < m`, `j < n`. From
    /// [`Self::sum_range_mul`] plus [`Self::sum_range_congr`] moving
    /// [`Self::mul_sum_range`] under the outer sum. Not the diagonal-grouped
    /// convolution — that is [`Self::sum_range_mul_eq_diag_add_corner`].
    pub sum_range_mul_double: NameId,
    /// `Rat.sumRange_mul_eq_diag_add_corner : ∀ f g n,`
    /// `mul (sumRange f n) (sumRange g n) = add (sumRange (fun k => sumRange`
    /// `(fun i => mul (f i) (g (sub k i))) (succ k)) n) (sumRange (fun i =>`
    /// `sumRange (fun k => mul (f i) (g (add (sub n i) k))) i) n)` — **the
    /// finite Cauchy product over `ℚ`, in its honest form**: a product of two
    /// partial sums is the antidiagonal-grouped convolution PLUS a corner term
    /// the naive identity drops (refuted at `n = 2` already over `ℕ`).
    ///
    /// Composes [`Self::sum_range_mul_double`] at `[f, g, n, n]` with
    /// [`Self::sum_range_rect_eq_diag_add_corner`] at the separable
    /// `F i j := f i * g j`. The `ℚ` counterpart of
    /// [`ComplexPrelude::sum_range_mul_eq_diag_add_corner`](crate::ComplexPrelude::sum_range_mul_eq_diag_add_corner),
    /// but stated redex-free: the triangle and corner here read as ordinary
    /// convolution sums rather than as `F` applications awaiting beta.
    pub sum_range_mul_eq_diag_add_corner: NameId,

    // --- polynomials (rat_prelude::polynomial) ------------------------------
    /// `Rat.pow : Rat → Nat → Rat`, `Nat.rec` on the exponent: `pow a zero ≡
    /// one`, `pow a (succ j) ≡ mul (pow a j) a` — mirroring `Int.pow`
    /// exactly, the new factor on the RIGHT.
    pub pow: NameId,
    /// `Rat.pow_zero : ∀ a, pow a zero = one` — `Eq.refl`.
    pub pow_zero: NameId,
    /// `Rat.pow_succ : ∀ a m, pow a (succ m) = mul (pow a m) a` — `Eq.refl`.
    pub pow_succ: NameId,
    /// `Rat.pow_add : ∀ a (m n : Nat), pow a (Nat.add m n) = mul (pow a m)
    /// (pow a n)` — the exponent law. Induction on `n` with `m` fixed, the
    /// `Rat` port of `Int.pow_add`; `Nat`, `Int`, `Complex` and `CReal` all
    /// already carry it. Needed to collapse an antidiagonal cell
    /// `(a i · x^i) · (b (k−i) · x^(k−i))` into `(a i · b (k−i)) · x^k`,
    /// which is the step between
    /// [`Self::sum_range_mul_eq_diag_add_corner`] and a convolution stated
    /// over [`Self::poly_eval`].
    pub pow_add: NameId,
    /// `Rat.pow_sub_add : ∀ x i k, Nat.le i k → pow x k = mul (pow x
    /// (Nat.sub k i)) (pow x i)` — the **antidiagonal cell collapse**: on the
    /// antidiagonal `i + j = k` the two powers `x^i` and `x^(k−i)` recombine
    /// into `x^k`. The `Nat.le i k` hypothesis is load-bearing, because
    /// `Nat.sub` truncates: without it the claim is false at `i = 3, k = 1`.
    /// No induction — `Nat.sub_add_cancel` lifted through `fun e => pow x e`,
    /// then [`Self::pow_add`].
    pub pow_sub_add: NameId,
    /// `Rat.pow_natDivSucc_two : ∀ n, pow (natDivSucc 1 1) n = normalize
    /// (ofNat 1) (Nat.pow 2 n) w`, where `w : 1 ≤ Nat.pow 2 n` is
    /// `Nat.pow_pos 2 n two_pos`.
    ///
    /// The bridge `creal/exponential.rs` names as still missing: `pow` (the
    /// repeated-multiplication form) and `normalize` (the direct
    /// `2ⁿ`-denominator form) are the same rational, but no lemma related
    /// the two representations. By induction on `n`, via `normalize_mul_normalize`
    /// at the step (`(rat_prelude/pow_bridge.rs`).
    pub pow_nat_div_succ_two: NameId,
    /// `Rat.polyEval : (Nat → Rat) → Nat → Rat → Rat`, `polyEval c n x :=
    /// sumRange (fun i => c i * x^i) n` — a polynomial given as a
    /// coefficient function and an explicit degree bound, evaluated at a
    /// point.
    pub poly_eval: NameId,
    /// `Rat.polyEval_zero : ∀ c x, polyEval c zero x = zero` — `Eq.refl`.
    pub poly_eval_zero: NameId,
    /// `Rat.polyEval_succ : ∀ c n x, polyEval c (succ n) x = polyEval c n x +
    /// c n * x^n` — `Eq.refl`.
    pub poly_eval_succ: NameId,
    /// `Rat.polyEval_add : ∀ c g n x, polyEval (fun i => c i + g i) n x =
    /// polyEval c n x + polyEval g n x` — evaluation is additive.
    pub poly_eval_add: NameId,
    /// `Rat.polyEval_smul : ∀ a c n x, polyEval (fun i => a * c i) n x = a *
    /// polyEval c n x` — a scalar distributes through evaluation.
    pub poly_eval_smul: NameId,

    // --- the finite Taylor expansion identity (rat_prelude::taylor) ---------
    /// `Rat.pow_one : ∀ a, pow a (succ zero) = a` — the missing `n = 1`
    /// instance `polynomial.rs` never needed (every other file's degree-1
    /// term arrived pre-simplified). Proved via `pow_succ` + `pow_zero` +
    /// `mul_comm` + `mul_one` (`pow a 1 = one * a = a * one = a`, the middle
    /// step because this prelude has no `one_mul`).
    pub pow_one: NameId,
    /// `Rat.add_sub_cancel_left : ∀ a x, add a (sub x a) = x` — the residue
    /// of a point from its own basepoint is the basepoint's error, restated:
    /// what turns `p(a) + c·(x−a)` back into a statement about `p(a)` and
    /// `x` without ever exposing `Rat.sub`'s own definition to the caller.
    pub add_sub_cancel_left: NameId,
    /// `Rat.sq_sub_sq : ∀ x a, sub (mul x x) (mul a a) = mul (sub x a) (add x
    /// a)` — the difference-of-squares factor theorem, `x² − a²
    /// factors through (x−a)`. The reusable algebraic core of the factor
    /// theorem at degree 2: `Self::taylor_deg2` (if built) and any future
    /// even-degree rung reach for this rather than re-deriving it. Proved
    /// via `mul_sub_mul` + `mul_comm` + `left_distrib`, no induction.
    pub sq_sub_sq: NameId,
    /// `Rat.polyEval_deg1 : ∀ c0 c1 t, polyEval (coeff2 c0 c1) 2 t = add c0
    /// (mul c1 t)` — the closed form for evaluating a degree-≤1 polynomial,
    /// where `coeff2 c0 c1` is the coefficient function built inline by
    /// `Nat.rec` (`i = 0 ↦ c0`, `i ≥ 1 ↦ c1`). Not itself a public
    /// `Definition` — `coeff2` is scaffolding local to this file, the same
    /// "inline `Nat.rec`, no named cast" move `bernoulli.rs`'s `L` uses —
    /// but its *evaluation law* is the reusable rung: [`Self::taylor_deg1`]
    /// instantiates it at `t = x` and `t = a` and needs nothing else about
    /// `coeff2`'s internals.
    pub poly_eval_deg1: NameId,
    /// `Rat.taylor_deg1 : ∀ c0 c1 x a, polyEval (coeff2 c0 c1) 2 x =
    /// polyEval (coeff2 c0 c1) 2 a + c1 * (x − a)` — the finite Taylor
    /// expansion identity (ADR-0603 row 3's algebraic core, no analysis, no
    /// limits, no MVT) at degree 1: a degree-≤1 polynomial equals its value
    /// at the center plus its (constant) derivative times `x − a`, exactly
    /// and for every `x`, `a` — not an approximation, and no remainder term
    /// (a degree-≤1 polynomial's own Taylor polynomial of degree 1 is
    /// itself). Reduces, at `n = 0`, to the ordinary Mean Value Theorem's
    /// polynomial case handled instead by `crate::mvt` over `CReal`; this
    /// is the same headline identity, over `ℚ`, algebraically, with the
    /// factor `c1` — the formal derivative's only nonzero coefficient — read
    /// off directly rather than searched for. Proved via
    /// [`Self::poly_eval_deg1`] (twice, at `x` and at `a`),
    /// [`Self::add_sub_cancel_left`], and `left_distrib` — no
    /// [`Self::sq_sub_sq`], which degree-1 has no use for.
    pub taylor_deg1: NameId,

    // --- Bernoulli's inequality and the harmonic power bound (rat_prelude::bernoulli) ---
    /// `Rat.bernoulli : ∀ t, Rat.le Rat.zero t →`
    /// `∀ n, Rat.le (L t n) (Rat.pow (Rat.add Rat.one t) n)`, where `L t n`
    /// is the inline `Nat.rec`-built companion `1 + n·t` — see
    /// `bernoulli.rs`'s module doc for why it is not a named cast. Spivak
    /// Chapter 2's Bernoulli's inequality, `t ≥ 0` case (not the general
    /// `t ≥ -1`; see the module doc for why the restriction is deliberate).
    pub bernoulli: NameId,
    /// `Rat.bernoulli_harmonic_bound : ∀ x t, Rat.le Rat.zero x →`
    /// `Rat.le Rat.zero t → Rat.le (Rat.mul x (Rat.add Rat.one t)) Rat.one →`
    /// `∀ m, Rat.le (Rat.mul (L t m) (Rat.pow x m)) Rat.one` — the
    /// cross-multiplied form of `xᵐ ≤ 1/(1+m·t)`, avoiding `Rat.inv`. The
    /// harmonic-shaped bound `geom_pair_within`'s own module doc
    /// (`creal/geometric.rs`) names as the missing piece blocking
    /// `CReal.geom_cauchy`; see `bernoulli.rs`'s module doc for exactly what
    /// bridging this rational fact back across a `CReal.pow` sample would
    /// still need.
    pub bernoulli_harmonic_bound: NameId,

    // --- `Rat.dotN`: the n-dimensional dot product (rat_prelude::vector) ---
    /// `Rat.dotN : (Nat → Rat) → (Nat → Rat) → Nat → Rat := fun u v n =>
    /// sumRange (fun i => u i * v i) n` — the finite-dimensional inner
    /// product. `matrix.rs`'s own `adj2` note applies here too: this kernel
    /// has no product/tuple type, so a "vector" is not reified as its own
    /// carrier — it is represented exactly the way [`Self::sum_range`]
    /// already represents a summand, a coefficient FUNCTION `Nat → Rat`
    /// together with an explicit dimension bound `n`.
    pub dot_n: NameId,
    /// `Rat.dotN_zero : ∀ u v, dotN u v zero = zero` — `Eq.refl`, the same
    /// way [`Self::sum_range_zero`] is.
    pub dot_n_zero: NameId,
    /// `Rat.dotN_succ : ∀ u v n, dotN u v (succ n) = dotN u v n + u n * v n`
    /// — `Eq.refl`, the same way [`Self::sum_range_succ`] is.
    pub dot_n_succ: NameId,
    /// `Rat.dotN_comm : ∀ u v n, dotN u v n = dotN v u n` — one
    /// [`Self::sum_range_congr`] applied to the pointwise
    /// [`Self::mul_comm`].
    pub dot_n_comm: NameId,
    /// `Rat.dotN_add_left : ∀ u1 u2 v n,`
    /// `dotN (fun i => u1 i + u2 i) v n = dotN u1 v n + dotN u2 v n` —
    /// linearity in the first argument. [`Self::right_distrib`] distributes
    /// the summand pointwise (via [`Self::sum_range_congr`]), then
    /// [`Self::sum_range_add`] splits the sum — the same two-step shape
    /// [`Self::expectation_add`] uses.
    pub dot_n_add_left: NameId,
    /// `Rat.dotN_smul_left : ∀ a u v n,`
    /// `dotN (fun i => a * u i) v n = a * dotN u v n` — the scalar half of
    /// bilinearity. [`Self::mul_assoc`] regroups the summand pointwise, then
    /// [`Self::mul_sum_range`] pulls the constant back out of the sum — the
    /// same two-step shape [`Self::expectation_smul`] uses.
    pub dot_n_smul_left: NameId,
    /// `Rat.dotN_self_nonneg : ∀ v n, le zero (dotN v v n)` — every diagonal
    /// dot product is nonnegative, since each summand is a square
    /// ([`Self::sq_nonneg`]) and [`Self::sum_range_nonneg`] carries that
    /// through the sum.
    pub dot_n_self_nonneg: NameId,
    /// `Rat.dotN_two : ∀ u v,`
    /// `dotN u v (succ (succ zero)) = u zero * v zero + u (succ zero) * v (succ zero)`
    /// — the n = 2 cross-check: unfolding [`Self::dot_n`]'s general
    /// recursion at the fixed dimension `matrix.rs`'s own 2×2 development
    /// lives at (`det2_mul`'s `row1a := a*e+b*g` is exactly a 2-dimensional
    /// dot product, written out by hand there because `Rat.adj2` cannot be
    /// reified). Two applications of [`Self::dot_n_succ`], one of
    /// [`Self::dot_n_zero`], one of [`Self::zero_add`] — no new algebra, a
    /// check that the general recursive definition collapses to the
    /// expected concrete arithmetic.
    pub dot_n_two: NameId,
    /// `Rat.dotN_cauchy_schwarz : ∀ u v n,`
    /// `(dotN u v n) * (dotN u v n) ≤ (dotN u u n) * (dotN v v n)` —
    /// Cauchy–Schwarz, in SQUARED form: ℚ has no square root, the same
    /// limit [`crate::creal_point::CPointPrelude::cauchy_schwarz`] (the
    /// plane) and [`Self::covariance_sq_le_variance_mul`] (probability)
    /// each record. The discriminant argument: `0 ≤ dotN (t*u+v) (t*u+v) n`
    /// for every rational `t` ([`Self::dot_n_self_nonneg`] plus
    /// bilinearity), unconditional over `A := dotN u u n`, `B := dotN u v
    /// n`, `C := dotN v v n`. `A ≥ 0` always ([`Self::dot_n_self_nonneg`]),
    /// so only `A = 0` vs `A > 0` needs a case split: `A > 0` closes at `t
    /// := -(B·A⁻¹)` (the minimizer, via [`Self::mul_inv_cancel`]); `A = 0,
    /// C > 0` reduces to the same case with `u`/`v` swapped
    /// ([`Self::dot_n_comm`] reads the result back); `A = 0, C = 0` closes
    /// at `t := 1` and `t := -1` (`B + B = 0`, no sign case-split on `B`
    /// itself) — the same three-case shape
    /// [`Self::covariance_sq_le_variance_mul`] uses, unweighted.
    pub dot_n_cauchy_schwarz: NameId,

    // --- matrices at symbolic dimension (rat_prelude::matrix_n) ------------
    /// `Rat.matMul : (Nat → Nat → Rat) → (Nat → Nat → Rat) → Nat → Nat → Nat
    /// → Rat`, `matMul A B k i j := sumRange (fun t => A i t * B t j) k` —
    /// matrix multiplication at **symbolic** dimension, one index up from
    /// [`Self::dot_n`]. `matMul A B k` is itself a `Nat → Nat → Rat`, so
    /// `matMul (matMul A B k) C m` is well-typed with no coercion. Every
    /// theorem about it is stated POINTWISE (`… i j = … i j`): `funext` is
    /// absent from this kernel, so an `Eq` between two matrices is not
    /// available (`rat_prelude::matrix_n`'s module doc).
    pub mat_mul: NameId,
    /// `Rat.matMul_zero : ∀ A B i j, matMul A B zero i j = zero` — `Eq.refl`.
    pub mat_mul_zero: NameId,
    /// `Rat.matMul_succ : ∀ A B k i j, matMul A B (succ k) i j = matMul A B k
    /// i j + A i k * B k j` — `Eq.refl`.
    pub mat_mul_succ: NameId,
    /// `Rat.matMul_assoc : ∀ A B C k m i j, matMul (matMul A B k) C m i j =
    /// matMul A (matMul B C m) k i j` — associativity of matrix
    /// multiplication at symbolic inner dimensions `k` and `m`, stated
    /// pointwise. Proved from [`Self::sum_range_swap`] (the Fubini
    /// interchange) plus [`Self::mul_sum_range`] and `mul_assoc`; **no new
    /// induction** on any dimension.
    pub mat_mul_assoc: NameId,
    /// `Rat.matMul_add_left : ∀ A1 A2 B k i j, matMul (fun r t => A1 r t + A2
    /// r t) B k i j = matMul A1 B k i j + matMul A2 B k i j`.
    pub mat_mul_add_left: NameId,
    /// `Rat.matMul_add_right : ∀ A B1 B2 k i j, matMul A (fun t r => B1 t r +
    /// B2 t r) k i j = matMul A B1 k i j + matMul A B2 k i j`.
    pub mat_mul_add_right: NameId,
    /// `Rat.matMul_smul_left : ∀ c A B k i j, matMul (fun r t => c * A r t) B
    /// k i j = c * matMul A B k i j`.
    pub mat_mul_smul_left: NameId,
    /// `Rat.sumRange_delta : ∀ f i n, (∀ t, Not (Eq Nat t i) → f t = zero) →
    /// Lt i n → sumRange f n = f i` — a sum whose summand vanishes away from
    /// one index collapses to the value at that index. The hypothesis is
    /// UNRESTRICTED (`∀ t`, not `∀ t, Lt t n →`) because its only consumers,
    /// the two [`Self::mat_id`] unit laws, have a summand that vanishes off
    /// the diagonal at every index whatsoever.
    pub sum_range_delta: NameId,
    /// `Rat.matId : Nat → Nat → Rat := fun i j => if Nat.beq i j then one
    /// else zero` — the identity matrix, at every dimension at once. It
    /// carries no dimension argument; the bound enters only as the `Lt i n`
    /// hypothesis of [`Self::mat_mul_id_left`]/[`Self::mat_mul_id_right`].
    pub mat_id: NameId,
    /// `Rat.matId_diag : ∀ i, matId i i = one`.
    pub mat_id_diag: NameId,
    /// `Rat.matId_off_diag : ∀ i j, Not (Eq Nat i j) → matId i j = zero`.
    pub mat_id_off_diag: NameId,
    /// `Rat.matMul_id_left : ∀ A n i j, Lt i n → matMul matId A n i j = A i
    /// j`. The `Lt i n` hypothesis is load-bearing: outside the summation
    /// range the delta never fires and the product is zero, not `A i j`.
    pub mat_mul_id_left: NameId,
    /// `Rat.matMul_id_right : ∀ A n i j, Lt j n → matMul A matId n i j = A i
    /// j`.
    pub mat_mul_id_right: NameId,

    // --- matrix transpose at symbolic dimension (rat_prelude::matrix_transpose) --
    /// `Rat.matTranspose : (Nat → Nat → Rat) → Nat → Nat → Rat := fun A i j
    /// => A j i` — the transpose, at every dimension at once (no bound
    /// argument, matching [`Self::mat_id`]'s shape).
    pub mat_transpose: NameId,
    /// `Rat.matTranspose_transpose : ∀ A i j, matTranspose (matTranspose A)
    /// i j = A i j` — the involution law, `Eq.refl`.
    pub mat_transpose_transpose: NameId,
    /// `Rat.matTranspose_mul : ∀ A B k i j, matTranspose (matMul A B k) i j
    /// = matMul (matTranspose B) (matTranspose A) k i j` — `(AB)^T = B^T
    /// A^T`, stated pointwise at symbolic dimension `k`. Row 1 of the graded
    /// family (`rat_prelude::matrix_transpose`'s module doc); row 2 does not
    /// apply (ADR-0716, argued from the statement's shape: no comparison, no
    /// search). Proved from [`Self::sum_range_congr`] and [`Self::mul_comm`]
    /// alone — no new induction.
    pub mat_transpose_mul: NameId,
    /// `Rat.matTranspose_eval_example : matTranspose [[2,3],[5,7]] 0 1 =
    /// ofInt 5` — the discriminating concrete evaluation test
    /// [`Self::mat_transpose`]'s new `Definition` needs (the kernel cannot
    /// tell a `Definition` is wrong from its type alone).
    pub mat_transpose_eval_example: NameId,
    /// `Rat.matTranspose_mul_example : matTranspose (matMul [[2,3],[5,7]]
    /// [[11,13],[17,19]] 2) 0 1 = ofInt 174` — row 3 of the graded family,
    /// [`Self::mat_transpose_mul`] itself applied at a concrete instance
    /// rather than a separate producer/verifier pair (ADR-0825's collapse).
    pub mat_transpose_mul_example: NameId,

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
    /// `Rat.covariance_comm : ∀ X Y p n, covariance X Y p n = covariance Y X p
    /// n` — `Cov[X,Y] = Cov[Y,X]`. Purely equational from `mul_comm` on the
    /// `E[X·Y]` term and on the `E[X]·E[Y]` term, **no `IsDistribution`
    /// hypothesis** — matching [`Self::covariance_add_right`]'s own
    /// unconditional form, and the lemma
    /// [`Self::covariance_sum_vars_left`] uses (twice, per step) to move
    /// [`Self::covariance_add_right`]'s bilinearity from `covariance`'s
    /// second argument to its first.
    pub covariance_comm: NameId,
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
    /// `Rat.variance_indicator : ∀ a X p n, IsDistribution p n →
    /// variance (Rat.indicator a X) p n =
    /// mul (expectation (Rat.indicator a X) p n)
    ///     (sub Rat.one (expectation (Rat.indicator a X) p n))` — the
    /// Bernoulli variable's variance, `p·(1−p)` where `p := E[𝟙[a≤X]]`.
    pub variance_indicator: NameId,
    /// `Rat.variance_indicator_le_quarter : ∀ q,
    /// le (sub (mul four q) (mul four (mul q q))) one` — `4q − 4q² ≤ 1`, i.e.
    /// `q(1−q) ≤ 1/4` with the division cleared (the same "no `Rat.inv`"
    /// choice [`Self::markov_inequality`] makes), where `four :=
    /// ((1+1)+1)+1`. Elementary, via the nonneg-square identity `0 ≤
    /// (2q−1)²`, no case split.
    pub variance_indicator_le_quarter: NameId,
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
    /// `Rat.covariance_smul_left : ∀ a X Y p n,
    /// covariance (fun k => a * X k) Y p n = a * covariance X Y p n` —
    /// bilinearity (the scalar half) of covariance in its FIRST argument.
    /// Purely algebraic, no `IsDistribution` hypothesis needed (matching
    /// [`Self::covariance_add_right`]'s own unconditional form):
    /// `Cov[aX,Y] = E[(aX)Y] − E[aX]E[Y] = a·E[XY] − a·(E[X]E[Y]) =
    /// a·Cov[X,Y]`, via [`Self::mul_assoc`] on the summand
    /// (`(a·Xk)·Yk = a·(Xk·Yk)`), [`Self::expectation_smul`] to pull `a`
    /// through both expectations, and the same `mul_sub_via_comm`
    /// (`rat_prelude::probability`, private) [`Self::variance_smul`] uses to
    /// pull `a` out of the resulting difference. The other building block
    /// [`Self::covariance_sq_le_variance_mul`]'s discriminant argument needs
    /// (`Var[tX]` already has one, via [`Self::variance_smul`]).
    pub covariance_smul_left: NameId,
    /// `Rat.covariance_sq_le_variance_mul : ∀ X Y p n, IsDistribution p n →
    /// (covariance X Y p n) * (covariance X Y p n) ≤
    /// (variance X p n) * (variance Y p n)` — the **probabilistic
    /// Cauchy–Schwarz inequality**, `cov(X,Y)² ≤ var(X)·var(Y)`, in SQUARED
    /// form (no square root — `ℚ` has none, the same limit
    /// `creal_point.rs`'s own `cauchy_schwarz` records). Proved by the
    /// discriminant argument: `Var[tX+Y] ≥ 0` for every rational `t`
    /// ([`Self::variance_nonneg`] plus [`Self::variance_add_eq`],
    /// [`Self::variance_smul`], [`Self::covariance_smul_left`]), a genuine
    /// case split on `variance X p n` and (nested, only when it vanishes) on
    /// `variance Y p n` via [`Self::lt_trichotomy`]: `0 < variance X p n`
    /// instantiates `t := −cov·inv(var X)`; `variance X p n = 0 ∧ 0 <
    /// variance Y p n` swaps roles (`Var[sY+X] ≥ 0`, `s := −cov·inv(var
    /// Y)`); `variance X p n = 0 ∧ variance Y p n = 0` needs no inverse at
    /// all — `t := one` and `t := neg one` pin `cov+cov = zero` directly,
    /// closed by the same "one term ≤ a nonneg sum" bound
    /// `rat_prelude::probability::term_le_sum_range` uses, applied to
    /// `add_sq_expand cov cov`.
    pub covariance_sq_le_variance_mul: NameId,
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
    /// `Rat.covariance_sumVars_left : ∀ X Y p n m,
    /// covariance (sumVars X m) Y p n = sumRange (fun j => covariance (X j) Y
    /// p n) m` — bilinearity of covariance over a FAMILY of variables in its
    /// FIRST argument, by induction on `m` mirroring
    /// [`Self::expectation_sum_vars`]'s own: the base case needs no
    /// `IsDistribution` either (`Cov[0,Y] = 0` unconditionally, via
    /// [`Self::expectation_smul`] at the zero scalar); the successor step
    /// moves [`Self::covariance_add_right`]'s bilinearity from `covariance`'s
    /// second argument to its first via [`Self::covariance_comm`] (twice).
    /// **The prerequisite the finite weak law of large numbers has been
    /// missing**: `Var[Σ_j X_j] = Σ_j Var[X_j]` under pairwise
    /// uncorrelatedness needs `Cov[Σ_j X_j, Y]` reduced to a sum first.
    pub covariance_sum_vars_left: NameId,
    /// `Rat.covariance_sumVars : ∀ X Y p n m m',
    /// covariance (sumVars X m) (sumVars Y m') p n =
    /// sumRange (fun i => sumRange (fun j => covariance (X i) (Y j) p n) m') m`
    /// — bilinearity of covariance over TWO families at once: `Cov[Σᵢ Xᵢ, Σⱼ
    /// Yⱼ] = Σᵢ Σⱼ Cov[Xᵢ, Yⱼ]`. Not a new induction: instantiate
    /// [`Self::covariance_sum_vars_left`] once at `Y := sumVars Y' m'` to
    /// reduce the first family, then again (roles reversed, via
    /// [`Self::covariance_comm`]) inside each term to reduce the second — see
    /// `rat_prelude::probability::declare_covariance_sum_vars`'s own doc for
    /// why `Rat.sumRange_swap` (the Fubini swap) is NOT needed here: the
    /// derivation already produces the `Σᵢ Σⱼ` order directly.
    pub covariance_sum_vars: NameId,
    /// `Rat.PairwiseUncorrelated X m p n := ∀ i j, Lt i m → Lt j m → Not (Eq
    /// i j) → covariance (X i) (X j) p n = zero` — **the honest, strictly
    /// weaker hypothesis in place of independence, now over a whole
    /// FAMILY**: a JOINT distribution over a product space is not
    /// expressible in this development (see [`Self::covariance`]'s own
    /// doc), only `Cov ~ 0` for every pair.
    pub pairwise_uncorrelated: NameId,
    /// `Rat.variance_sumVars : ∀ X p n, IsDistribution p n → ∀ m,
    /// PairwiseUncorrelated X m p n → variance (sumVars X m) p n =
    /// sumRange (fun j => variance (X j) p n) m` — **the headline**:
    /// `Var[Σ_{j<m} X_j] = Σ_{j<m} Var[X_j]` under pairwise
    /// uncorrelatedness, by induction on `m` from
    /// [`Self::variance_add_of_uncorrelated`] (the two-variable step),
    /// [`Self::covariance_sum_vars_left`] (reducing the needed cross term to
    /// a sum of covariances) and [`Self::sum_range_eq_zero_of_lt`]
    /// (collapsing that sum to zero from `PairwiseUncorrelated`'s own
    /// bounded zero facts).
    pub variance_sum_vars: NameId,
    /// `Rat.variance_scaled_mean : ∀ X p n m, IsDistribution p n →
    /// variance (fun k => inv (natDivSucc m 0) * X k) p n = (inv
    /// (natDivSucc m 0) * inv (natDivSucc m 0)) * variance X p n` —
    /// `Var[a·X] = a²·Var[X]` specialised at the sample-mean scalar `a :=
    /// 1/m`, a direct corollary of [`Self::variance_smul`] (`Rat.inv` is
    /// TOTAL, so this needs no `m ≠ 0` side condition).
    pub variance_scaled_mean: NameId,
    /// `Rat.chebyshev_sampleMean_uncorrelated : ∀ X eps p n m,
    /// IsDistribution p n → PairwiseUncorrelated X m p n → lt zero eps → le
    /// ((eps times eps) times expectation (indicator (eps times eps) (fun k
    /// => (Y k minus expectation Y p n) times (Y k minus expectation Y p
    /// n))) p n) ((a times a) times sumRange (fun j => variance (X j) p n)
    /// m)`, where `Y := fun k => a times sumVars X m k`, `a := inv
    /// (natDivSucc m 0)` —
    /// [`Self::chebyshev_inequality`] applied to the sample mean of `m`
    /// pairwise-uncorrelated variables, composing
    /// [`Self::variance_scaled_mean`] and [`Self::variance_sum_vars`]. NOT
    /// the classical `P(|X̄ − μ| ≥ ε) ≤ Var/(mε²)`, which needs identically
    /// distributed variables this development never assumes — the sum
    /// `Σ_{j<m} Var[X_j]` is left as-is.
    pub chebyshev_sample_mean_uncorrelated: NameId,
    /// `Rat.variance_sampleMean_uncorrelated : ∀ X p n, IsDistribution p n →
    /// ∀ m, PairwiseUncorrelated X m p n → variance (fun k => inv
    /// (natDivSucc m 0) * sumVars X m k) p n = (inv (natDivSucc m 0) * inv
    /// (natDivSucc m 0)) * sumRange (fun j => variance (X j) p n) m` — the
    /// QUANTITATIVE HEART of the weak law of large numbers, named on its
    /// own: `Var[sample mean] = (1/m)² · Σ_{j<m} Var[X_j]`. Composes
    /// [`Self::variance_scaled_mean`] and [`Self::variance_sum_vars`] —
    /// exactly the `combined_eq` step
    /// [`Self::chebyshev_sample_mean_uncorrelated`] already builds
    /// internally, now exposed standalone rather than buried inside the
    /// larger Chebyshev bound. [`Self::variance_sum_vars`] alone does NOT
    /// give this: it is the variance of the unscaled SUM, not of the mean.
    pub variance_sample_mean_uncorrelated: NameId,
    /// `Rat.weak_law_of_large_numbers` — a RENAMING, not a new result: the
    /// type is identical to
    /// [`Self::chebyshev_sample_mean_uncorrelated`]'s, registered under the
    /// name a reader searching for "the weak law of large numbers" will
    /// look for, with a proof that forwards directly to that theorem. This
    /// IS the weak law of large numbers in its standard finite-sample
    /// Chebyshev-bound shape: `ε²·E[𝟙(ε² ≤ (M−E[M])²)] ≤ Var[M]`, where `M`
    /// is the sample mean of `m` pairwise-uncorrelated variables and `Var[M]
    /// = (1/m)²·Σ_{j<m} Var[X_j]` shrinks as `m` grows whenever the
    /// individual variances stay bounded — stated at each finite `m` rather
    /// than as a limit. NOT the classical i.i.d. form (`Σ_{j<m} Var[X_j]`
    /// is left unsummed, a strictly more general hypothesis than a common
    /// variance `σ²`).
    pub weak_law_of_large_numbers: NameId,
    /// `Rat.bernoulli_law_of_large_numbers : ∀ A Y p n m q, IsDistribution p n
    /// → PairwiseUncorrelated (fun j => indicator (A j) (Y j)) m p n → (∀ j,
    /// Lt j m → expectation (indicator (A j) (Y j)) p n = q) → ∀ eps, lt zero
    /// eps → le (four * (eps*eps * expectation (indicator (eps*eps) devM) p
    /// n)) ((inv (natDivSucc m 0) * inv (natDivSucc m 0)) * natDivSucc m 0)`
    /// — Bernoulli's law of large numbers, assembled from
    /// [`Self::weak_law_of_large_numbers`] (the general theorem),
    /// [`Self::variance_indicator`] (each variable's variance is `q(1-q)`)
    /// and [`Self::variance_indicator_le_quarter`] (`4q(1-q) ≤ 1`). The
    /// right side is `(1/m)·1`, i.e. `1/m`, once `m > 0`; left unsimplified
    /// here to avoid a second `Rat.inv` identity this slice does not need.
    pub bernoulli_law_of_large_numbers: NameId,

    // --- the probabilistic Cauchy–Schwarz inequality (rat_prelude::probability) --
    /// `Rat.variance_scaled_add_nonneg : ∀ X Y p n, IsDistribution p n → ∀ t,
    /// le zero (add (mul (mul t t) (variance X p n)) (add (mul t
    /// (covariance X Y p n)) (add (mul t (covariance X Y p n)) (variance Y p
    /// n))))` — `Var[tX+Y] ≥ 0`, fully expanded into a quadratic in `t`, for
    /// every rational `t`. The discriminant fact
    /// [`Self::covariance_sq_le_variance_mul`] rests on, named once so both
    /// the direct case (instantiate at `X,Y`) and the role-swapped case
    /// (instantiate at `Y,X`, via [`Self::covariance_comm`]) reuse it.
    pub variance_scaled_add_nonneg: NameId,
    /// `Rat.covariance_sq_le_variance_mul_of_pos : ∀ X Y p n, IsDistribution
    /// p n → lt zero (variance X p n) → le (mul (covariance X Y p n)
    /// (covariance X Y p n)) (mul (variance X p n) (variance Y p n))` — the
    /// probabilistic Cauchy–Schwarz inequality, `cov(X,Y)² ≤ var(X)·var(Y)`,
    /// closed for the case `variance X p n ≠ 0` (in fact `> 0`, from
    /// [`Self::variance_nonneg`]). The discriminant argument: instantiate
    /// [`Self::variance_scaled_add_nonneg`] at `t := neg (covariance X Y p
    /// n) * inv (variance X p n)`, which makes `variance X p n * t = neg
    /// (covariance X Y p n)` (via [`Self::mul_inv_cancel_of_ne_zero`]) and
    /// collapses the quadratic to `0 ≤ variance Y p n − (covariance X Y p
    /// n)² · inv (variance X p n)`; multiplying through by `variance X p n`
    /// closes it. [`Self::covariance_sq_le_variance_mul`] still needs the
    /// symmetric case (`variance X p n = 0`) — see its own doc.
    pub covariance_sq_le_variance_mul_of_pos: NameId,
    /// `Rat.covariance_sq_le_variance_mul_of_zero_zero : ∀ X Y p n,
    /// IsDistribution p n → variance X p n = zero → variance Y p n = zero →
    /// le (mul (covariance X Y p n) (covariance X Y p n)) (mul (variance X
    /// p n) (variance Y p n))` — the probabilistic Cauchy–Schwarz
    /// inequality, closed for the case BOTH variances vanish. No inverse
    /// needed: [`Self::variance_scaled_add_nonneg`] at `t := one` and `t :=
    /// neg one` pin `covariance X Y p n + covariance X Y p n = zero`
    /// directly (`le_antisymm`); squaring and expanding via `add_sq_expand`
    /// gives `4·(covariance X Y p n)² = zero` as a nested sum, and the same
    /// "one term ≤ a nonneg sum" bound
    /// `rat_prelude::probability::term_le_sum_range` uses reads
    /// `(covariance X Y p n)² ≤ zero` off it.
    pub covariance_sq_le_variance_mul_of_zero_zero: NameId,

    // --- 2x2 linear algebra --------------------------------------------------
    /// `Rat.det2 : Rat → Rat → Rat → Rat → Rat`, `det2 a b c d := a·d − b·c`.
    /// The one new **definition** the `matrix` module adds; every other name in
    /// this section is a theorem about it.
    pub det2: NameId,
    /// `Rat.det2_swap_rows : ∀ a b c d, det2 c d a b = neg (det2 a b c d)`.
    pub det2_swap_rows: NameId,
    /// `Rat.det2_id : det2 1 0 0 1 = 1`.
    pub det2_id: NameId,
    /// `Rat.det2_scale_row : ∀ k a b c d, det2 (k·a) (k·b) c d = k · det2 a b c d`.
    pub det2_scale_row: NameId,
    /// `Rat.det2_row_add : ∀ a b c d k, det2 (a + k·c) (b + k·d) c d = det2 a b c d`
    /// — adding a multiple of row 2 to row 1 leaves the determinant fixed, the
    /// fact that makes Gaussian elimination sound.
    pub det2_row_add: NameId,
    /// `Rat.det2_mul : ∀ a b c d e f g h,`
    /// `det2 (a·e+b·g) (a·f+b·h) (c·e+d·g) (c·f+d·h) = det2 a b c d · det2 e f g h`
    /// — multiplicativity of the 2×2 determinant.
    pub det2_mul: NameId,
    /// `Rat.det2_eq_zero_of_lin_dep : ∀ a b c d s t,`
    /// `Or (Not (s = 0)) (Not (t = 0)) → s·a+t·c = 0 → s·b+t·d = 0 →`
    /// `det2 a b c d = 0`.
    ///
    /// The **easy direction** of "`det2 = 0` iff the rows are linearly
    /// dependent" — the first statement in this kernel about linear
    /// dependence rather than about solving. Stated with an explicit
    /// nontriviality disjunction rather than `∃ t, c = t·a ∧ d = t·b`,
    /// because that existential form is **false** at `a = b = 0` with
    /// `(c,d)` nonzero (no `t` scales `(0,0)` to a nonzero row) even though
    /// `det2` is then always `0`; the `s,t` form here has no such gap. The
    /// converse — `det2 = 0` implies such a combination exists — is not yet
    /// proved.
    pub det2_eq_zero_of_lin_dep: NameId,
    /// `Rat.mul_adj2_top_left : ∀ a b c d, a·d + b·(−c) = det2 a b c d` — the
    /// (1,1) entry of `A · adj(A) = det(A) · I`. `adj2` itself is not a kernel
    /// constant (a function returning four rationals needs a product type the
    /// kernel does not have), so the adjugate's entries `d, −b, −c, a` are
    /// written out directly in each of the four `mul_adj2_*` theorems.
    pub mul_adj2_top_left: NameId,
    /// `Rat.mul_adj2_top_right : ∀ a b c d, a·(−b) + b·a = 0` — the (1,2)
    /// entry.
    pub mul_adj2_top_right: NameId,
    /// `Rat.mul_adj2_bottom_left : ∀ a b c d, c·d + d·(−c) = 0` — the (2,1)
    /// entry.
    pub mul_adj2_bottom_left: NameId,
    /// `Rat.mul_adj2_bottom_right : ∀ a b c d, c·(−b) + d·a = det2 a b c d` —
    /// the (2,2) entry.
    pub mul_adj2_bottom_right: NameId,
    /// `Rat.inv2_top_left : ∀ a b c d, Not (det2 a b c d = 0) →`
    /// `(invD*d)*a + (invD*(-b))*c = 1`, `invD := Rat.inv (det2 a b c d)` —
    /// the (1,1) entry of `A⁻¹·A = I`.
    pub inv2_top_left: NameId,
    /// `Rat.inv2_top_right : ∀ a b c d, Not (det2 a b c d = 0) →`
    /// `(invD*d)*b + (invD*(-b))*d = 0` — the (1,2) entry of `A⁻¹·A = I`.
    pub inv2_top_right: NameId,
    /// `Rat.inv2_bottom_left : ∀ a b c d, Not (det2 a b c d = 0) →`
    /// `(invD*(-c))*a + (invD*a)*c = 0` — the (2,1) entry of `A⁻¹·A = I`.
    pub inv2_bottom_left: NameId,
    /// `Rat.inv2_bottom_right : ∀ a b c d, Not (det2 a b c d = 0) →`
    /// `(invD*(-c))*b + (invD*a)*d = 1` — the (2,2) entry of `A⁻¹·A = I`.
    pub inv2_bottom_right: NameId,
    /// `Rat.cramer_two_unique_x : ∀ a b c d x y u v,`
    /// `a*x+b*y=u → c*x+d*y=v → Not (det2 a b c d = 0) →`
    /// `x = Rat.div (det2 u b v d) (det2 a b c d)`.
    ///
    /// The **forward** direction of Cramer's rule for a 2×2 system: a
    /// solution must have this form. Existence is a different, unattempted
    /// argument, hence `_unique` rather than a bare `cramer_two_x`.
    pub cramer_two_unique_x: NameId,
    /// `Rat.cramer_two_unique_y : ∀ a b c d x y u v,`
    /// `a*x+b*y=u → c*x+d*y=v → Not (det2 a b c d = 0) →`
    /// `y = Rat.div (det2 a u c v) (det2 a b c d)` — the `y` companion of
    /// [`Self::cramer_two_unique_x`].
    pub cramer_two_unique_y: NameId,
    /// `Rat.cramer2_x : Rat → Rat → Rat → Rat → Rat → Rat → Rat`,
    /// `cramer2_x a b c d u v := Rat.div (det2 u b v d) (det2 a b c d)` — the
    /// Cramer solution **formula** for `x` (not a uniqueness statement about
    /// it, but the value itself). Defined unconditionally: `Rat.inv` is
    /// total, so no `D ≠ 0` hypothesis belongs on the value — only on
    /// theorems about it ([`Self::cramer2_solves`]).
    pub cramer2_x: NameId,
    /// `Rat.cramer2_y : Rat → Rat → Rat → Rat → Rat → Rat → Rat`,
    /// `cramer2_y a b c d u v := Rat.div (det2 a u c v) (det2 a b c d)` — the
    /// `y` companion of [`Self::cramer2_x`].
    pub cramer2_y: NameId,
    /// `Rat.cramer2_solves : ∀ a b c d u v, Not (det2 a b c d = 0) →`
    /// `a*(cramer2_x a b c d u v) + b*(cramer2_y a b c d u v) = u ∧`
    /// `c*(cramer2_x a b c d u v) + d*(cramer2_y a b c d u v) = v`.
    ///
    /// The **substitution** direction of Cramer's rule: the formulas actually
    /// solve the system. [`Self::cramer_two_unique_x`]/
    /// [`Self::cramer_two_unique_y`] are the converse (a solution, if one
    /// exists, must equal them) — uniqueness and existence are different
    /// theorems, and this kernel now has both.
    pub cramer2_solves: NameId,

    // --- the ℤ→ℚ cast, and Cassini read through `det2` (matrix.rs) ----------
    /// `Rat.ofInt : Int → Rat`, `ofInt x := Rat.mk x 1 pos red` — the
    /// canonical embedding of `ℤ` into `ℚ` at denominator `1`. `pos : 1 ≤ 1`
    /// does not depend on `x`; `red` is `Rat.gcd_one_right` at `natAbs x`, so
    /// no case split on `x` is needed (unlike `Rat.normalize`/`Rat.inv`).
    pub of_int: NameId,
    /// `Rat.ofInt_add : ∀ x y : Int, ofInt (x+y) = ofInt x + ofInt y` — `ofInt`
    /// is a ring homomorphism for `+`. Not definitional: `Rat.add` renormalises
    /// through `Rat.normalize`, so this goes through `Rat.add_cross` and
    /// `Rat.eq_of_cross`.
    pub of_int_add: NameId,
    /// `Rat.ofInt_mul : ∀ x y : Int, ofInt (x·y) = ofInt x · ofInt y` — the
    /// multiplicative companion of [`Self::of_int_add`], via `Rat.mul_cross`.
    pub of_int_mul: NameId,
    /// `Rat.ofInt_neg : ∀ x : Int, ofInt (neg x) = neg (ofInt x)` — **free**,
    /// unlike `add`/`mul`: `Rat.neg` does not renormalise, so both sides
    /// `δ`/`ι`-reduce to the same `Rat.mk` application up to the kernel's
    /// definitional proof irrelevance on the two `Prop`-typed fields.
    pub of_int_neg: NameId,
    /// `Rat.det2_fib : ∀ n,`
    /// `det2 (ofInt (ofNat (fib (n+2)))) (ofInt (ofNat (fib (n+1))))`
    /// `     (ofInt (ofNat (fib (n+1)))) (ofInt (ofNat (fib n)))`
    /// `= ofInt (pow (neg one) (succ n))`.
    ///
    /// Cassini's identity read through `det2`: for `M = [[1,1],[1,0]]`,
    /// `Mⁿ = [[fib(n+1), fib n],[fib n, fib(n-1)]]` and `det M = -1`, so
    /// `det (Mⁿ) = (-1)ⁿ` expands to exactly this. **Derived from
    /// `Int.fib_cassini`** by transporting it across `Rat.ofInt` and rewriting
    /// with [`Self::of_int_add`]/[`Self::of_int_mul`]/[`Self::of_int_neg`] —
    /// not reproved independently.
    pub det2_fib: NameId,

    // --- the 3×3 determinant (matrix.rs) ------------------------------------
    /// `Rat.det3 a b c d e f g h i :=`
    /// `(a*(e*i - f*h) - b*(d*i - f*g)) + c*(d*h - e*g)` — the determinant of
    /// `[[a,b,c],[d,e,f],[g,h,i]]`, cofactor-expanded along row 1. Nine
    /// explicit scalar arguments, matching [`Self::det2`]'s convention: no
    /// matrix carrier.
    pub det3: NameId,
    /// `Rat.det3_id : det3 1 0 0 0 1 0 0 0 1 = 1` — the 3×3 identity matrix
    /// has determinant 1.
    pub det3_id: NameId,
    /// `Rat.det3_cofactor_row1 : ∀ a b c d e f g h i,`
    /// `det3 a b c d e f g h i = (a * det2 e f h i - b * det2 d f g i) + c * det2 d e g h`
    /// — cofactor expansion along the first row, in terms of [`Self::det2`]
    /// applied to the three 2×2 minors.
    pub det3_cofactor_row1: NameId,
    /// `Rat.det3_scale_row : ∀ k a b c d e f g h i,`
    /// `det3 (k*a) (k*b) (k*c) d e f g h i = k * det3 a b c d e f g h i` —
    /// scaling row 1 scales the determinant. Rows 2/3 are not stated (`matrix.rs`'s
    /// `declare_det3_scale_row` doc comment explains why: the scale factor
    /// lands inside two of the three minors instead of outside all three
    /// uniformly), matching [`Self::det2_scale_row`]'s own row-1-only
    /// precedent.
    pub det3_scale_row: NameId,
    /// `Rat.det3_ofInt : ∀ a b c d e f g h i : Int,`
    /// `det3 (ofInt a) … (ofInt i) = ofInt ((a*(e*i-f*h) - b*(d*i-f*g)) + c*(d*h-e*g))`
    /// — the bridge a concrete `det3` example uses to push its arithmetic
    /// down to `Int`, which computes at concrete literals for free.
    pub det3_ofint: NameId,
    /// `Rat.det3_example_generic : det3 (ofInt 1) … (ofInt 10) = ofInt (-3)`
    /// — the determinant of `[[1,2,3],[4,5,6],[7,8,10]]`.
    pub det3_example_generic: NameId,
    /// `Rat.det3_example_diagonal : det3 (ofInt 2) (ofInt 0) … (ofInt 4) = ofInt 24`
    /// — the determinant of `diag(2,3,4)`.
    pub det3_example_diagonal: NameId,
    /// `Rat.det3_example_singular : det3 (ofInt 1) … (ofInt 9) = ofInt 0` —
    /// the determinant of `[[1,2,3],[4,5,6],[7,8,9]]`.
    pub det3_example_singular: NameId,

    // --- both-sided 2×2 invertibility, bridged into the general `matMul`/
    // `matId` pointwise encoding (`matrix_invertible.rs`) --------------------
    /// `Rat.matInv2 : (Nat → Nat → Rat) → Nat → Nat → Rat`,
    /// `matInv2 A i j := invD * (adjugate entry)`, `invD := Rat.inv (det2 (A
    /// 0 0) (A 0 1) (A 1 0) (A 1 1))` — the adjugate-based 2×2 inverse taking
    /// a GENERAL matrix `A` in `matrix_n`'s `Nat → Nat → Rat`
    /// encoding, not four separate scalars the way [`Self::det2`]/
    /// [`Self::inv2_top_left`] do. Bridges the fixed-size `det2`/`inv2`
    /// family into the symbolic-dimension `matMul`/`matId` family.
    pub mat_inv2: NameId,
    /// `Rat.matMul_matInv2_top_left : ∀ A, Not (det2 (A 0 0) (A 0 1) (A 1 0)
    /// (A 1 1) = 0) → matMul A (matInv2 A) 2 0 0 = matId 0 0` — the `(0,0)`
    /// entry of `A · A⁻¹ = I`, stated through the general `matMul`/`matId`
    /// encoding rather than raw scalars.
    pub matmul_matinv2_top_left: NameId,
    /// `Rat.matMul_matInv2_top_right : … matMul A (matInv2 A) 2 0 1 = matId
    /// 0 1` — the `(0,1)` entry of `A · A⁻¹ = I`.
    pub matmul_matinv2_top_right: NameId,
    /// `Rat.matMul_matInv2_bottom_left : … matMul A (matInv2 A) 2 1 0 = matId
    /// 1 0` — the `(1,0)` entry of `A · A⁻¹ = I`.
    pub matmul_matinv2_bottom_left: NameId,
    /// `Rat.matMul_matInv2_bottom_right : … matMul A (matInv2 A) 2 1 1 =
    /// matId 1 1` — the `(1,1)` entry of `A · A⁻¹ = I`.
    pub matmul_matinv2_bottom_right: NameId,
    /// `Rat.matInv2_matMul_top_left : ∀ A, Not (det2 … = 0) → matMul
    /// (matInv2 A) A 2 0 0 = matId 0 0` — the `(0,0)` entry of `A⁻¹ · A = I`,
    /// stated through `matMul`/`matId`; term-for-term the same statement as
    /// [`Self::inv2_top_left`] once both sides are unfolded, so its proof is
    /// [`Self::inv2_top_left`] itself plus the `matMul`/`matId` defeq bridge.
    pub matinv2_matmul_top_left: NameId,
    /// `Rat.matInv2_matMul_top_right : … matMul (matInv2 A) A 2 0 1 = matId
    /// 0 1` — the `(0,1)` entry of `A⁻¹ · A = I`.
    pub matinv2_matmul_top_right: NameId,
    /// `Rat.matInv2_matMul_bottom_left : … matMul (matInv2 A) A 2 1 0 =
    /// matId 1 0` — the `(1,0)` entry of `A⁻¹ · A = I`.
    pub matinv2_matmul_bottom_left: NameId,
    /// `Rat.matInv2_matMul_bottom_right : … matMul (matInv2 A) A 2 1 1 =
    /// matId 1 1` — the `(1,1)` entry of `A⁻¹ · A = I`.
    pub matinv2_matmul_bottom_right: NameId,
    /// `Rat.matInv2_eval_example : matInv2 A 0 0 = ofInt (−7)`, for the
    /// concrete `A := [[2, 3], [5, 7]]` (`det = −1`) — the discriminating
    /// evaluation test [`Self::mat_inv2`]'s new `Definition` needs (Hard
    /// Rules: the kernel accepts a well-typed `Definition` regardless of
    /// whether it computes the intended value). Distinguishes the correct
    /// adjugate entry from a swapped or sign-dropped one.
    pub mat_inv2_eval_example: NameId,
    /// `Rat.matInv2_example : matMul A (matInv2 A) 2 0 0 = ofInt 1`, for the
    /// concrete `A := [[2, 1], [1, 1]]` (`det = 1`) — **row 3 of the graded
    /// family, the ADR-0825 collapse**: [`Self::matmul_matinv2_top_left`]
    /// itself, applied at this concrete matrix, with its conclusion (still
    /// in named-constant form) bridged to the plain numeral `ofInt 1` by the
    /// kernel's own delta/beta/iota computation.
    pub mat_inv2_example: NameId,

    // --- the determinant at general `n` (`rat_prelude::matrix_det`) ----------
    /// `Rat.matSkip : Nat → Nat → Nat`,
    /// `matSkip p x := if Nat.ble p x then Nat.succ x else x` — the
    /// order-preserving injection `[0,n) → [0,n+1)` whose image misses `p`,
    /// which is how [`Self::mat_minor`] deletes an index without a container
    /// type.
    pub mat_skip: NameId,
    /// `Rat.matMinor : (Nat → Nat → Rat) → Nat → Nat → Nat → Nat → Rat`,
    /// `matMinor A i j r c := A (matSkip i r) (matSkip j c)` — the submatrix
    /// with row `i` and column `j` deleted, as an index reindex. Applied
    /// (five arguments) rather than matrix-valued, because this kernel has no
    /// `funext`.
    pub mat_minor: NameId,
    /// `Rat.altSign : Nat → Rat`, `(-1)^j`, by `Nat.rec` so that both
    /// defining equations are `Eq.refl`.
    pub alt_sign: NameId,
    /// `Rat.altSign_zero : altSign 0 = 1` — `Eq.refl`.
    pub alt_sign_zero: NameId,
    /// `Rat.altSign_succ : ∀ j, altSign (succ j) = neg (altSign j)` —
    /// `Eq.refl`.
    pub alt_sign_succ: NameId,
    /// `Rat.det : (Nat → Nat → Rat) → Nat → Rat` — the determinant at
    /// **general `n`**, by cofactor expansion along the first row. The
    /// `Nat.rec` motive is the function type `(Nat → Nat → Rat) → Rat`,
    /// because the recursive call is at the minor rather than at the same
    /// matrix.
    pub det: NameId,
    /// `Rat.det_zero : ∀ A, det A 0 = 1` — `Eq.refl`.
    pub det_zero: NameId,
    /// `Rat.det_succ : ∀ A m, det A (succ m) = sumRange (fun j => altSign j *
    /// (A 0 j * det (matMinor A 0 j) m)) (succ m)` — `Eq.refl`.
    pub det_succ: NameId,
    /// `Rat.det_one : ∀ A, det A 1 = A 0 0`.
    pub det_one: NameId,
    /// `Rat.det_eq_det2 : ∀ A, det A 2 = det2 (A 0 0) (A 0 1) (A 1 0)
    /// (A 1 1)` — the general-`n` determinant agrees with the fixed 2×2 one,
    /// **symbolically** in the matrix. Since [`Self::det2`] was written
    /// independently, this is the strongest available check that the cofactor
    /// recursion means what it says.
    pub det_eq_det2: NameId,
    /// `Rat.det_eq_det3 : ∀ A, det A 3 = det3 (A 0 0) … (A 2 2)` — the same
    /// agreement one dimension up, where the sign pattern first has three
    /// terms and `altSign 2` must come back to `+1`.
    pub det_eq_det3: NameId,
    /// `Rat.matMinor_eval_example : matMinor A 0 1 1 0 = ofInt 7` for the
    /// non-symmetric `A := [[1,2,3],[4,5,6],[7,8,9]]` — the discriminating
    /// evaluation test the new `Definition` needs (Hard Rules: a well-typed
    /// `Definition` is admitted whatever it computes). A transposed index
    /// gives 3 and a shift on the wrong axis gives 8.
    pub mat_minor_eval_example: NameId,
    /// `Rat.det_eval_example : det A 3 = ofInt 13` for
    /// `A := [[1,2,0],[0,1,3],[2,0,1]]` — inverting the alternating sign
    /// gives −13, so this separates the sign convention.
    pub det_eval_example: NameId,
    /// `Rat.det_eval_singular : det A 3 = 0` for the singular, zero-free
    /// `A := [[1,2,1],[2,1,3],[3,3,4]]` (row 2 = row 0 + row 1).
    pub det_eval_singular: NameId,
    /// `Rat.det_eval_example4 : det A 4 = ofInt 2` — the first dimension
    /// neither [`Self::det2`] nor [`Self::det3`] can reach.
    pub det_eval_example4: NameId,

    // --- the determinant laws (`rat_prelude::matrix_det`, ADR-1135) ---------
    /// `Rat.sumRange_head_of_tail_zero : ∀ f n, (∀ k, f (succ k) = 0) →
    /// sumRange f (succ n) = f 0` — the first summand of a sum whose tail
    /// vanishes. [`Self::sum_range_succ`] peels from the RIGHT, so nothing
    /// else in this prelude hands you the value at index `0`.
    pub sum_range_head_of_tail_zero: NameId,
    /// `Rat.det_congr : ∀ n A B, (∀ r c, A r c = B r c) → det A n = det B n`
    /// — the determinant respects **pointwise** equality of matrices.
    ///
    /// The lemma the absence of `funext` forces. [`Self::det`]'s recursive
    /// call is at the minor, so any induction over the dimension arrives at a
    /// matrix that is only *pointwise* the one the induction hypothesis is
    /// about; with `funext` one would rewrite the matrix argument, and
    /// without it `det` needs its own congruence.
    pub det_congr: NameId,
    /// `Rat.matMinor_matId : ∀ r c, matMinor matId 0 0 r c = matId r c` — the
    /// identity's leading minor is the identity, at every index pair.
    /// `Eq.refl`, because `Nat.ble 0 r ≡ true` and
    /// `Nat.beq (succ r) (succ c) ≡ Nat.beq r c`.
    pub mat_minor_mat_id: NameId,
    /// `Rat.det_matId : ∀ n, det matId n = 1` — the determinant of the
    /// identity at a **symbolic** dimension, the first of the four laws
    /// ADR-1120 left open over [`Self::det`].
    pub det_mat_id: NameId,

    // --- the index layer of Laplace expansion (`matrix_det`, ADR-1155) ------
    /// `Rat.matSkip_zero : ∀ x, matSkip 0 x = succ x` — `Eq.refl`, because
    /// `Nat.ble zero x` iota-reduces to `true` for every `x` (`ble`'s zero row
    /// is the constant `true` function, with no inner recursion).
    pub mat_skip_zero: NameId,
    /// `Rat.matSkip_succ_succ : ∀ p x, matSkip (succ p) (succ x) =
    /// succ (matSkip p x)` — the shift commutes with `succ` on both indices.
    /// **Not** `Eq.refl`: `succ (bool_select_nat c a b)` and
    /// `bool_select_nat c (succ a) (succ b)` are stuck against each other for
    /// a symbolic condition, so this is a two-branch `Bool.rec`.
    pub mat_skip_succ_succ: NameId,
    /// `Rat.matSkip_comm : ∀ a b, Nat.ble a b = true → ∀ x,
    /// matSkip a (matSkip b x) = matSkip (succ b) (matSkip a x)` — deleting
    /// index `b` and then `a` hits the same pair as deleting `a` and then the
    /// shifted `succ b`, **when `a ≤ b`**. The hypothesis is not decoration:
    /// at `a = 1`, `b = 0`, `x = 0` the two sides are `2` and `0`.
    ///
    /// Stated with the BOOLEAN `Nat.ble a b = true` rather than `Nat.le a b`
    /// so the successor step can invert it by ι-reduction:
    /// `ble (succ a') zero ≡ false`, so `b = 0` is discharged by
    /// [`NatOps::false_true_elim`](crate::NatOps::false_true_elim), and `ble (succ a') (succ b') ≡ ble a' b'`
    /// hands the induction hypothesis its premise with no bridging lemma.
    pub mat_skip_comm: NameId,
    /// `Rat.matMinor_col_comm : ∀ A i j a b, Nat.ble a b = true → ∀ r c,
    /// matMinor (matMinor A i a) j b r c = matMinor (matMinor A i (succ b)) j a r c`
    /// — deleting columns `a` then `b` reaches the same submatrix as deleting
    /// `succ b` then `a`, POINTWISE. The row indices are the same on both
    /// sides deliberately: a cofactor expansion of a cofactor expansion
    /// deletes row `0` twice, so only the columns are exchanged.
    pub mat_minor_col_comm: NameId,
    /// `Rat.det_minor_col_comm : ∀ m A i j a b, Nat.ble a b = true →
    /// det (matMinor (matMinor A i a) j b) m =
    /// det (matMinor (matMinor A i (succ b)) j a) m` —
    /// [`Self::mat_minor_col_comm`] carried through [`Self::det_congr`],
    /// which is the only way a pointwise matrix identity reaches a `det` in
    /// this kernel (there is no `funext`).
    pub det_minor_col_comm: NameId,
    /// `Rat.sumRange_peel_head : ∀ f n, sumRange f (succ n) =
    /// add (f 0) (sumRange (fun k => f (succ k)) n)` — peel the FIRST summand.
    /// [`Self::sum_range_succ`] peels from the right, so every left-side
    /// reindexing over `Rat.sumRange` starts here.
    pub sum_range_peel_head: NameId,
    /// `Rat.sumRange_matSkip : ∀ n f j, Nat.ble j n = true →
    /// add (sumRange (fun k => f (matSkip j k)) n) (f j) = sumRange f (succ n)`
    /// — summing over `[0, n)` reindexed by the injection that misses `j`
    /// recovers the full sum over `[0, n+1)` once `f j` is added back.
    ///
    /// The **range half** of a Laplace expansion: it converts a cofactor
    /// sum over a range one short, reindexed by `matSkip`, into a sum over
    /// the full range, which is what makes the plain rectangle Fubini
    /// [`Self::sum_range_swap`] applicable to a double cofactor expansion.
    pub sum_range_mat_skip: NameId,

    // --- the summand layer of Laplace expansion (`matrix_det`, ADR-1185) ----
    /// `Rat.unskip : Nat → Nat → Nat` — the LEFT INVERSE of
    /// [`Self::mat_skip`]: `unskip p q` is `q`'s position in `[0, n+1) \ {p}`,
    /// so `unskip p (matSkip p k) = k` ([`Self::unskip_mat_skip`]).
    ///
    /// Declared as a DOUBLE `Nat.rec` (`unskip 0 q ≡ Nat.pred q`,
    /// `unskip (succ p) 0 ≡ 0`, `unskip (succ p) (succ q) ≡ succ (unskip p q)`)
    /// rather than as the closed form `if ble (succ p) q then pred q else q`,
    /// even though the two agree at every pair below 8 (checked in
    /// `adr-1185-laplace-summand-checks.py`). The reason is the one
    /// [`Self::mat_skip_succ_succ`] records from the other side: the closed
    /// form leaves a *stuck* `Nat.ble` guard that a `Bool.rec` case split
    /// cannot reach, because reducing `ble (succ p) (succ c)` re-creates the
    /// very scrutinee the split abstracted. All three rows of the recursive
    /// form hold by ι alone, so the index lemmas above it are plain
    /// inductions.
    pub unskip: NameId,
    /// `Rat.unskip_zero : ∀ q, unskip 0 q = Nat.pred q` — `Eq.refl`.
    pub unskip_zero: NameId,
    /// `Rat.unskip_succ_zero : ∀ p, unskip (succ p) 0 = 0` — `Eq.refl`.
    pub unskip_succ_zero: NameId,
    /// `Rat.unskip_succ_succ : ∀ p q, unskip (succ p) (succ q) =
    /// succ (unskip p q)` — `Eq.refl`.
    pub unskip_succ_succ: NameId,
    /// `Rat.unskip_matSkip : ∀ p k, unskip p (matSkip p k) = k` — `unskip p`
    /// is a left inverse of the injection `matSkip p`, UNCONDITIONALLY (no
    /// `ble` premise: `matSkip p` never produces `p`, so its image is exactly
    /// where `unskip p` is well behaved).
    ///
    /// The index lemma that lets the Laplace summand be defined on the whole
    /// square: the inner column of a double cofactor expansion is `k`, but the
    /// summand has to be a function of the two COLUMNS `(p, q)`, and
    /// `k = unskip p q` is how it recovers it.
    pub unskip_mat_skip: NameId,
    /// `Rat.beq_matSkip : ∀ j k, Nat.beq j (matSkip j k) = false` —
    /// `matSkip j` misses `j`. The guard side of
    /// [`Self::unskip_mat_skip`]: it is what makes the diagonal branch of the
    /// Laplace summand unreachable along the reindexing.
    pub beq_mat_skip: NameId,
    /// `Rat.beq_matSkip_left : ∀ j k, Nat.beq (matSkip j k) j = false` —
    /// [`Self::beq_mat_skip`] with the arguments the other way round. Stated
    /// separately rather than derived, because the two cofactor expansions
    /// reach the summand's guard from opposite sides and this prelude has no
    /// `Nat.beq` commutativity.
    pub beq_mat_skip_left: NameId,
    /// `Rat.altSign_succ_add : ∀ n k, altSign (Nat.add (succ n) k) =
    /// neg (altSign (Nat.add n k))` — the parity step of the summand's sign.
    ///
    /// `Nat.add` recurses on its RIGHT argument, so `add n (succ k)` reduces
    /// and `add (succ n) k` does NOT; this is the missing half, and it is one
    /// `Nat.succ_add` followed by [`Self::alt_sign_succ`] (itself `Eq.refl`).
    pub alt_sign_succ_add: NameId,
    /// `Rat.ble_flip_of_false : ∀ x y, Nat.ble (succ x) y = false →
    /// Nat.ble y x = true` — the ONE `Nat.ble` inversion this development
    /// needs and `nat_prelude/ble.rs` does not carry. Declared in the `Rat`
    /// namespace, alongside `Rat.matSkip`/[`Self::unskip`], rather than into
    /// `Nat` from here: a prelude declaring into another prelude's namespace
    /// is what made `Nat.inverseIndex` collide across two files.
    pub ble_flip_of_false: NameId,
    /// `Rat.unskip_le : ∀ p q, Nat.ble q p = true → unskip p q = q` — below
    /// the deleted index, `unskip` is the identity.
    pub unskip_le: NameId,
    /// `Rat.unskip_gt : ∀ p q, Nat.ble p q = true → unskip p (succ q) = q` —
    /// above it, `unskip` shifts down by one. Stated at `succ q` rather than
    /// as `unskip p q = Nat.pred q` deliberately: the `pred` form's successor
    /// step needs `succ (pred q') = q'`, which is a further inversion, while
    /// this form's is the induction hypothesis verbatim.
    pub unskip_gt: NameId,
    /// `Rat.matMinor_double_comm_lo : ∀ A i a b, Nat.ble a b = true → ∀ r c,
    /// matMinor (matMinor A 0 a) i b r c =
    /// matMinor (matMinor A (succ i) (succ b)) 0 a r c` — the DOUBLE minor
    /// exchange, moving the rows as well as the columns.
    ///
    /// [`Self::mat_minor_col_comm`] keeps the rows fixed, which is what a
    /// double expansion along one row needs. Relating the row-`0` expansion to
    /// the row-`i` expansion moves them: `(0, i)` becomes `(succ i, 0)`. The
    /// row half is [`Self::mat_skip_comm`] at `a = 0` (whose premise
    /// `ble 0 i = true` is `Eq.refl`), the column half is the same lemma at
    /// `(a, b)`.
    pub mat_minor_double_comm_lo: NameId,
    /// `Rat.matMinor_double_comm_hi : ∀ A i a b, Nat.ble a b = true → ∀ r c,
    /// matMinor (matMinor A 0 (succ b)) i a r c =
    /// matMinor (matMinor A (succ i) a) 0 b r c` —
    /// [`Self::mat_minor_double_comm_lo`]'s mirror, for the case where the
    /// row-`0` expansion took the LARGER of the two columns first.
    pub mat_minor_double_comm_hi: NameId,
    /// `Rat.det_double_comm_lo : ∀ m A i a b, Nat.ble a b = true →
    /// det (matMinor (matMinor A 0 a) i b) m =
    /// det (matMinor (matMinor A (succ i) (succ b)) 0 a) m` —
    /// [`Self::mat_minor_double_comm_lo`] through [`Self::det_congr`].
    pub det_double_comm_lo: NameId,
    /// `Rat.det_double_comm_hi : ∀ m A i a b, Nat.ble a b = true →
    /// det (matMinor (matMinor A 0 (succ b)) i a) m =
    /// det (matMinor (matMinor A (succ i) a) 0 b) m` —
    /// [`Self::mat_minor_double_comm_hi`] through [`Self::det_congr`].
    pub det_double_comm_hi: NameId,
    /// `Rat.mul_perm4 : ∀ x a y b d, x * (a * (y * (b * d))) =
    /// y * (b * (x * (a * d)))` — the one product permutation both halves of
    /// the summand identification need, factored out because it is the same
    /// permutation on both sides of the sign.
    pub mul_perm4: NameId,
    /// `Rat.laplaceSummand : (Nat → Nat → Rat) → Nat → Nat → Nat → Nat → Rat`
    /// — `laplaceSummand A i m p q`, the Laplace double-expansion summand,
    /// defined on the WHOLE square `[0, n) × [0, n)`:
    ///
    /// ```text
    /// laplaceSummand A i m p q :=
    ///   if Nat.beq p q then 0
    ///   else altSign p * (A 0 p * (altSign (unskip p q + i)
    ///          * (A (succ i) q * det (matMinor (matMinor A 0 p) i (unskip p q)) m)))
    /// ```
    ///
    /// `p` is the column the row-`0` expansion takes and `q` the column the
    /// row-`succ i` expansion takes. Neither cofactor sum defines a value on
    /// the diagonal — each runs over a range one short — and `0` is what makes
    /// the two ranges fillable to the full square by
    /// [`Self::sum_range_mat_skip`], after which the double sum is a plain
    /// rectangle and [`Self::sum_range_swap`] is the whole reindexing.
    ///
    /// The trusted gate cannot tell you this is the right function; the
    /// evidence is [`Self::laplace_summand_row_zero`] and
    /// [`Self::laplace_summand_row_i`], which say it agrees with each
    /// parametrisation's own summand, plus the concrete evaluation in
    /// `rat_prelude_tests`.
    pub laplace_summand: NameId,
    /// `Rat.laplaceSummand_rowZero : ∀ A i m p k,
    /// laplaceSummand A i m p (matSkip p k) = altSign p * (A 0 p *
    /// (altSign (k + i) * (A (succ i) (matSkip p k) *
    /// det (matMinor (matMinor A 0 p) i k) m)))` — the summand agrees with the
    /// row-`0`-then-row-`i` parametrisation. Two rewrites and no case split:
    /// [`Self::beq_mat_skip`] kills the guard and
    /// [`Self::unskip_mat_skip`] recovers the inner column.
    pub laplace_summand_row_zero: NameId,
    /// `Rat.laplaceSummand_rowI : ∀ A i m q k,
    /// laplaceSummand A i m (matSkip q k) q = altSign (q + succ i) *
    /// (A (succ i) q * (altSign k * (A 0 (matSkip q k) *
    /// det (matMinor (matMinor A (succ i) q) 0 k) m)))` — the summand agrees
    /// with the row-`i`-then-row-`0` parametrisation.
    ///
    /// **The bulk of ADR-1155's named remainder.** Unlike
    /// [`Self::laplace_summand_row_zero`] this needs a case split on
    /// `Nat.ble q k` — which of the two columns is the larger — because
    /// `unskip (matSkip q k) q` is `q` in one order and `Nat.pred q` in the
    /// other, and the two double minors are related by DIFFERENT orientations
    /// of [`Self::mat_skip_comm`].
    pub laplace_summand_row_i: NameId,
    /// `Rat.laplaceSummand_diag : ∀ A i m p, laplaceSummand A i m p p = 0` —
    /// the diagonal branch. What makes both cofactor ranges fillable to the
    /// full square by [`Self::sum_range_mat_skip`] at no cost.
    pub laplace_summand_diag: NameId,
    /// `Rat.det_row_expansion : ∀ m A i, Nat.ble i m = true →
    /// det A (succ m) = sumRange (fun q => altSign (q + i) *
    /// (A i q * det (matMinor A i q) m)) (succ m)` — **cofactor expansion
    /// along a GENERAL row**, the second of the four laws ADR-1120 named over
    /// [`Self::det`] and the one ADR-1135 left unsized.
    ///
    /// [`Self::det_succ`] is the `i = 0` case, definitionally: `Nat.add`
    /// recurses on its right argument, so `add q 0 ≡ q` and the two statements
    /// are the same term.
    ///
    /// ONE induction on the dimension, whose step case-splits on the row.
    /// **Not** the classical route** — no walk to the top by adjacent row
    /// swaps and so no row antisymmetry, which ADR-1155 measured to be off the
    /// critical path: the row-`0`-then-row-`i-1` double sum and the
    /// row-`i`-then-row-`0` double sum are indexed by the same ordered pairs
    /// of distinct columns and agree TERMWISE for every `i` at once. They are
    /// therefore the two orders of summation of ONE function on the square,
    /// [`Self::laplace_summand`], and [`Self::sum_range_swap`] is the whole
    /// reindexing step — no triangle decomposition, no `Nat.sub` in any
    /// summation bound, and no aggregate type this kernel lacks.
    pub det_row_expansion: NameId,

    // --- transpose invariance (`matrix_det`, ADR-1210) ----------------------
    /// `Rat.matMinor_row_col_comm : ∀ A p q r c,
    /// matMinor (matMinor A 0 (succ q)) p 0 r c =
    /// matMinor (matMinor A (succ p) 0) 0 q r c` — deleting row `0` then
    /// column `succ q`, then row `p` and column `0`, reaches the same
    /// submatrix as deleting row `succ p` then column `0`, then row `0` and
    /// column `q`. POINTWISE, and **unconditionally**: unlike
    /// [`Self::mat_minor_col_comm`] it carries no `Nat.ble` hypothesis,
    /// because the two exchanges happen on DIFFERENT axes and never have to
    /// be ordered against each other. It is [`Self::mat_skip_succ_succ`] on
    /// each axis and nothing else.
    pub mat_minor_row_col_comm: NameId,
    /// `Rat.det_minor_row_col_comm : ∀ m A p q,
    /// det (matMinor (matMinor A 0 (succ q)) p 0) m =
    /// det (matMinor (matMinor A (succ p) 0) 0 q) m` —
    /// [`Self::mat_minor_row_col_comm`] carried through [`Self::det_congr`],
    /// which is the only route a pointwise matrix identity has to a `det` in
    /// a kernel with no `funext`.
    pub det_minor_row_col_comm: NameId,
    /// `Rat.det_col_expansion : ∀ m A, det A (succ m) =
    /// sumRange (fun p => altSign p * (A p 0 * det (matMinor A p 0) m))
    /// (succ m)` — **cofactor expansion along the first COLUMN**.
    ///
    /// The crux of transpose invariance, and it does NOT follow from
    /// [`Self::det_row_expansion`]: each column summand is the `c = 0` slice
    /// of the row-`p` expansion, so the row law constrains each summand's
    /// SIBLINGS and never the column sum itself (ADR-1210 §9). One induction
    /// on the dimension. Both sides peel their head — and the two heads are
    /// the SAME term — leaving a double sum that agrees termwise after one
    /// [`Self::sum_range_swap`]. The pointwise identity is unrestricted, so
    /// this needs [`Self::sum_range_congr`] rather than
    /// [`Self::sum_range_congr_lt`], and there is no diagonal guard, no
    /// [`Self::unskip`] and no `Nat.beq` anywhere in it.
    pub det_col_expansion: NameId,
    /// `Rat.matMinor_transpose : ∀ A q r c,
    /// matMinor (matTranspose A) 0 q r c = matTranspose (matMinor A q 0) r c`
    /// — the minor of a transpose is the transpose of the mirrored minor,
    /// POINTWISE. `Eq.refl`: both sides delta-beta-reduce to
    /// `A (matSkip q c) (matSkip 0 r)`.
    pub mat_minor_transpose: NameId,
    /// `Rat.det_transpose : ∀ n A, det (matTranspose A) n = det A n` — the
    /// determinant is invariant under transpose, at a **symbolic** dimension.
    /// The third of the four laws ADR-1120 named over [`Self::det`].
    ///
    /// Induction on the dimension with the matrix under the motive:
    /// `det_succ` on the transpose is expansion along `A`'s first COLUMN
    /// entry by entry, [`Self::mat_minor_transpose`] plus
    /// [`Self::det_congr`] turns each minor into a transpose the induction
    /// hypothesis can consume, and [`Self::det_col_expansion`] closes it.
    pub det_transpose: NameId,

    // --- alternating property (`matrix_det`, ADR-1310 step 2) --------------
    /// `Rat.det_alternating : ∀ m A i j, Nat.beq i j = false →
    /// Nat.ble i m = true → Nat.ble j m = true → (∀ c, A i c = A j c) →
    /// det A (succ m) = 0` — the ALTERNATING property: the determinant
    /// vanishes whenever two distinct rows agree pointwise, at a
    /// **symbolic** dimension. The second of the three theorems ADR-1310
    /// names as remaining toward multiplicativity, after
    /// [`Self::det_row_expansion`].
    ///
    /// Induction on `m`, case-splitting `i` and `j` against `0` in the step:
    /// when both are nonzero, expand along row `0`; when one is `0`, expand
    /// along row `1` or `2` (chosen to miss both). Every shift this needs —
    /// [`Self::mat_skip_zero`]'s branch and the OTHER `Nat.ble`-guarded
    /// branch of the same `bool_select_nat` — reduces by pure iota once the
    /// case split has put a `succ` at the right spot, so no extra `matSkip`
    /// lemma is needed beyond what is already declared. The `n=2` corner
    /// (`i=0,j=1`, no third row available) closes directly via
    /// [`Self::det_eq_det2`] and ordinary `Rat` algebra. Every branch that
    /// expands consumes the induction hypothesis directly at the minor —
    /// unlike ADR-1310's expectation, this did not need [`Self::det_congr`].
    pub det_alternating: NameId,

    // --- sign under a row swap (`matrix_det`, ADR-1310 step 3) -------------
    /// `Rat.det_row_swap : ∀ m A B i j, Nat.beq i j = false →
    /// Nat.ble i m = true → Nat.ble j m = true →
    /// (∀ c, B i c = A j c) → (∀ c, B j c = A i c) →
    /// (∀ r c, Nat.beq r i = false → Nat.beq r j = false → B r c = A r c) →
    /// det B (succ m) = Rat.neg (det A (succ m))` — the SIGN under a row
    /// swap, stated EXTENSIONALLY (three pointwise hypotheses relating `B`
    /// to `A`, no `matSwapRows` definition): the third of the three theorems
    /// ADR-1310 named toward multiplicativity, after
    /// [`Self::det_row_expansion`] and [`Self::det_alternating`].
    ///
    /// The classical `det(A + swap) = 0` argument: the matrix `C` with BOTH
    /// rows `i`,`j` set to `A i + A j` has `det C = 0` by
    /// [`Self::det_alternating`] directly. Expanding `C` bilinearly in rows
    /// `i` and `j` — row-ADDITIVITY, built from three applications of
    /// [`Self::det_row_expansion`] plus [`Self::sum_range_add`]/
    /// [`Self::sum_range_congr`] and distributivity, since a minor never
    /// depends on the row it deletes — gives four terms: both-rows-`A i`,
    /// both-rows-`A j` (each `0` again), row `i`=`A i`/row `j`=`A j` (`A`
    /// itself, pointwise), and row `i`=`A j`/row `j`=`A i` (the swap,
    /// bridged to `B`). `0 = 0 + det A + det B + 0` rearranges to
    /// `det B = neg (det A)` via [`Self::neg_eq_of_add_eq_zero`] and
    /// [`Self::neg_neg`].
    ///
    /// **No new induction**: every fact this combines is already
    /// dimension-general, so the whole argument is straight-line at a
    /// symbolic `m`. Row-multilinearity did NOT exist and had to be built;
    /// [`Self::det_congr`] WAS needed, twice — contrary to
    /// [`Self::det_alternating`]'s experience, unlike ADR-1310's original
    /// expectation for THAT theorem.
    pub det_row_swap: NameId,

    // --- row multilinearity (`matrix_det`, ADR-1440) -----------------------
    /// `Rat.det_row_replaced : ∀ m A M h t, Nat.ble t m = true →
    /// (∀ c, M t c = h c) →
    /// (∀ r, Nat.beq r t = false → ∀ c, M r c = A r c) →
    /// det M (succ m) = sumRange (fun q => altSign (q + t) *
    ///   (h q * det (matMinor A t q) m)) (succ m)` — **the row-`t` workhorse**:
    /// expanding along row `t` sees the rest of the matrix ONLY through `A`'s
    /// minors, so a matrix agreeing with `A` off row `t` has its determinant
    /// fixed by that row's own values.
    ///
    /// [`Self::det_row_expansion`] plus the observation that a row-`t` minor
    /// never mentions row `t` — [`Self::beq_mat_skip_left`] says
    /// `matSkip t r` is never `t`, so `hoff` discharges every index the minor
    /// reaches. Straight-line at a symbolic `m`; no new induction.
    /// [`Self::det_congr`] IS needed here, and every other theorem in this
    /// group reaches it through this one.
    pub det_row_replaced: NameId,
    /// `Rat.det_row_zero : ∀ m M t, Nat.ble t m = true →
    /// (∀ c, M t c = 0) → det M (succ m) = 0` — a zero row kills the
    /// determinant. [`Self::det_row_expansion`] plus
    /// [`Self::sum_range_eq_zero_of_lt`]; this prelude has `mul_zero` but no
    /// `zero_mul`, so `0 * X` goes through [`Self::mul_comm`] first.
    pub det_row_zero: NameId,
    /// `Rat.det_row_smul : ∀ m A M z t, Nat.ble t m = true →
    /// (∀ c, M t c = z * A t c) →
    /// (∀ r, Nat.beq r t = false → ∀ c, M r c = A r c) →
    /// det M (succ m) = z * det A (succ m)` — scaling one row scales the
    /// determinant. [`Self::det_row_replaced`] at `h := fun c => z * A t c`,
    /// [`Self::mul_sum_range`] to pull `z` back out, and one four-factor
    /// rearrangement per summand.
    pub det_row_smul: NameId,
    /// `Rat.det_row_multilinear : ∀ m A M coef t n, Nat.ble t m = true →
    /// (∀ c, M t c = sumRange (fun k => coef k c) n) →
    /// (∀ r, Nat.beq r t = false → ∀ c, M r c = A r c) →
    /// det M (succ m) = sumRange (fun k => sumRange (fun q =>
    ///   altSign (q + t) * (coef k q * det (matMinor A t q) m)) (succ m)) n`
    /// — **linearity in one row over a finite sum**, the Cauchy–Binet
    /// expansion step ADR-1310 names as step 4's first prerequisite and which
    /// nothing in this prelude supplied.
    ///
    /// A row of `A·B` is exactly a `Rat.sumRange` of rows of `B`, so this is
    /// what turns `det (A·B)` into a sum over index choices; applying it `n`
    /// times is the remaining work (see the "what is still missing" section of
    /// `rat_prelude/matrix_det.rs`).
    ///
    /// [`Self::det_row_replaced`], then two [`Self::mul_sum_range`]s around
    /// one [`Self::mul_comm`] to move the sum out of the middle of the
    /// summand, then [`Self::sum_range_swap`] — whose binder order is
    /// `(f, INNER bound, OUTER bound)`.
    pub det_row_multilinear: NameId,
    /// `Rat.det_matMul_2 : ∀ A B, det (matMul A B 2) 2 = det A 2 * det B 2`
    /// — **determinant multiplicativity at dimension 2**, symbolic in both
    /// matrices. The symbolic-`n` statement is not proved (ADR-1440).
    ///
    /// Cheap for a reason that does NOT generalize: the eight-variable ring
    /// identity is [`Self::det2_mul`], landed with the fixed-dimension
    /// `matrix` module long before [`Self::det`] existed, and
    /// [`Self::det_eq_det2`] already identifies `det A 2` with `det2` on the
    /// four entries. All that is left is reducing `matMul A B 2 i j` at the
    /// four index pairs — which works only because `2` is a literal, so
    /// `Rat.sumRange` iota-reduces; at a symbolic `n` nothing reduces and the
    /// general case needs [`Self::det_row_multilinear`] and an induction over
    /// the rows instead. `n = 3` is not done: there is no `det3_mul`, and that
    /// identity has eighteen variables.
    pub det_mat_mul_2: NameId,
    /// `Rat.det_row_selection_of_duplicate : ∀ m B g i j,
    /// Nat.beq i j = false → Nat.ble i m = true → Nat.ble j m = true →
    /// Eq Nat (g i) (g j) →
    /// Eq Rat (det (fun r c => B (g r) c) (succ m))
    ///        (mul (det (fun r c => matId (g r) c) (succ m)) (det B (succ m)))`
    /// — the FREE half of the ADR-1440 obligation-2 selection lemma: given
    /// an explicit duplicate pair, both sides are `0`.
    ///
    /// The full selection lemma `det (B∘g) n = det (matId∘g) n * det B n`
    /// needs a `MapsInto g n` hypothesis (the literal target with NO
    /// hypotheses is FALSE — counterexample `n=1, g 0 = 5`: `det (B∘g) 1 =
    /// B 5 0`, generically nonzero, while `det (matId∘g) 1 = matId 5 0 =
    /// 0`) and, for the injective case, a cursor induction this lane did
    /// not land (ADR-1470). `InjectiveOn` alone (this declaration's shape)
    /// needs neither `MapsInto` nor that induction.
    pub det_row_selection_of_duplicate: NameId,
    /// `Rat.det_congr_lt : ∀ n A B, (∀ r, Lt r n → ∀ c, A r c = B r c) →
    /// det A n = det B n` — the ROW-BOUNDED determinant congruence.
    ///
    /// [`Self::det_congr`] wants agreement at EVERY index pair. Every
    /// reindexing map the multiplicativity route builds — a `g` produced by a
    /// fold over a function space, or a `g` corrected to fix everything above
    /// a cursor — is under no control at all outside `[0,n)`, so the
    /// unrestricted form is unusable there.
    ///
    /// Only the ROW index is bounded. `det A n` reads `A` at `(r,c)` with
    /// both `r < n` and `c < n`, but the cofactor recursion reaches a column
    /// only through [`Self::mat_skip`], so bounding the row carries the
    /// induction and needs no `matSkip` bound lemma; bounding the column too
    /// would need `Lt (matSkip j c) (succ m)` from `Lt c m`, which nothing in
    /// this prelude supplies.
    pub det_congr_lt: NameId,
    /// `Rat.matSkip_lt_succ : ∀ p c m, Lt c m → Lt (matSkip p c) (succ m)` —
    /// the column bound, and the only reason [`Self::det_congr_lt`] stops at
    /// the row. Both branches of [`Self::mat_skip`]'s `bool_select_nat` are
    /// below `succ m`, so it is one `Bool.rec` on the guard and never a
    /// decision about it.
    pub mat_skip_lt_succ: NameId,
    /// `Rat.det_congr_entry_lt : ∀ n A B,
    /// (∀ r, Lt r n → ∀ c, Lt c n → A r c = B r c) → det A n = det B n` — the
    /// congruence bounded on BOTH indices, i.e. on exactly the square
    /// `det A n` reads.
    ///
    /// [`Self::det_congr_lt`] is the right tool when a reindexing map is under
    /// no control outside `[0,n)`; this is the right tool when the two
    /// matrices agree only where the determinant looks, which is what the
    /// identity laws give — [`Self::mat_mul_id_right`] is
    /// `Lt j n → matMul A matId n i j = A i j`, bounded in the COLUMN, so the
    /// row-bounded form cannot consume it.
    pub det_congr_entry_lt: NameId,
    /// `Rat.det_row_selection_injective : ∀ m B g, InjectiveOn g (succ m) →
    /// MapsInto g (succ m) → det (B∘g) (succ m) =
    /// det (matId∘g) (succ m) * det B (succ m)` — the SELECTION lemma's
    /// INJECTIVE half, ADR-1440's obligation 2 and the half ADR-1470 designed
    /// but did not build. Together with
    /// [`Self::det_row_selection_of_duplicate`] (the free, non-injective half)
    /// it covers every reindexing map, once a decision procedure for
    /// `InjectiveOn` splits them.
    ///
    /// `MapsInto` is load-bearing on the STATEMENT, not just the proof:
    /// ADR-1470's counterexample is `n = 1`, `g 0 = 5`, `B 5 0 = 7`, where the
    /// left side is `7` and the right side `0`.
    ///
    /// A CURSOR induction on how many trailing positions `g` already fixes,
    /// with the dimension and `B` outside the induction and `g` inside it (the
    /// step applies the induction hypothesis at a DIFFERENT map). Pigeonhole
    /// ([`crate::nat_prelude::NatPrelude::injective_on_imp_surjective_on`])
    /// supplies the preimage of the cursor, `Nat.transposition` brings it into
    /// place, and [`Self::det_row_swap`] pays for the move with one sign that
    /// [`Self::neg_mul`]/[`Self::neg_neg`] cancel. The base case needs
    /// [`Self::det_congr_lt`] rather than [`Self::det_congr`], because `g` is
    /// the identity only on `[0,n)`.
    pub det_row_selection_injective: NameId,
    /// `Rat.det_row_selection : ∀ m B g, MapsInto g (succ m) →
    /// det (B∘g) (succ m) = det (matId∘g) (succ m) * det B (succ m)` — **the
    /// SELECTION lemma**, with no injectivity hypothesis: ADR-1440's
    /// obligation 2 in the corrected form ADR-1470 states, closed.
    ///
    /// One `Or.elim` over
    /// [`crate::nat_prelude::NatPrelude::injective_on_or_duplicate`] joining
    /// [`Self::det_row_selection_injective`] to
    /// [`Self::det_row_selection_of_duplicate`].
    ///
    /// `MapsInto` cannot be dropped — ADR-1470's counterexample is `n = 1`,
    /// `g 0 = 5`, `B 5 0 = 7`, where the left side is `7` and the right `0`.
    pub det_row_selection: NameId,

    // --- the function-space aggregates (`sum_maps`, ADR-1543) --------------
    /// `Rat.prodRange : (Nat → Rat) → Nat → Rat`, `Nat.rec` on the bound:
    /// `prodRange f zero ≡ one`, `prodRange f (succ n) ≡ prodRange f n * f n`.
    /// The ℚ port of [`IntPrelude::prod_range`](crate::int_prelude::IntPrelude::prod_range);
    /// the Cauchy–Binet coefficient of an index map `g` is
    /// `prodRange (fun i => A i (g i)) n`.
    pub prod_range: NameId,
    /// `Rat.prodRange_zero : ∀ f, prodRange f zero = one` — `Eq.refl`.
    pub prod_range_zero: NameId,
    /// `Rat.prodRange_succ : ∀ f n, prodRange f (succ n) = prodRange f n * f n`
    /// — `Eq.refl`; peels the BACK factor.
    pub prod_range_succ: NameId,
    /// `Rat.prodRange_shiftFront : ∀ f n, prodRange f (succ n) =
    /// f 0 * prodRange (fun k => f (succ k)) n` — peels the FRONT factor,
    /// which is the end `Rat.sumMaps`'s `cons` reindexes at.
    pub prod_range_shift_front: NameId,
    /// `Rat.prodRange_congr : ∀ f g n, (∀ k, f k = g k) →
    /// prodRange f n = prodRange g n`.
    pub prod_range_congr: NameId,
    /// `Rat.sumRange_mul_right : ∀ f z n,
    /// sumRange (fun k => f k * z) n = sumRange f n * z`.
    pub sum_range_mul_right: NameId,
    /// `Rat.sumRange_mul_left : ∀ z f n,
    /// sumRange (fun k => z * f k) n = z * sumRange f n` — the same content as
    /// [`Self::mul_sum_range`] with the equation the other way round, which is
    /// the direction the `sumMaps` induction consumes.
    pub sum_range_mul_left: NameId,
    /// `Rat.sumMaps : Nat → Nat → ((Nat → Nat) → Rat) → Rat` — a finite sum
    /// **indexed by the function space** `[0,m) → [0,n)`, by structural
    /// recursion on `m` with a higher-order motive. The ℚ port of
    /// [`IntPrelude::sum_maps`](crate::int_prelude::IntPrelude::sum_maps);
    /// ADR-1135 recorded this index set as inexpressible here and `Int.sumMaps`
    /// refuted that, but no ℚ analogue existed until ADR-1543.
    pub sum_maps: NameId,
    /// `Rat.sumMaps_zero : ∀ n F, sumMaps 0 n F = F (fun _ => 0)`.
    pub sum_maps_zero: NameId,
    /// `Rat.sumMaps_succ : ∀ m n F, sumMaps (succ m) n F =
    /// sumRange (fun k => sumMaps m n (fun g => F (cons k g))) n`.
    pub sum_maps_succ: NameId,
    /// `Rat.sumMaps_congr : ∀ n m F G, (∀ g, F g = G g) →
    /// sumMaps m n F = sumMaps m n G`.
    pub sum_maps_congr: NameId,
    /// `Rat.sumMaps_mul_left : ∀ n z m H,
    /// sumMaps m n (fun g => z * H g) = z * sumMaps m n H`.
    pub sum_maps_mul_left: NameId,
    /// `Rat.sumMaps_mul_right : ∀ n z m H,
    /// sumMaps m n (fun g => H g * z) = sumMaps m n H * z` — what pulls the
    /// whole `det B n` factor out of the Cauchy–Binet sum.
    pub sum_maps_mul_right: NameId,

    // --- determinant multiplicativity (`det_mul`, ADR-1543) ----------------
    /// `Rat.matSetRow : Nat → (Nat → Rat) → (Nat → Nat → Rat) →
    /// (Nat → Nat → Rat)`, `matSetRow t h M := fun r c =>
    /// if Nat.beq r t then h c else M r c` — `M` with row `t` replaced.
    /// [`Self::det_row_smul`] and [`Self::det_row_replaced`] take the
    /// reference matrix as an ARGUMENT, so the Cauchy–Binet cursor needs the
    /// partially-replaced matrix as a term. The `bool_select_rat` encoding is
    /// [`Self::mat_id`]'s own, chosen over a recursion on `t` because both
    /// defining equations then cost one rewrite instead of an induction.
    pub mat_set_row: NameId,
    /// `Rat.matSetRow_at : ∀ t h M c, matSetRow t h M t c = h c` — one
    /// `Nat.beq_refl` rewrite.
    pub mat_set_row_at: NameId,
    /// `Rat.matSetRow_off : ∀ t h M r, Nat.beq r t = false → ∀ c,
    /// matSetRow t h M r c = M r c`.
    pub mat_set_row_off: NameId,
    /// `Rat.matSubstRows : (Nat → Nat → Rat) → Nat → Nat → (Nat → Nat) →
    /// (Nat → Nat → Rat) → (Nat → Nat → Rat)` — `matSubstRows B m s g M`
    /// replaces rows `[s, s+m)` of `M` by row `g i` of `B` at relative index
    /// `i`, by structural recursion on `m` peeling the OUTERMOST row first:
    /// `matSubstRows B (m+1) s g M = matSubstRows B m (s+1) (g ∘ succ)
    /// (matSetRow s (B (g 0)) M)`.
    ///
    /// That order is forced. [`Self::sum_maps`]'s `cons` extends a map at the
    /// FRONT, so `matSubstRows B (succ j) s (cons k g) M` and
    /// `matSubstRows B j (succ s) g (matSetRow s (B k) M)` are the SAME TERM
    /// up to ι and η, and no commutation lemma between "set row `s`" and
    /// "substitute the rows above `s`" is ever needed.
    pub mat_subst_rows: NameId,
    /// `Rat.matSubstRows_below : ∀ B m s g M r, Lt r s → ∀ c,
    /// matSubstRows B m s g M r c = M r c` — rows below the window survive.
    pub mat_subst_rows_below: NameId,
    /// `Rat.matSubstRows_at : ∀ B m s g M i, Lt i m → ∀ c,
    /// matSubstRows B m s g M (add s i) c = B (g i) c` — inside the window the
    /// row is the one `g` selects. The row is written `Nat.add s i` so that
    /// `add s 0` ι-reduces to `s` (`Nat.add` recurses on its RIGHT argument);
    /// the successor leg pays one `Nat.succ_add`.
    pub mat_subst_rows_at: NameId,
    /// `Rat.sumMaps_congr_mapsInto : ∀ n m F G,
    /// (∀ g, MapsInto g n → F g = G g) → sumMaps m n F = sumMaps m n G` —
    /// [`Self::sum_maps_congr`] with the pointwise hypothesis weakened to maps
    /// into the range, which is what [`Self::det_row_selection`]'s
    /// `MapsInto` hypothesis forces. Every map `sumMaps` enumerates IS such a
    /// map (a `cons` tower over the constant-zero one), and this carries it.
    pub sum_maps_congr_maps_into: NameId,
    /// `Rat.det_matMul_expand : ∀ m n A B,
    /// det (matMul A B n) (succ m) = sumMaps (succ m) n (fun g =>
    /// prodRange (fun i => A i (g i)) (succ m) * det (B ∘ g) (succ m))` —
    /// **ADR-1440's obligation 1**, the Cauchy–Binet expansion of a product's
    /// determinant over the function space of index maps.
    pub det_mat_mul_expand: NameId,
    /// `Rat.det_matMul : ∀ n A B, det (matMul A B n) n = det A n * det B n` —
    /// **determinant multiplicativity at a symbolic dimension**, the last of
    /// ADR-1120's four laws. [`Self::det_mat_mul_2`] is the fixed-dimension
    /// special case whose proof does not generalize.
    pub det_mat_mul: NameId,
    // --- row-echelon form (ADR-1554) -----------------------------------------
    /// `Rat.isZeroB : Rat → Bool` — the DECIDED zero test, `ble x 0 && ble 0 x`
    /// written as one nested `Bool.rec` so nothing but `Rat.ble` is needed.
    ///
    /// Row reduction has to BRANCH on whether a candidate pivot is zero, and a
    /// `Prop`-valued `Eq x 0` cannot drive a computation. Over `ℚ` the order is
    /// decidable, so this is a total function and no `Decidable` instance or
    /// choice principle is involved — ADR-0603's row 2 (a boundary refutation)
    /// is empty for this family for exactly that reason.
    pub is_zero_b: NameId,
    /// `Rat.isZeroB_zero : Rat.isZeroB Rat.zero = Bool.true` — `Eq.refl`.
    pub is_zero_b_zero: NameId,
    /// `Rat.eq_zero_of_isZeroB : ∀ x, Rat.isZeroB x = Bool.true →
    /// Eq Rat x Rat.zero`.
    ///
    /// **The bridge from the DECIDED zero test to the propositional one**, and
    /// the piece `Rat.rank` needs to turn "`leadingIndex` stopped here" into a
    /// statement about the entry. It is where the decidability of `ℚ`'s order is
    /// actually spent: `Rat.le_antisymm` over the two `Rat.ble` bridges.
    pub eq_zero_of_is_zero_b: NameId,
    /// `Rat.isZeroB_of_eq_zero : ∀ x, Eq Rat x Rat.zero →
    /// Rat.isZeroB x = Bool.true` — the converse of
    /// [`Self::eq_zero_of_is_zero_b`], by transport along the equation.
    pub is_zero_b_of_eq_zero: NameId,
    /// `Rat.ne_zero_of_isZeroB_false : ∀ x, Rat.isZeroB x = Bool.false →
    /// Not (Eq Rat x Rat.zero)` — the form a found pivot's nonzero-ness has to
    /// arrive in for `Rat.mul_inv_cancel_of_ne_zero` to consume it.
    pub ne_zero_of_is_zero_b_false: NameId,
    /// `Rat.rowSwap : Nat → Nat → Mat → Mat` — exchange rows `i` and `j`.
    /// Built from two [`Self::mat_set_row`] writes over the ORIGINAL matrix, so
    /// both rows read pre-swap values.
    pub row_swap: NameId,
    /// `Rat.rowScale : Nat → Rat → Mat → Mat` — `rowScale i k M` multiplies row
    /// `i` by `k`. Total in `k`; the inverse law [`Self::row_scale_inverse`] is
    /// what carries the `k ≠ 0` side condition.
    pub row_scale: NameId,
    /// `Rat.rowAddMul : Nat → Nat → Rat → Mat → Mat` — `rowAddMul i j k M` adds
    /// `k` times row `j` to row `i`.
    pub row_add_mul: NameId,
    /// `Rat.rowSwap_at_left : ∀ i j M c, rowSwap i j M i c = M j c`.
    pub row_swap_at_left: NameId,
    /// `Rat.rowSwap_at_right : ∀ i j M, Nat.beq j i = false → ∀ c,
    /// rowSwap i j M j c = M i c`.
    pub row_swap_at_right: NameId,
    /// `Rat.rowSwap_off : ∀ i j M r, Nat.beq r i = false → Nat.beq r j = false →
    /// ∀ c, rowSwap i j M r c = M r c`.
    pub row_swap_off: NameId,
    /// `Rat.rowScale_at : ∀ i k M c, rowScale i k M i c = k * M i c`.
    pub row_scale_at: NameId,
    /// `Rat.rowScale_off : ∀ i k M r, Nat.beq r i = false → ∀ c,
    /// rowScale i k M r c = M r c`.
    pub row_scale_off: NameId,
    /// `Rat.rowAddMul_at : ∀ i j k M c,
    /// rowAddMul i j k M i c = M i c + k * M j c`.
    pub row_add_mul_at: NameId,
    /// `Rat.rowAddMul_off : ∀ i j k M r, Nat.beq r i = false → ∀ c,
    /// rowAddMul i j k M r c = M r c`.
    pub row_add_mul_off: NameId,
    /// `Rat.rowSwap_involutive : ∀ i j M r c,
    /// rowSwap i j (rowSwap i j M) r c = M r c` — UNCONDITIONAL, `i = j`
    /// included. The `i = j` corner is not free: at `r = i` the outer write
    /// reads row `j` of the once-swapped matrix, which needs `Nat.beq j i`
    /// split before either `matSetRow` equation applies.
    pub row_swap_involutive: NameId,
    /// `Rat.rowAddMul_inverse : ∀ i j k M, Nat.beq j i = false → ∀ r c,
    /// rowAddMul i j (neg k) (rowAddMul i j k M) r c = M r c` — the inverse of
    /// an add-multiple is the same operation with `-k`. `j ≠ i` is REQUIRED
    /// (at `i = j` the operation scales row `i` by `1 + k` and its inverse is
    /// not `-k`), and it is stated as `Nat.beq j i` rather than `beq i j`
    /// because that is the orientation [`Self::mat_set_row_off`] consumes.
    pub row_add_mul_inverse: NameId,
    /// `Rat.rowScale_inverse : ∀ i k M, Not (Eq Rat k Rat.zero) → ∀ r c,
    /// rowScale i (inv k) (rowScale i k M) r c = M r c`.
    pub row_scale_inverse: NameId,
    /// `Rat.pivotSearchAux : Nat → Mat → Nat → Nat → Nat → Nat` — the fuelled
    /// COMPUTED pivot search. `pivotSearchAux fuel M c r rows` walks `r` upward
    /// looking for the first row below `rows` whose column-`c` entry is
    /// nonzero, returning `rows` when there is none. Structural recursion on
    /// the fuel; no `Exists`, no extraction (ADR-1554).
    pub pivot_search_aux: NameId,
    /// `Rat.pivotSearch : Mat → Nat → Nat → Nat → Nat` —
    /// `pivotSearch M c start rows`, [`Self::pivot_search_aux`] at the
    /// canonical fuel `rows`.
    pub pivot_search: NameId,
    /// `Rat.clearBelowAux : Nat → Mat → Nat → Nat → Nat → Nat → Mat` — the
    /// fuelled elimination sweep. `clearBelowAux fuel M pr pc r rows` subtracts
    /// the right multiple of pivot row `pr` from every row from `r` up to
    /// `rows`.
    pub clear_below_aux: NameId,
    /// `Rat.clearBelow : Mat → Nat → Nat → Nat → Mat` —
    /// `clearBelow M pr pc rows`, the sweep starting at `succ pr`.
    pub clear_below: NameId,
    /// `Rat.echelonAux : Nat → Mat → Nat → Nat → Nat → Nat → Mat` — one
    /// Gaussian-elimination step per unit of fuel.
    pub echelon_aux: NameId,
    /// `Rat.rowEchelon : Mat → Nat → Nat → Mat` — `rowEchelon A rows cols`.
    /// [`Self::echelon_aux`] at fuel `cols`, which is EXACT: the pivot column
    /// advances on every iteration of the loop (both the found and the
    /// all-zero-column branch increment it), so `cols` steps reach the exit
    /// guard and no more are possible.
    pub row_echelon: NameId,
    /// `Rat.leadingIndexAux : Nat → Mat → Nat → Nat → Nat → Nat`.
    pub leading_index_aux: NameId,
    /// `Rat.leadingIndex : Mat → Nat → Nat → Nat` — `leadingIndex M r cols` is
    /// the first column of row `r` carrying a nonzero entry, and `cols` when
    /// the row is zero. Total, computed, and the quantity `Rat.rank` will be
    /// read off next.
    pub leading_index: NameId,
    /// `Rat.echelonStepOk : Nat → Nat → Nat → Bool` — one adjacent-row test:
    /// the leading indices strictly increase, or both rows are zero.
    pub echelon_step_ok: NameId,
    /// `Rat.isEchelonAux : Nat → Mat → Nat → Nat → Nat → Bool`.
    pub is_echelon_aux: NameId,
    /// `Rat.isEchelon : Mat → Nat → Nat → Bool` — decidable row-echelon test:
    /// leading entries strictly move right, and zero rows sit at the bottom.
    pub is_echelon: NameId,

    // --- rank (`rat_prelude::rank`, ADR-1555) -------------------------------
    /// `Rat.nonzeroRowB : Mat → Nat → Nat → Bool`,
    /// `nonzeroRowB E cols r := Nat.ble (succ (leadingIndex E r cols)) cols` —
    /// "row `r` of `E` is nonzero", decided. A zero row's
    /// [`Self::leading_index`] is `cols`, so the strict comparison against
    /// `cols` is exactly the nonzero test. The row index comes LAST so that
    /// `nonzeroRowB E cols` is already the `Nat → Bool` predicate
    /// [`NatPrelude::count_range`](crate::NatPrelude::count_range) consumes.
    pub nonzero_row_b: NameId,
    /// `Rat.nonzeroRowB_eq_ble : ∀ E cols r, nonzeroRowB E cols r =
    /// Nat.ble (succ (leadingIndex E r cols)) cols` — the defining equation,
    /// `Eq.refl`.
    pub nonzero_row_b_eq_ble: NameId,
    /// `Rat.nonzeroRowB_zero_cols : ∀ E r, nonzeroRowB E 0 r = false` — with
    /// no columns every row is zero. `Eq.refl` at a SYMBOLIC matrix, because
    /// `Nat.ble (succ _) zero` ι-reduces to `false` without evaluating the
    /// leading index at all.
    pub nonzero_row_b_zero_cols: NameId,
    /// `Rat.rank : Mat → Nat → Nat → Nat`, `rank M rows cols :=
    /// Nat.countRange (nonzeroRowB (rowEchelon M rows cols) cols) rows` — the
    /// number of nonzero rows of the row-echelon form, **computed**.
    ///
    /// The count is deliberately NOT capped at `cols`: a cap would make
    /// `rank ≤ cols` hold by truncation rather than by a theorem, and would
    /// hide a broken elimination from the evaluation tests (ADR-1555).
    pub rank: NameId,
    /// `Rat.rank_eq_countRange : ∀ M rows cols, rank M rows cols =
    /// Nat.countRange (nonzeroRowB (rowEchelon M rows cols) cols) rows` —
    /// `Eq.refl`, and the only route every `Nat.countRange` law has to `rank`.
    pub rank_eq_count_range: NameId,
    /// `Rat.rank_le_rows : ∀ M rows cols, Le (rank M rows cols) rows` — one
    /// application of `Nat.countRange_le`. Uses no property of `rowEchelon`,
    /// which is why this half of the dimension bound is free and `rank ≤ cols`
    /// is not (it needs `rowEchelon_isEchelon`, ADR-1554 obligation 4).
    pub rank_le_rows: NameId,
    /// `Rat.rank_zero_rows : ∀ M cols, rank M 0 cols = 0` — `Eq.refl`.
    pub rank_zero_rows: NameId,
    /// `Rat.countRange_nonzeroRowB_zero : ∀ E n,
    /// Nat.countRange (nonzeroRowB E 0) n = 0` — the generalisation over the
    /// matrix that [`Self::rank_zero_cols`] needs: in `rank M rows 0` the
    /// matrix is `rowEchelon M rows 0`, which itself depends on the induction
    /// variable.
    pub count_range_nonzero_row_b_zero: NameId,
    /// `Rat.rank_zero_cols : ∀ M rows, rank M rows 0 = 0` — `rank ≤ cols` is
    /// open in general, but at `cols = 0` it holds as an EQUALITY, which is a
    /// control a definition counting rows regardless of the leading index
    /// would fail.
    pub rank_zero_cols: NameId,

    // --- rank-nullity in column form (`rat_prelude::nullity`, ADR-1558) -----
    /// `Rat.pivotColSearchAux : Mat → Nat → Nat → Nat → Nat → Nat → Bool`,
    /// `pivotColSearchAux E rows cols j fuel r` — `true` when some `r' >= r`
    /// below `rows` has `leadingIndex E r' cols = j`. Both exhaustion answers
    /// (fuel out, scan finished) are `false`, mirroring
    /// [`Self::pivot_search_aux`]'s single out-of-range answer.
    pub pivot_col_search_aux: NameId,
    /// `Rat.isPivotColB : Mat → Nat → Nat → Nat → Bool`,
    /// `isPivotColB E rows cols j := pivotColSearchAux E rows cols j rows 0` —
    /// "column `j` is a pivot column of `E`", decided. The column index comes
    /// LAST so `isPivotColB E rows cols` is already the `Nat → Bool` predicate
    /// [`NatPrelude::count_range`](crate::NatPrelude::count_range) consumes.
    pub is_pivot_col_b: NameId,
    /// `Rat.isPivotColB_eq_search : ∀ E rows cols j, isPivotColB E rows cols j
    /// = pivotColSearchAux E rows cols j rows 0` — the defining equation,
    /// `Eq.refl`.
    pub is_pivot_col_b_eq_search: NameId,
    /// `Rat.isPivotColB_zero_rows : ∀ E cols j, isPivotColB E 0 cols j = false`
    /// — with no rows there is no pivot. `Eq.refl` at a SYMBOLIC matrix,
    /// column count and column, because the fuel is `0` and `Nat.rec` takes its
    /// zero branch without evaluating the leading index.
    pub is_pivot_col_b_zero_rows: NameId,
    /// `Rat.rankCols : Mat → Nat → Nat → Nat`, `rankCols M rows cols :=
    /// Nat.countRange (isPivotColB (rowEchelon M rows cols) rows cols) cols` —
    /// the number of PIVOT COLUMNS of the row-echelon form, **computed**.
    ///
    /// The column-form counterpart of [`Self::rank`]. `rank = rankCols` is the
    /// bridge, and it is open (ADR-1558): it is where
    /// `rowEchelon_isEchelon` is genuinely required.
    pub rank_cols: NameId,
    /// `Rat.rankCols_eq_countRange : ∀ M rows cols, rankCols M rows cols =
    /// Nat.countRange (isPivotColB (rowEchelon M rows cols) rows cols) cols` —
    /// `Eq.refl`, the route every `Nat.countRange` law has to `rankCols`.
    pub rank_cols_eq_count_range: NameId,
    /// `Rat.nullity : Mat → Nat → Nat → Nat`, `nullity M rows cols :=
    /// Nat.countRange (Nat.setCompl (isPivotColB (rowEchelon M rows cols) rows cols)) cols`
    /// — the FREE columns, **computed**. Deliberately not `cols - rank`: the
    /// subtraction form inherits `rank ≤ cols`, which is open.
    pub nullity: NameId,
    /// `Rat.nullity_eq_countRange : ∀ M rows cols, nullity M rows cols =
    /// Nat.countRange (Nat.setCompl (isPivotColB (rowEchelon M rows cols) rows cols)) cols`
    /// — `Eq.refl`.
    pub nullity_eq_count_range: NameId,
    /// `Rat.rank_nullity : ∀ M rows cols,
    /// Nat.add (rankCols M rows cols) (nullity M rows cols) = cols` — **the
    /// rank-nullity theorem in column form**, one application of
    /// `Nat.countRange_compl`, symbolic in all three arguments. No property of
    /// `rowEchelon` is used, which is exactly what the column form buys.
    pub rank_nullity: NameId,
    /// `Rat.rankCols_le_cols : ∀ M rows cols, Le (rankCols M rows cols) cols` —
    /// one `Nat.countRange_le`. Free here, where the row-form `rank ≤ cols` is
    /// not: a count over `[0, cols)` cannot exceed `cols` whatever the
    /// predicate does.
    pub rank_cols_le_cols: NameId,
    /// `Rat.nullity_le_cols : ∀ M rows cols, Le (nullity M rows cols) cols` —
    /// the same bound at the complementary predicate.
    pub nullity_le_cols: NameId,
    /// `Rat.rankCols_zero_cols : ∀ M rows, rankCols M rows 0 = 0` — `Eq.refl`.
    pub rank_cols_zero_cols: NameId,
    /// `Rat.nullity_zero_cols : ∀ M rows, nullity M rows 0 = 0` — `Eq.refl`,
    /// the degenerate instance of [`Self::rank_nullity`] at `cols = 0`.
    pub nullity_zero_cols: NameId,
    /// `Rat.countRange_isPivotColB_zeroRows : ∀ E cols n,
    /// Nat.countRange (isPivotColB E 0 cols) n = 0` — the generalisation over
    /// the matrix that [`Self::rank_cols_zero_rows`] needs, for the same reason
    /// [`Self::count_range_nonzero_row_b_zero`] exists.
    pub count_range_is_pivot_col_b_zero_rows: NameId,
    /// `Rat.rankCols_zero_rows : ∀ M cols, rankCols M 0 cols = 0` — with no
    /// rows there are no pivot columns.
    pub rank_cols_zero_rows: NameId,
    /// `Rat.nullity_zero_rows : ∀ M cols, nullity M 0 cols = cols` — with no
    /// rows EVERY column is free. The discriminating degenerate control: a
    /// `nullity` that returned `0` satisfies
    /// [`Self::rank_cols_zero_rows`] and fails this.
    pub nullity_zero_rows: NameId,

    // --- obligation 2, range half (`rat_prelude::pivot_bound`, ADR-1558) ----
    /// `Rat.pivotSearchAux_le_rows : ∀ M c rows fuel r,
    /// Le (pivotSearchAux M c rows fuel r) rows` — the pivot scan never returns
    /// an index past the row count, whatever the fuel and wherever it starts.
    /// The range half of ADR-1554 obligation 2; the content half (WHICH
    /// disjunct holds) is still open.
    pub pivot_search_aux_le_rows: NameId,
    /// `Rat.pivotSearch_le_rows : ∀ M c start rows,
    /// Le (pivotSearch M c start rows) rows` —
    /// [`Self::pivot_search_aux_le_rows`] at the fuel `pivotSearch` picks. No
    /// bound on `start` is required.
    pub pivot_search_le_rows: NameId,

    // --- the rank/rankCols bridge (`rat_prelude::rank_bridge`, ADR-1562) ----
    /// `Rat.pivotColOfRow : Mat → Nat → Nat → Nat`,
    /// `pivotColOfRow E cols r := leadingIndex E r cols` — the pivot COLUMN of
    /// a row, with the row index LAST so `pivotColOfRow E cols` is already the
    /// `Nat → Nat` map
    /// [`NatPrelude::count_range_bij`](crate::NatPrelude::count_range_bij)
    /// wants. `leadingIndex` takes `r` in the middle, and a lambda at the use
    /// site is what the counting laws cannot see through.
    pub pivot_col_of_row: NameId,
    /// `Rat.pivotColOfRow_eq_leadingIndex : ∀ E cols r,
    /// pivotColOfRow E cols r = leadingIndex E r cols` — the defining equation,
    /// `Eq.refl`.
    pub pivot_col_of_row_eq_leading_index: NameId,
    /// `Rat.pivotRowSearchAux : Mat → Nat → Nat → Nat → Nat → Nat → Nat`,
    /// `pivotRowSearchAux E rows cols j fuel r` — the first `r' ≥ r` below
    /// `rows` whose leading index is `j`, and `rows` for both exhaustion
    /// answers. [`Self::pivot_col_search_aux`]'s scan with the answer changed
    /// from `Bool` to the row index.
    pub pivot_row_search_aux: NameId,
    /// `Rat.pivotRowOfCol : Mat → Nat → Nat → Nat → Nat`,
    /// `pivotRowOfCol E rows cols j := pivotRowSearchAux E rows cols j rows 0`
    /// — the pivot ROW of a column, **computed**. The inverse map `τ` of the
    /// bridge; the column index comes LAST so `pivotRowOfCol E rows cols` is
    /// already a `Nat → Nat` map.
    pub pivot_row_of_col: NameId,
    /// `Rat.pivotRowOfCol_eq_search : ∀ E rows cols j, pivotRowOfCol E rows
    /// cols j = pivotRowSearchAux E rows cols j rows 0` — the defining
    /// equation, `Eq.refl`.
    pub pivot_row_of_col_eq_search: NameId,
    /// `Rat.pivotColSearchAux_eq_ble : ∀ E rows cols j fuel r,
    /// pivotColSearchAux E rows cols j fuel r =
    /// Nat.ble (succ (pivotRowSearchAux E rows cols j fuel r)) rows` — the
    /// `Bool` scan answers `true` exactly when the `Nat` scan lands in range.
    /// One fuel induction; the base case needs `ble (succ rows) rows = false`.
    pub pivot_col_search_aux_eq_ble: NameId,
    /// `Rat.isPivotColB_eq_ble : ∀ E rows cols j, isPivotColB E rows cols j =
    /// Nat.ble (succ (pivotRowOfCol E rows cols j)) rows` — ADR-1558's
    /// pivot-column TEST and this file's pivot-row MAP are the same scan.
    pub is_pivot_col_b_eq_ble: NameId,
    /// `Rat.pivotRowOfCol_lt_rows : ∀ E rows cols j,
    /// isPivotColB E rows cols j = true → Lt (pivotRowOfCol E rows cols j) rows`
    /// — a pivot column's row is a real row.
    pub pivot_row_of_col_lt_rows: NameId,
    /// `Rat.pivotRowSearchAux_leadingIndex : ∀ E rows cols j fuel r,
    /// Lt (pivotRowSearchAux E rows cols j fuel r) rows →
    /// Eq Nat (leadingIndex E (pivotRowSearchAux E rows cols j fuel r) cols) j`
    /// — if the scan landed in range it landed on a row with leading index `j`.
    pub pivot_row_search_aux_leading_index: NameId,
    /// `Rat.leadingIndex_pivotRowOfCol : ∀ E rows cols j,
    /// isPivotColB E rows cols j = true →
    /// Eq Nat (leadingIndex E (pivotRowOfCol E rows cols j) cols) j` — **the
    /// round trip that makes the bridge cheap.** It supplies three of
    /// [`NatPrelude::count_range_bij`](crate::NatPrelude::count_range_bij)'s
    /// five hypotheses at once when the COLUMNS are taken as the left-hand
    /// count: injectivity of `pivotRowOfCol`, the selected half of its
    /// `MapsInto`, and one round-trip equation verbatim.
    pub leading_index_pivot_row_of_col: NameId,
    /// `Rat.rank_eq_rankCols_of_pivotSection : ∀ M rows cols,
    /// (∀ r, Lt r rows → nonzeroRowB (rowEchelon M rows cols) cols r = true →
    ///    Eq Nat (pivotRowOfCol E rows cols (pivotColOfRow E cols r)) r) →
    /// Eq Nat (rank M rows cols) (rankCols M rows cols)` — **the bridge**,
    /// through `Nat.countRange_bij` with the COLUMNS as the left-hand count.
    /// The single hypothesis is the weakest form of ADR-1554 obligation 4 the
    /// bridge consumes: *the first row whose leading index is row `r`'s is `r`
    /// itself*. Every other hypothesis of the counting law is discharged from
    /// the two scans alone.
    pub rank_eq_rank_cols_of_pivot_section: NameId,
    /// `Rat.rank_le_cols_of_pivotSection : ∀ M rows cols,
    /// (the section hypothesis) → Le (rank M rows cols) cols` — the bound
    /// ADR-1555 left open, transported from the free
    /// [`Self::rank_cols_le_cols`] across the bridge.
    pub rank_le_cols_of_pivot_section: NameId,
    /// `Rat.rank_nullity_rows_of_pivotSection : ∀ M rows cols,
    /// (the section hypothesis) →
    /// Eq Nat (Nat.add (rank M rows cols) (nullity M rows cols)) cols` —
    /// **rank-nullity in the ROW form**, `Rat.rank_nullity` with `rankCols`
    /// rewritten to `rank` across the bridge and nothing else.
    pub rank_nullity_rows_of_pivot_section: NameId,

    // --- obligation 2's VALUE half (`rat_prelude::pivot_content`, ADR-1562) --
    /// `Rat.pivotSearchAux_ne_zero : ∀ M c rows fuel r,
    /// Lt (pivotSearchAux M c rows fuel r) rows →
    /// Not (Eq Rat (M (pivotSearchAux M c rows fuel r) c) Rat.zero)` — if the
    /// pivot scan landed in range, the entry it landed on is nonzero.
    pub pivot_search_aux_ne_zero: NameId,
    /// `Rat.pivotSearch_ne_zero : ∀ M c start rows,
    /// Lt (pivotSearch M c start rows) rows →
    /// Not (Eq Rat (M (pivotSearch M c start rows) c) Rat.zero)` — the **value
    /// half** of ADR-1554 obligation 2, and the half obligation 3 spends
    /// through `Rat.mul_inv_cancel_of_ne_zero`. The range half is
    /// [`Self::pivot_search_le_rows`]; the exhaustion disjunct (the answer is
    /// `rows` and the column is zero throughout the scanned range) is still
    /// open, and needs a different induction — one carrying the accumulated
    /// range in its motive.
    pub pivot_search_ne_zero: NameId,
    /// `Rat.pivotSearchAux_column_zero : ∀ M c rows q fuel r, Le r q →
    /// Lt q rows → Lt q (Nat.add r fuel) →
    /// Eq Nat (pivotSearchAux M c rows fuel r) rows → Eq Rat (M q c) Rat.zero`.
    pub pivot_search_aux_column_zero: NameId,
    /// `Rat.pivotSearch_column_zero : ∀ M c start rows q, Le start q →
    /// Lt q rows → Eq Nat (pivotSearch M c start rows) rows →
    /// Eq Rat (M q c) Rat.zero` — ADR-1554 obligation 2's **exhaustion
    /// disjunct**, which ADR-1562 left open: *the scan answered `rows`, and
    /// then the column is zero at every row it passed.* With
    /// [`Self::pivot_search_le_rows`] (range) and [`Self::pivot_search_ne_zero`]
    /// (value), obligation 2 is complete.
    pub pivot_search_column_zero: NameId,

    // --- what `leadingIndex` ANSWERS (`rat_prelude::leading_index`) ---------
    /// `Rat.leadingIndexAux_eq_of_first_nonzero : ∀ M r cols j c fuel,
    /// Le c j → Lt j cols → Lt j (Nat.add c fuel) →
    /// (∀ k, Le c k → Lt k j → Eq Rat (M r k) Rat.zero) →
    /// Not (Eq Rat (M r j) Rat.zero) →
    /// Eq Nat (leadingIndexAux M r cols fuel c) j`.
    pub leading_index_aux_eq_of_first_nonzero: NameId,
    /// `Rat.leadingIndex_eq_of_first_nonzero : ∀ M r cols j, Lt j cols →
    /// (∀ k, Lt k j → Eq Rat (M r k) Rat.zero) →
    /// Not (Eq Rat (M r j) Rat.zero) → Eq Nat (leadingIndex M r cols) j`.
    ///
    /// The characterization a freshly-pivoted row satisfies: zero left of the
    /// pivot column (the clause `echelonAux` maintains) and nonzero AT it
    /// ([`Self::pivot_search_ne_zero`]).
    pub leading_index_eq_of_first_nonzero: NameId,
    /// `Rat.leadingIndexAux_eq_cols_of_zero : ∀ M r cols c fuel,
    /// Le cols (Nat.add c fuel) →
    /// (∀ k, Le c k → Lt k cols → Eq Rat (M r k) Rat.zero) →
    /// Eq Nat (leadingIndexAux M r cols fuel c) cols`.
    pub leading_index_aux_eq_cols_of_zero: NameId,
    /// `Rat.leadingIndex_eq_cols_of_zero_row : ∀ M r cols,
    /// (∀ k, Lt k cols → Eq Rat (M r k) Rat.zero) →
    /// Eq Nat (leadingIndex M r cols) cols` — *a zero row's leading index is
    /// `cols`*, ADR-1554 §3's design decision as a theorem rather than a
    /// property of the definition.
    pub leading_index_eq_cols_of_zero_row: NameId,

    // --- obligation 3 (`rat_prelude::clear_below`, ADR-1571) ----------------
    /// `Rat.add_neg_div_mul_cancel : ∀ a b, Not (Eq Rat b Rat.zero) →
    /// Eq Rat (Rat.add a (Rat.mul (Rat.neg (Rat.div a b)) b)) Rat.zero` — the
    /// arithmetic core ADR-1554 names for obligation 3, at the exact shape
    /// `Rat.clearBelowAux` produces (the multiplier is on the LEFT).
    pub add_neg_div_mul_cancel: NameId,
    /// `Rat.clearBelowAux_off : ∀ pr pc rows q c fuel M r, Lt q r →
    /// Eq Rat (clearBelowAux pr pc rows fuel M r q c) (M q c)` — a row
    /// strictly above the sweep's cursor is untouched, at ANY fuel.
    pub clear_below_aux_off: NameId,
    /// `Rat.clearBelow_off : ∀ M pr pc rows q c, Le q pr →
    /// Eq Rat (clearBelow M pr pc rows q c) (M q c)` — obligation 3's
    /// "rows outside the range are untouched" half.
    pub clear_below_off: NameId,
    /// `Rat.clearBelowAux_zero : ∀ pr pc rows q fuel M r, Lt pr r → Le r q →
    /// Lt q rows → Lt q (Nat.add r fuel) → Not (Eq Rat (M pr pc) Rat.zero) →
    /// Eq Rat (clearBelowAux pr pc rows fuel M r q pc) Rat.zero`.
    ///
    /// The fuel bound is a real hypothesis: an exhausted sweep returns `M`
    /// untouched, which is indistinguishable from a finished one.
    pub clear_below_aux_zero: NameId,
    /// `Rat.clearBelow_zero : ∀ M pr pc rows q, Lt pr q → Lt q rows →
    /// Not (Eq Rat (M pr pc) Rat.zero) →
    /// Eq Rat (clearBelow M pr pc rows q pc) Rat.zero` — obligation 3's
    /// "everything below the pivot is zeroed in the pivot column" half, and
    /// the statement ADR-1554 asks for. Spends obligation 2's value half
    /// ([`Self::pivot_search_ne_zero`]) through the nonzero-pivot hypothesis.
    pub clear_below_zero: NameId,
    /// `Rat.clearBelowAux_preserves_zero : ∀ pr pc rows k q fuel M r,
    /// Le pr r → Le r q → Lt q rows →
    /// (∀ s, Le pr s → Lt s rows → Eq Rat (M s k) Rat.zero) →
    /// Eq Rat (clearBelowAux pr pc rows fuel M r q k) Rat.zero`.
    pub clear_below_aux_preserves_zero: NameId,
    /// `Rat.clearBelow_preserves_zero : ∀ M pr pc rows k q, Lt pr q →
    /// Lt q rows → (∀ s, Le pr s → Lt s rows → Eq Rat (M s k) Rat.zero) →
    /// Eq Rat (clearBelow M pr pc rows q k) Rat.zero` — *a column already zero
    /// from the pivot row down STAYS zero.*
    ///
    /// Unlike [`Self::clear_below_zero`] this needs NO fuel bound: its
    /// conclusion is about a value the sweep PRESERVES rather than one it
    /// creates, so the exhausted answer satisfies it directly.
    pub clear_below_preserves_zero: NameId,
    /// `Rat.rowSwap_preserves_zero_range : ∀ M pr piv rows k, Le pr piv →
    /// Lt piv rows → (∀ s, Le pr s → Lt s rows → Eq Rat (M s k) Rat.zero) →
    /// ∀ s, Le pr s → Lt s rows → Eq Rat (rowSwap pr piv M s k) Rat.zero` —
    /// *a column already zero from the pivot row down survives the pivot
    /// swap.*
    ///
    /// The row ADR-1571 §3's table recorded as the one missing prerequisite of
    /// obligation 4. Its twin for the sweep is
    /// [`Self::clear_below_preserves_zero`].
    pub row_swap_preserves_zero_range: NameId,
    /// `Rat.leadingIndexAux_congr_row : ∀ M N r r' cols,
    /// (∀ j, Eq Rat (M r j) (N r' j)) → ∀ fuel c,
    /// Eq Nat (leadingIndexAux M r cols fuel c)
    ///        (leadingIndexAux N r' cols fuel c)`.
    pub leading_index_aux_congr_row: NameId,
    /// `Rat.leadingIndex_congr_row : ∀ M N r r' cols,
    /// (∀ j, Eq Rat (M r j) (N r' j)) →
    /// Eq Nat (leadingIndex M r cols) (leadingIndex N r' cols)` — *the scan
    /// reads nothing but its own row.*
    ///
    /// Pointwise in, pointwise out: no `funext`, which is what ADR-1555 found
    /// the ROW form of rank invariance needs. The invariant's clause about the
    /// already-processed prefix survives a pivot step through this together
    /// with [`Self::clear_below_row_swap_off`].
    pub leading_index_congr_row: NameId,
    /// `Rat.clearBelow_rowSwap_off : ∀ M pr piv pc rows r c, Lt r pr →
    /// Le pr piv → Eq Rat (clearBelow (rowSwap pr piv M) pr pc rows r c)
    /// (M r c)` — *one whole pivot step leaves every row above the cursor
    /// exactly as it was.*
    pub clear_below_row_swap_off: NameId,
    /// `Rat.pivotSearchAux_ge_start : ∀ M c rows fuel r,
    /// Lt (pivotSearchAux M c rows fuel r) rows →
    /// Le r (pivotSearchAux M c rows fuel r)`.
    pub pivot_search_aux_ge_start: NameId,
    /// `Rat.pivotSearch_ge_start : ∀ M c start rows,
    /// Lt (pivotSearch M c start rows) rows →
    /// Le start (pivotSearch M c start rows)` — *a pivot found IN RANGE is at
    /// or below where the search started.*
    ///
    /// The hypothesis is not decoration: both exhaustion routes answer `rows`,
    /// which is not `≥ start` when the scan began past the row count. With
    /// [`Self::pivot_search_le_rows`] (no hypothesis needed) it pins the found
    /// pivot to `[start, rows)`, which is what
    /// [`Self::row_swap_preserves_zero_range`] and
    /// [`Self::clear_below_row_swap_off`] both demand.
    pub pivot_search_ge_start: NameId,
    /// `Rat.isEchelonAux_of_pairs : ∀ M rows cols fuel r,
    /// (∀ q, Le r q → Lt (succ q) rows →
    ///   Eq Bool (echelonStepOk (leadingIndex M q cols)
    ///            (leadingIndex M (succ q) cols) cols) true) →
    /// Eq Bool (isEchelonAux M rows cols fuel r) true`.
    pub is_echelon_aux_of_pairs: NameId,
    /// `Rat.isEchelon_of_pairs : ∀ M rows cols,
    /// (∀ q, Lt (succ q) rows →
    ///   Eq Bool (echelonStepOk (leadingIndex M q cols)
    ///            (leadingIndex M (succ q) cols) cols) true) →
    /// Eq Bool (isEchelon M rows cols) true` — *the `Bool` predicate is exactly
    /// the adjacent-pair condition.*
    ///
    /// No fuel bound, and ADR-1571 §2's rule forces that: `isEchelonAux`
    /// answers `true` on exhaustion and `true` is the conclusion.
    pub is_echelon_of_pairs: NameId,
    /// `Rat.echelonStepOk_of_lt : ∀ l1 l2 cols, Lt l1 l2 →
    /// Eq Bool (echelonStepOk l1 l2 cols) true` — the FIRST disjunct of the
    /// test as a lemma.
    pub echelon_step_ok_of_lt: NameId,
    /// `Rat.echelonStepOk_both_cols : ∀ cols,
    /// Eq Bool (echelonStepOk cols cols cols) true` — the SECOND disjunct at
    /// the only pair of values that can satisfy it, i.e. two zero rows in a
    /// row.
    pub echelon_step_ok_both_cols: NameId,
    /// `Rat.echelonAux_isEchelon : ∀ rows cols fuel M pr pc,
    /// Le pc cols →
    /// (∀ r, Lt (succ r) pr → Eq Bool (echelonStepOk (leadingIndex M r cols)
    ///        (leadingIndex M (succ r) cols) cols) true) →
    /// (∀ r, Lt r pr → Lt (leadingIndex M r cols) pc) →
    /// (∀ s c, Le pr s → Lt s rows → Lt c pc → Eq Rat (M s c) Rat.zero) →
    /// Le cols (Nat.add pc fuel) →
    /// Eq Bool (isEchelon (echelonAux rows cols fuel M pr pc) rows cols) true`
    /// — **ADR-1554's obligation 4**, with the exit derivation folded into the
    /// induction so nothing has to name the final cursors.
    pub echelon_aux_is_echelon: NameId,
    /// `Rat.rowEchelon_isEchelon : ∀ M rows cols,
    /// Eq Bool (isEchelon (rowEchelon M rows cols) rows cols) true` —
    /// **obligation 4, unconditional.** Gaussian elimination produces a matrix
    /// in row-echelon form.
    pub row_echelon_is_echelon: NameId,
    /// `Rat.lt_of_echelonStepOk : ∀ l1 l2 cols,
    /// Eq Bool (echelonStepOk l1 l2 cols) true → Lt l2 cols → Lt l1 l2` —
    /// decoding the test: a second row leading strictly inside the width forces
    /// the FIRST disjunct, because the second requires `Le cols l2`.
    pub lt_of_echelon_step_ok: NameId,
    /// `Rat.pairs_of_isEchelonAux : ∀ E rows cols q fuel r, Le r q →
    /// Lt (succ q) rows → Lt q (Nat.add r fuel) →
    /// Eq Bool (isEchelonAux E rows cols fuel r) true →
    /// Eq Bool (echelonStepOk (leadingIndex E q cols)
    ///          (leadingIndex E (succ q) cols) cols) true`.
    pub pairs_of_is_echelon_aux: NameId,
    /// `Rat.pairs_of_isEchelon : ∀ E rows cols,
    /// Eq Bool (isEchelon E rows cols) true → ∀ q, Lt (succ q) rows →
    /// Eq Bool (echelonStepOk (leadingIndex E q cols)
    ///          (leadingIndex E (succ q) cols) cols) true` — the converse of
    /// [`Self::is_echelon_of_pairs`], which unlike it DOES need a fuel bound in
    /// the `…Aux` form (ADR-1571 §2's rule, in the other direction).
    pub pairs_of_is_echelon: NameId,
    /// `Rat.leadingIndex_strict_below : ∀ E rows cols, (the pair condition) →
    /// ∀ r, Lt r rows → Lt (leadingIndex E r cols) cols →
    /// ∀ q, Lt q r → Lt (leadingIndex E q cols) (leadingIndex E r cols)` —
    /// *adjacent strict increase, extended to distance*, by induction on the
    /// UPPER row so no arithmetic on indices is ever formed.
    pub leading_index_strict_below: NameId,
    /// `Rat.pivotRowSearchAux_eq_of_first : ∀ E rows cols j r fuel start,
    /// Le start r → Lt r rows → Lt r (Nat.add start fuel) →
    /// (∀ q, Le start q → Lt q r → Not (Eq Nat (leadingIndex E q cols) j)) →
    /// Eq Nat (leadingIndex E r cols) j →
    /// Eq Nat (pivotRowSearchAux E rows cols j fuel start) r`.
    pub pivot_row_search_aux_eq_of_first: NameId,
    /// `Rat.pivotRowOfCol_eq_of_first : ∀ E rows cols j r, Lt r rows →
    /// (∀ q, Lt q r → Not (Eq Nat (leadingIndex E q cols) j)) →
    /// Eq Nat (leadingIndex E r cols) j →
    /// Eq Nat (pivotRowOfCol E rows cols j) r`.
    pub pivot_row_of_col_eq_of_first: NameId,
    /// `Rat.pivotSection_of_isEchelon : ∀ E rows cols,
    /// Eq Bool (isEchelon E rows cols) true → (the pivot section at E)` — the
    /// implication ADR-1562 §2 identified and ADR-1574 made derivable.
    pub pivot_section_of_is_echelon: NameId,
    /// `Rat.rank_eq_rankCols : ∀ M rows cols,
    /// Eq Nat (rank M rows cols) (rankCols M rows cols)` — **unconditional**,
    /// [`Self::rank_eq_rank_cols_of_pivot_section`] with its hypothesis
    /// discharged.
    pub rank_eq_rank_cols: NameId,
    /// `Rat.rank_le_cols : ∀ M rows cols, Le (rank M rows cols) cols` —
    /// **unconditional**, the bound ADR-1555 stated as open.
    pub rank_le_cols: NameId,
    /// `Rat.rank_nullity_rows : ∀ M rows cols,
    /// Eq Nat (Nat.add (rank M rows cols) (nullity M rows cols)) cols` —
    /// **rank-nullity in the ROW form, unconditional.**
    pub rank_nullity_rows: NameId,

    /// ADR-1578: the ℕ/ℤ/ℚ instances of `nat_prelude::structures`'s
    /// `Alg.*` record spine, three generic theorems, and a generic
    /// `det_one` over an arbitrary `Alg.CommRing`. See [`algebra_instances`].
    pub algebra: AlgebraNames,
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
        mul_inv_cancel_of_ne_zero: child(kernel, "mul_inv_cancel_of_ne_zero"),
        inv_pos: child(kernel, "inv_pos"),
        one_ne_zero: child(kernel, "one_ne_zero"),
        is_field: child(kernel, "IsField"),
        rat_is_field: child(kernel, "rat_isField"),
        mul_left_cancel_of_ne_zero: child(kernel, "mul_left_cancel_of_ne_zero"),
        is_ordered_field: child(kernel, "IsOrderedField"),
        rat_is_ordered_field: child(kernel, "rat_isOrderedField"),
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
        lt_of_sq_lt: child(kernel, "lt_of_sq_lt"),
        mul_sub_mul: child(kernel, "mul_sub_mul"),
        bounds_mul: child(kernel, "bounds_mul"),
        neg_mul_le_of_bounds: child(kernel, "neg_mul_le_of_bounds"),
        nat_div_succ_mul: child(kernel, "natDivSucc_mul"),
        nat_index_compose: child(kernel, "nat_index_compose"),
        nat_index_symm: child(kernel, "nat_index_symm"),
        nat_div_succ_le_scaled: child(kernel, "natDivSucc_le_scaled"),
        nat_div_succ_le_one: child(kernel, "natDivSucc_le_one"),
        nat_div_succ_antitone: child(kernel, "natDivSucc_antitone"),
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
        decidable_le: child(kernel, "decidable_le"),
        sum_range: child(kernel, "sumRange"),
        sum_range_zero: child(kernel, "sumRange_zero"),
        sum_range_succ: child(kernel, "sumRange_succ"),
        sum_range_congr: child(kernel, "sumRange_congr"),
        sum_range_add: child(kernel, "sumRange_add"),
        mul_sum_range: child(kernel, "mul_sumRange"),
        sum_range_le: child(kernel, "sumRange_le"),
        sum_range_nonneg: child(kernel, "sumRange_nonneg"),
        sum_range_congr_lt: child(kernel, "sumRange_congr_lt"),
        sum_range_eq_zero_of_lt: child(kernel, "sumRange_eq_zero_of_lt"),
        sum_range_swap: child(kernel, "sumRange_swap"),
        sum_range_split: child(kernel, "sumRange_split"),
        sum_range_diagonal: child(kernel, "sumRange_diagonal"),
        sum_range_rect_eq_diag_add_corner: child(kernel, "sumRange_rect_eq_diag_add_corner"),
        sum_range_mul: child(kernel, "sumRange_mul"),
        sum_range_mul_double: child(kernel, "sumRange_mul_double"),
        sum_range_mul_eq_diag_add_corner: child(kernel, "sumRange_mul_eq_diag_add_corner"),
        pow: child(kernel, "pow"),
        pow_zero: child(kernel, "pow_zero"),
        pow_succ: child(kernel, "pow_succ"),
        pow_add: child(kernel, "pow_add"),
        pow_sub_add: child(kernel, "pow_sub_add"),
        pow_nat_div_succ_two: child(kernel, "pow_natDivSucc_two"),
        poly_eval: child(kernel, "polyEval"),
        poly_eval_zero: child(kernel, "polyEval_zero"),
        poly_eval_succ: child(kernel, "polyEval_succ"),
        poly_eval_add: child(kernel, "polyEval_add"),
        poly_eval_smul: child(kernel, "polyEval_smul"),
        pow_one: child(kernel, "pow_one"),
        add_sub_cancel_left: child(kernel, "add_sub_cancel_left"),
        sq_sub_sq: child(kernel, "sq_sub_sq"),
        poly_eval_deg1: child(kernel, "polyEval_deg1"),
        taylor_deg1: child(kernel, "taylor_deg1"),
        bernoulli: child(kernel, "bernoulli"),
        bernoulli_harmonic_bound: child(kernel, "bernoulli_harmonic_bound"),
        dot_n: child(kernel, "dotN"),
        dot_n_zero: child(kernel, "dotN_zero"),
        dot_n_succ: child(kernel, "dotN_succ"),
        dot_n_comm: child(kernel, "dotN_comm"),
        dot_n_add_left: child(kernel, "dotN_add_left"),
        dot_n_smul_left: child(kernel, "dotN_smul_left"),
        dot_n_self_nonneg: child(kernel, "dotN_self_nonneg"),
        dot_n_two: child(kernel, "dotN_two"),
        dot_n_cauchy_schwarz: child(kernel, "dotN_cauchy_schwarz"),
        mat_mul: child(kernel, "matMul"),
        mat_mul_zero: child(kernel, "matMul_zero"),
        mat_mul_succ: child(kernel, "matMul_succ"),
        mat_mul_assoc: child(kernel, "matMul_assoc"),
        mat_mul_add_left: child(kernel, "matMul_add_left"),
        mat_mul_add_right: child(kernel, "matMul_add_right"),
        mat_mul_smul_left: child(kernel, "matMul_smul_left"),
        sum_range_delta: child(kernel, "sumRange_delta"),
        mat_id: child(kernel, "matId"),
        mat_id_diag: child(kernel, "matId_diag"),
        mat_id_off_diag: child(kernel, "matId_off_diag"),
        mat_mul_id_left: child(kernel, "matMul_id_left"),
        mat_mul_id_right: child(kernel, "matMul_id_right"),
        mat_transpose: child(kernel, "matTranspose"),
        mat_transpose_transpose: child(kernel, "matTranspose_transpose"),
        mat_transpose_mul: child(kernel, "matTranspose_mul"),
        mat_transpose_eval_example: child(kernel, "matTranspose_eval_example"),
        mat_transpose_mul_example: child(kernel, "matTranspose_mul_example"),
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
        covariance_comm: child(kernel, "covariance_comm"),
        variance_add_eq: child(kernel, "variance_add_eq"),
        variance_add_of_uncorrelated: child(kernel, "variance_add_of_uncorrelated"),
        indicator: child(kernel, "indicator"),
        indicator_nonneg: child(kernel, "indicator_nonneg"),
        indicator_le: child(kernel, "indicator_le"),
        variance_indicator: child(kernel, "variance_indicator"),
        variance_indicator_le_quarter: child(kernel, "variance_indicator_le_quarter"),
        markov_constructed: child(kernel, "markov_constructed"),
        chebyshev_inequality: child(kernel, "chebyshev_inequality"),
        covariance_add_right: child(kernel, "covariance_add_right"),
        covariance_smul_left: child(kernel, "covariance_smul_left"),
        covariance_sq_le_variance_mul: child(kernel, "covariance_sq_le_variance_mul"),
        sum_vars: child(kernel, "sumVars"),
        expectation_sum_vars: child(kernel, "expectation_sumVars"),
        covariance_sum_vars_left: child(kernel, "covariance_sumVars_left"),
        covariance_sum_vars: child(kernel, "covariance_sumVars"),
        pairwise_uncorrelated: child(kernel, "PairwiseUncorrelated"),
        variance_sum_vars: child(kernel, "variance_sumVars"),
        variance_scaled_mean: child(kernel, "variance_scaled_mean"),
        chebyshev_sample_mean_uncorrelated: child(kernel, "chebyshev_sampleMean_uncorrelated"),
        variance_sample_mean_uncorrelated: child(kernel, "variance_sampleMean_uncorrelated"),
        weak_law_of_large_numbers: child(kernel, "weak_law_of_large_numbers"),
        bernoulli_law_of_large_numbers: child(kernel, "bernoulli_law_of_large_numbers"),
        variance_scaled_add_nonneg: child(kernel, "variance_scaled_add_nonneg"),
        covariance_sq_le_variance_mul_of_pos: child(kernel, "covariance_sq_le_variance_mul_of_pos"),
        covariance_sq_le_variance_mul_of_zero_zero: child(
            kernel,
            "covariance_sq_le_variance_mul_of_zero_zero",
        ),
        det2: child(kernel, "det2"),
        det2_swap_rows: child(kernel, "det2_swap_rows"),
        det2_id: child(kernel, "det2_id"),
        det2_scale_row: child(kernel, "det2_scale_row"),
        det2_row_add: child(kernel, "det2_row_add"),
        det2_mul: child(kernel, "det2_mul"),
        det2_eq_zero_of_lin_dep: child(kernel, "det2_eq_zero_of_lin_dep"),
        mul_adj2_top_left: child(kernel, "mul_adj2_top_left"),
        mul_adj2_top_right: child(kernel, "mul_adj2_top_right"),
        mul_adj2_bottom_left: child(kernel, "mul_adj2_bottom_left"),
        mul_adj2_bottom_right: child(kernel, "mul_adj2_bottom_right"),
        inv2_top_left: child(kernel, "inv2_top_left"),
        inv2_top_right: child(kernel, "inv2_top_right"),
        inv2_bottom_left: child(kernel, "inv2_bottom_left"),
        inv2_bottom_right: child(kernel, "inv2_bottom_right"),
        cramer_two_unique_x: child(kernel, "cramer_two_unique_x"),
        cramer_two_unique_y: child(kernel, "cramer_two_unique_y"),
        cramer2_x: child(kernel, "cramer2_x"),
        cramer2_y: child(kernel, "cramer2_y"),
        cramer2_solves: child(kernel, "cramer2_solves"),
        of_int: child(kernel, "ofInt"),
        of_int_add: child(kernel, "ofInt_add"),
        of_int_mul: child(kernel, "ofInt_mul"),
        of_int_neg: child(kernel, "ofInt_neg"),
        det2_fib: child(kernel, "det2_fib"),
        det3: child(kernel, "det3"),
        det3_id: child(kernel, "det3_id"),
        det3_cofactor_row1: child(kernel, "det3_cofactor_row1"),
        det3_scale_row: child(kernel, "det3_scale_row"),
        det3_ofint: child(kernel, "det3_ofInt"),
        det3_example_generic: child(kernel, "det3_example_generic"),
        det3_example_diagonal: child(kernel, "det3_example_diagonal"),
        det3_example_singular: child(kernel, "det3_example_singular"),
        mat_inv2: child(kernel, "matInv2"),
        matmul_matinv2_top_left: child(kernel, "matMul_matInv2_top_left"),
        matmul_matinv2_top_right: child(kernel, "matMul_matInv2_top_right"),
        matmul_matinv2_bottom_left: child(kernel, "matMul_matInv2_bottom_left"),
        matmul_matinv2_bottom_right: child(kernel, "matMul_matInv2_bottom_right"),
        matinv2_matmul_top_left: child(kernel, "matInv2_matMul_top_left"),
        matinv2_matmul_top_right: child(kernel, "matInv2_matMul_top_right"),
        matinv2_matmul_bottom_left: child(kernel, "matInv2_matMul_bottom_left"),
        matinv2_matmul_bottom_right: child(kernel, "matInv2_matMul_bottom_right"),
        mat_inv2_eval_example: child(kernel, "matInv2_eval_example"),
        mat_inv2_example: child(kernel, "matInv2_example"),
        mat_skip: child(kernel, "matSkip"),
        mat_minor: child(kernel, "matMinor"),
        alt_sign: child(kernel, "altSign"),
        alt_sign_zero: child(kernel, "altSign_zero"),
        alt_sign_succ: child(kernel, "altSign_succ"),
        det: child(kernel, "det"),
        det_zero: child(kernel, "det_zero"),
        det_succ: child(kernel, "det_succ"),
        det_one: child(kernel, "det_one"),
        det_eq_det2: child(kernel, "det_eq_det2"),
        det_eq_det3: child(kernel, "det_eq_det3"),
        mat_minor_eval_example: child(kernel, "matMinor_eval_example"),
        det_eval_example: child(kernel, "det_eval_example"),
        det_eval_singular: child(kernel, "det_eval_singular"),
        det_eval_example4: child(kernel, "det_eval_example4"),
        sum_range_head_of_tail_zero: child(kernel, "sumRange_head_of_tail_zero"),
        det_congr: child(kernel, "det_congr"),
        mat_minor_mat_id: child(kernel, "matMinor_matId"),
        det_mat_id: child(kernel, "det_matId"),
        mat_skip_zero: child(kernel, "matSkip_zero"),
        mat_skip_succ_succ: child(kernel, "matSkip_succ_succ"),
        mat_skip_comm: child(kernel, "matSkip_comm"),
        mat_minor_col_comm: child(kernel, "matMinor_col_comm"),
        det_minor_col_comm: child(kernel, "det_minor_col_comm"),
        sum_range_peel_head: child(kernel, "sumRange_peel_head"),
        sum_range_mat_skip: child(kernel, "sumRange_matSkip"),
        unskip: child(kernel, "unskip"),
        unskip_zero: child(kernel, "unskip_zero"),
        unskip_succ_zero: child(kernel, "unskip_succ_zero"),
        unskip_succ_succ: child(kernel, "unskip_succ_succ"),
        unskip_mat_skip: child(kernel, "unskip_matSkip"),
        beq_mat_skip: child(kernel, "beq_matSkip"),
        beq_mat_skip_left: child(kernel, "beq_matSkip_left"),
        alt_sign_succ_add: child(kernel, "altSign_succ_add"),
        ble_flip_of_false: child(kernel, "ble_flip_of_false"),
        unskip_le: child(kernel, "unskip_le"),
        unskip_gt: child(kernel, "unskip_gt"),
        mat_minor_double_comm_lo: child(kernel, "matMinor_double_comm_lo"),
        mat_minor_double_comm_hi: child(kernel, "matMinor_double_comm_hi"),
        det_double_comm_lo: child(kernel, "det_double_comm_lo"),
        det_double_comm_hi: child(kernel, "det_double_comm_hi"),
        mul_perm4: child(kernel, "mul_perm4"),
        laplace_summand: child(kernel, "laplaceSummand"),
        laplace_summand_row_zero: child(kernel, "laplaceSummand_rowZero"),
        laplace_summand_row_i: child(kernel, "laplaceSummand_rowI"),
        laplace_summand_diag: child(kernel, "laplaceSummand_diag"),
        det_row_expansion: child(kernel, "det_row_expansion"),
        mat_minor_row_col_comm: child(kernel, "matMinor_row_col_comm"),
        det_minor_row_col_comm: child(kernel, "det_minor_row_col_comm"),
        det_col_expansion: child(kernel, "det_col_expansion"),
        mat_minor_transpose: child(kernel, "matMinor_transpose"),
        det_transpose: child(kernel, "det_transpose"),
        det_alternating: child(kernel, "det_alternating"),
        det_row_swap: child(kernel, "det_row_swap"),
        det_row_replaced: child(kernel, "det_row_replaced"),
        det_row_zero: child(kernel, "det_row_zero"),
        det_row_smul: child(kernel, "det_row_smul"),
        det_row_multilinear: child(kernel, "det_row_multilinear"),
        det_mat_mul_2: child(kernel, "det_matMul_2"),
        det_row_selection_of_duplicate: child(kernel, "det_row_selection_of_duplicate"),
        det_congr_lt: child(kernel, "det_congr_lt"),
        mat_skip_lt_succ: child(kernel, "matSkip_lt_succ"),
        det_congr_entry_lt: child(kernel, "det_congr_entry_lt"),
        det_row_selection_injective: child(kernel, "det_row_selection_injective"),
        det_row_selection: child(kernel, "det_row_selection"),
        prod_range: child(kernel, "prodRange"),
        prod_range_zero: child(kernel, "prodRange_zero"),
        prod_range_succ: child(kernel, "prodRange_succ"),
        prod_range_shift_front: child(kernel, "prodRange_shiftFront"),
        prod_range_congr: child(kernel, "prodRange_congr"),
        sum_range_mul_right: child(kernel, "sumRange_mul_right"),
        sum_range_mul_left: child(kernel, "sumRange_mul_left"),
        sum_maps: child(kernel, "sumMaps"),
        sum_maps_zero: child(kernel, "sumMaps_zero"),
        sum_maps_succ: child(kernel, "sumMaps_succ"),
        sum_maps_congr: child(kernel, "sumMaps_congr"),
        sum_maps_mul_left: child(kernel, "sumMaps_mul_left"),
        sum_maps_mul_right: child(kernel, "sumMaps_mul_right"),
        mat_set_row: child(kernel, "matSetRow"),
        mat_set_row_at: child(kernel, "matSetRow_at"),
        mat_set_row_off: child(kernel, "matSetRow_off"),
        mat_subst_rows: child(kernel, "matSubstRows"),
        mat_subst_rows_below: child(kernel, "matSubstRows_below"),
        mat_subst_rows_at: child(kernel, "matSubstRows_at"),
        sum_maps_congr_maps_into: child(kernel, "sumMaps_congr_mapsInto"),
        det_mat_mul_expand: child(kernel, "det_matMul_expand"),
        det_mat_mul: child(kernel, "det_matMul"),
        is_zero_b: child(kernel, "isZeroB"),
        is_zero_b_zero: child(kernel, "isZeroB_zero"),
        eq_zero_of_is_zero_b: child(kernel, "eq_zero_of_isZeroB"),
        is_zero_b_of_eq_zero: child(kernel, "isZeroB_of_eq_zero"),
        ne_zero_of_is_zero_b_false: child(kernel, "ne_zero_of_isZeroB_false"),
        row_swap: child(kernel, "rowSwap"),
        row_scale: child(kernel, "rowScale"),
        row_add_mul: child(kernel, "rowAddMul"),
        row_swap_at_left: child(kernel, "rowSwap_at_left"),
        row_swap_at_right: child(kernel, "rowSwap_at_right"),
        row_swap_off: child(kernel, "rowSwap_off"),
        row_scale_at: child(kernel, "rowScale_at"),
        row_scale_off: child(kernel, "rowScale_off"),
        row_add_mul_at: child(kernel, "rowAddMul_at"),
        row_add_mul_off: child(kernel, "rowAddMul_off"),
        row_swap_involutive: child(kernel, "rowSwap_involutive"),
        row_add_mul_inverse: child(kernel, "rowAddMul_inverse"),
        row_scale_inverse: child(kernel, "rowScale_inverse"),
        pivot_search_aux: child(kernel, "pivotSearchAux"),
        pivot_search: child(kernel, "pivotSearch"),
        clear_below_aux: child(kernel, "clearBelowAux"),
        clear_below: child(kernel, "clearBelow"),
        echelon_aux: child(kernel, "echelonAux"),
        row_echelon: child(kernel, "rowEchelon"),
        leading_index_aux: child(kernel, "leadingIndexAux"),
        leading_index: child(kernel, "leadingIndex"),
        echelon_step_ok: child(kernel, "echelonStepOk"),
        is_echelon_aux: child(kernel, "isEchelonAux"),
        is_echelon: child(kernel, "isEchelon"),
        nonzero_row_b: child(kernel, "nonzeroRowB"),
        nonzero_row_b_eq_ble: child(kernel, "nonzeroRowB_eq_ble"),
        nonzero_row_b_zero_cols: child(kernel, "nonzeroRowB_zero_cols"),
        rank: child(kernel, "rank"),
        rank_eq_count_range: child(kernel, "rank_eq_countRange"),
        rank_le_rows: child(kernel, "rank_le_rows"),
        rank_zero_rows: child(kernel, "rank_zero_rows"),
        count_range_nonzero_row_b_zero: child(kernel, "countRange_nonzeroRowB_zero"),
        rank_zero_cols: child(kernel, "rank_zero_cols"),
        pivot_col_search_aux: child(kernel, "pivotColSearchAux"),
        is_pivot_col_b: child(kernel, "isPivotColB"),
        is_pivot_col_b_eq_search: child(kernel, "isPivotColB_eq_search"),
        is_pivot_col_b_zero_rows: child(kernel, "isPivotColB_zero_rows"),
        rank_cols: child(kernel, "rankCols"),
        rank_cols_eq_count_range: child(kernel, "rankCols_eq_countRange"),
        nullity: child(kernel, "nullity"),
        nullity_eq_count_range: child(kernel, "nullity_eq_countRange"),
        rank_nullity: child(kernel, "rank_nullity"),
        rank_cols_le_cols: child(kernel, "rankCols_le_cols"),
        nullity_le_cols: child(kernel, "nullity_le_cols"),
        rank_cols_zero_cols: child(kernel, "rankCols_zero_cols"),
        nullity_zero_cols: child(kernel, "nullity_zero_cols"),
        count_range_is_pivot_col_b_zero_rows: child(kernel, "countRange_isPivotColB_zeroRows"),
        rank_cols_zero_rows: child(kernel, "rankCols_zero_rows"),
        nullity_zero_rows: child(kernel, "nullity_zero_rows"),
        pivot_search_aux_le_rows: child(kernel, "pivotSearchAux_le_rows"),
        pivot_search_le_rows: child(kernel, "pivotSearch_le_rows"),
        pivot_col_of_row: child(kernel, "pivotColOfRow"),
        pivot_col_of_row_eq_leading_index: child(kernel, "pivotColOfRow_eq_leadingIndex"),
        pivot_row_search_aux: child(kernel, "pivotRowSearchAux"),
        pivot_row_of_col: child(kernel, "pivotRowOfCol"),
        pivot_row_of_col_eq_search: child(kernel, "pivotRowOfCol_eq_search"),
        pivot_col_search_aux_eq_ble: child(kernel, "pivotColSearchAux_eq_ble"),
        is_pivot_col_b_eq_ble: child(kernel, "isPivotColB_eq_ble"),
        pivot_row_of_col_lt_rows: child(kernel, "pivotRowOfCol_lt_rows"),
        pivot_row_search_aux_leading_index: child(kernel, "pivotRowSearchAux_leadingIndex"),
        leading_index_pivot_row_of_col: child(kernel, "leadingIndex_pivotRowOfCol"),
        rank_eq_rank_cols_of_pivot_section: child(kernel, "rank_eq_rankCols_of_pivotSection"),
        rank_le_cols_of_pivot_section: child(kernel, "rank_le_cols_of_pivotSection"),
        rank_nullity_rows_of_pivot_section: child(kernel, "rank_nullity_rows_of_pivotSection"),
        pivot_search_aux_ne_zero: child(kernel, "pivotSearchAux_ne_zero"),
        pivot_search_ne_zero: child(kernel, "pivotSearch_ne_zero"),
        pivot_search_aux_column_zero: child(kernel, "pivotSearchAux_column_zero"),
        pivot_search_column_zero: child(kernel, "pivotSearch_column_zero"),
        leading_index_aux_eq_of_first_nonzero: child(kernel, "leadingIndexAux_eq_of_first_nonzero"),
        leading_index_eq_of_first_nonzero: child(kernel, "leadingIndex_eq_of_first_nonzero"),
        leading_index_aux_eq_cols_of_zero: child(kernel, "leadingIndexAux_eq_cols_of_zero"),
        leading_index_eq_cols_of_zero_row: child(kernel, "leadingIndex_eq_cols_of_zero_row"),
        add_neg_div_mul_cancel: child(kernel, "add_neg_div_mul_cancel"),
        clear_below_aux_off: child(kernel, "clearBelowAux_off"),
        clear_below_off: child(kernel, "clearBelow_off"),
        clear_below_aux_zero: child(kernel, "clearBelowAux_zero"),
        clear_below_zero: child(kernel, "clearBelow_zero"),
        clear_below_aux_preserves_zero: child(kernel, "clearBelowAux_preserves_zero"),
        clear_below_preserves_zero: child(kernel, "clearBelow_preserves_zero"),
        row_swap_preserves_zero_range: child(kernel, "rowSwap_preserves_zero_range"),
        leading_index_aux_congr_row: child(kernel, "leadingIndexAux_congr_row"),
        leading_index_congr_row: child(kernel, "leadingIndex_congr_row"),
        clear_below_row_swap_off: child(kernel, "clearBelow_rowSwap_off"),
        pivot_search_aux_ge_start: child(kernel, "pivotSearchAux_ge_start"),
        pivot_search_ge_start: child(kernel, "pivotSearch_ge_start"),
        is_echelon_aux_of_pairs: child(kernel, "isEchelonAux_of_pairs"),
        is_echelon_of_pairs: child(kernel, "isEchelon_of_pairs"),
        echelon_step_ok_of_lt: child(kernel, "echelonStepOk_of_lt"),
        echelon_step_ok_both_cols: child(kernel, "echelonStepOk_both_cols"),
        echelon_aux_is_echelon: child(kernel, "echelonAux_isEchelon"),
        row_echelon_is_echelon: child(kernel, "rowEchelon_isEchelon"),
        lt_of_echelon_step_ok: child(kernel, "lt_of_echelonStepOk"),
        pairs_of_is_echelon_aux: child(kernel, "pairs_of_isEchelonAux"),
        pairs_of_is_echelon: child(kernel, "pairs_of_isEchelon"),
        leading_index_strict_below: child(kernel, "leadingIndex_strict_below"),
        pivot_row_search_aux_eq_of_first: child(kernel, "pivotRowSearchAux_eq_of_first"),
        pivot_row_of_col_eq_of_first: child(kernel, "pivotRowOfCol_eq_of_first"),
        pivot_section_of_is_echelon: child(kernel, "pivotSection_of_isEchelon"),
        rank_eq_rank_cols: child(kernel, "rank_eq_rankCols"),
        rank_le_cols: child(kernel, "rank_le_cols"),
        rank_nullity_rows: child(kernel, "rank_nullity_rows"),
        algebra: algebra_instances::intern_algebra_instances(kernel),
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
        matrix::declare_matrix_laws(&mut d, prelude)?;
        lattice::declare_lattice(&mut d, prelude)?;
        abs::declare_abs(&mut d, prelude)?;
        decide::declare_decide(&mut d, prelude)?;
        decidable::declare_decidable(&mut d, prelude)?;
        sum::declare_sum(&mut d, prelude)?;
        sum_maps::declare_sum_maps_all(&mut d, prelude)?;
        diagonal::declare_diagonal(&mut d, prelude)?;
        polynomial::declare_polynomial(&mut d, prelude)?;
        taylor::declare_taylor(&mut d, prelude)?;
        pow_bridge::declare_pow_bridge(&mut d, prelude)?;
        bernoulli::declare_bernoulli(&mut d, prelude)?;
        vector::declare_vector(&mut d, prelude)?;
        matrix_n::declare_matrix_n(&mut d, prelude)?;
        matrix_transpose::declare_matrix_transpose(&mut d, prelude)?;
        matrix_invertible::declare_matrix_invertible(&mut d, prelude)?;
        matrix_det::declare_matrix_det(&mut d, prelude)?;
        matrix_det_selection::declare_det_row_selection(&mut d, prelude)?;
        matrix_det_mul::declare_matrix_det_mul(&mut d, prelude)?;
        det_mul::declare_det_mul(&mut d, prelude)?;
        echelon::declare_echelon(&mut d, prelude)?;
        rank::declare_rank(&mut d, prelude)?;
        nullity::declare_nullity(&mut d, prelude)?;
        pivot_bound::declare_pivot_bound(&mut d, prelude)?;
        rank_bridge::declare_rank_bridge(&mut d, prelude)?;
        pivot_content::declare_pivot_content(&mut d, prelude)?;
        clear_below::declare_clear_below_post(&mut d, prelude)?;
        leading_index::declare_leading_index_facts(&mut d, prelude)?;
        echelon_invariant::declare_echelon_invariant(&mut d, prelude)?;
        echelon_section::declare_echelon_section(&mut d, prelude)?;
        probability::declare_probability(&mut d, prelude)?;
        algebra_instances::declare_algebra_instances_all(
            d.kernel(),
            &prelude.int.nat.logic,
            &prelude,
            &prelude.int.nat.structures,
            &prelude.algebra,
        )?;
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

#[cfg(test)]
mod matrix_invertible_tests;

#[cfg(test)]
mod sum_maps_tests;

#[cfg(test)]
mod det_mul_tests;

#[cfg(test)]
mod echelon_tests;

#[cfg(test)]
mod rank_tests;

#[cfg(test)]
mod nullity_tests;

#[cfg(test)]
mod rank_bridge_tests;

#[cfg(test)]
mod pivot_content_tests;

#[cfg(test)]
mod clear_below_tests;

#[cfg(test)]
mod leading_index_tests;

#[cfg(test)]
mod echelon_invariant_tests;

#[cfg(test)]
mod echelon_section_tests;

#[cfg(test)]
mod cas_ivt_bridge_tests;

#[cfg(test)]
mod cas_evt_bridge_tests;

#[cfg(test)]
mod cas_extremum_deriv_bridge_tests;

#[cfg(test)]
mod cas_mvt_secant_bridge_tests;

#[cfg(test)]
mod cas_taylor_remainder_bridge_tests;

#[cfg(test)]
mod cas_geometry_bridge_tests;

#[cfg(test)]
mod cas_geometry_mul_bridge_tests;

#[cfg(test)]
mod cas_geometry_frac_bridge_tests;

#[cfg(test)]
mod cas_partial_fractions_bridge_tests;

#[cfg(test)]
mod cas_geometry_pair_bridge_tests;
