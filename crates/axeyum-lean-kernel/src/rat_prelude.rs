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

mod core;
mod defs;
mod laws;
mod ops;
mod statements;

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
    /// `Rat.nat_gauss : ∀ (k a b : Nat), 1 ≤ k → gcd k a = 1 → k ∣ a*b → k ∣ b`
    /// — Gauss's lemma, the coprime-cancellation step uniqueness rests on.
    pub nat_gauss: NameId,
    /// `Rat.nat_dvd_antisymm_pos : ∀ (a b : Nat), 1 ≤ a → 1 ≤ b → a ∣ b → b ∣ a → a = b`.
    pub nat_dvd_antisymm_pos: NameId,
    /// `Rat.nat_mul_right_cancel : ∀ (c a b : Nat), 1 ≤ c → a*c = b*c → a = b`.
    pub nat_mul_right_cancel: NameId,
    /// `Rat.of_nat_inj : ∀ (a b : Nat), Int.ofNat a = Int.ofNat b → a = b`.
    pub of_nat_inj: NameId,
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
        sub: child(kernel, "sub"),
        div: child(kernel, "div"),
        gcd_one_right: child(kernel, "gcd_one_right"),
        nat_gauss: child(kernel, "nat_gauss"),
        nat_dvd_antisymm_pos: child(kernel, "nat_dvd_antisymm_pos"),
        nat_mul_right_cancel: child(kernel, "nat_mul_right_cancel"),
        of_nat_inj: child(kernel, "of_nat_inj"),
        int_mul_right_cancel: child(kernel, "int_mul_right_cancel"),
        int_le_of_mul_le_mul_right: child(kernel, "int_le_of_mul_le_mul_right"),
        int_lt_of_mul_lt_mul_right: child(kernel, "int_lt_of_mul_lt_mul_right"),
        int_mul_le_mul_right: child(kernel, "int_mul_le_mul_right"),
        int_mul_lt_mul_right: child(kernel, "int_mul_lt_mul_right"),
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
